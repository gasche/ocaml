(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                 Stephen Dolan, University of Cambridge                 *)
(*                                                                        *)
(*   Copyright 2016 Stephen Dolan.                                        *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* Insert instrumentation for afl-fuzz *)

open Lambda
open Cmm

let afl_area_ptr = Cconst_symbol "caml_afl_area_ptr"
let afl_prev_loc = Cconst_symbol "caml_afl_prev_loc"
let afl_map_size = 1 lsl 16

type status = Active | Suspended

let op oper args = Cop (oper, args, Debuginfo.none)

let rec with_afl_logging status b =
  if !status = Suspended
  then instrument status b
  else if !Clflags.afl_inst_ratio < 100 &&
          Random.int 100 >= !Clflags.afl_inst_ratio
  then instrument status b else
  let instrumentation =
    (* The instrumentation that afl-fuzz requires is:

         cur_location = <COMPILE_TIME_RANDOM>;
         shared_mem[cur_location ^ prev_location]++;
         prev_location = cur_location >> 1;

       See http://lcamtuf.coredump.cx/afl/technical_details.txt or
       docs/technical_details.txt in afl-fuzz source for for a full
       description of what's going on.
    *)
    let cur_location = Random.int afl_map_size in
    let cur_pos = Ident.create "pos" in
    let afl_area = Ident.create "shared_mem" in
    Clet(afl_area, op (Cload (Word_int, Asttypes.Mutable)) [afl_area_ptr],
    Clet(cur_pos,  op Cxor [op (Cload (Word_int, Asttypes.Mutable))
      [afl_prev_loc]; Cconst_int cur_location],
    Csequence(
      op (Cstore(Byte_unsigned, Assignment))
         [op Cadda [Cvar afl_area; Cvar cur_pos];
          op Cadda [op (Cload (Byte_unsigned, Asttypes.Mutable))
                       [op Cadda [Cvar afl_area; Cvar cur_pos]];
                    Cconst_int 1]],
      op (Cstore(Word_int, Assignment))
         [afl_prev_loc; Cconst_int (cur_location lsr 1)]))) in
  Csequence(instrumentation, instrument status b)

and instrument st =

(* If e1 and e2 are two subexpressions of a function definition, let
   us say that e1 dominates e2 if all execution paths evaluating e2
   must have evaluated e1 first. For example, e1 dominates e2 in (e1;
   e2) and in (if e1 then e2), but not in (f e1 e2): argument
   evaluation order is unspecified, so e2 may run before e1 in (f e1
   e2).

   We assume that the operations Csuspendafl and Crestoreafl have been
   inserted in the code by the compiler in a way that respects the
   following property: all (restoreafl) are dominated by
   a (suspendafl), and all paths from a (suspendafl) contain
   a (restoreafl).

   Using this assumption, we can optimize away (suspendafl) and
   (restoreafl): instead of writing a mutable reference to
   suspend/restore afl instrumentation at runtime, we can
   *symbolically* evaluate the value of this reference at any point in
   the program. This is done by the code below, which recursively
   traverses the function's code in evaluation order, respecting the
   following invariants:

   - if e1, e2 are immediate subexpressions of the current expression
     and e1 dominates e2, then writes to the symbolic state made by
     e1's instrumentation will affect e2's input state

   - if e1, e2 do not dominate each other, their writes will not
     affect each other (this is ensured by taking fresh copies of the
     symbolic state when evaluating e1 and e2, through the (fresh)
     function below.)

   Note: using mutable state in the implementation is a hack, it would
   be nicer to use a state monad, but then the usual annoyances with
   {List,Array}.map translating into uglier monadic code would apply.
*)

  let fresh st = ref !st in
  let log_child e = with_afl_logging (fresh st) e in
  let instrument_child e = instrument (fresh st) e in
  function
  (* suspend or restore instructions *)
  | Csequence(Cop((Csuspendafl | Crestoreafl) as change, [], _) as oper, body) ->
    begin
      let new_status = match change with
        | Csuspendafl -> Suspended
        | Crestoreafl -> Active
        | _ -> assert false
      in
      st := new_status;
      Csequence(oper, instrument st body)
    end

  (* these cases add logging, as they may be targets of conditional branches *)
  | Cifthenelse (cond, t, f) ->
     let cond = instrument st cond in
     Cifthenelse (cond, log_child t, log_child f)
  | Cloop e ->
     Cloop (log_child e)
  | Ctrywith (e, ex, handler) ->
     let e = instrument st e in
     Ctrywith (e, ex, log_child handler)
  | Cswitch (e, cases, handlers, dbg) ->
     let e = instrument st e in
     Cswitch (e, cases, Array.map log_child handlers, dbg)

  (* these cases add no logging, but instrument subexpressions *)
  | Clet (v, e, body) ->
    let e = instrument st e in
    let body = instrument st body in
    Clet (v, e, body)
  | Cassign (v, e) -> Cassign (v, instrument st e)
  | Ctuple es -> Ctuple (List.map instrument_child es)
  | Cop (op, es, dbg) -> Cop (op, List.map instrument_child es, dbg)
  | Csequence (e1, e2) ->
    let e1 = instrument st e1 in
    let e2 = instrument st e2 in
    Csequence (e1, e2)
  | Ccatch (isrec, cases, body) ->
     let body = instrument st body in
     let instrument_case (nfail, ids, e) = nfail, ids, instrument_child e in
     Ccatch (isrec, List.map instrument_case cases, body)
  | Cexit (ex, args) -> Cexit (ex, List.map instrument_child args)

  (* these are base cases and have no logging *)
  | Cconst_int _ | Cconst_natint _ | Cconst_float _
  | Cconst_symbol _ | Cconst_pointer _ | Cconst_natpointer _
  | Cblockheader _ | Cvar _ as c -> c

(* We assume that instrumentation is always active when a function
   starts. If we wanted to have suspensions range over function calls,
   then we would need to either change the status to
   Active|Suspended|Unknown, or to have a whitelist of function calls
   that always start in suspended state (this might be enough to
   handle CamlinternalOO calls in the class caching machinery, for
   example). *)
let instrument_function c =
  with_afl_logging (ref Active) c

let instrument_initialiser c =
  (* Each instrumented module calls caml_setup_afl at
     initialisation, which is a no-op on the second and subsequent
     calls *)
  with_afl_logging (ref Active)
    (Csequence
       (Cop (Cextcall ("caml_setup_afl", typ_int, false, None),
             [Cconst_int 0],
             Debuginfo.none),
        c))
