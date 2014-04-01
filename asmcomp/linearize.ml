(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Transformation of Mach code into a list of pseudo-instructions. *)

ouvre Reg
ouvre Mach

type label = int

soit label_counter = ref 99

soit new_label() = incr label_counter; !label_counter

type instruction =
  { modifiable desc: instruction_desc;
    modifiable next: instruction;
    arg: Reg.t array;
    res: Reg.t array;
    dbg: Debuginfo.t;
    live: Reg.Set.t }

et instruction_desc =
    Lend
  | Lop de operation
  | Lreloadretaddr
  | Lreturn
  | Llabel de label
  | Lbranch de label
  | Lcondbranch de test * label
  | Lcondbranch3 de label option * label option * label option
  | Lswitch de label array
  | Lsetuptrap de label
  | Lpushtrap
  | Lpoptrap
  | Lraise de Lambda.raise_kind

soit has_fallthrough = fonction
  | Lreturn | Lbranch _ | Lswitch _ | Lraise _
  | Lop Itailcall_ind | Lop (Itailcall_imm _) -> faux
  | _ -> vrai

type fundecl =
  { fun_name: string;
    fun_body: instruction;
    fun_fast: bool;
    fun_dbg : Debuginfo.t }

(* Invert a test *)

soit invert_integer_test = fonction
    Isigned cmp -> Isigned(Cmm.negate_comparison cmp)
  | Iunsigned cmp -> Iunsigned(Cmm.negate_comparison cmp)

soit invert_test = fonction
    Itruetest -> Ifalsetest
  | Ifalsetest -> Itruetest
  | Iinttest(cmp) -> Iinttest(invert_integer_test cmp)
  | Iinttest_imm(cmp, n) -> Iinttest_imm(invert_integer_test cmp, n)
  | Ifloattest(cmp, neg) -> Ifloattest(cmp, not neg)
  | Ieventest -> Ioddtest
  | Ioddtest -> Ieventest

(* The "end" instruction *)

soit rec end_instr =
  { desc = Lend;
    next = end_instr;
    arg = [||];
    res = [||];
    dbg = Debuginfo.none;
    live = Reg.Set.empty }

(* Cons an instruction (live, debug empty) *)

soit instr_cons d a r n =
  { desc = d; next = n; arg = a; res = r;
    dbg = Debuginfo.none; live = Reg.Set.empty }

(* Cons a simple instruction (arg, res, live empty) *)

soit cons_instr d n =
  { desc = d; next = n; arg = [||]; res = [||];
    dbg = Debuginfo.none; live = Reg.Set.empty }

(* Build an instruction with arg, res, dbg, live taken from
   the given Mach.instruction *)

soit copy_instr d i n =
  { desc = d; next = n;
    arg = i.Mach.arg; res = i.Mach.res;
    dbg = i.Mach.dbg; live = i.Mach.live }

(*
   Label the beginning of the given instruction sequence.
   - If the sequence starts with a branch, jump over it.
   - If the sequence is the end, (tail call position), just do nothing
*)

soit get_label n = filtre n.desc avec
    Lbranch lbl -> (lbl, n)
  | Llabel lbl -> (lbl, n)
  | Lend -> (-1, n)
  | _ -> soit lbl = new_label() dans (lbl, cons_instr (Llabel lbl) n)

(* Check the fallthrough label *)
soit check_label n = filtre n.desc avec
  | Lbranch lbl -> lbl
  | Llabel lbl -> lbl
  | _ -> -1

(* Discard all instructions up to the next label.
   This function is to be called before adding a non-terminating
   instruction. *)

soit rec discard_dead_code n =
  filtre n.desc avec
    Lend -> n
  | Llabel _ -> n
(* Do not discard Lpoptrap or Istackoffset instructions,
   as this may cause a stack imbalance later during assembler generation. *)
  | Lpoptrap -> n
  | Lop(Istackoffset _) -> n
  | _ -> discard_dead_code n.next

(*
   Add a branch in front of a continuation.
   Discard dead code in the continuation.
   Does not insert anything if we're just falling through
   or if we jump to dead code after the end of function (lbl=-1)
*)

soit add_branch lbl n =
  si lbl >= 0 alors
    soit n1 = discard_dead_code n dans
    filtre n1.desc avec
    | Llabel lbl1 quand lbl1 = lbl -> n1
    | _ -> cons_instr (Lbranch lbl) n1
  sinon
    discard_dead_code n

(* Current labels for exit handler *)

soit exit_label = ref []

soit find_exit_label k =
  essaie
    List.assoc k !exit_label
  avec
  | Not_found -> Misc.fatal_error "Linearize.find_exit_label"

soit is_next_catch n = filtre !exit_label avec
| (n0,_)::_  quand n0=n -> vrai
| _ -> faux

(* Linearize an instruction [i]: add it in front of the continuation [n] *)

soit rec linear i n =
  filtre i.Mach.desc avec
    Iend -> n
  | Iop(Itailcall_ind | Itailcall_imm _ tel op) ->
      copy_instr (Lop op) i (discard_dead_code n)
  | Iop(Imove | Ireload | Ispill)
    quand i.Mach.arg.(0).loc = i.Mach.res.(0).loc ->
      linear i.Mach.next n
  | Iop op ->
      copy_instr (Lop op) i (linear i.Mach.next n)
  | Ireturn ->
      soit n1 = copy_instr Lreturn i (discard_dead_code n) dans
      si !Proc.contains_calls
      alors cons_instr Lreloadretaddr n1
      sinon n1
  | Iifthenelse(test, ifso, ifnot) ->
      soit n1 = linear i.Mach.next n dans
      début filtre (ifso.Mach.desc, ifnot.Mach.desc, n1.desc) avec
        Iend, _, Lbranch lbl ->
          copy_instr (Lcondbranch(test, lbl)) i (linear ifnot n1)
      | _, Iend, Lbranch lbl ->
          copy_instr (Lcondbranch(invert_test test, lbl)) i (linear ifso n1)
      | Iexit nfail1, Iexit nfail2, _
            quand is_next_catch nfail1 ->
          soit lbl2 = find_exit_label nfail2 dans
          copy_instr
            (Lcondbranch (invert_test test, lbl2)) i (linear ifso n1)
      | Iexit nfail, _, _ ->
          soit n2 = linear ifnot n1
          et lbl = find_exit_label nfail dans
          copy_instr (Lcondbranch(test, lbl)) i n2
      | _,  Iexit nfail, _ ->
          soit n2 = linear ifso n1 dans
          soit lbl = find_exit_label nfail dans
          copy_instr (Lcondbranch(invert_test test, lbl)) i n2
      | Iend, _, _ ->
          soit (lbl_end, n2) = get_label n1 dans
          copy_instr (Lcondbranch(test, lbl_end)) i (linear ifnot n2)
      | _,  Iend, _ ->
          soit (lbl_end, n2) = get_label n1 dans
          copy_instr (Lcondbranch(invert_test test, lbl_end)) i
                     (linear ifso n2)
      | _, _, _ ->
        (* Should attempt branch prediction here *)
          soit (lbl_end, n2) = get_label n1 dans
          soit (lbl_else, nelse) = get_label (linear ifnot n2) dans
          copy_instr (Lcondbranch(invert_test test, lbl_else)) i
            (linear ifso (add_branch lbl_end nelse))
      fin
  | Iswitch(index, cases) ->
      soit lbl_cases = Array.create (Array.length cases) 0 dans
      soit (lbl_end, n1) = get_label(linear i.Mach.next n) dans
      soit n2 = ref (discard_dead_code n1) dans
      pour i = Array.length cases - 1 descendant_jusqu'a 0 faire
        soit (lbl_case, ncase) =
                get_label(linear cases.(i) (add_branch lbl_end !n2)) dans
        lbl_cases.(i) <- lbl_case;
        n2 := discard_dead_code ncase
      fait;
      (* Switches with 1 and 2 branches have been eliminated earlier.
         Here, we do something for switches with 3 branches. *)
      si Array.length index = 3 alors début
        soit fallthrough_lbl = check_label !n2 dans
        soit find_label n =
          soit lbl = lbl_cases.(index.(n)) dans
          si lbl = fallthrough_lbl alors None sinon Some lbl dans
        copy_instr (Lcondbranch3(find_label 0, find_label 1, find_label 2))
                   i !n2
      fin sinon
        copy_instr (Lswitch(Array.map (fonc n -> lbl_cases.(n)) index)) i !n2
  | Iloop body ->
      soit lbl_head = new_label() dans
      soit n1 = linear i.Mach.next n dans
      soit n2 = linear body (cons_instr (Lbranch lbl_head) n1) dans
      cons_instr (Llabel lbl_head) n2
  | Icatch(io, body, handler) ->
      soit (lbl_end, n1) = get_label(linear i.Mach.next n) dans
      soit (lbl_handler, n2) = get_label(linear handler n1) dans
      exit_label := (io, lbl_handler) :: !exit_label ;
      soit n3 = linear body (add_branch lbl_end n2) dans
      exit_label := List.tl !exit_label;
      n3
  | Iexit nfail ->
      soit n1 = linear i.Mach.next n dans
      soit lbl = find_exit_label nfail dans
      add_branch lbl n1
  | Itrywith(body, handler) ->
      soit (lbl_join, n1) = get_label (linear i.Mach.next n) dans
      soit (lbl_body, n2) =
        get_label (cons_instr Lpushtrap
                    (linear body (cons_instr Lpoptrap n1))) dans
      cons_instr (Lsetuptrap lbl_body)
        (linear handler (add_branch lbl_join n2))
  | Iraise k ->
      copy_instr (Lraise k) i (discard_dead_code n)

soit fundecl f =
  { fun_name = f.Mach.fun_name;
    fun_body = linear f.Mach.fun_body end_instr;
    fun_fast = f.Mach.fun_fast;
    fun_dbg  = f.Mach.fun_dbg }
