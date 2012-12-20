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

(* Liveness analysis.
   Annotate mach code with the set of regs live at each point. *)

open Mach

let live_at_exit = ref []
let find_live_at_exit k =
  try
    List.assoc k !live_at_exit
  with
  | Not_found -> Misc.fatal_error "Spill.find_live_at_exit"

let live_at_break = ref Reg.Set.empty
let live_at_raise = ref Reg.Set.empty

let rec live i finally =
  (* finally is the set of registers live after execution of the
     instruction sequence.
     The result of the function is the set of registers live just
     before the instruction sequence.
     The instruction i is annotated by the set of registers live across
     the instruction. *)
  match i.desc with
    Iend ->
      i.live <- finally;
      finally
  | Ireturn | Iop(Itailcall_ind) | Iop(Itailcall_imm _) ->
      (* i.live remains empty since no regs are live across *)
      Reg.set_of_array i.arg
  | Iifthenelse(test, ifso, ifnot) ->
      let at_join = live i.next finally in
      let at_fork = Reg.Set.union (live ifso at_join) (live ifnot at_join) in
      i.live <- at_fork;
      Reg.add_set_array at_fork i.arg
  | Iswitch(index, cases) ->
      let at_join = live i.next finally in
      let at_fork = ref Reg.Set.empty in
      for i = 0 to Array.length cases - 1 do
        at_fork := Reg.Set.union !at_fork (live cases.(i) at_join)
      done;
      i.live <- !at_fork;
      Reg.add_set_array !at_fork i.arg
  | Iloop(body) ->
      let at_top = ref Reg.Set.empty in
      (* Yes, there are better algorithms, but we'll just iterate till
         reaching a fixpoint. *)
      begin try
        while true do
          let new_at_top = Reg.Set.union !at_top (live body !at_top) in
          if Reg.Set.equal !at_top new_at_top then raise Exit;
          at_top := new_at_top
        done
      with Exit -> ()
      end;
      i.live <- !at_top;
      !at_top
  | Icatch(nfail, body, handler) ->
      let at_join = live i.next finally in
      let before_handler = live handler at_join in
      let before_body =
          live_at_exit := (nfail,before_handler) :: !live_at_exit ;
          let before_body = live body at_join in
          live_at_exit := List.tl !live_at_exit ;
          before_body in
      i.live <- before_body;
      before_body
  | Iexit nfail ->
      let this_live = find_live_at_exit nfail in
      i.live <- this_live ;
      this_live
  | Itrywith(body, handler) ->
      let at_join = live i.next finally in
      let before_handler = live handler at_join in
      let saved_live_at_raise = !live_at_raise in
      live_at_raise := Reg.Set.remove Proc.loc_exn_bucket before_handler;
      let before_body = live body at_join in
      live_at_raise := saved_live_at_raise;
      i.live <- before_body;
      before_body
  | Iraise ->
      (* i.live remains empty since no regs are live across *)
      Reg.add_set_array !live_at_raise i.arg
  | _ ->
      let across_after = Reg.diff_set_array (live i.next finally) i.res in
      let across =
        match i.desc with
          Iop Icall_ind | Iop(Icall_imm _) | Iop(Iextcall _)
        | Iop(Iintop Icheckbound) | Iop(Iintop_imm(Icheckbound, _)) ->
            (* The function call may raise an exception, branching to the
               nearest enclosing try ... with. Similarly for bounds checks.
               Hence, everything that must be live at the beginning of
               the exception handler must also be live across this instr. *)
             Reg.Set.union across_after !live_at_raise
         | _ ->
             across_after in
      i.live <- across;
      Reg.add_set_array across i.arg

let fundecl ppf f =
  let initially_live = live f.fun_body Reg.Set.empty in
  (* Sanity check: only function parameters can be live at entrypoint *)
  let wrong_live = Reg.Set.diff initially_live (Reg.set_of_array f.fun_args) in
  if not (Reg.Set.is_empty wrong_live) then begin
    Format.fprintf ppf "%a@." Printmach.regset wrong_live;
    Misc.fatal_error "Liveness.fundecl"
  end


(* why not here ? *)
exception All_regs

let used_registers f =
  let set = ref IntSet.empty in
  let pysical_set set pset = Reg.Set.fold
    (fun reg pset -> match reg with
    | { Reg.loc = Reg.Reg i } -> IntSet.add i pset
    | _ -> pset) set pset in
  let instr_registers i pset =
    let destroyed = Proc.destroyed_at_oper i.desc in
    let pset = pysical_set (Reg.set_of_array destroyed) pset in
    let pset = pysical_set (Reg.set_of_array i.res) pset in
    let call_registers =
      match i.desc with
      | Iop( Icall_ind | Itailcall_ind |
             Iextcall _ ) ->
         (* In fact not all registers are lost when doing extcall
            (like on windows) see proc.ml
            (this is sufficient for my quick and dirty hack) *)
         raise All_regs
      | Iop( Icall_imm s | Itailcall_imm s) ->
         if s = f.fun_name
         then pset
         else
           begin match register_usage s with
                 | None -> raise All_regs
                 | Some s -> IntSet.union s pset
           end
      | _ -> pset
    in
    call_registers
  in
  instr_iter (fun i -> set := instr_registers i !set) f.fun_body;
  !set

let used_registers f =
  try Some (used_registers f) with
  | All_regs -> None
