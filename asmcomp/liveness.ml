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

ouvre Mach

soit live_at_exit = ref []
soit find_live_at_exit k =
  essaie
    List.assoc k !live_at_exit
  avec
  | Not_found -> Misc.fatal_error "Spill.find_live_at_exit"

soit live_at_break = ref Reg.Set.empty
soit live_at_raise = ref Reg.Set.empty

soit rec live i finally =
  (* finally is the set of registers live after execution of the
     instruction sequence.
     The result of the function is the set of registers live just
     before the instruction sequence.
     The instruction i is annotated by the set of registers live across
     the instruction. *)
  filtre i.desc avec
    Iend ->
      i.live <- finally;
      finally
  | Ireturn | Iop(Itailcall_ind) | Iop(Itailcall_imm _) ->
      (* i.live remains empty since no regs are live across *)
      Reg.set_of_array i.arg
  | Iifthenelse(test, ifso, ifnot) ->
      soit at_join = live i.next finally dans
      soit at_fork = Reg.Set.union (live ifso at_join) (live ifnot at_join) dans
      i.live <- at_fork;
      Reg.add_set_array at_fork i.arg
  | Iswitch(index, cases) ->
      soit at_join = live i.next finally dans
      soit at_fork = ref Reg.Set.empty dans
      pour i = 0 à Array.length cases - 1 faire
        at_fork := Reg.Set.union !at_fork (live cases.(i) at_join)
      fait;
      i.live <- !at_fork;
      Reg.add_set_array !at_fork i.arg
  | Iloop(body) ->
      soit at_top = ref Reg.Set.empty dans
      (* Yes, there are better algorithms, but we'll just iterate till
         reaching a fixpoint. *)
      début essaie
        pendant_que vrai faire
          soit new_at_top = Reg.Set.union !at_top (live body !at_top) dans
          si Reg.Set.equal !at_top new_at_top alors raise Exit;
          at_top := new_at_top
        fait
      avec Exit -> ()
      fin;
      i.live <- !at_top;
      !at_top
  | Icatch(nfail, body, handler) ->
      soit at_join = live i.next finally dans
      soit before_handler = live handler at_join dans
      soit before_body =
          live_at_exit := (nfail,before_handler) :: !live_at_exit ;
          soit before_body = live body at_join dans
          live_at_exit := List.tl !live_at_exit ;
          before_body dans
      i.live <- before_body;
      before_body
  | Iexit nfail ->
      soit this_live = find_live_at_exit nfail dans
      i.live <- this_live ;
      this_live
  | Itrywith(body, handler) ->
      soit at_join = live i.next finally dans
      soit before_handler = live handler at_join dans
      soit saved_live_at_raise = !live_at_raise dans
      live_at_raise := Reg.Set.remove Proc.loc_exn_bucket before_handler;
      soit before_body = live body at_join dans
      live_at_raise := saved_live_at_raise;
      i.live <- before_body;
      before_body
  | Iraise _ ->
      (* i.live remains empty since no regs are live across *)
      Reg.add_set_array !live_at_raise i.arg
  | _ ->
      soit across_after = Reg.diff_set_array (live i.next finally) i.res dans
      soit across =
        filtre i.desc avec
          Iop Icall_ind | Iop(Icall_imm _) | Iop(Iextcall _)
        | Iop(Iintop Icheckbound) | Iop(Iintop_imm(Icheckbound, _)) ->
            (* The function call may raise an exception, branching to the
               nearest enclosing try ... with. Similarly for bounds checks.
               Hence, everything that must be live at the beginning of
               the exception handler must also be live across this instr. *)
             Reg.Set.union across_after !live_at_raise
         | _ ->
             across_after dans
      i.live <- across;
      Reg.add_set_array across i.arg

soit fundecl ppf f =
  soit initially_live = live f.fun_body Reg.Set.empty dans
  (* Sanity check: only function parameters can be live at entrypoint *)
  soit wrong_live = Reg.Set.diff initially_live (Reg.set_of_array f.fun_args) dans
  si not (Reg.Set.is_empty wrong_live) alors début
    Format.fprintf ppf "%a@." Printmach.regset wrong_live;
    Misc.fatal_error "Liveness.fundecl"
  fin
