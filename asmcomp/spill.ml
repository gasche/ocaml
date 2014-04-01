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

(* Insertion of moves to suggest possible spilling / reloading points
   before register allocation. *)

ouvre Reg
ouvre Mach

(* We say that a register is "destroyed" if it is live across a construct
   that potentially destroys all physical registers: function calls or
   try...with constructs.

   The "destroyed" registers must therefore reside in the stack during
   these instructions.. We will insert spills (stores) just after they
   are defined, and reloads just before their first use following a
   "destroying" construct.

   Instructions with more live registers than actual registers also
   "destroy" registers: we mark as "destroyed" the registers live
   across the instruction that haven't been used for the longest time.
   These registers will be spilled and reloaded as described above. *)

(* Association of spill registers to registers *)

soit spill_env = ref (Reg.Map.empty : Reg.t Reg.Map.t)

soit spill_reg r =
  essaie
    Reg.Map.find r !spill_env
  avec Not_found ->
    soit spill_r = Reg.create r.typ dans
    spill_r.spill <- vrai;
    si not (Reg.anonymous r) alors spill_r.raw_name <- r.raw_name;
    spill_env := Reg.Map.add r spill_r !spill_env;
    spill_r

(* Record the position of last use of registers *)

soit use_date = ref (Reg.Map.empty : int Reg.Map.t)
soit current_date = ref 0

soit record_use regv =
  pour i = 0 à Array.length regv - 1 faire
    soit r = regv.(i) dans
    soit prev_date = essaie Reg.Map.find r !use_date avec Not_found -> 0 dans
    si !current_date > prev_date alors
      use_date := Reg.Map.add r !current_date !use_date
  fait

(* Check if the register pressure overflows the maximum pressure allowed
   at that point. If so, spill enough registers to lower the pressure. *)

soit add_superpressure_regs op live_regs res_regs spilled =
  soit max_pressure = Proc.max_register_pressure op dans
  soit regs = Reg.add_set_array live_regs res_regs dans
  (* Compute the pressure in each register class *)
  soit pressure = Array.create Proc.num_register_classes 0 dans
  Reg.Set.iter
    (fonc r ->
      si Reg.Set.mem r spilled alors () sinon début
        filtre r.loc avec
          Stack s -> ()
        | _ -> soit c = Proc.register_class r dans
               pressure.(c) <- pressure.(c) + 1
      fin)
    regs;
  (* Check if pressure is exceeded for each class. *)
  soit rec check_pressure cl spilled =
    si cl >= Proc.num_register_classes alors
      spilled
    sinon si pressure.(cl) <= max_pressure.(cl) alors
      check_pressure (cl+1) spilled
    sinon début
      (* Find the least recently used, unspilled, unallocated, live register
         in the class *)
      soit lru_date = ref 1000000 et lru_reg = ref Reg.dummy dans
      Reg.Set.iter
        (fonc r ->
          si Proc.register_class r = cl &&
             not (Reg.Set.mem r spilled) &&
             r.loc = Unknown
          alors début
            essaie
              soit d = Reg.Map.find r !use_date dans
              si d < !lru_date alors début
                lru_date := d;
                lru_reg := r
              fin
            avec Not_found ->                 (* Should not happen *)
              ()
          fin)
        live_regs;
      si !lru_reg != Reg.dummy alors début
        pressure.(cl) <- pressure.(cl) - 1;
        check_pressure cl (Reg.Set.add !lru_reg spilled)
      fin sinon
        (* Couldn't find any spillable register, give up for this class *)
        check_pressure (cl+1) spilled
    fin dans
  check_pressure 0 spilled

(* A-list recording what is destroyed at if-then-else points. *)

soit destroyed_at_fork = ref ([] : (instruction * Reg.Set.t) list)

(* First pass: insert reload instructions based on an approximation of
   what is destroyed at pressure points. *)

soit add_reloads regset i =
  Reg.Set.fold
    (fonc r i -> instr_cons (Iop Ireload) [|spill_reg r|] [|r|] i)
    regset i

soit reload_at_exit = ref []

soit find_reload_at_exit k =
  essaie
    List.assoc k !reload_at_exit
  avec
  | Not_found -> Misc.fatal_error "Spill.find_reload_at_exit"

soit reload_at_break = ref Reg.Set.empty

soit rec reload i before =
  incr current_date;
  record_use i.arg;
  record_use i.res;
  filtre i.desc avec
    Iend ->
      (i, before)
  | Ireturn | Iop(Itailcall_ind) | Iop(Itailcall_imm _) ->
      (add_reloads (Reg.inter_set_array before i.arg) i,
       Reg.Set.empty)
  | Iop(Icall_ind | Icall_imm _ | Iextcall(_, vrai)) ->
      (* All regs live across must be spilled *)
      soit (new_next, finally) = reload i.next i.live dans
      (add_reloads (Reg.inter_set_array before i.arg)
                   (instr_cons_debug i.desc i.arg i.res i.dbg new_next),
       finally)
  | Iop op ->
      soit new_before =
        (* Quick check to see if the register pressure is below the maximum *)
        si Reg.Set.cardinal i.live + Array.length i.res <=
           Proc.safe_register_pressure op
        alors before
        sinon add_superpressure_regs op i.live i.res before dans
      soit after =
        Reg.diff_set_array (Reg.diff_set_array new_before i.arg) i.res dans
      soit (new_next, finally) = reload i.next after dans
      (add_reloads (Reg.inter_set_array new_before i.arg)
                   (instr_cons_debug i.desc i.arg i.res i.dbg new_next),
       finally)
  | Iifthenelse(test, ifso, ifnot) ->
      soit at_fork = Reg.diff_set_array before i.arg dans
      soit date_fork = !current_date dans
      soit (new_ifso, after_ifso) = reload ifso at_fork dans
      soit date_ifso = !current_date dans
      current_date := date_fork;
      soit (new_ifnot, after_ifnot) = reload ifnot at_fork dans
      current_date := max date_ifso !current_date;
      soit (new_next, finally) =
        reload i.next (Reg.Set.union after_ifso after_ifnot) dans
      soit new_i =
        instr_cons (Iifthenelse(test, new_ifso, new_ifnot))
        i.arg i.res new_next dans
      destroyed_at_fork := (new_i, at_fork) :: !destroyed_at_fork;
      (add_reloads (Reg.inter_set_array before i.arg) new_i,
       finally)
  | Iswitch(index, cases) ->
      soit at_fork = Reg.diff_set_array before i.arg dans
      soit date_fork = !current_date dans
      soit date_join = ref 0 dans
      soit after_cases = ref Reg.Set.empty dans
      soit new_cases =
        Array.map
          (fonc c ->
            current_date := date_fork;
            soit (new_c, after_c) = reload c at_fork dans
            after_cases := Reg.Set.union !after_cases after_c;
            date_join := max !date_join !current_date;
            new_c)
          cases dans
      current_date := !date_join;
      soit (new_next, finally) = reload i.next !after_cases dans
      (add_reloads (Reg.inter_set_array before i.arg)
                   (instr_cons (Iswitch(index, new_cases))
                               i.arg i.res new_next),
       finally)
  | Iloop(body) ->
      soit date_start = !current_date dans
      soit at_head = ref before dans
      soit final_body = ref body dans
      début essaie
        pendant_que vrai faire
          current_date := date_start;
          soit (new_body, new_at_head) = reload body !at_head dans
          soit merged_at_head = Reg.Set.union !at_head new_at_head dans
          si Reg.Set.equal merged_at_head !at_head alors début
            final_body := new_body;
            raise Exit
          fin;
          at_head := merged_at_head
        fait
      avec Exit -> ()
      fin;
      soit (new_next, finally) = reload i.next Reg.Set.empty dans
      (instr_cons (Iloop(!final_body)) i.arg i.res new_next,
       finally)
  | Icatch(nfail, body, handler) ->
      soit new_set = ref Reg.Set.empty dans
      reload_at_exit := (nfail, new_set) :: !reload_at_exit ;
      soit (new_body, after_body) = reload body before dans
      soit at_exit = !new_set dans
      reload_at_exit := List.tl !reload_at_exit ;
      soit (new_handler, after_handler) = reload handler at_exit dans
      soit (new_next, finally) =
        reload i.next (Reg.Set.union after_body after_handler) dans
      (instr_cons (Icatch(nfail, new_body, new_handler)) i.arg i.res new_next,
       finally)
  | Iexit nfail ->
      soit set = find_reload_at_exit nfail dans
      set := Reg.Set.union !set before;
      (i, Reg.Set.empty)
  | Itrywith(body, handler) ->
      soit (new_body, after_body) = reload body before dans
      soit (new_handler, after_handler) = reload handler handler.live dans
      soit (new_next, finally) =
        reload i.next (Reg.Set.union after_body after_handler) dans
      (instr_cons (Itrywith(new_body, new_handler)) i.arg i.res new_next,
       finally)
  | Iraise _ ->
      (add_reloads (Reg.inter_set_array before i.arg) i, Reg.Set.empty)

(* Second pass: add spill instructions based on what we've decided to reload.
   That is, any register that may be reloaded in the future must be spilled
   just after its definition. *)

(*
   As an optimization, if a register needs to be spilled in one branch of
   a conditional but not in the other, then we spill it late on entrance
   in the branch that needs it spilled.
   NB: This strategy is turned off in loops, as it may prevent a spill from
   being lifted up all the way out of the loop.
   NB again: This strategy is also off in switch arms
   as it generates many useless spills inside switch arms
   NB ter: is it the same thing for catch bodies ?
*)


soit spill_at_exit = ref []
soit find_spill_at_exit k =
  essaie
    List.assoc k !spill_at_exit
  avec
  | Not_found -> Misc.fatal_error "Spill.find_spill_at_exit"

soit spill_at_raise = ref Reg.Set.empty
soit inside_loop = ref faux
et inside_arm = ref faux
et inside_catch = ref faux

soit add_spills regset i =
  Reg.Set.fold
    (fonc r i -> instr_cons (Iop Ispill) [|r|] [|spill_reg r|] i)
    regset i

soit rec spill i finally =
  filtre i.desc avec
    Iend ->
      (i, finally)
  | Ireturn | Iop(Itailcall_ind) | Iop(Itailcall_imm _) ->
      (i, Reg.Set.empty)
  | Iop Ireload ->
      soit (new_next, after) = spill i.next finally dans
      soit before1 = Reg.diff_set_array after i.res dans
      (instr_cons i.desc i.arg i.res new_next,
       Reg.add_set_array before1 i.res)
  | Iop _ ->
      soit (new_next, after) = spill i.next finally dans
      soit before1 = Reg.diff_set_array after i.res dans
      soit before =
        filtre i.desc avec
          Iop Icall_ind | Iop(Icall_imm _) | Iop(Iextcall _)
        | Iop(Iintop Icheckbound) | Iop(Iintop_imm(Icheckbound, _)) ->
            Reg.Set.union before1 !spill_at_raise
        | _ ->
            before1 dans
      (instr_cons_debug i.desc i.arg i.res i.dbg
                  (add_spills (Reg.inter_set_array after i.res) new_next),
       before)
  | Iifthenelse(test, ifso, ifnot) ->
      soit (new_next, at_join) = spill i.next finally dans
      soit (new_ifso, before_ifso) = spill ifso at_join dans
      soit (new_ifnot, before_ifnot) = spill ifnot at_join dans
      si
        !inside_loop || !inside_arm
      alors
        (instr_cons (Iifthenelse(test, new_ifso, new_ifnot))
                     i.arg i.res new_next,
         Reg.Set.union before_ifso before_ifnot)
      sinon début
        soit destroyed = List.assq i !destroyed_at_fork dans
        soit spill_ifso_branch =
          Reg.Set.diff (Reg.Set.diff before_ifso before_ifnot) destroyed
        et spill_ifnot_branch =
          Reg.Set.diff (Reg.Set.diff before_ifnot before_ifso) destroyed dans
        (instr_cons
            (Iifthenelse(test, add_spills spill_ifso_branch new_ifso,
                               add_spills spill_ifnot_branch new_ifnot))
            i.arg i.res new_next,
         Reg.Set.diff (Reg.Set.diff (Reg.Set.union before_ifso before_ifnot)
                                    spill_ifso_branch)
                       spill_ifnot_branch)
      fin
  | Iswitch(index, cases) ->
      soit (new_next, at_join) = spill i.next finally dans
      soit saved_inside_arm = !inside_arm dans
      inside_arm := vrai ;
      soit before = ref Reg.Set.empty dans
      soit new_cases =
        Array.map
          (fonc c ->
            soit (new_c, before_c) = spill c at_join dans
            before := Reg.Set.union !before before_c;
            new_c)
          cases dans
      inside_arm := saved_inside_arm ;
      (instr_cons (Iswitch(index, new_cases)) i.arg i.res new_next,
       !before)
  | Iloop(body) ->
      soit (new_next, _) = spill i.next finally dans
      soit saved_inside_loop = !inside_loop dans
      inside_loop := vrai;
      soit at_head = ref Reg.Set.empty dans
      soit final_body = ref body dans
      début essaie
        pendant_que vrai faire
          soit (new_body, before_body) = spill body !at_head dans
          soit new_at_head = Reg.Set.union !at_head before_body dans
          si Reg.Set.equal new_at_head !at_head alors début
            final_body := new_body; raise Exit
          fin;
          at_head := new_at_head
        fait
      avec Exit -> ()
      fin;
      inside_loop := saved_inside_loop;
      (instr_cons (Iloop(!final_body)) i.arg i.res new_next,
       !at_head)
  | Icatch(nfail, body, handler) ->
      soit (new_next, at_join) = spill i.next finally dans
      soit (new_handler, at_exit) = spill handler at_join dans
      soit saved_inside_catch = !inside_catch dans
      inside_catch := vrai ;
      spill_at_exit := (nfail, at_exit) :: !spill_at_exit ;
      soit (new_body, before) = spill body at_join dans
      spill_at_exit := List.tl !spill_at_exit;
      inside_catch := saved_inside_catch ;
      (instr_cons (Icatch(nfail, new_body, new_handler)) i.arg i.res new_next,
       before)
  | Iexit nfail ->
      (i, find_spill_at_exit nfail)
  | Itrywith(body, handler) ->
      soit (new_next, at_join) = spill i.next finally dans
      soit (new_handler, before_handler) = spill handler at_join dans
      soit saved_spill_at_raise = !spill_at_raise dans
      spill_at_raise := before_handler;
      soit (new_body, before_body) = spill body at_join dans
      spill_at_raise := saved_spill_at_raise;
      (instr_cons (Itrywith(new_body, new_handler)) i.arg i.res new_next,
       before_body)
  | Iraise _ ->
      (i, !spill_at_raise)

(* Entry point *)

soit fundecl f =
  spill_env := Reg.Map.empty;
  use_date := Reg.Map.empty;
  current_date := 0;
  soit (body1, _) = reload f.fun_body Reg.Set.empty dans
  soit (body2, tospill_at_entry) = spill body1 Reg.Set.empty dans
  soit new_body =
    add_spills (Reg.inter_set_array tospill_at_entry f.fun_args) body2 dans
  spill_env := Reg.Map.empty;
  use_date := Reg.Map.empty;
  { fun_name = f.fun_name;
    fun_args = f.fun_args;
    fun_body = new_body;
    fun_fast = f.fun_fast;
    fun_dbg  = f.fun_dbg }
