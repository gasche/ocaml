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

(* Renaming of registers at reload points to split live ranges. *)

ouvre Reg
ouvre Mach

(* Substitutions are represented by register maps *)

type subst = Reg.t Reg.Map.t

soit subst_reg r (sub : subst) =
  essaie
    Reg.Map.find r sub
  avec Not_found ->
    r

soit subst_regs rv sub =
  filtre sub avec
    None -> rv
  | Some s ->
      soit n = Array.length rv dans
      soit nv = Array.create n Reg.dummy dans
      pour i = 0 à n-1 faire nv.(i) <- subst_reg rv.(i) s fait;
      nv

(* We maintain equivalence classes of registers using a standard
   union-find algorithm *)

soit equiv_classes = ref (Reg.Map.empty : Reg.t Reg.Map.t)

soit rec repres_reg r =
  essaie
    repres_reg(Reg.Map.find r !equiv_classes)
  avec Not_found ->
    r

soit repres_regs rv =
  soit n = Array.length rv dans
  pour i = 0 à n-1 faire rv.(i) <- repres_reg rv.(i) fait

(* Identify two registers.
   The second register is chosen as canonical representative. *)

soit identify r1 r2 =
  soit repres1 = repres_reg r1 dans
  soit repres2 = repres_reg r2 dans
  si repres1.stamp = repres2.stamp alors () sinon début
    equiv_classes := Reg.Map.add repres1 repres2 !equiv_classes
  fin

(* Identify the image of a register by two substitutions.
   Be careful to use the original register as canonical representative
   in case it does not belong to the domain of one of the substitutions. *)

soit identify_sub sub1 sub2 reg =
  essaie
    soit r1 = Reg.Map.find reg sub1 dans
    essaie
      soit r2 = Reg.Map.find reg sub2 dans
      identify r1 r2
    avec Not_found ->
      identify r1 reg
  avec Not_found ->
    essaie
      soit r2 = Reg.Map.find reg sub2 dans
      identify r2 reg
    avec Not_found ->
      ()

(* Identify registers so that the two substitutions agree on the
   registers live before the given instruction. *)

soit merge_substs sub1 sub2 i =
  filtre (sub1, sub2) avec
    (None, None) -> None
  | (Some s1, None) -> sub1
  | (None, Some s2) -> sub2
  | (Some s1, Some s2) ->
      Reg.Set.iter (identify_sub s1 s2) (Reg.add_set_array i.live i.arg);
      sub1

(* Same, for N substitutions *)

soit merge_subst_array subv instr =
  soit rec find_one_subst i =
    si i >= Array.length subv alors None sinon début
      filtre subv.(i) avec
        None -> find_one_subst (i+1)
      | Some i' tel sub ->
          pour j = i+1 à Array.length subv - 1 faire
            filtre subv.(j) avec
              None -> ()
            | Some j' ->
                Reg.Set.iter (identify_sub i' j')
                             (Reg.add_set_array instr.live instr.arg)
          fait;
          sub
    fin dans
  find_one_subst 0

(* First pass: rename registers at reload points *)

soit exit_subst = ref []

soit find_exit_subst k =
  essaie
    List.assoc k !exit_subst avec
  | Not_found -> Misc.fatal_error "Split.find_exit_subst"

soit rec rename i sub =
  filtre i.desc avec
    Iend ->
      (i, sub)
  | Ireturn | Iop(Itailcall_ind) | Iop(Itailcall_imm _) ->
      (instr_cons i.desc (subst_regs i.arg sub) [||] i.next,
       None)
  | Iop Ireload quand i.res.(0).loc = Unknown ->
      début filtre sub avec
        None -> rename i.next sub
      | Some s ->
          soit oldr = i.res.(0) dans
          soit newr = Reg.clone i.res.(0) dans
          soit (new_next, sub_next) =
            rename i.next (Some(Reg.Map.add oldr newr s)) dans
          (instr_cons i.desc i.arg [|newr|] new_next,
           sub_next)
      fin
  | Iop _ ->
      soit (new_next, sub_next) = rename i.next sub dans
      (instr_cons_debug i.desc (subst_regs i.arg sub) (subst_regs i.res sub)
                        i.dbg new_next,
       sub_next)
  | Iifthenelse(tst, ifso, ifnot) ->
      soit (new_ifso, sub_ifso) = rename ifso sub dans
      soit (new_ifnot, sub_ifnot) = rename ifnot sub dans
      soit (new_next, sub_next) =
        rename i.next (merge_substs sub_ifso sub_ifnot i.next) dans
      (instr_cons (Iifthenelse(tst, new_ifso, new_ifnot))
                  (subst_regs i.arg sub) [||] new_next,
       sub_next)
  | Iswitch(index, cases) ->
      soit new_sub_cases = Array.map (fonc c -> rename c sub) cases dans
      soit sub_merge =
        merge_subst_array (Array.map (fonc (n, s) -> s) new_sub_cases) i.next dans
      soit (new_next, sub_next) = rename i.next sub_merge dans
      (instr_cons (Iswitch(index, Array.map (fonc (n, s) -> n) new_sub_cases))
                  (subst_regs i.arg sub) [||] new_next,
       sub_next)
  | Iloop(body) ->
      soit (new_body, sub_body) = rename body sub dans
      soit (new_next, sub_next) = rename i.next (merge_substs sub sub_body i) dans
      (instr_cons (Iloop(new_body)) [||] [||] new_next,
       sub_next)
  | Icatch(nfail, body, handler) ->
      soit new_subst = ref None dans
      exit_subst := (nfail, new_subst) :: !exit_subst ;
      soit (new_body, sub_body) = rename body sub dans
      soit sub_entry_handler = !new_subst dans
      exit_subst := List.tl !exit_subst;
      soit (new_handler, sub_handler) = rename handler sub_entry_handler dans
      soit (new_next, sub_next) =
        rename i.next (merge_substs sub_body sub_handler i.next) dans
      (instr_cons (Icatch(nfail, new_body, new_handler)) [||] [||] new_next,
       sub_next)
  | Iexit nfail ->
      soit r = find_exit_subst nfail dans
      r := merge_substs !r sub i;
      (i, None)
  | Itrywith(body, handler) ->
      soit (new_body, sub_body) = rename body sub dans
      soit (new_handler, sub_handler) = rename handler sub dans
      soit (new_next, sub_next) =
        rename i.next (merge_substs sub_body sub_handler i.next) dans
      (instr_cons (Itrywith(new_body, new_handler)) [||] [||] new_next,
       sub_next)
  | Iraise k ->
      (instr_cons_debug (Iraise k) (subst_regs i.arg sub) [||] i.dbg i.next,
       None)

(* Second pass: replace registers by their final representatives *)

soit set_repres i =
  instr_iter (fonc i -> repres_regs i.arg; repres_regs i.res) i

(* Entry point *)

soit fundecl f =
  equiv_classes := Reg.Map.empty;
  soit new_args = Array.copy f.fun_args dans
  soit (new_body, sub_body) = rename f.fun_body (Some Reg.Map.empty) dans
  repres_regs new_args;
  set_repres new_body;
  equiv_classes := Reg.Map.empty;
  { fun_name = f.fun_name;
    fun_args = new_args;
    fun_body = new_body;
    fun_fast = f.fun_fast;
    fun_dbg  = f.fun_dbg }
