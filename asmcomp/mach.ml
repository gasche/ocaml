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

(* Representation of machine code by sequences of pseudoinstructions *)

type integer_comparison =
    Isigned de Cmm.comparison
  | Iunsigned de Cmm.comparison

type integer_operation =
    Iadd | Isub | Imul | Imulh | Idiv | Imod
  | Iand | Ior | Ixor | Ilsl | Ilsr | Iasr
  | Icomp de integer_comparison
  | Icheckbound

type test =
    Itruetest
  | Ifalsetest
  | Iinttest de integer_comparison
  | Iinttest_imm de integer_comparison * int
  | Ifloattest de Cmm.comparison * bool
  | Ioddtest
  | Ieventest

type operation =
    Imove
  | Ispill
  | Ireload
  | Iconst_int de nativeint
  | Iconst_float de string
  | Iconst_symbol de string
  | Iconst_blockheader de nativeint
  | Icall_ind
  | Icall_imm de string
  | Itailcall_ind
  | Itailcall_imm de string
  | Iextcall de string * bool
  | Istackoffset de int
  | Iload de Cmm.memory_chunk * Arch.addressing_mode
  | Istore de Cmm.memory_chunk * Arch.addressing_mode
  | Ialloc de int
  | Iintop de integer_operation
  | Iintop_imm de integer_operation * int
  | Inegf | Iabsf | Iaddf | Isubf | Imulf | Idivf
  | Ifloatofint | Iintoffloat
  | Ispecific de Arch.specific_operation

type instruction =
  { desc: instruction_desc;
    next: instruction;
    arg: Reg.t array;
    res: Reg.t array;
    dbg: Debuginfo.t;
    modifiable live: Reg.Set.t }

et instruction_desc =
    Iend
  | Iop de operation
  | Ireturn
  | Iifthenelse de test * instruction * instruction
  | Iswitch de int array * instruction array
  | Iloop de instruction
  | Icatch de int * instruction * instruction
  | Iexit de int
  | Itrywith de instruction * instruction
  | Iraise de Lambda.raise_kind

type fundecl =
  { fun_name: string;
    fun_args: Reg.t array;
    fun_body: instruction;
    fun_fast: bool;
    fun_dbg : Debuginfo.t }

soit rec dummy_instr =
  { desc = Iend;
    next = dummy_instr;
    arg = [||];
    res = [||];
    dbg = Debuginfo.none;
    live = Reg.Set.empty }

soit end_instr () =
  { desc = Iend;
    next = dummy_instr;
    arg = [||];
    res = [||];
    dbg = Debuginfo.none;
    live = Reg.Set.empty }

soit instr_cons d a r n =
  { desc = d; next = n; arg = a; res = r;
    dbg = Debuginfo.none; live = Reg.Set.empty }

soit instr_cons_debug d a r dbg n =
  { desc = d; next = n; arg = a; res = r; dbg = dbg; live = Reg.Set.empty }

soit rec instr_iter f i =
  filtre i.desc avec
    Iend -> ()
  | _ ->
      f i;
      filtre i.desc avec
        Iend -> ()
      | Ireturn | Iop(Itailcall_ind) | Iop(Itailcall_imm _) -> ()
      | Iifthenelse(tst, ifso, ifnot) ->
          instr_iter f ifso; instr_iter f ifnot; instr_iter f i.next
      | Iswitch(index, cases) ->
          pour i = 0 à Array.length cases - 1 faire
            instr_iter f cases.(i)
          fait;
          instr_iter f i.next
      | Iloop(body) ->
          instr_iter f body; instr_iter f i.next
      | Icatch(_, body, handler) ->
          instr_iter f body; instr_iter f handler; instr_iter f i.next
      | Iexit _ -> ()
      | Itrywith(body, handler) ->
          instr_iter f body; instr_iter f handler; instr_iter f i.next
      | Iraise _ -> ()
      | _ ->
          instr_iter f i.next
