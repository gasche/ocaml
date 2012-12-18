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
    Isigned of Cmm.comparison
  | Iunsigned of Cmm.comparison

type integer_operation =
    Iadd | Isub | Imul | Idiv | Imod
  | Iand | Ior | Ixor | Ilsl | Ilsr | Iasr
  | Icomp of integer_comparison
  | Icheckbound

type test =
    Itruetest
  | Ifalsetest
  | Iinttest of integer_comparison
  | Iinttest_imm of integer_comparison * int
  | Ifloattest of Cmm.comparison * bool
  | Ioddtest
  | Ieventest

type operation =
    Imove
  | Ispill
  | Ireload
  | Iconst_int of nativeint
  | Iconst_float of string
  | Iconst_symbol of string
  | Icall_ind
  | Icall_imm of string
  | Itailcall_ind
  | Itailcall_imm of string
  | Iextcall of string * bool
  | Istackoffset of int
  | Iload of Cmm.memory_chunk * Arch.addressing_mode
  | Istore of Cmm.memory_chunk * Arch.addressing_mode
  | Ialloc of int
  | Iintop of integer_operation
  | Iintop_imm of integer_operation * int
  | Inegf | Iabsf | Iaddf | Isubf | Imulf | Idivf
  | Ifloatofint | Iintoffloat
  | Ispecific of Arch.specific_operation

type instruction =
  { desc: instruction_desc;
    next: instruction;
    arg: Reg.t array;
    res: Reg.t array;
    dbg: Debuginfo.t;
    mutable live: Reg.Set.t }

and instruction_desc =
    Iend
  | Iop of operation
  | Ireturn
  | Iifthenelse of test * instruction * instruction
  | Iswitch of int array * instruction array
  | Iloop of instruction
  | Icatch of int * instruction * instruction
  | Iexit of int
  | Itrywith of instruction * instruction
  | Iraise

type fundecl =
  { fun_name: string;
    fun_args: Reg.t array;
    fun_body: instruction;
    fun_fast: bool;
    fun_dbg : Debuginfo.t }

let rec dummy_instr =
  { desc = Iend;
    next = dummy_instr;
    arg = [||];
    res = [||];
    dbg = Debuginfo.none;
    live = Reg.Set.empty }

let end_instr () =
  { desc = Iend;
    next = dummy_instr;
    arg = [||];
    res = [||];
    dbg = Debuginfo.none;
    live = Reg.Set.empty }

let instr_cons d a r n =
  { desc = d; next = n; arg = a; res = r;
    dbg = Debuginfo.none; live = Reg.Set.empty }

let instr_cons_debug d a r dbg n =
  { desc = d; next = n; arg = a; res = r; dbg = dbg; live = Reg.Set.empty }

let rec instr_iter f i =
  match i.desc with
    Iend -> ()
  | _ ->
      f i;
      match i.desc with
        Iend -> ()
      | Ireturn | Iop(Itailcall_ind) | Iop(Itailcall_imm _) -> ()
      | Iifthenelse(tst, ifso, ifnot) ->
          instr_iter f ifso; instr_iter f ifnot; instr_iter f i.next
      | Iswitch(index, cases) ->
          for i = 0 to Array.length cases - 1 do
            instr_iter f cases.(i)
          done;
          instr_iter f i.next
      | Iloop(body) ->
          instr_iter f body; instr_iter f i.next
      | Icatch(_, body, handler) ->
          instr_iter f body; instr_iter f handler; instr_iter f i.next
      | Iexit _ -> ()
      | Itrywith(body, handler) ->
          instr_iter f body; instr_iter f handler; instr_iter f i.next
      | Iraise -> ()
      | _ ->
          instr_iter f i.next

exception All_regs

module Int = struct
  type t = int
  let compare x y = x - y
end
module IntSet = Set.Make(Int)

let register_usage_table = Hashtbl.create 0
let register_usage s =
  try
    Some (Hashtbl.find register_usage_table s)
  with
  | Not_found ->
     None

let used_registers i =
  let set = ref IntSet.empty in
  let pysical_set set pset = Reg.Set.fold
    (fun reg pset -> match reg with
    | { Reg.loc = Reg.Reg i } -> IntSet.add i pset
    | _ -> pset) set pset in
  let instr_registers i pset =
    let pset = pysical_set i.live pset in
    let pset = pysical_set (Reg.set_of_array i.arg) pset in
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
         begin match register_usage s with
               | None -> raise All_regs
               | Some s -> IntSet.union s pset
         end
      | _ -> pset
    in
    call_registers
  in
  instr_iter (fun i -> set := instr_registers i !set) i;
  !set

let add_register_usage f =
  try
    let r = used_registers f.fun_body in
    Hashtbl.add register_usage_table f.fun_name r
  with
  | All_regs -> ()
