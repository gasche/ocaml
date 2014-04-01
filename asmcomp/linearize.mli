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

type label = int
val new_label: unit -> label

type instruction =
  { modifiable desc: instruction_desc;
    modifiable next: instruction;
    arg: Reg.t array;
    res: Reg.t array;
    dbg: Debuginfo.t;
    live: Reg.Set.t }

et instruction_desc =
    Lend
  | Lop de Mach.operation
  | Lreloadretaddr
  | Lreturn
  | Llabel de label
  | Lbranch de label
  | Lcondbranch de Mach.test * label
  | Lcondbranch3 de label option * label option * label option
  | Lswitch de label array
  | Lsetuptrap de label
  | Lpushtrap
  | Lpoptrap
  | Lraise de Lambda.raise_kind

val has_fallthrough :  instruction_desc -> bool
val end_instr: instruction
val instr_cons:
  instruction_desc -> Reg.t array -> Reg.t array -> instruction -> instruction
val invert_test: Mach.test -> Mach.test

type fundecl =
  { fun_name: string;
    fun_body: instruction;
    fun_fast: bool;
    fun_dbg : Debuginfo.t }

val fundecl: Mach.fundecl -> fundecl
