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

(* Selection of pseudo-instructions, assignment of pseudo-registers,
   sequentialization. *)

type environment = (Ident.t, Reg.t array) Tbl.t

val size_expr : environment -> Cmm.expression -> int

classe virtuelle selector_generic : objet
  (* The following methods must or can be overridden by the processor
     description *)
  méthode virtuelle is_immediate : int -> bool
    (* Must be defined to indicate whether a constant is a suitable
       immediate operand to arithmetic instructions *)
  méthode virtuelle select_addressing :
    Cmm.memory_chunk -> Cmm.expression -> Arch.addressing_mode * Cmm.expression
    (* Must be defined to select addressing modes *)
  méthode is_simple_expr: Cmm.expression -> bool
    (* Can be overridden to reflect special extcalls known to be pure *)
  méthode select_operation :
    Cmm.operation ->
    Cmm.expression list -> Mach.operation * Cmm.expression list
    (* Can be overridden to deal with special arithmetic instructions *)
  méthode select_condition : Cmm.expression -> Mach.test * Cmm.expression
    (* Can be overridden to deal with special test instructions *)
  méthode select_store :
    Arch.addressing_mode -> Cmm.expression -> Mach.operation * Cmm.expression
    (* Can be overridden to deal with special store constant instructions *)
  méthode regs_for : Cmm.machtype -> Reg.t array
    (* Return an array of fresh registers of the given type.
       Default implementation is like Reg.createv.
       Can be overridden if float values are stored as pairs of
       integer registers. *)
  méthode insert_op :
    Mach.operation -> Reg.t array -> Reg.t array -> Reg.t array
    (* Can be overridden to deal with 2-address instructions
       or instructions with hardwired input/output registers *)
  méthode insert_op_debug :
    Mach.operation -> Debuginfo.t -> Reg.t array -> Reg.t array -> Reg.t array
    (* Can be overridden to deal with 2-address instructions
       or instructions with hardwired input/output registers *)
  méthode emit_extcall_args :
    environment -> Cmm.expression list -> Reg.t array * int
    (* Can be overridden to deal with stack-based calling conventions *)
  méthode emit_stores :
    environment -> Cmm.expression list -> Reg.t array -> unit
    (* Fill a freshly allocated block.  Can be overridden for architectures
       that do not provide Arch.offset_addressing. *)

  (* The following method is the entry point and should not be overridden *)
  méthode emit_fundecl : Cmm.fundecl -> Mach.fundecl

  (* The following methods should not be overridden.  They cannot be
     declared "private" in the current implementation because they
     are not always applied to "self", but ideally they should be private. *)
  méthode extract : Mach.instruction
  méthode insert : Mach.instruction_desc -> Reg.t array -> Reg.t array -> unit
  méthode insert_debug : Mach.instruction_desc -> Debuginfo.t ->
                                        Reg.t array -> Reg.t array -> unit
  méthode insert_move : Reg.t -> Reg.t -> unit
  méthode insert_move_args : Reg.t array -> Reg.t array -> int -> unit
  méthode insert_move_results : Reg.t array -> Reg.t array -> int -> unit
  méthode insert_moves : Reg.t array -> Reg.t array -> unit
  méthode emit_expr :
    (Ident.t, Reg.t array) Tbl.t -> Cmm.expression -> Reg.t array option
  méthode emit_tail : (Ident.t, Reg.t array) Tbl.t -> Cmm.expression -> unit
fin
