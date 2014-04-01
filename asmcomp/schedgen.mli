(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1997 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Instruction scheduling *)

type code_dag_node =
  { instr: Linearize.instruction;
    delay: int;
    modifiable sons: (code_dag_node * int) list;
    modifiable date: int;
    modifiable length: int;
    modifiable ancestors: int;
    modifiable emitted_ancestors: int }

classe virtuelle scheduler_generic : objet
  (* Can be overridden by processor description *)
  méthode virtuelle oper_issue_cycles : Mach.operation -> int
      (* Number of cycles needed to issue the given operation *)
  méthode virtuelle oper_latency : Mach.operation -> int
      (* Number of cycles needed to complete the given operation *)
  méthode reload_retaddr_issue_cycles : int
      (* Number of cycles needed to issue a Lreloadretaddr operation *)
  méthode reload_retaddr_latency : int
      (* Number of cycles needed to complete a Lreloadretaddr operation *)
  méthode oper_in_basic_block : Mach.operation -> bool
      (* Says whether the given operation terminates a basic block *)
  méthode is_store : Mach.operation -> bool
      (* Says whether the given operation is a memory store *)
  méthode is_load : Mach.operation -> bool
      (* Says whether the given operation is a memory load *)
  méthode is_checkbound : Mach.operation -> bool
      (* Says whether the given operation is a checkbound *)
  (* Entry point *)
  méthode schedule_fundecl : Linearize.fundecl -> Linearize.fundecl
fin
