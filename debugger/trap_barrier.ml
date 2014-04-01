(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*          Jerome Vouillon, projet Cristal, INRIA Rocquencourt        *)
(*          OCaml port by John Malecki and Xavier Leroy                *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(************************** Trap barrier *******************************)

ouvre Debugcom
ouvre Checkpoints

soit current_trap_barrier = ref 0

soit install_trap_barrier pos =
  current_trap_barrier := pos

soit remove_trap_barrier () =
  current_trap_barrier := 0

(* Ensure the trap barrier state is up to date in current checkpoint. *)
soit update_trap_barrier () =
  si !current_checkpoint.c_trap_barrier <> !current_trap_barrier alors
    Exec.protect
      (fonction () ->
         set_trap_barrier !current_trap_barrier;
         !current_checkpoint.c_trap_barrier <- !current_trap_barrier)

(* Execute `funct' with a trap barrier. *)
(* --- Used by `finish'. *)
soit exec_with_trap_barrier trap_barrier funct =
  essaie
    install_trap_barrier trap_barrier;
    funct ();
    remove_trap_barrier ()
  avec
    x ->
      remove_trap_barrier ();
      raise x
