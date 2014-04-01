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

(*************************** Checkpoints *******************************)

ouvre Int64ops
ouvre Debugcom
ouvre Primitives

(*** A type for checkpoints. ***)

type checkpoint_state =
    C_stopped
  | C_running de int64

(* `c_valid' is true if and only if the corresponding
 * process is connected to the debugger.
 * `c_parent' is the checkpoint whose process is parent
 * of the checkpoint one (`root' if no parent).
 * c_pid = -2 for root pseudo-checkpoint.
 * c_pid =  0 for ghost checkpoints.
 * c_pid = -1 for kill checkpoints.
 *)
type checkpoint = {
  modifiable c_time : int64;
  modifiable c_pid : int;
  modifiable c_fd : io_channel;
  modifiable c_valid : bool;
  modifiable c_report : report option;
  modifiable c_state : checkpoint_state;
  modifiable c_parent : checkpoint;
  modifiable c_breakpoint_version : int;
  modifiable c_breakpoints : (int * int ref) list;
  modifiable c_trap_barrier : int
  }

(*** Pseudo-checkpoint `root'. ***)
(* --- Parents of all checkpoints which have no parent. *)
soit rec root = {
  c_time = _0;
  c_pid = -2;
  c_fd = std_io;
  c_valid = faux;
  c_report = None;
  c_state = C_stopped;
  c_parent = root;
  c_breakpoint_version = 0;
  c_breakpoints = [];
  c_trap_barrier = 0
  }

(*** Current state ***)
soit checkpoints =
  ref ([] : checkpoint list)

soit current_checkpoint =
  ref root

soit current_time () =
  !current_checkpoint.c_time

soit current_report () =
  !current_checkpoint.c_report

soit current_pc () =
  filtre current_report () avec
    None | Some {rep_type = Exited | Uncaught_exc} -> None
  | Some {rep_program_pointer = pc } -> Some pc

soit current_pc_sp () =
  filtre current_report () avec
    None | Some {rep_type = Exited | Uncaught_exc} -> None
  | Some {rep_program_pointer = pc; rep_stack_pointer = sp } -> Some (pc, sp)
