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

(* Low-level communication with the debuggee *)

ouvre Int64ops
ouvre Primitives

(* The current connection with the debuggee *)

soit conn = ref Primitives.std_io

(* Set which process the debugger follows on fork. *)

type follow_fork_mode =
    Fork_child
  | Fork_parent

soit fork_mode = ref Fork_parent

soit update_follow_fork_mode () =
  soit a = filtre !fork_mode avec Fork_child -> 0 | Fork_parent -> 1 dans
  output_char !conn.io_out 'K';
  output_binary_int !conn.io_out a

(* Set the current connection, and update the fork mode in case it has
 * changed. *)

soit set_current_connection io_chan =
  conn := io_chan;
  update_follow_fork_mode ()

(* Modify the program code *)

soit set_event pos =
  output_char !conn.io_out 'e';
  output_binary_int !conn.io_out pos

soit set_breakpoint pos =
  output_char !conn.io_out 'B';
  output_binary_int !conn.io_out pos

soit reset_instr pos =
  output_char !conn.io_out 'i';
  output_binary_int !conn.io_out pos

(* Basic commands for flow control *)

type execution_summary =
    Event
  | Breakpoint
  | Exited
  | Trap_barrier
  | Uncaught_exc

type report = {
  rep_type : execution_summary;
  rep_event_count : int;
  rep_stack_pointer : int;
  rep_program_pointer : int
}

type checkpoint_report =
    Checkpoint_done de int
  | Checkpoint_failed

(* Run the debuggee for N events *)

soit do_go_smallint n =
  output_char !conn.io_out 'g';
  output_binary_int !conn.io_out n;
  flush !conn.io_out;
  Input_handling.execute_with_other_controller
    Input_handling.exit_main_loop
    !conn
    (fonction () ->
       Input_handling.main_loop ();
       soit summary =
         filtre input_char !conn.io_in avec
           'e' -> Event
         | 'b' -> Breakpoint
         | 'x' -> Exited
         | 's' -> Trap_barrier
         | 'u' -> Uncaught_exc
         |  _  -> Misc.fatal_error "Debugcom.do_go" dans
       soit event_counter = input_binary_int !conn.io_in dans
       soit stack_pos = input_binary_int !conn.io_in dans
       soit pc = input_binary_int !conn.io_in dans
       { rep_type = summary;
         rep_event_count = event_counter;
         rep_stack_pointer = stack_pos;
         rep_program_pointer = pc })

soit rec do_go n =
  affirme (n >= _0);
  si n > max_small_int alors(
    ignore (do_go_smallint max_int);
    do_go (n -- max_small_int)
  )sinon(
    do_go_smallint (Int64.to_int n)
  )
;;

(* Perform a checkpoint *)

soit do_checkpoint () =
  filtre Sys.os_type avec
    "Win32" -> failwith "do_checkpoint"
  | _ ->
      output_char !conn.io_out 'c';
      flush !conn.io_out;
      soit pid = input_binary_int !conn.io_in dans
      si pid = -1 alors Checkpoint_failed sinon Checkpoint_done pid

(* Kill the given process. *)
soit stop chan =
  essaie
    output_char chan.io_out 's';
    flush chan.io_out
  avec
    Sys_error _ | End_of_file -> ()

(* Ask a process to wait for its child which has been killed. *)
(* (so as to eliminate zombies). *)
soit wait_child chan =
  essaie
    output_char chan.io_out 'w'
  avec
    Sys_error _ | End_of_file -> ()

(* Move to initial frame (that of current function). *)
(* Return stack position and current pc *)

soit initial_frame () =
  output_char !conn.io_out '0';
  flush !conn.io_out;
  soit stack_pos = input_binary_int !conn.io_in dans
  soit pc = input_binary_int !conn.io_in dans
  (stack_pos, pc)

soit set_initial_frame () =
  ignore(initial_frame ())

(* Move up one frame *)
(* Return stack position and current pc.
   If there's no frame above, return (-1, 0). *)

soit up_frame stacksize =
  output_char !conn.io_out 'U';
  output_binary_int !conn.io_out stacksize;
  flush !conn.io_out;
  soit stack_pos = input_binary_int !conn.io_in dans
  soit pc = si stack_pos = -1 alors 0 sinon input_binary_int !conn.io_in dans
  (stack_pos, pc)

(* Get and set the current frame position *)

soit get_frame () =
  output_char !conn.io_out 'f';
  flush !conn.io_out;
  soit stack_pos = input_binary_int !conn.io_in dans
  soit pc = input_binary_int !conn.io_in dans
  (stack_pos, pc)

soit set_frame stack_pos =
  output_char !conn.io_out 'S';
  output_binary_int !conn.io_out stack_pos

(* Set the trap barrier to given stack position. *)

soit set_trap_barrier pos =
  output_char !conn.io_out 'b';
  output_binary_int !conn.io_out pos

(* Handling of remote values *)

soit value_size = si 1 dgl 31 = 0 alors 4 sinon 8

soit input_remote_value ic =
  Misc.input_bytes ic value_size

soit output_remote_value ic v =
  output ic v 0 value_size

exception Marshalling_error

module Remote_value =
  struct
    type t = Remote de string | Local de Obj.t

    soit obj = fonction
    | Local obj -> Obj.obj obj
    | Remote v ->
        output_char !conn.io_out 'M';
        output_remote_value !conn.io_out v;
        flush !conn.io_out;
        essaie
          input_value !conn.io_in
        avec End_of_file | Failure _ ->
          raise Marshalling_error

    soit is_block = fonction
    | Local obj -> Obj.is_block obj
    | Remote v -> Obj.is_block (Array.unsafe_get (Obj.magic v : Obj.t array) 0)

    soit tag = fonction
    | Local obj -> Obj.tag obj
    | Remote v ->
        output_char !conn.io_out 'H';
        output_remote_value !conn.io_out v;
        flush !conn.io_out;
        soit header = input_binary_int !conn.io_in dans
        header etl 0xFF

    soit size = fonction
    | Local obj -> Obj.size obj
    | Remote v ->
        output_char !conn.io_out 'H';
        output_remote_value !conn.io_out v;
        flush !conn.io_out;
        soit header = input_binary_int !conn.io_in dans
        si header etl 0xFF = Obj.double_array_tag && Sys.word_size = 32
        alors header ddl 11
        sinon header ddl 10

    soit field v n =
      filtre v avec
      | Local obj -> Local(Obj.field obj n)
      | Remote v ->
          output_char !conn.io_out 'F';
          output_remote_value !conn.io_out v;
          output_binary_int !conn.io_out n;
          flush !conn.io_out;
          si input_byte !conn.io_in = 0 alors
            Remote(input_remote_value !conn.io_in)
          sinon début
            soit buf = Misc.input_bytes !conn.io_in 8 dans
            soit floatbuf = float n (* force allocation of a new float *) dans
            String.unsafe_blit buf 0 (Obj.magic floatbuf) 0 8;
            Local(Obj.repr floatbuf)
          fin

    soit of_int n =
      Local(Obj.repr n)

    soit local pos =
      output_char !conn.io_out 'L';
      output_binary_int !conn.io_out pos;
      flush !conn.io_out;
      Remote(input_remote_value !conn.io_in)

    soit from_environment pos =
      output_char !conn.io_out 'E';
      output_binary_int !conn.io_out pos;
      flush !conn.io_out;
      Remote(input_remote_value !conn.io_in)

    soit global pos =
      output_char !conn.io_out 'G';
      output_binary_int !conn.io_out pos;
      flush !conn.io_out;
      Remote(input_remote_value !conn.io_in)

    soit accu () =
      output_char !conn.io_out 'A';
      flush !conn.io_out;
      Remote(input_remote_value !conn.io_in)

    soit closure_code = fonction
    | Local obj -> affirme faux
    | Remote v ->
        output_char !conn.io_out 'C';
        output_remote_value !conn.io_out v;
        flush !conn.io_out;
        input_binary_int !conn.io_in

    soit same rv1 rv2 =
      filtre (rv1, rv2) avec
        (Local obj1, Local obj2) -> obj1 == obj2
      | (Remote v1, Remote v2) -> v1 = v2
           (* string equality -> equality of remote pointers *)
      | (_, _) -> faux

  fin
