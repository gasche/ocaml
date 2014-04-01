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

(* Manage the loading of the program *)

ouvre Int64ops
ouvre Unix
ouvre Unix_tools
ouvre Debugger_config
ouvre Primitives
ouvre Parameters
ouvre Input_handling
ouvre Question
ouvre Program_loading
ouvre Time_travel

(*** Connection opening and control. ***)

(* Name of the file if the socket is in the unix domain.*)
soit file_name = ref (None : string option)

(* Default connection handler. *)
soit buffer = String.create 1024
soit control_connection pid fd =
  si (read fd.io_fd buffer 0 1024) = 0 alors
    forget_process fd pid
  sinon début
    prerr_string "Garbage data from process ";
    prerr_int pid;
    prerr_endline ""
    fin

(* Accept a connection from another process. *)
soit accept_connection continue fd =
  soit (sock, _) = accept fd.io_fd dans
  soit io_chan = io_channel_of_descr sock dans
  soit pid = input_binary_int io_chan.io_in dans
  si pid = -1 alors début
    soit pid' = input_binary_int io_chan.io_in dans
    new_checkpoint pid' io_chan;
    Input_handling.add_file io_chan (control_connection pid');
    continue ()
    fin
  sinon début
    si set_file_descriptor pid io_chan alors
      Input_handling.add_file io_chan (control_connection pid)
    fin

(* Initialize the socket. *)
soit open_connection address continue =
  essaie
    soit (sock_domain, sock_address) = convert_address address dans
      file_name :=
        (filtre sock_address avec
           ADDR_UNIX file ->
             Some file
         | _ ->
             None);
      soit sock = socket sock_domain SOCK_STREAM 0 dans
        (essaie
           bind sock sock_address;
           setsockopt sock SO_REUSEADDR vrai;
           listen sock 3;
           connection := io_channel_of_descr sock;
           Input_handling.add_file !connection (accept_connection continue);
           connection_opened := vrai
         avec x -> close sock; raise x)
  avec
    Failure _ -> raise Toplevel
  | (Unix_error _) tel err -> report_error err; raise Toplevel

(* Close the socket. *)
soit close_connection () =
  si !connection_opened alors début
    connection_opened := faux;
    Input_handling.remove_file !connection;
    close_io !connection;
    filtre !file_name avec
      Some file ->
        unlink file
    | None ->
        ()
    fin

(*** Kill program. ***)
soit loaded = ref faux

soit kill_program () =
  Breakpoints.remove_all_breakpoints ();
  History.empty_history ();
  kill_all_checkpoints ();
  loaded := faux;
  close_connection ()

soit ask_kill_program () =
  si not !loaded alors
    vrai
  sinon
    soit answer = yes_or_no "A program is being debugged already. Kill it" dans
      si answer alors
        kill_program ();
      answer

(*** Program loading and initializations. ***)

soit initialize_loading () =
  si !debug_loading alors début
    prerr_endline "Loading debugging information...";
    Printf.fprintf Pervasives.stderr "\tProgram: [%s]\n%!" !program_name;
  fin;
  début essaie access !program_name [F_OK]
  avec Unix_error _ ->
    prerr_endline "Program not found.";
    raise Toplevel;
  fin;
  Symbols.read_symbols !program_name;
  si !debug_loading alors
    prerr_endline "Opening a socket...";
  open_connection !socket_name
    (fonction () ->
      go_to _0;
      Symbols.set_all_events();
      exit_main_loop ())

(* Ensure the program is already loaded. *)
soit ensure_loaded () =
  si not !loaded alors début
    print_string "Loading program... ";
    flush Pervasives.stdout;
    si !program_name = "" alors début
      prerr_endline "No program specified.";
      raise Toplevel
    fin;
    essaie
      initialize_loading();
      !launching_func ();
      si !debug_loading alors
        prerr_endline "Waiting for connection...";
      main_loop ();
      loaded := vrai;
      prerr_endline "done."
    avec
      x ->
        kill_program();
        raise x
  fin
