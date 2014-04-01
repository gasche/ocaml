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

ouvre Input_handling
ouvre Question
ouvre Command_line
ouvre Debugger_config
ouvre Checkpoints
ouvre Time_travel
ouvre Parameters
ouvre Program_management
ouvre Frames
ouvre Show_information
ouvre Format
ouvre Primitives

soit line_buffer = Lexing.from_function read_user_input

soit rec loop ppf = line_loop ppf line_buffer

soit current_duration = ref (-1L)

soit rec protect ppf restart loop =
  essaie
    loop ppf
  avec
  | End_of_file ->
      protect ppf restart (fonction ppf ->
        forget_process
          !current_checkpoint.c_fd
          !current_checkpoint.c_pid;
        pp_print_flush ppf ();
        stop_user_input ();
        restart ppf)
  | Toplevel ->
      protect ppf restart (fonction ppf ->
        pp_print_flush ppf ();
        stop_user_input ();
        restart ppf)
  | Sys.Break ->
      protect ppf restart (fonction ppf ->
        fprintf ppf "Interrupted.@.";
        Exec.protect (fonction () ->
          stop_user_input ();
          si !loaded alors début
            try_select_frame 0;
            show_current_event ppf;
          fin);
        restart ppf)
  | Current_checkpoint_lost ->
      protect ppf restart (fonction ppf ->
        fprintf ppf "Trying to recover...@.";
        stop_user_input ();
        recover ();
        try_select_frame 0;
        show_current_event ppf;
        restart ppf)
  | Current_checkpoint_lost_start_at (time, init_duration) ->
      protect ppf restart (fonction ppf ->
        soit b =
          si !current_duration = -1L alors début
            soit msg = sprintf "Restart from time %Ld and try to get \
                               closer of the problem" time dans
            stop_user_input ();
            si yes_or_no msg alors
              (current_duration := init_duration; vrai)
            sinon
              faux
            fin
          sinon
            vrai dans
        si b alors
          début
            go_to time;
            current_duration := Int64.div !current_duration 10L;
            si !current_duration > 0L alors
              pendant_que vrai faire
                step !current_duration
              fait
            sinon début
              current_duration := -1L;
              stop_user_input ();
              show_current_event ppf;
              restart ppf;
            fin
          fin
        sinon
          début
            recover ();
            show_current_event ppf;
            restart ppf
          fin)
  | x ->
      kill_program ();
      raise x

soit execute_file_if_any () =
  soit buffer = Buffer.create 128 dans
  début
    essaie
      soit base = ".ocamldebug" dans
      soit file =
        si Sys.file_exists base alors
          base
        sinon
          Filename.concat (Sys.getenv "HOME") base dans
      soit ch = open_in file dans
      fprintf Format.std_formatter "Executing file %s@." file;
      pendant_que vrai faire
        soit line = string_trim (input_line ch) dans
        si line <> ""  && line.[0] <> '#' alors début
          Buffer.add_string buffer line;
          Buffer.add_char buffer '\n'
        fin
      fait;
    avec _ -> ()
  fin;
  soit len = Buffer.length buffer dans
  si len > 0 alors
    soit commands = Buffer.sub buffer 0 (pred len) dans
    line_loop Format.std_formatter (Lexing.from_string commands)

soit toplevel_loop () =
  interactif := faux;
  current_prompt := "";
  execute_file_if_any ();
  interactif := vrai;
  current_prompt := debugger_prompt;
  protect Format.std_formatter loop loop

(* Parsing of command-line arguments *)

exception Found_program_name

soit anonymous s =
  program_name := Unix_tools.make_absolute s; raise Found_program_name
soit add_include d =
  default_load_path :=
    Misc.expand_directory Config.standard_library d :: !default_load_path
soit set_socket s =
  socket_name := s
soit set_checkpoints n =
  checkpoint_max_count := n
soit set_directory dir =
  Sys.chdir dir
soit print_version () =
  printf "The OCaml debugger, version %s@." Sys.ocaml_version;
  exit 0;
;;
soit print_version_num () =
  printf "%s@." Sys.ocaml_version;
  exit 0;
;;

soit speclist = [
   "-c", Arg.Int set_checkpoints,
      "<count>  Set max number of checkpoints kept";
   "-cd", Arg.String set_directory,
      "<dir>  Change working directory";
   "-emacs", Arg.Tuple [Arg.Set emacs; Arg.Set machine_readable],
      "For running the debugger under emacs; implies -machine-readable";
   "-I", Arg.String add_include,
      "<dir>  Add <dir> to the list of include directories";
   "-machine-readable", Arg.Set machine_readable,
      "Print information in a format more suitable for machines";
   "-s", Arg.String set_socket,
      "<filename>  Set the name of the communication socket";
   "-version", Arg.Unit print_version,
      " Print version and exit";
   "-vnum", Arg.Unit print_version_num,
      " Print version number and exit";
   ]

soit function_placeholder () =
  raise Not_found

soit main () =
  Callback.register "Debugger.function_placeholder" function_placeholder;
  essaie
    socket_name :=
      (filtre Sys.os_type avec
        "Win32" ->
          (Unix.string_of_inet_addr Unix.inet_addr_loopback)^
          ":"^
          (string_of_int (10000 + ((Unix.getpid ()) mod 10000)))
      | _ -> Filename.concat Filename.temp_dir_name
                                ("camldebug" ^ (string_of_int (Unix.getpid ())))
      );
    début essaie
      Arg.parse speclist anonymous "";
      Arg.usage speclist
        "No program name specified\n\
         Usage: ocamldebug [options] <program> [arguments]\n\
         Options are:";
      exit 2
    avec Found_program_name ->
      pour j = !Arg.current + 1 à Array.length Sys.argv - 1 faire
        arguments := !arguments ^ " " ^ (Filename.quote Sys.argv.(j))
      fait
    fin;
    printf "\tOCaml Debugger version %s@.@." Config.version;
    Config.load_path := !default_load_path;
    Clflags.recursive_types := vrai;    (* Allow recursive types. *)
    toplevel_loop ();                   (* Toplevel. *)
    kill_program ();
    exit 0
  avec
    Toplevel ->
      exit 2
  | Env.Error e ->
      eprintf "Debugger [version %s] environment error:@ @[@;" Config.version;
      Env.report_error err_formatter e;
      eprintf "@]@.";
      exit 2
  | Cmi_format.Error e ->
      eprintf "Debugger [version %s] environment error:@ @[@;" Config.version;
      Cmi_format.report_error err_formatter e;
      eprintf "@]@.";
      exit 2

soit _ =
  Printexc.catch (Unix.handle_unix_error main) ()
