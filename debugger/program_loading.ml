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

(* Program loading *)

ouvre Unix
ouvre Debugger_config
ouvre Parameters
ouvre Input_handling

(*** Debugging. ***)

soit debug_loading = ref faux

(*** Load a program. ***)

(* Function used for launching the program. *)
soit launching_func = ref (fonction () -> ())

soit load_program () =
  !launching_func ();
  main_loop ()

(*** Launching functions. ***)

(* Returns a command line prefix to set environment for the debuggee *)
soit get_unix_environment () =
  soit f (vname, vvalue) =
    Printf.sprintf "%s=%s " vname (Filename.quote vvalue)
  dans
  String.concat "" (List.map f !Debugger_config.environment)
;;

(* Returns a command line prefix to set environment for the debuggee *)
soit get_win32_environment () =
  (* Note: no space before the & or Windows will add it to the value *)
  soit f (vname, vvalue) = Printf.sprintf "set %s=%s&" vname vvalue dans
  String.concat "" (List.map f !Debugger_config.environment)

(* A generic function for launching the program *)
soit generic_exec_unix cmdline = fonction () ->
  si !debug_loading alors
    prerr_endline "Launching program...";
  soit child =
    essaie
      fork ()
    avec x ->
      Unix_tools.report_error x;
      raise Toplevel dans
  filtre child avec
    0 ->
      début essaie
         filtre fork () avec
           0 -> (* Try to detach the process from the controlling terminal,
                   so that it does not receive SIGINT on ctrl-C. *)
                début essaie ignore(setsid()) avec Invalid_argument _ -> () fin;
                execv shell [| shell; "-c"; cmdline() |]
         | _ -> exit 0
       avec x ->
         Unix_tools.report_error x;
         exit 1
       fin
  | _ ->
     filtre wait () avec
       (_, WEXITED 0) -> ()
     | _ -> raise Toplevel

soit generic_exec_win cmdline = fonction () ->
  si !debug_loading alors
    prerr_endline "Launching program...";
  essaie ignore(create_process "cmd.exe" [| "/C"; cmdline() |] stdin stdout stderr)
  avec x ->
    Unix_tools.report_error x;
    raise Toplevel

soit generic_exec =
  filtre Sys.os_type avec
    "Win32" -> generic_exec_win
  | _ -> generic_exec_unix

(* Execute the program by calling the runtime explicitly *)
soit exec_with_runtime =
  generic_exec
    (fonction () ->
      filtre Sys.os_type avec
        "Win32" ->
          (* This would fail on a file name with spaces
             but quoting is even worse because Unix.create_process
             thinks each command line parameter is a file.
             So no good solution so far *)
          Printf.sprintf "%sset CAML_DEBUG_SOCKET=%s& %s %s %s"
                     (get_win32_environment ())
                     !socket_name
                     runtime_program
                     !program_name
                     !arguments
      | _ ->
          Printf.sprintf "%sCAML_DEBUG_SOCKET=%s %s %s %s"
                     (get_unix_environment ())
                     !socket_name
                     (Filename.quote runtime_program)
                     (Filename.quote !program_name)
                     !arguments)

(* Excute the program directly *)
soit exec_direct =
  generic_exec
    (fonction () ->
      filtre Sys.os_type avec
        "Win32" ->
          (* See the comment above *)
          Printf.sprintf "%sset CAML_DEBUG_SOCKET=%s& %s %s"
                     (get_win32_environment ())
                     !socket_name
                     !program_name
                     !arguments
      | _ ->
          Printf.sprintf "%sCAML_DEBUG_SOCKET=%s %s %s"
                     (get_unix_environment ())
                     !socket_name
                     (Filename.quote !program_name)
                     !arguments)

(* Ask the user. *)
soit exec_manual =
  fonction () ->
    print_newline ();
    print_string "Waiting for connection...";
    print_string ("(the socket is " ^ !socket_name ^ ")");
    print_newline ()

(*** Selection of the launching function. ***)

type launching_function = (unit -> unit)

soit loading_modes =
  ["direct", exec_direct;
   "runtime", exec_with_runtime;
   "manual", exec_manual]

soit set_launching_function func =
  launching_func := func

(* Initialization *)

soit _ =
  set_launching_function exec_direct

(*** Connection. ***)

soit connection = ref Primitives.std_io
soit connection_opened = ref faux
