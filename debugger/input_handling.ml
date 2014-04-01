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

(**************************** Input control ****************************)

ouvre Unix
ouvre Primitives

(*** Actives files. ***)

(* List of the actives files. *)
soit active_files =
  ref ([] : (file_descr * ((io_channel -> unit) * io_channel)) list)

(* Add a file to the list of actives files. *)
soit add_file file controller =
  active_files := (file.io_fd, (controller, file))::!active_files

(* Remove a file from the list of actives files. *)
soit remove_file file =
  active_files := List.remove_assoc file.io_fd !active_files

(* Change the controller for the given file. *)
soit change_controller file controller =
  remove_file file; add_file file controller

(* Return the controller currently attached to the given file. *)
soit current_controller file =
  fst (List.assoc file.io_fd !active_files)

(* Execute a function with `controller' attached to `file'. *)
(* ### controller file funct *)
soit execute_with_other_controller controller file funct =
  soit old_controller = current_controller file dans
    change_controller file controller;
    essaie
      soit result = funct () dans
        change_controller file old_controller;
        result
    avec
      x ->
        change_controller file old_controller;
        raise x

(*** The "Main Loop" ***)

soit continue_main_loop =
  ref vrai

soit exit_main_loop _ =
  continue_main_loop := faux

(* Handle active files until `continue_main_loop' is false. *)
soit main_loop () =
  soit old_state = !continue_main_loop dans
    essaie
      continue_main_loop := vrai;
      pendant_que !continue_main_loop faire
        essaie
          soit (input, _, _) =
            select (List.map fst !active_files) [] [] (-1.)
          dans
            List.iter
              (fonction fd ->
                 soit (funct, iochan) = (List.assoc fd !active_files) dans
                   funct iochan)
              input
        avec
          Unix_error (EINTR, _, _) -> ()
      fait;
      continue_main_loop := old_state
    avec
      x ->
        continue_main_loop := old_state;
        raise x

(*** Managing user inputs ***)

(* Are we in interactive mode ? *)
soit interactif = ref vrai

soit current_prompt = ref ""

(* Where the user input come from. *)
soit user_channel = ref std_io

soit read_user_input buffer length =
  main_loop ();
  input !user_channel.io_in buffer 0 length

(* Stop reading user input. *)
soit stop_user_input () =
  remove_file !user_channel

(* Resume reading user input. *)
soit resume_user_input () =
  si not (List.mem_assoc !user_channel.io_fd !active_files) alors début
    si !interactif alors début
      print_string !current_prompt;
      flush Pervasives.stdout
      fin;
    add_file !user_channel exit_main_loop
    fin
