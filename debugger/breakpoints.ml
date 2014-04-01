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

(******************************* Breakpoints ***************************)

ouvre Checkpoints
ouvre Debugcom
ouvre Instruct
ouvre Primitives
ouvre Printf

(*** Debugging. ***)
soit debug_breakpoints = ref faux

(*** Data. ***)

(* Number of the last added breakpoint. *)
soit breakpoint_number = ref 0

(* Breakpoint number -> event. *)
soit breakpoints = ref ([] : (int * debug_event) list)

(* Program counter -> breakpoint count. *)
soit positions = ref ([] : (int * int ref) list)

(* Versions of the breakpoint list. *)
soit current_version = ref 0
soit max_version = ref 0

(*** Miscellaneous. ***)

(* Mark breakpoints as installed in current checkpoint. *)
soit copy_breakpoints () =
  !current_checkpoint.c_breakpoints <- !positions;
  !current_checkpoint.c_breakpoint_version <- !current_version

(* Announce a new version of the breakpoint list. *)
soit new_version () =
  incr max_version;
  current_version := !max_version

(*** Information about breakpoints. ***)

soit breakpoints_count () =
  List.length !breakpoints

(* List of breakpoints at `pc'. *)
soit rec breakpoints_at_pc pc =
  début essaie
    soit ev = Symbols.event_at_pc pc dans
    filtre ev.ev_repr avec
      Event_child {contents = pc'} -> breakpoints_at_pc pc'
    | _                            -> []
  avec Not_found ->
   []
  fin
    @
  List.map fst (List.filter (fonction (_, {ev_pos = pos}) -> pos = pc)
                            !breakpoints)

(* Is there a breakpoint at `pc' ? *)
soit breakpoint_at_pc pc =
  breakpoints_at_pc pc <> []

(*** Set and remove breakpoints ***)

(* Remove all breakpoints. *)
soit remove_breakpoints pos =
  si !debug_breakpoints alors
    (print_string "Removing breakpoints..."; print_newline ());
  List.iter
    (fonction (pos, _) ->
       si !debug_breakpoints alors début
         print_int pos;
         print_newline()
       fin;
       reset_instr pos;
       Symbols.set_event_at_pc pos)
    pos

(* Set all breakpoints. *)
soit set_breakpoints pos =
  si !debug_breakpoints alors
    (print_string "Setting breakpoints..."; print_newline ());
  List.iter
    (fonction (pos, _) ->
       si !debug_breakpoints alors début
         print_int pos;
         print_newline()
       fin;
       set_breakpoint pos)
    pos

(* Ensure the current version in installed in current checkpoint. *)
soit update_breakpoints () =
  si !debug_breakpoints alors début
    prerr_string "Updating breakpoints... ";
    prerr_int !current_checkpoint.c_breakpoint_version;
    prerr_string " ";
    prerr_int !current_version;
    prerr_endline ""
  fin;
  si !current_checkpoint.c_breakpoint_version <> !current_version alors
    Exec.protect
      (fonction () ->
         remove_breakpoints !current_checkpoint.c_breakpoints;
         set_breakpoints !positions;
         copy_breakpoints ())

soit change_version version pos =
  Exec.protect
    (fonction () ->
       current_version := version;
       positions := pos)

(* Execute given function with no breakpoint in current checkpoint. *)
(* --- `goto' runs faster this way (does not stop on each breakpoint). *)
soit execute_without_breakpoints f =
  soit version = !current_version
  et pos = !positions
  dans
    change_version 0 [];
    essaie
      f ();
      change_version version pos
    avec
      x ->
        change_version version pos

(* Add a position in the position list. *)
(* Change version if necessary. *)
soit insert_position pos =
  essaie
    incr (List.assoc pos !positions)
  avec
    Not_found ->
      positions := (pos, ref 1) :: !positions;
      new_version ()

(* Remove a position in the position list. *)
(* Change version if necessary. *)
soit remove_position pos =
  soit count = List.assoc pos !positions dans
    decr count;
    si !count = 0 alors début
      positions := List.remove_assoc pos !positions;
      new_version ()
    fin

(* Insert a new breakpoint in lists. *)
soit rec new_breakpoint =
  fonction
    {ev_repr = Event_child pc} ->
      new_breakpoint (Symbols.any_event_at_pc !pc)
  | event ->
      Exec.protect
        (fonction () ->
           incr breakpoint_number;
           insert_position event.ev_pos;
           breakpoints := (!breakpoint_number, event) :: !breakpoints);
      printf "Breakpoint %d at %d: %s" !breakpoint_number event.ev_pos
             (Pos.get_desc event);
      print_newline ()

(* Remove a breakpoint from lists. *)
soit remove_breakpoint number =
  essaie
    soit ev = List.assoc number !breakpoints dans
    soit pos = ev.ev_pos dans
      Exec.protect
        (fonction () ->
           breakpoints := List.remove_assoc number !breakpoints;
           remove_position pos;
           printf "Removed breakpoint %d at %d: %s" number ev.ev_pos
                  (Pos.get_desc ev);
           print_newline ()
        )
  avec
    Not_found ->
      prerr_endline ("No breakpoint number " ^ (string_of_int number) ^ ".");
      raise Not_found

soit remove_all_breakpoints () =
  List.iter (fonction (number, _) -> remove_breakpoint number) !breakpoints

(*** Temporary breakpoints. ***)

(* Temporary breakpoint position. *)
soit temporary_breakpoint_position = ref (None : int option)

(* Execute `funct' with a breakpoint added at `pc'. *)
(* --- Used by `finish'. *)
soit exec_with_temporary_breakpoint pc funct =
  soit previous_version = !current_version dans
    soit remove () =
      temporary_breakpoint_position := None;
      current_version := previous_version;
      soit count = List.assoc pc !positions dans
        decr count;
        si !count = 0 alors début
          positions := List.remove_assoc pc !positions;
          reset_instr pc;
          Symbols.set_event_at_pc pc
        fin

    dans
      Exec.protect (fonction () -> insert_position pc);
      temporary_breakpoint_position := Some pc;
      essaie
        funct ();
        Exec.protect remove
      avec
        x ->
          Exec.protect remove;
          raise x
