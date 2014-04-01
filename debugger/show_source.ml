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

ouvre Debugger_config
ouvre Instruct
ouvre Parameters
ouvre Primitives
ouvre Printf
ouvre Source

(* Print a line; return the beginning of the next line *)
soit print_line buffer line_number start point before =
  soit next = next_linefeed buffer start
  et content = buffer_content buffer
  dans
    printf "%i " line_number;
    si point <= next && point >= start alors
      (print_string (String.sub content start (point - start));
       print_string (si before alors event_mark_before sinon event_mark_after);
       print_string (String.sub content point (next - point)))
    sinon
      print_string (String.sub content start (next - start));
    print_newline ();
    next

(* Tell Emacs we are nowhere in the source. *)
soit show_no_point () =
  si !emacs alors printf "\026\026H\n"

(* Print the line containing the point *)
soit show_point ev selected =
  soit mdle = ev.ev_module dans
  soit before = (ev.ev_kind = Event_before) dans
  si !emacs && selected alors
    début essaie
      soit buffer = get_buffer (Events.get_pos ev) mdle dans
      soit source = source_of_module ev.ev_loc.Location.loc_start mdle dans
      printf "\026\026M%s:%i:%i" source
        (snd (start_and_cnum buffer ev.ev_loc.Location.loc_start))
        (snd (start_and_cnum buffer ev.ev_loc.Location.loc_end));
      printf "%s\n" (si before alors ":before" sinon ":after")
    avec
      Out_of_range -> (* point_of_coord *)
        prerr_endline "Position out of range."
    | Not_found    -> (* Events.get_pos || get_buffer *)
        prerr_endline ("No source file for " ^ mdle ^ ".");
        show_no_point ()
    fin
  sinon
    début essaie
      soit pos = Events.get_pos ev dans
      soit buffer = get_buffer pos mdle dans
      soit start, point = start_and_cnum buffer pos dans
      ignore(print_line buffer pos.Lexing.pos_lnum start point before)
    avec
      Out_of_range -> (* point_of_coord *)
        prerr_endline "Position out of range."
    | Not_found    -> (* Events.get_pos || get_buffer *)
        prerr_endline ("No source file for " ^ mdle ^ ".")
    fin

(* Display part of the source. *)
soit show_listing pos mdle start stop point before =
  essaie
    soit buffer = get_buffer pos mdle dans
      soit rec aff (line_start, line_number) =
        si line_number <= stop alors
          aff (print_line buffer line_number line_start point before + 1,
               line_number + 1)
      dans
        aff (pos_of_line buffer start)
  avec
    Out_of_range -> (* pos_of_line *)
      prerr_endline "Position out of range."
  | Not_found    -> (* get_buffer *)
      prerr_endline ("No source file for " ^ mdle ^ ".")
