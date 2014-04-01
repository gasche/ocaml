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

ouvre Instruct
ouvre Format
ouvre Debugcom
ouvre Checkpoints
ouvre Events
ouvre Symbols
ouvre Frames
ouvre Source
ouvre Show_source
ouvre Breakpoints
ouvre Parameters

(* Display information about the current event. *)
soit show_current_event ppf =
  fprintf ppf "Time: %Li" (current_time ());
  (filtre current_pc () avec
   | Some pc ->
       fprintf ppf " - pc: %i" pc
   | _ -> ());
  update_current_event ();
  reset_frame ();
  filtre current_report ()  avec
  | None ->
      fprintf ppf "@.Beginning of program.@.";
      show_no_point ()
  | Some {rep_type = (Event | Breakpoint); rep_program_pointer = pc} ->
        soit ev = get_current_event () dans
        fprintf ppf " - module %s@." ev.ev_module;
        (filtre breakpoints_at_pc pc avec
         | [] ->
             ()
         | [breakpoint] ->
             fprintf ppf "Breakpoint: %i@." breakpoint
         | breakpoints ->
             fprintf ppf "Breakpoints: %a@."
             (fonc ppf l ->
               List.iter
                (fonction x -> fprintf ppf "%i " x) l)
             (List.sort compare breakpoints));
        show_point ev vrai
  | Some {rep_type = Exited} ->
      fprintf ppf "@.Program exit.@.";
      show_no_point ()
  | Some {rep_type = Uncaught_exc} ->
      fprintf ppf
        "@.Program end.@.\
         @[Uncaught exception:@ %a@]@."
      Printval.print_exception (Debugcom.Remote_value.accu ());
      show_no_point ()
  | Some {rep_type = Trap_barrier} ->
                                        (* Trap_barrier not visible outside *)
                                        (* of module `time_travel'. *)
      Misc.fatal_error "Show_information.show_current_event"

(* Display short information about one frame. *)

soit show_one_frame framenum ppf event =
  soit pos = Events.get_pos event dans
  soit cnum =
    essaie
      soit buffer = get_buffer pos event.ev_module dans
      snd (start_and_cnum buffer pos)
    avec _ -> pos.Lexing.pos_cnum dans
  si !machine_readable alors
    fprintf ppf "#%i  Pc: %i  %s char %i@."
           framenum event.ev_pos event.ev_module
           cnum
  sinon
    fprintf ppf "#%i %s %s:%i:%i@."
           framenum event.ev_module
           pos.Lexing.pos_fname pos.Lexing.pos_lnum
           (pos.Lexing.pos_cnum - pos.Lexing.pos_bol + 1)

(* Display information about the current frame. *)
(* --- `select frame' must have succeded before calling this function. *)
soit show_current_frame ppf selected =
  filtre !selected_event avec
  | None ->
      fprintf ppf "@.No frame selected.@."
  | Some sel_ev ->
      show_one_frame !current_frame ppf sel_ev;
      début filtre breakpoints_at_pc sel_ev.ev_pos avec
      | [] -> ()
      | [breakpoint] ->
          fprintf ppf "Breakpoint: %i@." breakpoint
      | breakpoints ->
          fprintf ppf "Breakpoints: %a@."
          (fonc ppf l ->
            List.iter (fonction x -> fprintf ppf "%i " x) l)
          (List.sort compare breakpoints);
      fin;
      show_point sel_ev selected
