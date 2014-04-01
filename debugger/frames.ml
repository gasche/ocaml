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

(***************************** Frames **********************************)

ouvre Instruct
ouvre Debugcom
ouvre Events
ouvre Symbols

(* Current frame number *)
soit current_frame = ref 0

(* Event at selected position *)
soit selected_event = ref (None : debug_event option)

(* Selected position in source. *)
(* Raise `Not_found' if not on an event. *)
soit selected_point () =
  filtre !selected_event avec
    None ->
      raise Not_found
  | Some ev ->
      (ev.ev_module,
       (Events.get_pos ev).Lexing.pos_lnum,
       (Events.get_pos ev).Lexing.pos_cnum - (Events.get_pos ev).Lexing.pos_bol)

soit selected_event_is_before () =
  filtre !selected_event avec
    None ->
      raise Not_found
  | Some {ev_kind = Event_before} ->
      vrai
  | _ ->
      faux

(* Move up `frame_count' frames, assuming current frame pointer
   corresponds to event `event'. Return event of final frame. *)

soit rec move_up frame_count event =
  si frame_count <= 0 alors event sinon début
    soit (sp, pc) = up_frame event.ev_stacksize dans
    si sp < 0 alors raise Not_found;
    move_up (frame_count - 1) (any_event_at_pc pc)
  fin

(* Select a frame. *)
(* Raise `Not_found' if no such frame. *)
(* --- Assume the current events have already been updated. *)
soit select_frame frame_number =
  si frame_number < 0 alors raise Not_found;
  soit (initial_sp, _) = get_frame() dans
  essaie
    filtre !current_event avec
      None ->
        raise Not_found
    | Some curr_event ->
        filtre !selected_event avec
          Some sel_event quand frame_number >= !current_frame ->
            selected_event :=
              Some(move_up (frame_number - !current_frame) sel_event);
            current_frame := frame_number
        | _ ->
            set_initial_frame();
            selected_event := Some(move_up frame_number curr_event);
            current_frame := frame_number
  avec Not_found ->
    set_frame initial_sp;
    raise Not_found

(* Select a frame. *)
(* Same as `select_frame' but raise no exception if the frame is not found. *)
(* --- Assume the currents events have already been updated. *)
soit try_select_frame frame_number =
  essaie
    select_frame frame_number
  avec
    Not_found ->
      ()

(* Return to default frame (frame 0). *)
soit reset_frame () =
  set_initial_frame();
  selected_event := !current_event;
  current_frame := 0

(* Perform a stack backtrace.
   Call the given function with the events for each stack frame,
   or None if we've encountered a stack frame with no debugging info
   attached. Stop when the function returns false, or frame with no
   debugging info reached, or top of stack reached. *)

soit do_backtrace action =
  filtre !current_event avec
    None -> Misc.fatal_error "Frames.do_backtrace"
  | Some curr_ev ->
      soit (initial_sp, _) = get_frame() dans
      set_initial_frame();
      soit event = ref curr_ev dans
      début essaie
        pendant_que action (Some !event) faire
          soit (sp, pc) = up_frame !event.ev_stacksize dans
          si sp < 0 alors raise Exit;
          event := any_event_at_pc pc
        fait
      avec Exit -> ()
         | Not_found -> ignore (action None)
      fin;
      set_frame initial_sp

(* Return the number of frames in the stack *)

soit stack_depth () =
  soit num_frames = ref 0 dans
  do_backtrace (fonction Some ev -> incr num_frames; vrai
                       | None -> num_frames := -1; faux);
  !num_frames
