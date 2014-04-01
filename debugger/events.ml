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

(********************************* Events ******************************)

ouvre Instruct

soit get_pos ev =
  filtre ev.ev_kind avec
  | Event_before -> ev.ev_loc.Location.loc_start
  | Event_after _ -> ev.ev_loc.Location.loc_end
  | _ -> ev.ev_loc.Location.loc_start
;;


(*** Current events. ***)

(* Event at current position *)
soit current_event =
  ref (None : debug_event option)

(* Current position in source. *)
(* Raise `Not_found' if not on an event (beginning or end of program). *)
soit get_current_event () =
  filtre !current_event avec
  | None -> raise Not_found
  | Some ev -> ev

soit current_event_is_before () =
  filtre !current_event avec
    None ->
      raise Not_found
  | Some {ev_kind = Event_before} ->
      vrai
  | _ ->
      faux
