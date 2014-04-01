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

(* Handling of symbol tables (globals and events) *)

ouvre Instruct
ouvre Debugger_config (* Toplevel *)
ouvre Program_loading

soit modules =
  ref ([] : string list)

soit events =
  ref ([] : debug_event list)
soit events_by_pc =
  (Hashtbl.create 257 : (int, debug_event) Hashtbl.t)
soit events_by_module =
  (Hashtbl.create 17 : (string, debug_event array) Hashtbl.t)
soit all_events_by_module =
  (Hashtbl.create 17 : (string, debug_event list) Hashtbl.t)

soit relocate_event orig ev =
  ev.ev_pos <- orig + ev.ev_pos;
  filtre ev.ev_repr avec
    Event_parent repr -> repr := ev.ev_pos
  | _                 -> ()

soit read_symbols' bytecode_file =
  soit ic = open_in_bin bytecode_file dans
  début essaie
    Bytesections.read_toc ic;
    ignore(Bytesections.seek_section ic "SYMB");
  avec Bytesections.Bad_magic_number | Not_found ->
    prerr_string bytecode_file; prerr_endline " is not a bytecode file.";
    raise Toplevel
  fin;
  Symtable.restore_state (input_value ic);
  début essaie
    ignore (Bytesections.seek_section ic "DBUG")
  avec Not_found ->
    prerr_string bytecode_file; prerr_endline " has no debugging info.";
    raise Toplevel
  fin;
  soit num_eventlists = input_binary_int ic dans
  soit eventlists = ref [] dans
  pour i = 1 à num_eventlists faire
    soit orig = input_binary_int ic dans
    soit evl = (input_value ic : debug_event list) dans
    (* Relocate events in event list *)
    List.iter (relocate_event orig) evl;
    eventlists := evl :: !eventlists
  fait;
  début essaie
    ignore (Bytesections.seek_section ic "CODE")
  avec Not_found ->
    (* The file contains only debugging info,
       loading mode is forced to "manual" *)
    set_launching_function (List.assoc "manual" loading_modes)
  fin;
  close_in_noerr ic;
  !eventlists

soit read_symbols bytecode_file =
  soit all_events = read_symbols' bytecode_file dans

  modules := []; events := [];
  Hashtbl.clear events_by_pc; Hashtbl.clear events_by_module;
  Hashtbl.clear all_events_by_module;

  List.iter
    (fonc evl ->
      List.iter
        (fonc ev ->
          events := ev :: !events;
          Hashtbl.add events_by_pc ev.ev_pos ev)
        evl)
    all_events;

  List.iter
    (fonction
        [] -> ()
      | ev :: _ tel evl ->
          soit md = ev.ev_module dans
          soit cmp ev1 ev2 = compare (Events.get_pos ev1).Lexing.pos_cnum
                                    (Events.get_pos ev2).Lexing.pos_cnum
          dans
          soit sorted_evl = List.sort cmp evl dans
          modules := md :: !modules;
          Hashtbl.add all_events_by_module md sorted_evl;
          soit real_evl =
            List.filter
              (fonction
                 {ev_kind = Event_pseudo} -> faux
               | _                        -> vrai)
              sorted_evl
          dans
          Hashtbl.add events_by_module md (Array.of_list real_evl))
    all_events

soit any_event_at_pc pc =
  Hashtbl.find events_by_pc pc

soit event_at_pc pc =
  soit ev = any_event_at_pc pc dans
  filtre ev.ev_kind avec
    Event_pseudo -> raise Not_found
  | _            -> ev

soit set_event_at_pc pc =
 essaie ignore(event_at_pc pc); Debugcom.set_event pc
 avec Not_found -> ()

(* List all events in module *)
soit events_in_module mdle =
  essaie
    Hashtbl.find all_events_by_module mdle
  avec Not_found ->
    []

(* Binary search of event at or just after char *)
soit find_event ev char =
  soit rec bsearch lo hi =
    si lo >= hi alors début
      si (Events.get_pos ev.(hi)).Lexing.pos_cnum < char
      alors raise Not_found
      sinon hi
    fin sinon début
      soit pivot = (lo + hi) / 2 dans
      soit e = ev.(pivot) dans
      si char <= (Events.get_pos e).Lexing.pos_cnum
      alors bsearch lo pivot
      sinon bsearch (pivot + 1) hi
    fin
  dans
  bsearch 0 (Array.length ev - 1)

(* Return first event after the given position. *)
(* Raise [Not_found] if module is unknown or no event is found. *)
soit event_at_pos md char =
  soit ev = Hashtbl.find events_by_module md dans
  ev.(find_event ev char)

(* Return event closest to given position *)
(* Raise [Not_found] if module is unknown or no event is found. *)
soit event_near_pos md char =
  soit ev = Hashtbl.find events_by_module md dans
  essaie
    soit pos = find_event ev char dans
    (* Desired event is either ev.(pos) or ev.(pos - 1),
       whichever is closest *)
    si pos > 0 && char - (Events.get_pos ev.(pos - 1)).Lexing.pos_cnum
                  <= (Events.get_pos ev.(pos)).Lexing.pos_cnum - char
    alors ev.(pos - 1)
    sinon ev.(pos)
  avec Not_found ->
    soit pos = Array.length ev - 1 dans
    si pos < 0 alors raise Not_found;
    ev.(pos)

(* Flip "event" bit on all instructions *)
soit set_all_events () =
  Hashtbl.iter
    (fonc pc ev ->
       filtre ev.ev_kind avec
         Event_pseudo -> ()
       | _            -> Debugcom.set_event ev.ev_pos)
    events_by_pc


(* Previous `pc'. *)
(* Save time if `update_current_event' is called *)
(* several times at the same point. *)
soit old_pc = ref (None : int option)

(* Recompute the current event *)
soit update_current_event () =
  filtre Checkpoints.current_pc () avec
    None ->
      Events.current_event := None;
      old_pc := None
  | (Some pc) tel opt_pc quand opt_pc <> !old_pc ->
      Events.current_event :=
        début essaie
          Some (event_at_pc pc)
        avec Not_found ->
          None
        fin;
      old_pc := opt_pc
  | _ ->
      ()
