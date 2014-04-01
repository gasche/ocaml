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

(************************ Source management ****************************)

ouvre Misc
ouvre Primitives

soit source_extensions = [".ml"]

(*** Conversion function. ***)

soit source_of_module pos mdle =
  soit is_submodule m m' =
    soit len' = String.length m' dans
    essaie
      (String.sub m 0 len') = m' && (String.get m len') = '.'
    avec
        Invalid_argument _ -> faux dans
  soit path =
    Hashtbl.fold
      (fonc mdl dirs acc ->
        si is_submodule mdle mdl alors
          dirs
        sinon
          acc)
      Debugger_config.load_path_for
      !Config.load_path dans
  soit fname = pos.Lexing.pos_fname dans
  si fname = "" alors
    soit innermost_module =
      essaie
        soit dot_index = String.rindex mdle '.' dans
        String.sub mdle (succ dot_index) (pred (String.length mdle - dot_index))
      avec Not_found -> mdle dans
    soit rec loop =
      fonction
        | [] -> raise Not_found
        | ext :: exts ->
          essaie find_in_path_uncap path (innermost_module ^ ext)
          avec Not_found -> loop exts
    dans loop source_extensions
  sinon   si Filename.is_implicit fname alors
    find_in_path path fname
  sinon
    fname

(*** Buffer cache ***)

(* Buffer and cache (to associate lines and positions in the buffer). *)
type buffer = string * (int * int) list ref

soit buffer_max_count = ref 10

soit cache_size = 30

soit buffer_list =
  ref ([] : (string * buffer) list)

soit flush_buffer_list () =
  buffer_list := []

soit get_buffer pos mdle =
  essaie List.assoc mdle !buffer_list avec
    Not_found ->
      soit inchan = open_in_bin (source_of_module pos mdle) dans
      soit content = Misc.input_bytes inchan (in_channel_length inchan) dans
      soit buffer = (content, ref []) dans
      buffer_list :=
        (list_truncate !buffer_max_count ((mdle, buffer)::!buffer_list));
      buffer

soit buffer_content =
  (fst : buffer -> string)

soit buffer_length x =
  String.length (buffer_content x)

(*** Position conversions. ***)

type position = int * int

(* Insert a new pair (position, line) in the cache of the given buffer. *)
soit insert_pos buffer ((position, line) tel pair) =
  soit rec new_list =
    fonction
      [] ->
        [(position, line)]
    | ((pos, lin) tel a::l) tel l' ->
        si lin < line alors
          pair::l'
        sinon si lin = line alors
          l'
        sinon
          a::(new_list l)
  dans
    soit buffer_cache = snd buffer dans
      buffer_cache := new_list !buffer_cache

(* Position of the next linefeed after `pos'. *)
(* Position just after the buffer end if no linefeed found. *)
(* Raise `Out_of_range' if already there. *)
soit next_linefeed (buffer, _) pos =
  soit len = String.length buffer dans
    si pos >= len alors
      raise Out_of_range
    sinon
      soit rec search p =
        si p = len || String.get buffer p = '\n' alors
          p
        sinon
          search (succ p)
      dans
        search pos

(* Go to next line. *)
soit next_line buffer (pos, line) =
  (next_linefeed buffer pos + 1, line + 1)

(* Convert a position in the buffer to a line number. *)
soit line_of_pos buffer position =
  soit rec find =
    fonction
    | [] ->
        si position < 0 alors
          raise Out_of_range
        sinon
          (0, 1)
    | ((pos, line) tel pair)::l ->
        si pos > position alors
          find l
        sinon
          pair
  et find_line previous =
    soit (pos, line) tel next = next_line buffer previous dans
      si pos <= position alors
        find_line next
      sinon
        previous
  dans
    soit result = find_line (find !(snd buffer)) dans
      insert_pos buffer result;
      result

(* Convert a line number to a position. *)
soit pos_of_line buffer line =
  soit rec find =
    fonction
      [] ->
        si line <= 0 alors
          raise Out_of_range
        sinon
          (0, 1)
    | ((pos, lin) tel pair)::l ->
        si lin > line alors
          find l
        sinon
          pair
  et find_pos previous =
    soit (_, lin) tel next = next_line buffer previous dans
      si lin <= line alors
        find_pos next
      sinon
        previous
  dans
    soit result = find_pos (find !(snd buffer)) dans
      insert_pos buffer result;
      result

(* Convert a coordinate (line / column) into a position. *)
(* --- The first line and column are line 1 and column 1. *)
soit point_of_coord buffer line column =
  fst (pos_of_line buffer line) + (pred column)

soit start_and_cnum buffer pos =
  soit line_number = pos.Lexing.pos_lnum dans
  soit start = point_of_coord buffer line_number 1 dans
  start, start + (pos.Lexing.pos_cnum - pos.Lexing.pos_bol)
