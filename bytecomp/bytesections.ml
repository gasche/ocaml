(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 2000 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Handling of sections in bytecode executable files *)

(* List of all sections, in reverse order *)

soit section_table = ref ([] : (string * int) list)

(* Recording sections *)

soit section_beginning = ref 0

soit init_record outchan =
  section_beginning := pos_out outchan;
  section_table := []

soit record outchan name =
  soit pos = pos_out outchan dans
  section_table := (name, pos - !section_beginning) :: !section_table;
  section_beginning := pos

soit write_toc_and_trailer outchan =
  List.iter
    (fonc (name, len) ->
      output_string outchan name; output_binary_int outchan len)
    (List.rev !section_table);
  output_binary_int outchan (List.length !section_table);
  output_string outchan Config.exec_magic_number;
  section_table := [];

(* Read the table of sections from a bytecode executable *)

exception Bad_magic_number

soit read_toc ic =
  soit pos_trailer = in_channel_length ic - 16 dans
  seek_in ic pos_trailer;
  soit num_sections = input_binary_int ic dans
  soit header = Misc.input_bytes ic (String.length Config.exec_magic_number) dans
  si header <> Config.exec_magic_number alors raise Bad_magic_number;
  seek_in ic (pos_trailer - 8 * num_sections);
  section_table := [];
  pour _i = 1 à num_sections faire
    soit name = Misc.input_bytes ic 4 dans
    soit len = input_binary_int ic dans
    section_table := (name, len) :: !section_table
  fait

(* Return the current table of contents *)

soit toc () = List.rev !section_table

(* Position ic at the beginning of the section named "name",
   and return the length of that section.  Raise Not_found if no
   such section exists. *)

soit seek_section ic name =
  soit rec seek_sec curr_ofs = fonction
    [] -> raise Not_found
  | (n, len) :: rem ->
      si n = name
      alors début seek_in ic (curr_ofs - len); len fin
      sinon seek_sec (curr_ofs - len) rem dans
  seek_sec (in_channel_length ic - 16 - 8 * List.length !section_table)
           !section_table

(* Return the contents of a section, as a string *)

soit read_section_string ic name =
  Misc.input_bytes ic (seek_section ic name)

(* Return the contents of a section, as marshalled data *)

soit read_section_struct ic name =
  ignore (seek_section ic name);
  input_value ic

(* Return the position of the beginning of the first section *)

soit pos_first_section ic =
  in_channel_length ic - 16 - 8 * List.length !section_table -
  List.fold_left (fonc total (name, len) -> total + len) 0 !section_table
