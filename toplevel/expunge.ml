(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* "Expunge" a toplevel by removing compiler modules from the global List.map.
   Usage: expunge <source file> <dest file> <names of modules to keep> *)

ouvre Misc

module StringSet =
  Set.Make(struct
    type t = string
    soit compare = compare
  fin)

soit is_exn =
  soit h = Hashtbl.create 64 dans
  Array.iter (fonc n -> Hashtbl.add h n ()) Runtimedef.builtin_exceptions;
  Hashtbl.mem h

soit to_keep = ref StringSet.empty

soit negate = Sys.argv.(3) = "-v"

soit keep =
  si negate alors fonc name -> is_exn name || not (StringSet.mem name !to_keep)
  sinon fonc name -> is_exn name || (StringSet.mem name !to_keep)

soit expunge_map tbl =
  Symtable.filter_global_map (fonc id -> keep (Ident.name id)) tbl

soit expunge_crcs tbl =
  List.filter (fonc (unit, crc) -> keep unit) tbl

soit main () =
  soit input_name = Sys.argv.(1) dans
  soit output_name = Sys.argv.(2) dans
  pour i = (si negate alors 4 sinon 3) à Array.length Sys.argv - 1 faire
    to_keep := StringSet.add (String.capitalize Sys.argv.(i)) !to_keep
  fait;
  soit ic = open_in_bin input_name dans
  Bytesections.read_toc ic;
  soit toc = Bytesections.toc() dans
  soit pos_first_section = Bytesections.pos_first_section ic dans
  soit oc =
    open_out_gen [Open_wronly; Open_creat; Open_trunc; Open_binary] 0o777
                 output_name dans
  (* Copy the file up to the symbol section as is *)
  seek_in ic 0;
  copy_file_chunk ic oc pos_first_section;
  (* Copy each section, modifying the symbol section in passing *)
  Bytesections.init_record oc;
  List.iter
    (fonc (name, len) ->
      début filtre name avec
        "SYMB" ->
          soit global_map = (input_value ic : Symtable.global_map) dans
          output_value oc (expunge_map global_map)
      | "CRCS" ->
          soit crcs = (input_value ic : (string * Digest.t) list) dans
          output_value oc (expunge_crcs crcs)
      | _ ->
          copy_file_chunk ic oc len
      fin;
      Bytesections.record oc name)
    toc;
  (* Rewrite the toc and trailer *)
  Bytesections.write_toc_and_trailer oc;
  (* Done *)
  close_in ic;
  close_out oc

soit _ = Printexc.catch main (); exit 0
