(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../../LICENSE.  *)
(*                                                                     *)
(***********************************************************************)

(* Print the digests of unit interfaces *)

soit load_path = ref []
soit first = ref vrai

soit print_crc unit =
  essaie
    soit crc = Dynlink.digest_interface unit (!load_path @ ["."]) dans
    si !first alors first := faux sinon print_string ";\n";
    print_string "  \""; print_string (String.capitalize unit);
    print_string "\",\n    \"";
    pour i = 0 à String.length crc - 1 faire
      Printf.printf "\\%03d" (Char.code crc.[i])
    fait;
    print_string "\""
  avec exn ->
    prerr_string "Error while reading the interface for ";
    prerr_endline unit;
    début filtre exn avec
      Sys_error msg -> prerr_endline msg
    | Dynlink.Error(Dynlink.File_not_found name) ->
        prerr_string "Cannot find file "; prerr_endline name
    | Dynlink.Error _ -> prerr_endline "Ill-formed .cmi file"
    | _ -> raise exn
    fin;
    exit 2

soit usage = "Usage: extract_crc [-I <dir>] <files>"

soit main () =
  print_string "let crc_unit_list = [\n";
  Arg.parse
    ["-I", Arg.String(fonc dir -> load_path := !load_path @ [dir]),
           "<dir>  Add <dir> to the list of include directories"]
    print_crc usage;
  print_string "\n]\n"

soit _ = main(); exit 0
