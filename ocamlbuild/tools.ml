(***********************************************************************)
(*                                                                     *)
(*                             ocamlbuild                              *)
(*                                                                     *)
(*  Nicolas Pouillard, Berke Durak, projet Gallium, INRIA Rocquencourt *)
(*                                                                     *)
(*  Copyright 2007 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)


(* Original author: Nicolas Pouillard *)
(* Tools *)

ouvre My_std
ouvre Format
ouvre Log
ouvre Pathname.Operators
ouvre Tags.Operators
ouvre Rule

soit pp_l = List.print String.print

soit tags_of_pathname p =
  Configuration.tags_of_filename (Pathname.to_string p)
  ++("file:"^p)
  ++("extension:"^Pathname.get_extension p)

soit opt_print elt ppf =
  fonction
  | Some x -> fprintf ppf "@[<2>Some@ %a@]" elt x
  | None -> pp_print_string ppf "None"

soit path_and_context_of_string s =
  si Pathname.is_implicit s alors
    soit b = Pathname.basename s dans
    soit d = Pathname.dirname s dans
    si d <> Pathname.current_dir_name alors
      soit () = Pathname.define_context d [d] dans
      [s]
    sinon
      soit include_dirs = Pathname.include_dirs_of d dans
      List.map (fonc include_dir -> include_dir/b) include_dirs
  sinon [s]
