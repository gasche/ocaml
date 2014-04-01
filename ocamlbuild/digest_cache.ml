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

ouvre My_std
ouvre Pathname.Operators

soit digests = Hashtbl.create 103

soit get = Hashtbl.find digests

soit put = Hashtbl.replace digests

soit _digests = paresseux (!Options.build_dir / (Pathname.mk "_digests"))

soit finalize () =
  with_output_file !*_digests début fonc oc ->
    Hashtbl.iter début fonc name digest ->
      Printf.fprintf oc "%S: %S\n" name digest
    fin digests
  fin

soit init () =
  Shell.chdir !Options.build_dir;
  si Pathname.exists !*_digests alors
    with_input_file !*_digests début fonc ic ->
      essaie pendant_que vrai faire
        soit l = input_line ic dans
        Scanf.sscanf l "%S: %S" put
      fait avec End_of_file -> ()
    fin;
  My_unix.at_exit_once finalize
