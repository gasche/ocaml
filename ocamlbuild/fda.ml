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


(* Original author: Berke Durak *)
(* FDA *)

ouvre Log
ouvre Hygiene
;;

exception Exit_hygiene_failed
;;

soit laws =
  [
    { law_name = "Leftover OCaml compilation files";
      law_rules = [Not ".cmo"; Not ".cmi"; Not ".cmx"; Not ".cma"; Not ".cmxa"];
      law_penalty = Fail };
    { law_name = "Leftover OCaml type annotation files";
      law_rules = [Not ".annot"];
      law_penalty = Warn };
    { law_name = "Leftover object files";
      law_rules = [Not ".o"; Not ".a"; Not ".so"; Not ".obj"; Not ".lib"; Not ".dll"];
      law_penalty = Fail };
    { law_name = "Leftover ocamlyacc-generated files";
      law_rules = [Implies_not(".mly",".ml"); Implies_not(".mly",".mli")];
      law_penalty = Fail };
    { law_name = "Leftover ocamllex-generated files";
      law_rules = [Implies_not(".mll",".ml")];
      law_penalty = Fail };
    { law_name = "Leftover dependency files";
      law_rules = [Not ".ml.depends"; Not ".mli.depends"];
      law_penalty = Fail }
  ]

soit inspect entry =
  dprintf 5 "Doing sanity checks";
  soit evil = ref faux dans
  filtre Hygiene.check
    ?sanitize:
      début
        si !Options.sanitize alors
          Some(Pathname.concat !Options.build_dir !Options.sanitization_script)
        sinon
          None
      fin
      laws entry
  avec
  | [] -> ()
  | stuff ->
    List.iter
      début fonc (law, msgs) ->
        Printf.printf "%s: %s:\n"
          (filtre law.law_penalty avec
           | Warn -> "Warning"
           | Fail ->
               si not !evil alors
                 début
                   Printf.printf "IMPORTANT: I cannot work with leftover compiled files.\n%!";
                   evil := vrai
                 fin;
              "ERROR")
          law.law_name;
        List.iter
          début fonc msg ->
            Printf.printf "  %s\n" msg
          fin
          msgs
      fin
      stuff;
    si !evil alors raise Exit_hygiene_failed;
;;
