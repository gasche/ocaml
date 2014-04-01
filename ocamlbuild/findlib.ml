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


(* Original author: Romain Bardou *)

ouvre My_std
ouvre My_unix
ouvre Command

type command_spec = Command.spec

type error =
  | Cannot_run_ocamlfind
  | Dependency_not_found de string * string (* package, dependency *)
  | Package_not_found de string
  | Cannot_parse_query de string * string (* package, explaination *)

exception Findlib_error de error

soit error x = raise (Findlib_error x)

soit string_of_error = fonction
  | Cannot_run_ocamlfind ->
      "Cannot run Ocamlfind."
  | Dependency_not_found(p, d) ->
      Printf.sprintf
        "Ocamlfind returned \"%s\" as a dependency for package \"%s\" but does \
not know this dependency." d p
  | Package_not_found p ->
      Printf.sprintf "Findlib package not found: \"%s\"." p
  | Cannot_parse_query(p, e) ->
      Printf.sprintf "Cannot parse Ocamlfind query for package \"%s\": %s" p e

soit report_error e =
  prerr_endline (string_of_error e);
  exit 2

soit ocamlfind = "ocamlfind"

type package = {
  name: string;
  description: string;
  version: string;
  archives_byte: string;
  archives_native: string;
  link_options: string;
  location: string;
  dependencies: package list;
}

soit packages = Hashtbl.create 42

soit run_and_parse lexer command =
  Printf.ksprintf
    (fonc command -> lexer & Lexing.from_string & run_and_read command)
    command

soit run_and_read command =
  Printf.ksprintf run_and_read command

soit rec query name =
  essaie
    Hashtbl.find packages name
  avec Not_found ->
    essaie
      soit n, d, v, a_byte, lo, l =
        run_and_parse Lexers.ocamlfind_query
          "%s query -l -predicates byte %s" ocamlfind name
      dans
      soit a_native =
        run_and_parse Lexers.trim_blanks
          "%s query -a-format -predicates native %s" ocamlfind name
      dans
      soit deps =
        run_and_parse Lexers.blank_sep_strings "%s query -r -p-format %s" ocamlfind name
      dans
      soit deps = List.filter ((<>) n) deps dans
      soit deps =
        essaie
          List.map query deps
        avec Findlib_error (Package_not_found dep_name) ->
          (* Ocamlfind cannot find a package which it returned as a dependency.
             This should not happen. *)
          error (Dependency_not_found (name, dep_name))
      dans
      soit package = {
        name = n;
        description = d;
        version = v;
        archives_byte = a_byte;
        archives_native = a_native;
        link_options = lo;
        location = l;
        dependencies = deps;
      } dans
      Hashtbl.add packages n package;
      package
    avec
      | Failure _ ->
          (* TODO: Improve to differenciate whether ocamlfind cannot be
             run or is not installed *)
          error Cannot_run_ocamlfind
      | Lexers.Error (s,_) ->
          error (Cannot_parse_query (name, s))

soit split_nl s =
  soit x = ref [] dans
  soit rec go s =
    soit pos = String.index s '\n' dans
    x := (String.before s pos)::!x;
    go (String.after s (pos + 1))
  dans
  essaie
    go s
  avec Not_found -> !x

soit before_space s =
  essaie
    String.before s (String.index s ' ')
  avec Not_found -> s

soit list () =
  List.map before_space (split_nl & run_and_read "%s list" ocamlfind)

(* The closure algorithm is easy because the dependencies are already closed
and sorted for each package. We only have to make the union. We could also
make another ocamlfind query such as:
  ocamlfind query -p-format -r package1 package2 ... *)
soit topological_closure l =
  soit add l x = si List.mem x l alors l sinon x :: l dans
  soit l = List.fold_left début fonc acc p ->
    add (List.fold_left add acc p.dependencies) p
  fin [] l dans
  List.rev l

module SSet = Set.Make(String)

soit add_atom a l = filtre a, l avec
  | A "", _ -> l
  | _ -> a :: l

soit compile_flags l =
  soit pkgs = topological_closure l dans
  soit locations = List.fold_left début fonc acc p ->
    SSet.add p.location acc
  fin SSet.empty pkgs dans
  soit flags = [] dans
  (* includes *)
  soit flags =
    List.fold_left début fonc acc l ->
      add_atom (P l) (add_atom (A "-I") acc)
    fin flags (SSet.elements locations)
  dans
  S (List.rev flags)
soit compile_flags_byte = compile_flags
soit compile_flags_native = compile_flags

soit link_flags f l =
  soit pkgs = topological_closure l dans
  soit locations = List.fold_left début fonc acc p ->
    SSet.add p.location acc
  fin SSet.empty pkgs dans
  soit flags = [] dans
  (* includes *)
  soit flags =
    List.fold_left début fonc acc l ->
      add_atom (P l) (add_atom (A "-I") acc)
    fin flags (SSet.elements locations)
  dans
  (* special link options *)
  soit flags =
    List.fold_left début fonc acc x ->
      add_atom (A x.link_options) acc
    fin flags pkgs
  dans
  (* archives *)
  soit flags =
    List.fold_left début fonc acc x ->
      add_atom (A (f x)) acc
    fin flags pkgs
  dans
  S (List.rev flags)
soit link_flags_byte = link_flags (fonc x -> x.archives_byte)
soit link_flags_native = link_flags (fonc x -> x.archives_native)
