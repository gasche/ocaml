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
(* Report *)

ouvre My_std
ouvre Log
ouvre Format
ouvre Solver

soit sources_glob = Glob.parse "<*.ml> or <*.mli> or <*.c> or <*.h>";;

soit rec analyze f bt =
  filtre bt avec
  | Leaf r ->
      fprintf f "Ocamlbuild knows of no rules that apply to a target named %a. \
                 This can happen if you ask Ocamlbuild to build a target with the \
                 wrong extension (e.g. .opt instead of .native) or if the source \
                 files live in directories that have not been specified as \
                 include directories."
              Resource.print r;
      faux
  | Depth(r, bt) ->
      si Glob.eval sources_glob r alors
        début
          fprintf f "Ocamlbuild cannot find or build %a.  A file with such a name would \
                     usually be a source file.  I suspect you have given a wrong target \
                     name to Ocamlbuild."
                  Resource.print r;
          faux
        fin
      sinon
        analyze f bt
  | Choice bl -> List.for_all (analyze f) bl
  | Target(_, bt) -> analyze f bt

soit rec print_backtrace f =
  fonction
  | Target (name, backtrace) ->
      fprintf f "@\n- @[<2>Failed to build the target %s%a@]" name print_backtrace backtrace
  | Leaf r ->
      fprintf f "@\n- @[<2>Building %a@]" Resource.print r
  | Depth (r, backtrace) ->
      fprintf f "@\n- @[<v2>Building %a:%a@]" Resource.print r print_backtrace backtrace
  | Choice [backtrace] -> print_backtrace f backtrace
  | Choice backtraces ->
      fprintf f "@\n- @[<v2>Failed to build all of these:";
      List.iter (print_backtrace f) backtraces;
      fprintf f "@]"

soit print_backtrace_analyze f bt = ignore (analyze f bt)
