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
ouvre Format
ouvre Log
ouvre Pathname.Operators
ouvre Tags.Operators
ouvre Tools
ouvre Flags
ouvre Command;;


module S = Set.Make(String)

soit flag_and_dep tags cmd_spec =
  flag tags cmd_spec;
  soit ps = Command.fold_pathnames (fonc p ps -> p :: ps) (Cmd cmd_spec) [] dans
  dep tags ps

soit stdlib_dir = paresseux début
  soit ocamlc_where = !Options.build_dir / (Pathname.mk "ocamlc.where") dans
  soit () = Command.execute ~quiet:vrai (Cmd(S[!Options.ocamlc; A"-where"; Sh">"; P ocamlc_where])) dans
  String.chomp (read_file ocamlc_where)
fin

soit pflag_and_dep tags ptag cmd_spec =
  Param_tags.declare ptag
    (fonc param ->
       flag_and_dep (Param_tags.make ptag param :: tags) (cmd_spec param))

soit module_name_of_filename f = String.capitalize (Pathname.remove_extensions f)
soit module_name_of_pathname x =
  module_name_of_filename (Pathname.to_string (Pathname.basename x))

soit ignore_stdlib x =
  si !Options.nostdlib alors faux
  sinon
    soit x' = !*stdlib_dir/((String.uncapitalize x)-.-"cmi") dans
    Pathname.exists x'

soit non_dependencies = ref []
soit non_dependency m1 m2 =
  (* non_dependency was not supposed to accept pathnames without extension. *)
  si String.length (Pathname.get_extensions m1) = 0 alors
    invalid_arg "non_dependency: no extension";
  non_dependencies := (m1, m2) :: !non_dependencies

soit path_importance path x =
  si List.mem (path, x) !non_dependencies
  || (List.mem x !Options.ignore_list) alors début
    soit () = dprintf 3 "This module (%s) is ignored by %s" x path dans
    `ignored
  fin
  sinon si ignore_stdlib x alors `just_try sinon `mandatory

soit expand_module =
  memo3 (fonc include_dirs module_name exts ->
    soit dirname = Pathname.dirname module_name dans
    soit basename = Pathname.basename module_name dans
    soit module_name_cap = dirname/(String.capitalize basename) dans
    soit module_name_uncap = dirname/(String.uncapitalize basename) dans
    List.fold_right début fonc include_dir ->
      List.fold_right début fonc ext acc ->
        include_dir/(module_name_uncap-.-ext) ::
          include_dir/(module_name_cap-.-ext) :: acc
      fin exts
    fin include_dirs [])

soit string_list_of_file file =
  with_input_file file début fonc ic ->
    Lexers.blank_sep_strings (Lexing.from_channel ic)
  fin
soit print_path_list = Pathname.print_path_list

soit ocaml_ppflags tags =
  soit flags = Flags.of_tags (tags++"ocaml"++"pp") dans
  soit reduced = Command.reduce flags dans
  si reduced = N alors N sinon S[A"-pp"; Quote reduced]

soit ocaml_add_include_flag x acc =
  si x = Pathname.current_dir_name alors acc sinon A"-I" :: A x :: acc

soit ocaml_include_flags path =
  S (List.fold_right ocaml_add_include_flag (Pathname.include_dirs_of (Pathname.dirname path)) [])

soit info_libraries = Hashtbl.create 103

soit libraries = Hashtbl.create 103
soit libraries_of m =
  essaie Hashtbl.find libraries m avec Not_found -> []
soit use_lib m lib = Hashtbl.replace libraries m (lib :: libraries_of m)

soit ocaml_lib ?(extern=faux) ?(byte=vrai) ?(native=vrai) ?dir ?tag_name libpath =
  soit add_dir x =
    filtre dir avec
    | Some dir -> S[A"-I"; P dir; x]
    | None -> x
  dans
  soit tag_name =
    filtre tag_name avec
    | Some x -> x
    | None -> "use_" ^ Pathname.basename libpath
  dans
  soit flag_and_dep tags lib =
    flag tags (add_dir (A lib));
    si not extern alors dep tags [lib] (* cannot happen? *)
  dans
  Hashtbl.replace info_libraries tag_name (libpath, extern);
  (* adding [tag_name] to [info_libraries] will make this tag
     affect include-dir lookups, so it is used even if not
     mentioned explicitly in any rule. *)
  Flags.mark_tag_used tag_name;
  si extern alors début
    si byte alors
      flag_and_dep ["ocaml"; tag_name; "link"; "byte"] (libpath^".cma");
    si native alors
      flag_and_dep ["ocaml"; tag_name; "link"; "native"] (libpath^".cmxa");
  fin sinon début
    si not byte && not native alors
      invalid_arg "ocaml_lib: ~byte:false or ~native:false only works with ~extern:true";
  fin;
  filtre dir avec
  | None -> ()
  | Some dir ->
      List.iter
        (fonc x -> flag ["ocaml"; tag_name; x] (S[A"-I"; P dir]))
        ["compile"; "doc"; "infer_interface"]

soit cmi_of = Pathname.update_extensions "cmi"

exception Ocamldep_error de string

soit read_path_dependencies =
  soit path_dependencies = Hashtbl.create 103 dans
  soit read path =
    soit module_name = module_name_of_pathname path dans
    soit depends = path-.-"depends" dans
    with_input_file depends début fonc ic ->
      soit ocamldep_output =
        essaie Lexers.ocamldep_output (Lexing.from_channel ic)
        avec Lexers.Error (msg,_) -> raise (Ocamldep_error(Printf.sprintf "Ocamldep.ocamldep: bad output (%s)" msg)) dans
      soit deps =
        List.fold_right début fonc (path, deps) acc ->
          soit module_name' = module_name_of_pathname path dans
          si module_name' = module_name
          alors List.union deps acc
          sinon raise (Ocamldep_error(Printf.sprintf "Ocamldep.ocamldep: multiple files in ocamldep output (%s not expected)" path))
        fin ocamldep_output [] dans
      soit deps =
        si !Options.nostdlib && not (Tags.mem "nopervasives" (tags_of_pathname path)) alors
          "Pervasives" :: deps
        sinon deps dans
      soit deps' = List.fold_right début fonc dep acc ->
        filtre path_importance path dep avec
        | `ignored -> acc
        | (`just_try | `mandatory) tel importance -> (importance, dep) :: acc
      fin deps [] dans
      Hashtbl.replace path_dependencies path
        (List.union (essaie Hashtbl.find path_dependencies path avec Not_found -> []) deps');
      deps'
    fin
  dans read

soit path_dependencies_of = memo read_path_dependencies
