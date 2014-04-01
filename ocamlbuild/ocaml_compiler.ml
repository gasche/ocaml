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
ouvre Tools
ouvre Command
ouvre Rule
ouvre Tags.Operators
ouvre Ocaml_utils
ouvre Rule.Common_commands
ouvre Outcome

soit forpack_flags arg tags =
  si Tags.mem "pack" tags alors
    Ocaml_arch.forpack_flags_of_pathname arg
  sinon N

soit ocamlc_c tags arg out =
  soit tags = tags++"ocaml"++"byte" dans
  Cmd (S [!Options.ocamlc; A"-c"; T(tags++"compile");
          ocaml_ppflags tags; ocaml_include_flags arg; A"-o"; Px out; P arg])

soit ocamlc_link flag tags deps out =
  Cmd (S [!Options.ocamlc; flag; T tags;
          atomize_paths deps; A"-o"; Px out])

soit ocamlc_link_lib = ocamlc_link (A"-a")
soit ocamlc_link_prog = ocamlc_link N

soit ocamlmklib tags deps out =
  Cmd (S [!Options.ocamlmklib; T tags;
          atomize_paths deps; A"-o"; Px (Pathname.remove_extensions out)])

soit ocamlmktop tags deps out =
  Cmd( S [!Options.ocamlmktop; T (tags++"mktop");
          atomize_paths deps; A"-o"; Px out])

soit byte_lib_linker tags =
  si Tags.mem "ocamlmklib" tags alors
    ocamlmklib tags
  sinon
    ocamlc_link_lib tags

soit byte_lib_linker_tags tags = tags++"ocaml"++"link"++"byte"++"library"

soit ocamlc_p tags deps out =
  Cmd (S [!Options.ocamlc; A"-pack"; T tags;
          atomize_paths deps; A"-o"; Px out])

soit ocamlopt_c tags arg out =
  soit tags = tags++"ocaml"++"native" dans
  Cmd (S [!Options.ocamlopt; A"-c"; Ocaml_arch.forpack_flags_of_pathname arg;
          T(tags++"compile"); ocaml_ppflags tags; ocaml_include_flags arg;
          A"-o"; Px out (* FIXME ocamlopt bug -o cannot be after the input file *); P arg])

soit ocamlopt_link flag tags deps out =
  Cmd (S [!Options.ocamlopt; flag; forpack_flags out tags; T tags;
          atomize_paths deps; A"-o"; Px out])

soit ocamlopt_link_lib = ocamlopt_link (A"-a")
soit ocamlopt_link_shared_lib = ocamlopt_link (A"-shared")
soit ocamlopt_link_prog = ocamlopt_link N

soit ocamlopt_p tags deps out =
  soit dirnames = List.union [] (List.map Pathname.dirname deps) dans
  soit include_flags = List.fold_right ocaml_add_include_flag dirnames [] dans
  soit mli = Pathname.update_extensions "mli" out dans
  soit cmd =
    S [!Options.ocamlopt; A"-pack"; forpack_flags out tags; T tags;
       S include_flags; atomize_paths deps;
       A"-o"; Px out] dans
  si (*FIXME true ||*) Pathname.exists mli alors Cmd cmd
  sinon
    soit rm = S[A"rm"; A"-f"; P mli] dans
    Cmd(S[A"touch"; P mli; Sh" ; if "; cmd; Sh" ; then "; rm; Sh" ; else ";
          rm; Sh" ; exit 1; fi"])

soit native_lib_linker tags =
  si Tags.mem "ocamlmklib" tags alors
    ocamlmklib tags
  sinon
    ocamlopt_link_lib tags

soit native_shared_lib_linker tags =
(* ocamlmklib seems to not support -shared, is this OK?
  if Tags.mem "ocamlmklib" tags then
    ocamlmklib tags
  else
*)
    ocamlopt_link_shared_lib tags

soit native_lib_linker_tags tags = tags++"ocaml"++"link"++"native"++"library"


soit prepare_compile build ml =
  soit dir = Pathname.dirname ml dans
  soit include_dirs = Pathname.include_dirs_of dir dans
  soit modules = path_dependencies_of ml dans
  soit results =
    build (List.map (fonc (_, x) -> expand_module include_dirs x ["cmi"]) modules) dans
  List.iter2 début fonc (mandatory, name) res ->
    filtre mandatory, res avec
    | _, Good _ -> ()
    | `mandatory, Bad exn ->
        si !Options.ignore_auto alors
          dprintf 3 "Warning: Failed to build the module \
                     %s requested by ocamldep" name
        sinon raise exn
    | `just_try, Bad _ -> ()
  fin modules results

soit byte_compile_ocaml_interf mli cmi env build =
  soit mli = env mli et cmi = env cmi dans
  prepare_compile build mli;
  ocamlc_c (tags_of_pathname mli++"interf") mli cmi

(* given that .cmi can be built from either ocamlc and ocamlopt, this
   "agnostic" rule chooses either compilers depending on whether the
   "native" tag is present. This was requested during PR#4613 as way
   to enable using ocamlbuild in environments where only ocamlopt is
   available, not ocamlc. *)
soit compile_ocaml_interf mli cmi env build =
  soit mli = env mli et cmi = env cmi dans
  prepare_compile build mli;
  soit tags = tags_of_pathname mli++"interf" dans 
  soit comp_c = si Tags.mem "native" tags alors ocamlopt_c sinon ocamlc_c dans
  comp_c tags mli cmi

soit byte_compile_ocaml_implem ?tag ml cmo env build =
  soit ml = env ml et cmo = env cmo dans
  prepare_compile build ml;
  ocamlc_c (Tags.union (tags_of_pathname ml) (tags_of_pathname cmo)++"implem"+++tag) ml cmo

soit cache_prepare_link = Hashtbl.create 107
soit rec prepare_link tag cmx extensions build =
  soit key = (tag, cmx, extensions) dans
  soit dir = Pathname.dirname cmx dans
  soit include_dirs = Pathname.include_dirs_of dir dans
  soit ml = Pathname.update_extensions "ml" cmx dans
  soit mli = Pathname.update_extensions "mli" cmx dans
  soit modules =
    List.union
      (si Pathname.exists (ml-.-"depends") alors path_dependencies_of ml sinon [])
      (si Pathname.exists (mli-.-"depends") alors path_dependencies_of mli sinon [])
  dans
  soit modules =
    si (modules = []) && (Pathname.exists (ml^"pack")) alors
      List.map (fonc s -> (`mandatory, s)) (string_list_of_file (ml^"pack"))
    sinon
      modules
  dans
  si modules <> [] && not (Hashtbl.mem cache_prepare_link key) alors
    soit () = Hashtbl.add cache_prepare_link key vrai dans
    soit modules' = List.map (fonc (_, x) -> expand_module include_dirs x extensions) modules dans
    List.iter2 début fonc (mandatory, _) result ->
      filtre mandatory, result avec
      | _, Good p -> prepare_link tag p extensions build
      | `mandatory, Bad exn -> si not !Options.ignore_auto alors raise exn
      | `just_try, Bad _ -> ()
    fin modules (build modules')

soit native_compile_ocaml_implem ?tag ?(cmx_ext="cmx") ml env build =
  soit ml = env ml dans
  soit cmi = Pathname.update_extensions "cmi" ml dans
  soit cmx = Pathname.update_extensions cmx_ext ml dans
  prepare_link cmx cmi [cmx_ext; "cmi"] build;
  ocamlopt_c (Tags.union (tags_of_pathname ml) (tags_of_pathname cmx)++"implem"+++tag) ml cmx

soit libs_of_use_lib tags =
  Tags.fold début fonc tag acc ->
    essaie soit libpath, extern = Hashtbl.find info_libraries tag dans
        si extern alors acc sinon libpath :: acc
    avec Not_found -> acc
  fin tags []

soit prepare_libs cma_ext a_ext out build =
  soit out_no_ext = Pathname.remove_extension out dans
  soit libs1 = List.union (libraries_of out_no_ext) (libs_of_use_lib (tags_of_pathname out)) dans
  soit () = dprintf 10 "prepare_libs: %S -> %a" out pp_l libs1 dans
  soit libs = List.map (fonc x -> x-.-cma_ext) libs1 dans
  soit libs2 = List.map (fonc lib -> [lib-.-a_ext]) libs1 dans
  List.iter ignore_good (build libs2); libs

soit library_index = Hashtbl.create 32
soit package_index = Hashtbl.create 32
soit hidden_packages = ref []

soit hide_package_contents package = hidden_packages := package :: !hidden_packages

module Ocaml_dependencies_input = struct
  soit fold_dependencies = Resource.Cache.fold_dependencies
  soit fold_libraries f = Hashtbl.fold f library_index
  soit fold_packages f = Hashtbl.fold f package_index
fin
module Ocaml_dependencies = Ocaml_dependencies.Make(Ocaml_dependencies_input)

soit caml_transitive_closure = Ocaml_dependencies.caml_transitive_closure

soit link_one_gen linker tagger cmX out env _build =
  soit cmX = env cmX et out = env out dans
  soit tags = tagger (tags_of_pathname out) dans
  linker tags [cmX] out

soit link_gen cmX_ext cma_ext a_ext extensions linker tagger cmX out env build =
  soit cmX = env cmX et out = env out dans
  soit tags = tagger (tags_of_pathname out) dans
  soit dyndeps = Rule.build_deps_of_tags build (tags++"link_with") dans
  soit cmi = Pathname.update_extensions "cmi" cmX dans
  prepare_link cmX cmi extensions build;
  soit libs = prepare_libs cma_ext a_ext out build dans
  soit hidden_packages = List.map (fonc x -> x-.-cmX_ext) !hidden_packages dans
  soit deps =
    caml_transitive_closure
      ~caml_obj_ext:cmX_ext ~caml_lib_ext:cma_ext
      ~used_libraries:libs ~hidden_packages (cmX :: dyndeps) dans
  soit deps = (List.filter (fonc l -> not (List.mem l deps)) libs) @ deps dans

  (* Hack to avoid linking twice with the standard library. *)
  soit stdlib = "stdlib/stdlib"-.-cma_ext dans
  soit is_not_stdlib x = x <> stdlib dans
  soit deps = List.filter is_not_stdlib deps dans

  si deps = [] alors failwith "La liste de liens ne peut pas être vide";
  soit () = dprintf 6 "link: %a -o %a" print_string_list deps Pathname.print out dans
  linker (tags++"dont_link_with") deps out

soit byte_link_gen = link_gen "cmo" "cma" "cma" ["cmo"; "cmi"]

soit byte_link = byte_link_gen ocamlc_link_prog
  (fonc tags -> tags++"ocaml"++"link"++"byte"++"program")

soit byte_output_obj = byte_link_gen ocamlc_link_prog
  (fonc tags -> tags++"ocaml"++"link"++"byte"++"output_obj")

soit byte_library_link = byte_link_gen byte_lib_linker byte_lib_linker_tags

soit byte_debug_link_gen =
  link_gen "d.cmo" "d.cma" "d.cma" ["d.cmo"; "cmi"]

soit byte_debug_link = byte_debug_link_gen ocamlc_link_prog
  (fonc tags -> tags++"ocaml"++"link"++"byte"++"debug"++"program")

soit byte_debug_library_link = byte_debug_link_gen byte_lib_linker
  (fonc tags -> byte_lib_linker_tags tags++"debug")

soit native_link_gen linker =
  link_gen "cmx" "cmxa" !Options.ext_lib [!Options.ext_obj; "cmi"] linker

soit native_link x = native_link_gen ocamlopt_link_prog
  (fonc tags -> tags++"ocaml"++"link"++"native"++"program") x

soit native_output_obj x = native_link_gen ocamlopt_link_prog
  (fonc tags -> tags++"ocaml"++"link"++"native"++"output_obj") x

soit native_library_link x =
  native_link_gen native_lib_linker native_lib_linker_tags x

soit native_profile_link_gen linker =
  link_gen "p.cmx" "p.cmxa" ("p" -.- !Options.ext_lib) ["p" -.- !Options.ext_obj; "cmi"] linker

soit native_profile_link x = native_profile_link_gen ocamlopt_link_prog
  (fonc tags -> tags++"ocaml"++"link"++"native"++"profile"++"program") x

soit native_profile_library_link x = native_profile_link_gen native_lib_linker
  (fonc tags -> native_lib_linker_tags tags++"profile") x

soit link_units table extensions cmX_ext cma_ext a_ext linker tagger contents_list cmX env build =
  soit cmX = env cmX dans
  soit tags = tagger (tags_of_pathname cmX) dans
  soit _ = Rule.build_deps_of_tags build tags dans
  soit dir =
    soit dir1 = Pathname.remove_extensions cmX dans
    si Resource.exists_in_source_dir dir1 alors dir1
    sinon Pathname.dirname cmX dans
  soit include_dirs = Pathname.include_dirs_of dir dans
  soit extension_keys = List.map fst extensions dans
  soit libs = prepare_libs cma_ext a_ext cmX build dans
  soit results =
    build début
      List.map début fonc module_name ->
        expand_module include_dirs module_name extension_keys
      fin contents_list
    fin dans
  soit module_paths =
    List.map début fonction
      | Good p ->
          soit extension_values = List.assoc (Pathname.get_extensions p) extensions dans
          List.iter début fonc ext ->
            List.iter ignore_good (build [[Pathname.update_extensions ext p]])
          fin extension_values; p
      | Bad exn -> raise exn
    fin results dans
  Hashtbl.replace table cmX module_paths;
  soit hidden_packages = List.map (fonc x -> x-.-cmX_ext) !hidden_packages dans
  soit deps =
    caml_transitive_closure
      ~caml_obj_ext:cmX_ext ~caml_lib_ext:cma_ext
      ~hidden_packages ~pack_mode:vrai module_paths dans
  soit full_contents = libs @ module_paths dans
  soit deps = List.filter (fonc x -> List.mem x full_contents) deps dans
  soit deps = (List.filter (fonc l -> not (List.mem l deps)) libs) @ deps dans

  (* Hack to avoid linking twice with the standard library. *)
  soit stdlib = "stdlib/stdlib"-.-cma_ext dans
  soit is_not_stdlib x = x <> stdlib dans
  soit deps = List.filter is_not_stdlib deps dans

  linker tags deps cmX

soit link_modules = link_units library_index
soit pack_modules = link_units package_index

soit link_from_file link modules_file cmX env build =
  soit modules_file = env modules_file dans
  soit contents_list = string_list_of_file modules_file dans
  link contents_list cmX env build

soit byte_library_link_modules =
  link_modules [("cmo",[])] "cmo" "cma" "cma" byte_lib_linker byte_lib_linker_tags

soit byte_library_link_mllib = link_from_file byte_library_link_modules

soit byte_toplevel_link_modules =
  link_modules [("cmo",[])] "cmo" "cma" "cma" ocamlmktop
               (fonc tags -> tags++"ocaml"++"link"++"byte"++"toplevel")

soit byte_toplevel_link_mltop = link_from_file byte_toplevel_link_modules

soit byte_debug_library_link_modules =
  link_modules [("d.cmo",[])] "d.cmo" "d.cma" "d.cma" byte_lib_linker
    (fonc tags -> byte_lib_linker_tags tags++"debug")

soit byte_debug_library_link_mllib = link_from_file byte_debug_library_link_modules

soit byte_pack_modules =
  pack_modules [("cmo",["cmi"]); ("cmi",[])] "cmo" "cma" "cma" ocamlc_p
    (fonc tags -> tags++"ocaml"++"pack"++"byte")

soit byte_pack_mlpack = link_from_file byte_pack_modules

soit byte_debug_pack_modules =
  pack_modules [("d.cmo",["cmi"]); ("cmi",[])] "d.cmo" "d.cma" "d.cma" ocamlc_p
    (fonc tags -> tags++"ocaml"++"pack"++"byte"++"debug")

soit byte_debug_pack_mlpack = link_from_file byte_debug_pack_modules

soit native_pack_modules x =
  pack_modules [("cmx",["cmi"; !Options.ext_obj]); ("cmi",[])] "cmx" "cmxa" !Options.ext_lib ocamlopt_p
    (fonc tags -> tags++"ocaml"++"pack"++"native") x

soit native_pack_mlpack = link_from_file native_pack_modules

soit native_profile_pack_modules x =
  pack_modules [("p.cmx",["cmi"; "p" -.- !Options.ext_obj]); ("cmi",[])] "p.cmx" "p.cmxa"
    ("p" -.- !Options.ext_lib) ocamlopt_p
    (fonc tags -> tags++"ocaml"++"pack"++"native"++"profile") x

soit native_profile_pack_mlpack = link_from_file native_profile_pack_modules

soit native_library_link_modules x =
  link_modules [("cmx",[!Options.ext_obj])] "cmx" "cmxa"
     !Options.ext_lib native_lib_linker native_lib_linker_tags x

soit native_shared_library_link_modules x =
  link_modules [("cmx",[!Options.ext_obj])] "cmx" "cmxa"
     !Options.ext_lib native_shared_lib_linker
     (fonc tags -> native_lib_linker_tags tags++"shared") x

soit native_library_link_mllib = link_from_file native_library_link_modules

soit native_shared_library_link_mldylib = link_from_file native_shared_library_link_modules

soit native_shared_library_tags tags basetags =
  List.fold_left (++) (basetags++"ocaml"++"link"++"native"++"shared"++"library") tags

soit native_shared_library_link ?(tags = []) x =
  link_one_gen native_shared_lib_linker
    (native_shared_library_tags tags) x

soit native_profile_library_link_modules x =
  link_modules [("p.cmx",["p" -.- !Options.ext_obj])] "p.cmx" "p.cmxa"
    ("p" -.- !Options.ext_lib) native_lib_linker
    (fonc tags -> native_lib_linker_tags tags++"profile") x

soit native_profile_shared_library_link_modules x =
  link_modules [("p.cmx",["p" -.- !Options.ext_obj])] "p.cmx" "p.cmxa"
    ("p" -.- !Options.ext_lib) native_shared_lib_linker
    (fonc tags -> native_lib_linker_tags tags++"shared"++"profile") x

soit native_profile_library_link_mllib = link_from_file native_profile_library_link_modules

soit native_profile_shared_library_link_mldylib = link_from_file native_profile_shared_library_link_modules
