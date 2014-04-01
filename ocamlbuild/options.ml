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

soit version = "ocamlbuild "^(Sys.ocaml_version);;

type command_spec = Command.spec

ouvre My_std
ouvre Arg
ouvre Format
ouvre Command

soit entry = ref None
soit build_dir = ref (Filename.concat (Sys.getcwd ()) "_build")
soit include_dirs = ref []
soit exclude_dirs = ref []
soit nothing_should_be_rebuilt = ref faux
soit sanitize = ref vrai
soit sanitization_script = ref "sanitize.sh"
soit hygiene = ref vrai
soit ignore_auto = ref vrai
soit plugin = ref vrai
soit just_plugin = ref faux
soit native_plugin = ref vrai
soit make_links = ref vrai
soit nostdlib = ref faux
soit use_menhir = ref faux
soit catch_errors = ref vrai
soit use_ocamlfind = ref vrai

(* Currently only ocamlfind and menhir is defined as no-core tool,
   perhaps later we need something better *)
soit is_core_tool = fonction "ocamlfind" | "menhir" -> faux | _ -> vrai

soit find_tool cmd =
  soit dir = Ocamlbuild_where.bindir dans
  soit core_tool = is_core_tool cmd dans
  soit opt = cmd ^ ".opt" dans
  soit search_in_path = memo Command.search_in_path dans
  si sys_file_exists !dir alors
    soit long = filename_concat !dir cmd dans
    soit long_opt = long ^ ".opt" dans
      (* This defines how the command will be found *)
    soit choices =
      [(fonc () -> si file_or_exe_exists long_opt alors Some long_opt sinon None);
       (fonc () -> si file_or_exe_exists long alors Some long sinon None)] dans
      (* For non core tool the preference is too look at PATH first *)
    soit choices' =
      [fonc () ->
        essaie soit _ = search_in_path opt dans Some opt
        avec Not_found -> Some cmd]
    dans
    soit choices = si core_tool alors choices @ choices' sinon choices' @ choices dans
    essaie
      filtre (List.find (fonc choice -> not (choice () = None)) choices) () avec
        Some cmd -> cmd
      | None -> raise Not_found
    avec Not_found -> failwith (Printf.sprintf "Can't find tool: %s" cmd)
  sinon
    essaie soit _ = search_in_path opt dans opt
    avec Not_found -> cmd

soit mk_virtual_solvers =
  List.iter début fonc cmd ->
    soit solver () =
      A (find_tool cmd)
    dans Command.setup_virtual_command_solver (String.uppercase cmd) solver
  fin

soit () =
  mk_virtual_solvers
    ["ocamlc"; "ocamlopt"; "ocamldep"; "ocamldoc";
    "ocamlyacc"; "menhir"; "ocamllex"; "ocamlmklib"; "ocamlmktop"; "ocamlfind"]
soit ocamlc = ref (V"OCAMLC")
soit ocamlopt = ref (V"OCAMLOPT")
soit ocamldep = ref (V"OCAMLDEP")
soit ocamldoc = ref (V"OCAMLDOC")
soit ocamlyacc = ref N
soit ocamllex = ref (V"OCAMLLEX")
soit ocamlmklib = ref (V"OCAMLMKLIB")
soit ocamlmktop = ref (V"OCAMLMKTOP")
soit ocamlrun = ref N
soit ocamlfind_cmd = ref (V"OCAMLFIND")
soit ocamlfind arg = S[!ocamlfind_cmd; arg]
soit program_to_execute = ref faux
soit must_clean = ref faux
soit show_documentation = ref faux
soit recursive = ref faux
soit ext_lib = ref Ocamlbuild_config.a
soit ext_obj = ref Ocamlbuild_config.o
soit ext_dll = ref Ocamlbuild_config.so
soit exe = ref Ocamlbuild_config.exe

soit targets_internal = ref []
soit ocaml_libs_internal = ref []
soit ocaml_mods_internal = ref []
soit ocaml_pkgs_internal = ref []
soit ocaml_syntax = ref None
soit ocaml_lflags_internal = ref []
soit ocaml_cflags_internal = ref []
soit ocaml_docflags_internal = ref []
soit ocaml_ppflags_internal = ref []
soit ocaml_yaccflags_internal = ref []
soit ocaml_lexflags_internal = ref []
soit program_args_internal = ref []
soit ignore_list_internal = ref []
soit tags_internal = ref [["quiet"]]
soit tag_lines_internal = ref []
soit show_tags_internal = ref []
soit plugin_tags_internal = ref []
soit log_file_internal = ref "_log"

soit my_include_dirs = ref [[Filename.current_dir_name]]
soit my_exclude_dirs = ref [[".svn"; "CVS"]]

soit dummy = "*invalid-dummy-string*";; (* Dummy string for delimiting the latest argument *)

(* The JoCaml support will be in a plugin when the plugin system will support
 * multiple/installed plugins *)
soit use_jocaml () =
  ocamlc := A "jocamlc";
  ocamlopt := A "jocamlopt";
  ocamldep := A "jocamldep";
  ocamlyacc := A "jocamlyacc";
  ocamllex := A "jocamllex";
  ocamlmklib := A "jocamlmklib";
  ocamlmktop := A "jocamlmktop";
  ocamlrun := A "jocamlrun";
;;

soit add_to rxs x =
  soit xs = Lexers.comma_or_blank_sep_strings (Lexing.from_string x) dans
  rxs := xs :: !rxs
soit add_to' rxs x =
  si x <> dummy alors
    rxs := [x] :: !rxs
  sinon
    ()
soit set_cmd rcmd = String (fonc s -> rcmd := Sh s)
soit set_build_dir s =
  make_links := faux;
  si Filename.is_relative s alors
    build_dir := Filename.concat (Sys.getcwd ()) s
  sinon
    build_dir := s
soit spec = ref (
  Arg.align
  [
   "-version", Unit (fonc () -> print_endline version; raise Exit_OK), " Display the version";
   "-vnum", Unit (fonc () -> print_endline Sys.ocaml_version; raise Exit_OK),
            " Display the version number";
   "-quiet", Unit (fonc () -> Log.level := 0), " Make as quiet as possible";
   "-verbose", Int (fonc i -> Log.classic_display := vrai; Log.level := i + 2), "<level> Set the verbosity level";
   "-documentation", Set show_documentation, " Show rules and flags";
   "-log", Set_string log_file_internal, "<file> Set log file";
   "-no-log", Unit (fonc () -> log_file_internal := ""), " No log file";
   "-clean", Set must_clean, " Remove build directory and other files, then exit";
   "-r", Set recursive, " Traverse directories by default (true: traverse)";

   "-I", String (add_to' my_include_dirs), "<path> Add to include directories";
   "-Is", String (add_to my_include_dirs), "<path,...> (same as above, but accepts a (comma or blank)-separated list)";
   "-X", String (add_to' my_exclude_dirs), "<path> Directory to ignore";
   "-Xs", String (add_to my_exclude_dirs), "<path,...> (idem)";

   "-lib", String (add_to' ocaml_libs_internal), "<flag> Link to this ocaml library";
   "-libs", String (add_to ocaml_libs_internal), "<flag,...> (idem)";
   "-mod", String (add_to' ocaml_mods_internal), "<module> Link to this ocaml module";
   "-mods", String (add_to ocaml_mods_internal), "<module,...> (idem)";
   "-pkg", String (add_to' ocaml_pkgs_internal), "<package> Link to this ocaml findlib package";
   "-pkgs", String (add_to ocaml_pkgs_internal), "<package,...> (idem)";
   "-package", String (add_to' ocaml_pkgs_internal), "<package> (idem)";
   "-syntax", String (fonc syntax -> ocaml_syntax := Some syntax), "<syntax> Specify syntax using ocamlfind";
   "-lflag", String (add_to' ocaml_lflags_internal), "<flag> Add to ocamlc link flags";
   "-lflags", String (add_to ocaml_lflags_internal), "<flag,...> (idem)";
   "-cflag", String (add_to' ocaml_cflags_internal), "<flag> Add to ocamlc compile flags";
   "-cflags", String (add_to ocaml_cflags_internal), "<flag,...> (idem)";
   "-docflag", String (add_to' ocaml_docflags_internal), "<flag> Add to ocamldoc flags";
   "-docflags", String (add_to ocaml_docflags_internal), "<flag,...> (idem)";
   "-yaccflag", String (add_to' ocaml_yaccflags_internal), "<flag> Add to ocamlyacc flags";
   "-yaccflags", String (add_to ocaml_yaccflags_internal), "<flag,...> (idem)";
   "-lexflag", String (add_to' ocaml_lexflags_internal), "<flag> Add to ocamllex flags";
   "-lexflags", String (add_to ocaml_lexflags_internal), "<flag,...> (idem)";
   "-ppflag", String (add_to' ocaml_ppflags_internal), "<flag> Add to ocaml preprocessing flags";
   "-pp", String (add_to ocaml_ppflags_internal), "<flag,...> (idem)";
   "-tag", String (add_to' tags_internal), "<tag> Add to default tags";
   "-tags", String (add_to tags_internal), "<tag,...> (idem)";
   "-plugin-tag", String (add_to' plugin_tags_internal), "<tag> Use this tag when compiling the myocamlbuild.ml plugin";
   "-plugin-tags", String (add_to plugin_tags_internal), "<tag,...> (idem)";
   "-tag-line", String (add_to' tag_lines_internal), "<tag> Use this line of tags (as in _tags)";
   "-show-tags", String (add_to' show_tags_internal), "<path> Show tags that applies on that pathname";

   "-ignore", String (add_to ignore_list_internal), "<module,...> Don't try to build these modules";
   "-no-links", Clear make_links, " Don't make links of produced final targets";
   "-no-skip", Clear ignore_auto, " Don't skip modules that are requested by ocamldep but cannot be built";
   "-no-hygiene", Clear hygiene, " Don't apply sanity-check rules";
   "-no-plugin", Clear plugin, " Don't build myocamlbuild.ml";
   "-no-stdlib", Set nostdlib, " Don't ignore stdlib modules";
   "-dont-catch-errors", Clear catch_errors, " Don't catch and display exceptions (useful to display the call stack)";
   "-just-plugin", Set just_plugin, " Just build myocamlbuild.ml";
   "-byte-plugin", Clear native_plugin, " Don't use a native plugin but bytecode";
   "-plugin-option", String ignore, " Use the option only when plugin is run";
   "-sanitization-script", Set_string sanitization_script, " Change the file name for the generated sanitization script";
   "-no-sanitize", Clear sanitize, " Do not generate sanitization script";
   "-nothing-should-be-rebuilt", Set nothing_should_be_rebuilt, " Fail if something needs to be rebuilt";
   "-classic-display", Set Log.classic_display, " Display executed commands the old-fashioned way";
   "-use-menhir", Set use_menhir, " Use menhir instead of ocamlyacc";
   "-use-jocaml", Unit use_jocaml, " Use jocaml compilers instead of ocaml ones";
   "-use-ocamlfind", Set use_ocamlfind, " Option deprecated. Now enabled by default. Use -no-ocamlfind to disable";
   "-no-ocamlfind", Clear use_ocamlfind, " Don't use ocamlfind";

   "-j", Set_int Command.jobs, "<N> Allow N jobs at once (0 for unlimited)";

   "-build-dir", String set_build_dir, "<path> Set build directory (implies no-links)";
   "-install-lib-dir", Set_string Ocamlbuild_where.libdir, "<path> Set the install library directory";
   "-install-bin-dir", Set_string Ocamlbuild_where.bindir, "<path> Set the install binary directory";
   "-where", Unit (fonc () -> print_endline !Ocamlbuild_where.libdir; raise Exit_OK), " Display the install library directory";
   "-which", String (fonc cmd -> print_endline (find_tool cmd); raise Exit_OK), "<command> Display path to the tool command";
   "-ocamlc", set_cmd ocamlc, "<command> Set the OCaml bytecode compiler";
   "-ocamlopt", set_cmd ocamlopt, "<command> Set the OCaml native compiler";
   "-ocamldep", set_cmd ocamldep, "<command> Set the OCaml dependency tool";
   "-ocamldoc", set_cmd ocamldoc, "<command> Set the OCaml documentation generator";
   "-ocamlyacc", set_cmd ocamlyacc, "<command> Set the ocamlyacc tool";
   "-menhir", set_cmd ocamlyacc, "<command> Set the menhir tool (use it after -use-menhir)";
   "-ocamllex", set_cmd ocamllex, "<command> Set the ocamllex tool";
   (* Not set since we perhaps want to replace ocamlmklib *)
   (* "-ocamlmklib", set_cmd ocamlmklib, "<command> Set the ocamlmklib tool"; *)
   "-ocamlmktop", set_cmd ocamlmktop, "<command> Set the ocamlmktop tool";
   "-ocamlrun", set_cmd ocamlrun, "<command> Set the ocamlrun tool";

   "--", Rest (fonc x -> program_to_execute := vrai; add_to' program_args_internal x),
   " Stop argument processing, remaining arguments are given to the user program";
  ])

soit add x =
  spec := !spec @ [x]

soit targets = ref []
soit ocaml_libs = ref []
soit ocaml_mods = ref []
soit ocaml_pkgs = ref []
soit ocaml_lflags = ref []
soit ocaml_cflags = ref []
soit ocaml_ppflags = ref []
soit ocaml_docflags = ref []
soit ocaml_yaccflags = ref []
soit ocaml_lexflags = ref []
soit program_args = ref []
soit ignore_list = ref []
soit tags = ref []
soit tag_lines = ref []
soit show_tags = ref []
soit plugin_tags = ref []

soit init () =
  soit anon_fun = add_to' targets_internal dans
  soit usage_msg = sprintf "Usage %s [options] <target>" Sys.argv.(0) dans
  soit argv' = Array.concat [Sys.argv; [|dummy|]] dans
  parse_argv argv' !spec anon_fun usage_msg;
  Shell.mkdir_p !build_dir;

  soit () =
    soit log = !log_file_internal dans
    si log = "" alors Log.init None
    sinon si not (Filename.is_implicit log) alors
      failwith
        (sprintf "Nom de fichier de journal incorrect: le nom de fichier doit être implicite (pas %S)" log)
    sinon
      soit log = filename_concat !build_dir log dans
      Shell.mkdir_p (Filename.dirname log);
      Shell.rm_f log;
      soit log = si !Log.level > 0 alors Some log sinon None dans
      Log.init log
  dans

  si !use_ocamlfind alors début
    ocamlfind_cmd := A "ocamlfind";
    soit cmd = Command.string_of_command_spec !ocamlfind_cmd dans
    début essaie ignore(Command.search_in_path cmd)
    avec Not_found -> failwith "ocamlfind introuvable dans le path, mais -no-ocamlfind n'est pas utilisé" fin;
    (* TODO: warning message when using an option such as -ocamlc *)
    (* Note that plugins can still modify these variables After_options.
       This design decision can easily be changed. *)
    ocamlc := ocamlfind & A"ocamlc";
    ocamlopt := ocamlfind & A"ocamlopt";
    ocamldep := ocamlfind & A"ocamldep";
    ocamldoc := ocamlfind & A"ocamldoc";
    ocamlmktop := ocamlfind & A"ocamlmktop";
  fin;

  soit reorder x y = x := !x @ (List.concat (List.rev !y)) dans
  reorder targets targets_internal;
  reorder ocaml_libs ocaml_libs_internal;
  reorder ocaml_mods ocaml_mods_internal;
  reorder ocaml_pkgs ocaml_pkgs_internal;
  reorder ocaml_cflags ocaml_cflags_internal;
  reorder ocaml_lflags ocaml_lflags_internal;
  reorder ocaml_ppflags ocaml_ppflags_internal;
  reorder ocaml_docflags ocaml_docflags_internal;
  reorder ocaml_yaccflags ocaml_yaccflags_internal;
  reorder ocaml_lexflags ocaml_lexflags_internal;
  reorder program_args program_args_internal;
  reorder tags tags_internal;
  reorder tag_lines tag_lines_internal;
  reorder ignore_list ignore_list_internal;
  reorder show_tags show_tags_internal;
  reorder plugin_tags plugin_tags_internal;

  soit check_dir dir =
    si Filename.is_implicit dir alors
      sys_file_exists dir
    sinon
      failwith
        (sprintf "Les répertoires inclus ou exclus doivent être implicites (not %S)" dir)
  dans
  soit dir_reorder my dir =
    soit d = !dir dans
    reorder dir my;
    dir := List.filter check_dir (!dir @ d)
  dans
  dir_reorder my_include_dirs include_dirs;
  dir_reorder my_exclude_dirs exclude_dirs;

  ignore_list := List.map String.capitalize !ignore_list
;;
