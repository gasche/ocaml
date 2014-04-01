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
ouvre My_std
ouvre Log
ouvre Pathname.Operators
ouvre Command
ouvre Tools
ouvre Ocaml_specific
ouvre Format
;;

exception Exit_build_error de string
exception Exit_silently

soit clean () =
  Log.finish ();
  Shell.rm_rf !Options.build_dir;
  si !Options.make_links alors début
    soit entry =
      Slurp.map (fonc _ _ _ -> vrai)
        (Slurp.slurp Filename.current_dir_name)
    dans
    Slurp.force (Resource.clean_up_links entry)
  fin;
  raise Exit_silently
;;

soit show_tags () =
  si List.length !Options.show_tags > 0 alors
    Log.eprintf "Warning: the following tags do not include \
    dynamically-generated tags, such as link, compile, pack, byte, native, c, \
    pdf... (this list is by no means exhaustive).\n";
  List.iter début fonc path ->
    Log.eprintf "@[<2>Tags for %S:@ {. %a .}@]" path Tags.print (tags_of_pathname path)
  fin !Options.show_tags
;;

soit show_documentation () =
  Rule.show_documentation ();
  Flags.show_documentation ();
;;

(* these tags are used in an ad-hoc way by the ocamlbuild implementation;
   this means that even if they were not part of any flag declaration,
   they should be marked as useful, to avoid the "unused tag" warning. *)
soit builtin_useful_tags =
  Tags.of_list
    ["include"; "traverse"; "not_hygienic";
     "pack"; "ocamlmklib"; "native"; "thread"; "nopervasives"]
;;

soit proceed () =
  Hooks.call_hook Hooks.Before_options;
  Options.init ();
  si !Options.must_clean alors clean ();
  Hooks.call_hook Hooks.After_options;
  soit options_wd = Sys.getcwd () dans
  soit first_run_for_plugin =
    (* If we are in the first run before launching the plugin, we
       should skip the user-visible operations (hygiene) that may need
       information from the plugin to run as the user expects it.
       
       Note that we don't need to disable the [Hooks] call as they are
       no-ops anyway, before any plugin has registered hooks. *)
    Plugin.we_need_a_plugin () && not !Options.just_plugin dans

  soit target_dirs = List.union [] (List.map Pathname.dirname !Options.targets) dans

  Configuration.parse_string
    "<**/*.ml> or <**/*.mli> or <**/*.mlpack> or <**/*.ml.depends>: ocaml\n\
     <**/*.byte>: ocaml, byte, program\n\
     <**/*.odoc>: ocaml, doc\n\
     <**/*.native>: ocaml, native, program\n\
     <**/*.cma>: ocaml, byte, library\n\
     <**/*.cmxa>: ocaml, native, library\n\
     <**/*.cmo>: ocaml, byte\n\
     <**/*.cmi>: ocaml, byte, native\n\
     <**/*.cmx>: ocaml, native\n\
    ";

  Configuration.tag_any !Options.tags;
  si !Options.recursive
  || Sys.file_exists (* authorized since we're not in build *) "_tags"
  || Sys.file_exists (* authorized since we're not in build *) "myocamlbuild.ml"
  alors Configuration.tag_any ["traverse"];

  (* options related to findlib *)
  List.iter
    (fonc pkg -> Configuration.tag_any [Param_tags.make "package" pkg])
    !Options.ocaml_pkgs;

  début filtre !Options.ocaml_syntax avec
  | Some syntax -> Configuration.tag_any [Param_tags.make "syntax" syntax]
  | None -> () fin;

  soit newpwd = Sys.getcwd () dans
  Sys.chdir Pathname.pwd;
  soit entry_include_dirs = ref [] dans
  soit entry =
    Slurp.filter
      début fonc path name _ ->
        soit dir =
          si path = Filename.current_dir_name alors
            None
          sinon
            Some path
        dans
        soit path_name = path/name dans
        si name = "_tags" alors
          ignore (Configuration.parse_file ?dir path_name);

        (List.mem name ["_oasis"] || (String.length name > 0 && name.[0] <> '_'))
        && (name <> !Options.build_dir && not (List.mem name !Options.exclude_dirs))
        && début
          not (path_name <> Filename.current_dir_name && Pathname.is_directory path_name)
          || début
            soit tags = tags_of_pathname path_name dans
            (si Tags.mem "include" tags
              || List.mem path_name !Options.include_dirs alors
              (entry_include_dirs := path_name :: !entry_include_dirs; vrai)
            sinon
              Tags.mem "traverse" tags
              || List.exists (Pathname.is_prefix path_name) !Options.include_dirs
              || List.exists (Pathname.is_prefix path_name) target_dirs)
            && ((* beware: !Options.build_dir is an absolute directory *)
                Pathname.normalize !Options.build_dir
                <> Pathname.normalize (Pathname.pwd/path_name))
          fin
        fin
      fin
      (Slurp.slurp Filename.current_dir_name)
  dans
  Hooks.call_hook Hooks.Before_hygiene;
  soit hygiene_entry =
    Slurp.map début fonc path name () ->
      soit tags = tags_of_pathname (path/name) dans
      not (Tags.mem "not_hygienic" tags) && not (Tags.mem "precious" tags)
    fin entry dans
  si !Options.hygiene && not first_run_for_plugin alors
    Fda.inspect hygiene_entry
  sinon
    Slurp.force hygiene_entry;
  soit entry = hygiene_entry dans
  Hooks.call_hook Hooks.After_hygiene;
  Options.include_dirs := Pathname.current_dir_name :: List.rev !entry_include_dirs;
  dprintf 3 "include directories are:@ %a" print_string_list !Options.include_dirs;
  Options.entry := Some entry;

  List.iter Configuration.parse_string !Options.tag_lines;

  Hooks.call_hook Hooks.Before_rules;
  Ocaml_specific.init ();
  Hooks.call_hook Hooks.After_rules;

  Sys.chdir options_wd;
  Plugin.execute_plugin_if_needed ();

  (* [Param_tags.init ()] is called *after* the plugin is executed, as
     some of the parametrized tags present in the _tags files parsed
     will be declared by the plugin, and would therefore result in
     "tag X does not expect a parameter" warnings if initialized
     before. Note that [Plugin.rebuild_plugin_if_needed] is careful to
     partially initialize the tags that it uses for plugin compilation. *)
  Param_tags.init ();

  Sys.chdir newpwd;
  (*let () = dprintf 0 "source_dir_path_set:@ %a" StringSet.print source_dir_path_set*)

  si !Options.show_documentation alors début
    show_documentation ();
    raise Exit_silently
  fin;

  soit all_tags = Tags.union builtin_useful_tags (Flags.get_used_tags ()) dans
  Configuration.check_tags_usage all_tags;

  Digest_cache.init ();

  Sys.catch_break vrai;

  show_tags ();

  soit targets =
    List.map début fonc starget ->
      soit starget = Resource.import starget dans
      soit target = path_and_context_of_string starget dans
      soit ext = Pathname.get_extension starget dans
      (target, starget, ext)
    fin !Options.targets dans

  essaie
    soit targets =
      List.map début fonc (target, starget, ext) ->
        Shell.mkdir_p (Pathname.dirname starget);
        soit target = Solver.solve_target starget target dans
        (target, ext)
      fin targets dans

    Command.dump_parallel_stats ();

    Log.finish ();

    Shell.chdir Pathname.pwd;

    soit call spec = sys_command (Command.string_of_command_spec spec) dans

    soit cmds =
      List.fold_right début fonc (target, ext) acc ->
        soit cmd = !Options.build_dir/target dans
        soit link x =
          si !Options.make_links alors ignore (call (S [A"ln"; A"-sf"; P x; A Pathname.current_dir_name])) dans
        filtre ext avec
        | "byte" | "native" | "top" ->
            link cmd; cmd :: acc
        | "html" ->
            link (Pathname.dirname cmd); acc
        | _ ->
            si !Options.program_to_execute alors
              eprintf "Warning: Won't execute %s whose extension is neither .byte nor .native" cmd;
            acc
      fin targets [] dans

    si !Options.program_to_execute alors
      début
        filtre List.rev cmds avec
        | [] -> raise (Exit_usage "Using -- requires one target");
        | cmd :: rest ->
          si rest <> [] alors dprintf 0 "Warning: Using -- only run the last target";
          soit cmd_spec = S [P cmd; atomize !Options.program_args] dans
          dprintf 3 "Running the user command:@ %a" Pathname.print cmd;
          raise (Exit_with_code (call cmd_spec)) (* Exit with the exit code of the called command *)
      fin
    sinon
      ()
  avec
  | Ocaml_dependencies.Circular_dependencies(seen, p) ->
      raise
        (Exit_build_error
          (sbprintf "@[<2>Circular dependencies: %S already seen in@ %a@]@." p pp_l seen))
;;

ouvre Exit_codes;;

soit main () =
  soit exit rc =
    Log.finish ~how:(si rc <> 0 alors `Error sinon `Success) ();
    Pervasives.exit rc
  dans
  essaie
    proceed ()
  avec e ->
    si !Options.catch_errors alors
      essaie raise e avec
      | Exit_OK -> exit rc_ok
      | Fda.Exit_hygiene_failed ->
          Log.eprintf "Exiting due to hygiene violations.";
          exit rc_hygiene
      | Exit_usage u ->
          Log.eprintf "Usage:@ %s." u;
          exit rc_usage
      | Exit_system_error msg ->
          Log.eprintf "System error:@ %s." msg;
          exit rc_system_error
      | Exit_with_code rc ->
          exit rc
      | Exit_silently ->
          Log.finish ~how:`Quiet ();
          Pervasives.exit rc_ok
      | Exit_silently_with_code rc ->
          Log.finish ~how:`Quiet ();
          Pervasives.exit rc
      | Solver.Failed backtrace ->
          Log.raw_dprintf (-1) "@[<v0>@[<2>Solver failed:@ %a@]@\n@[<v2>Backtrace:%a@]@]@."
            Report.print_backtrace_analyze backtrace Report.print_backtrace backtrace;
          exit rc_solver_failed
      | Failure s ->
          Log.eprintf "Failure:@ %s." s;
          exit rc_failure
      | Solver.Circular(r, rs) ->
          Log.eprintf "Circular build detected@ (%a already seen in %a)"
          Resource.print r (List.print Resource.print) rs;
          exit rc_circularity
      | Invalid_argument s ->
          Log.eprintf
            "INTERNAL ERROR: Invalid argument %s\n\
            This is likely to be a bug, please report this to the ocamlbuild\n\
            developers." s;
          exit rc_invalid_argument
      | Ocaml_utils.Ocamldep_error msg ->
          Log.eprintf "Ocamldep error: %s" msg;
          exit rc_ocamldep_error
      | Lexers.Error (msg,loc) ->
          Log.eprintf "%aLexing error: %s." Loc.print_loc loc msg;
          exit rc_lexing_error
      | Arg.Bad msg ->
          Log.eprintf "%s" msg;
          exit rc_usage
      | Exit_build_error msg ->
          Log.eprintf "%s" msg;
          exit rc_build_error
      | Arg.Help msg ->
          Log.eprintf "%s" msg;
          exit rc_ok
      | e ->
          essaie
            Log.eprintf "%a" My_unix.report_error e;
            exit 100
          avec
          | e ->
            Log.eprintf "Exception@ %s." (Printexc.to_string e);
            exit 100
    sinon raise e
;;
