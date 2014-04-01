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
ouvre Rule
ouvre Tools
ouvre Command
;;


soit plugin                = "myocamlbuild"
soit plugin_file           = plugin^".ml"
soit plugin_config_file    = plugin^"_config.ml"
soit plugin_config_file_interface = plugin^"_config.mli"
soit we_need_a_plugin ()      = !Options.plugin && sys_file_exists plugin_file
soit we_have_a_plugin ()      = sys_file_exists ((!Options.build_dir/plugin)^(!Options.exe))
soit we_have_a_config_file () = sys_file_exists plugin_config_file
soit we_have_a_config_file_interface () = sys_file_exists plugin_config_file_interface

module Make(U:sig fin) =
  struct
    soit we_need_a_plugin = we_need_a_plugin ()
    soit we_have_a_plugin = we_have_a_plugin ()
    soit we_have_a_config_file = we_have_a_config_file ()
    soit we_have_a_config_file_interface = we_have_a_config_file_interface ()
    soit up_to_date_or_copy fn =
      soit fn' = !Options.build_dir/fn dans
      Pathname.exists fn &&
        début
          Pathname.exists fn' && Pathname.same_contents fn fn' ||
          début
            Shell.cp fn fn';
            faux
          fin
        fin

    soit rebuild_plugin_if_needed () =
      soit a = up_to_date_or_copy plugin_file dans
      soit b = (not we_have_a_config_file) || up_to_date_or_copy plugin_config_file dans
      soit c = (not we_have_a_config_file_interface) || up_to_date_or_copy plugin_config_file_interface dans
      si a && b && c && we_have_a_plugin alors
        () (* Up to date *)
           (* FIXME: remove ocamlbuild_config.ml in _build/ if removed in parent *)
      sinon début
        si !Options.native_plugin
            && not (sys_file_exists ((!Ocamlbuild_where.libdir)/"ocamlbuildlib.cmxa")) alors
          début
            Options.native_plugin := faux;
            eprintf "Warning: Won't be able to compile a native plugin"
          fin;
        soit plugin_config =
          si we_have_a_config_file alors
            si we_have_a_config_file_interface alors
              S[P plugin_config_file_interface; P plugin_config_file]
            sinon P plugin_config_file
          sinon N dans

        soit cma, cmo, compiler, byte_or_native =
          si !Options.native_plugin alors
            "cmxa", "cmx", !Options.ocamlopt, "native"
          sinon
            "cma", "cmo", !Options.ocamlc, "byte"
        dans


        soit (unix_spec, ocamlbuild_lib_spec, ocamlbuild_module_spec) =

          soit use_light_mode =
            not !Options.native_plugin && !*My_unix.is_degraded dans
          soit use_ocamlfind_pkgs =
            !Options.use_ocamlfind && !Options.plugin_tags <> [] dans
          (* The plugin has the following dependencies that must be
             included during compilation:

             - unix.cmxa, if it is available
             - ocamlbuildlib.cm{a,xa}, the library part of ocamlbuild
             - ocamlbuild.cm{o,x}, the module that performs the
               initialization work of the ocamlbuild executable, using
               modules of ocamlbuildlib.cmxa

             We pass all this stuff to the compilation command for the
             plugin, with two independent important details to handle:

             (1) ocamlbuild is designed to still work in environments
             where Unix is not available for some reason; in this
             case, we should not link unix, and use the
             "ocamlbuildlight.cmo" initialization module, which runs
             a "light" version of ocamlbuild without unix. There is
             also an ocamlbuildlightlib.cma archive to be used in that
             case.

             The boolean variable [use_light_mode] tells us whether we
             are in this unix-deprived scenario.

             (2) there are risks of compilation error due to
             double-linking of native modules when the user passes its
             own tags to the plugin compilation process (as was added
             to support modular construction of
             ocamlbuild plugins). Indeed, if we hard-code linking to
             unix.cmxa in all cases, and the user
             enables -use-ocamlfind and
             passes -plugin-tag "package(unix)" (or package(foo) for
             any foo which depends on unix), the command-line finally
             executed will be

               ocamlfind ocamlopt unix.cmxa -package unix myocamlbuild.ml

             which fails with a compilation error due to doubly-passed
             native modules.

             To sanest way to solve this problem at the ocamlbuild level
             is to pass "-package unix" instead of unix.cmxa when we
             detect that such a situation may happen. OCamlfind will see
             that the same package is demanded twice, and only request
             it once to the compiler. Similarly, we use "-package
             ocamlbuild" instead of linking ocamlbuildlib.cmxa[1].

             We switch to this behavior when two conditions, embodied in
             the boolean variable [use_ocamlfind_pkgs], are met:
             (a) use-ocamlfind is enabled
             (b) the user is passing some plugin tags

             Condition (a) is overly conservative as the double-linking
             issue may also happen in non-ocamlfind situations, such as
             "-plugin-tags use_unix" -- but it's unclear how one would
             avoid the issue in that case, except by documenting that
             people should not do that, or getting rid of the
             hard-linking logic entirely, with the corresponding risks
             of regression.

             Condition (b) should not be necessary (we expect using
             ocamlfind packages to work whenever ocamlfind
             is available), but allows the behavior in absence
             of -plugin-tags to be completely unchanged, to reassure us
             about potential regressions introduced by this option.

             [1]: we may wonder whether to use "-package ocamlbuildlight"
             in unix-deprived situations, but currently ocamlfind
             doesn't know about the ocamlbuildlight library. As
             a compromise we always use "-package ocamlbuild" when
             use_ocamlfind_pkgs is set. An ocamlfind and -plugin-tags
             user in unix-deprived environment may want to mutate the
             META of ocamlbuild to point to ocamlbuildlightlib instead
             of ocamlbuildlib.
          *)

          soit unix_lib =
            si use_ocamlfind_pkgs alors `Package "unix"
            sinon si use_light_mode alors `Nothing
            sinon `Lib "unix" dans

          soit ocamlbuild_lib =
            si use_ocamlfind_pkgs alors `Package "ocamlbuild"
            sinon si use_light_mode alors `Local_lib "ocamlbuildlightlib"
            sinon `Local_lib "ocamlbuildlib" dans

          soit ocamlbuild_module =
            si use_light_mode alors `Local_mod "ocamlbuildlight"
            sinon `Local_mod "ocamlbuild" dans

          soit dir = !Ocamlbuild_where.libdir dans
          soit dir = si Pathname.is_implicit dir alors Pathname.pwd/dir sinon dir dans

          soit in_dir file =
            soit path = dir/file dans
            si not (sys_file_exists path) alors failwith
              (sprintf "Cannot find %S in ocamlbuild -where directory" file);
            path dans

          soit spec = fonction
            | `Nothing -> N
            | `Package pkg -> S[A "-package"; A pkg]
            | `Lib lib -> P (lib -.- cma)
            | `Local_lib llib -> S [A "-I"; A dir; P (in_dir (llib -.- cma))]
            | `Local_mod lmod -> P (in_dir (lmod -.- cmo)) dans

          (spec unix_lib, spec ocamlbuild_lib, spec ocamlbuild_module)
        dans

        soit plugin_tags =
          Tags.of_list !Options.plugin_tags
          ++ "ocaml" ++ "program" ++ "link" ++ byte_or_native dans

        (* The plugin is compiled before [Param_tags.init()] is called
           globally, which means that parametrized tags have not been
           made effective yet. The [partial_init] calls below initializes
           precisely those that will be used during the compilation of
           the plugin, and no more.
        *)
        Param_tags.partial_init plugin_tags;

        soit cmd =
          (* The argument order is important: we carefully put the
             plugin source files before the ocamlbuild.cm{o,x} module
             doing the main initialization, so that user global
             side-effects (setting options, installing flags..) are
             performed brefore ocamlbuild's main routine. This is
             a fragile thing to rely upon and we insist that our users
             use the more robust [dispatch] registration instead, but
             we still aren't going to break that now.

             For the same reason we place the user plugin-tags after
             the plugin libraries (in case a tag would, say, inject
             a .cmo that also relies on them), but before the main
             plugin source file and ocamlbuild's initialization. *)
          Cmd(S[compiler;
                unix_spec; ocamlbuild_lib_spec;
                T plugin_tags;
                plugin_config; P plugin_file;
                ocamlbuild_module_spec;
                A"-o"; Px (plugin^(!Options.exe))])
        dans
        Shell.chdir !Options.build_dir;
        Shell.rm_f (plugin^(!Options.exe));
        Command.execute cmd;
        si !Options.just_plugin alors début
          Log.finish ();
          raise Exit_OK;
        fin;
      fin

    soit execute_plugin_if_needed () =
      si we_need_a_plugin alors
        début
          rebuild_plugin_if_needed ();
          Shell.chdir Pathname.pwd;
          soit runner = si !Options.native_plugin alors N sinon !Options.ocamlrun dans
          soit argv = List.tl (Array.to_list Sys.argv) dans
          soit passed_argv = List.filter (fonc s -> s <> "-plugin-option") argv dans
          soit spec = S[runner; P(!Options.build_dir/plugin^(!Options.exe));
                       A"-no-plugin"; atomize passed_argv] dans
          Log.finish ();
          soit rc = sys_command (Command.string_of_command_spec spec) dans
          raise (Exit_silently_with_code rc);
        fin
      sinon si not (sys_file_exists plugin_file) && !Options.plugin_tags <> [] alors
        eprintf "Warning: option -plugin-tag(s) has no effect \
                 in absence of plugin file %S" plugin_file
      sinon
        ()
  fin
;;

soit execute_plugin_if_needed () =
  soit module P = Make(struct fin) dans
  P.execute_plugin_if_needed ()
;;
