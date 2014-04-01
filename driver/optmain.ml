(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

ouvre Config
ouvre Clflags
ouvre Compenv

soit process_interface_file ppf name =
  Optcompile.interface ppf name (output_prefix name)

soit process_implementation_file ppf name =
  soit opref = output_prefix name dans
  Optcompile.implementation ppf name opref;
  objfiles := (opref ^ ".cmx") :: !objfiles

soit cmxa_present = ref faux;;

soit process_file ppf name =
  si Filename.check_suffix name ".ml"
  || Filename.check_suffix name ".mlt" alors
    process_implementation_file ppf name
  sinon si Filename.check_suffix name !Config.interface_suffix alors début
    soit opref = output_prefix name dans
    Optcompile.interface ppf name opref;
    si !make_package alors objfiles := (opref ^ ".cmi") :: !objfiles
  fin
  sinon si Filename.check_suffix name ".cmx" alors
    objfiles := name :: !objfiles
  sinon si Filename.check_suffix name ".cmxa" alors début
    cmxa_present := vrai;
    objfiles := name :: !objfiles
  fin sinon si Filename.check_suffix name ".cmi" && !make_package alors
    objfiles := name :: !objfiles
  sinon si Filename.check_suffix name ext_obj
       || Filename.check_suffix name ext_lib alors
    ccobjs := name :: !ccobjs
  sinon si Filename.check_suffix name ".c" alors début
    Optcompile.c_file name;
    ccobjs := (Filename.chop_suffix (Filename.basename name) ".c" ^ ext_obj)
              :: !ccobjs
  fin
  sinon
    raise(Arg.Bad("don't know what to do with " ^ name))

soit usage = "Usage: ocamlopt <options> <files>\nOptions are:"

soit ppf = Format.err_formatter

(* Error messages to standard error formatter *)
soit anonymous filename =
  readenv ppf Before_compile; process_file ppf filename;;
soit impl filename =
  readenv ppf Before_compile; process_implementation_file ppf filename;;
soit intf filename =
  readenv ppf Before_compile; process_interface_file ppf filename;;

soit show_config () =
  Config.print_config stdout;
  exit 0;
;;

module Options = Main_args.Make_optcomp_options (struct
  soit set r () = r := vrai
  soit clear r () = r := faux

  soit _a = set make_archive
  soit _absname = set Location.absname
  soit _annot = set annotations
  soit _binannot = set binary_annotations
  soit _c = set compile_only
  soit _cc s = c_compiler := Some s
  soit _cclib s = ccobjs := Misc.rev_split_words s @ !ccobjs
  soit _ccopt s = first_ccopts := s :: !first_ccopts
  soit _compact = clear optimize_for_speed
  soit _config () = show_config ()
  soit _for_pack s = for_package := Some s
  soit _g = set debug
  soit _i () = print_types := vrai; compile_only := vrai
  soit _I dir = include_dirs := dir :: !include_dirs
  soit _impl = impl
  soit _inline n = inline_threshold := n * 8
  soit _intf = intf
  soit _intf_suffix s = Config.interface_suffix := s
  soit _keep_locs = set keep_locs
  soit _labels = clear classic
  soit _linkall = set link_everything
  soit _no_app_funct = clear applicative_functors
  soit _noassert = set noassert
  soit _noautolink = set no_auto_link
  soit _nodynlink = clear dlcode
  soit _nolabels = set classic
  soit _nostdlib = set no_std_include
  soit _o s = output_name := Some s
  soit _output_obj = set output_c_object
  soit _p = set gprofile
  soit _pack = set make_package
  soit _pp s = preprocessor := Some s
  soit _ppx s = first_ppx := s :: !first_ppx
  soit _principal = set principal
  soit _rectypes = set recursive_types
  soit _runtime_variant s = runtime_variant := s
  soit _short_paths = clear real_paths
  soit _strict_sequence = set strict_sequence
  soit _trans_mod = set transparent_modules
  soit _shared () = shared := vrai; dlcode := vrai
  soit _S = set keep_asm_file
  soit _thread = set use_threads
  soit _unsafe = set fast
  soit _v () = print_version_and_library "compilateur de code natif"
  soit _version () = print_version_string ()
  soit _vnum () = print_version_string ()
  soit _verbose = set verbose
  soit _w s = Warnings.parse_options faux s
  soit _warn_error s = Warnings.parse_options vrai s
  soit _warn_help = Warnings.help_warnings
  soit _where () = print_standard_library ()

  soit _nopervasives = set nopervasives
  soit _dsource = set dump_source
  soit _dparsetree = set dump_parsetree
  soit _dtypedtree = set dump_typedtree
  soit _drawlambda = set dump_rawlambda
  soit _dlambda = set dump_lambda
  soit _dclambda = set dump_clambda
  soit _dcmm = set dump_cmm
  soit _dsel = set dump_selection
  soit _dcombine = set dump_combine
  soit _dlive () = dump_live := vrai; Printmach.print_live := vrai
  soit _dspill = set dump_spill
  soit _dsplit = set dump_split
  soit _dinterf = set dump_interf
  soit _dprefer = set dump_prefer
  soit _dalloc = set dump_regalloc
  soit _dreload = set dump_reload
  soit _dscheduling = set dump_scheduling
  soit _dlinear = set dump_linear
  soit _dstartup = set keep_startup_file

  soit anonymous = anonymous
fin);;

soit main () =
  native_code := vrai;
  soit ppf = Format.err_formatter dans
  essaie
    readenv ppf Before_args;
    Arg.parse (Arch.command_line_options @ Options.list) anonymous usage;
    readenv ppf Before_link;
    si
      List.length (List.filter (fonc x -> !x)
                     [make_package; make_archive; shared;
                      compile_only; output_c_object]) > 1
    alors
      fatal "Please specify at most one of -pack, -a, -shared, -c, -output-obj";
    si !make_archive alors début
      si !cmxa_present alors
        fatal "Option -a cannot be used with .cmxa input files.";
      Compmisc.init_path vrai;
      soit target = extract_output !output_name dans
      Asmlibrarian.create_archive (get_objfiles ()) target;
      Warnings.check_fatal ();
    fin
    sinon si !make_package alors début
      Compmisc.init_path vrai;
      soit target = extract_output !output_name dans
      Asmpackager.package_files ppf (get_objfiles ()) target;
      Warnings.check_fatal ();
    fin
    sinon si !shared alors début
      Compmisc.init_path vrai;
      soit target = extract_output !output_name dans
      Asmlink.link_shared ppf (get_objfiles ()) target;
      Warnings.check_fatal ();
    fin
    sinon si not !compile_only && !objfiles <> [] alors début
      soit target =
        si !output_c_object alors
          soit s = extract_output !output_name dans
          si (Filename.check_suffix s Config.ext_obj
            || Filename.check_suffix s Config.ext_dll)
          alors s
          sinon
            fatal
              (Printf.sprintf
                 "The extension of the output file must be %s or %s"
                 Config.ext_obj Config.ext_dll
              )
        sinon
          default_output !output_name
      dans
      Compmisc.init_path vrai;
      Asmlink.link ppf (get_objfiles ()) target;
      Warnings.check_fatal ();
    fin;
    exit 0
  avec x ->
      Location.report_exception ppf x;
      exit 2

soit _ = main ()
