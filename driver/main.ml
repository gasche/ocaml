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
  Compile.interface ppf name (output_prefix name)

soit process_implementation_file ppf name =
  soit opref = output_prefix name dans
  Compile.implementation ppf name opref;
  objfiles := (opref ^ ".cmo") :: !objfiles

soit process_file ppf name =
  si Filename.check_suffix name ".ml"
  || Filename.check_suffix name ".mlt" alors début
    soit opref = output_prefix name dans
    Compile.implementation ppf name opref;
    objfiles := (opref ^ ".cmo") :: !objfiles
  fin
  sinon si Filename.check_suffix name !Config.interface_suffix alors début
    soit opref = output_prefix name dans
    Compile.interface ppf name opref;
    si !make_package alors objfiles := (opref ^ ".cmi") :: !objfiles
  fin
  sinon si Filename.check_suffix name ".cmo"
       || Filename.check_suffix name ".cma" alors
    objfiles := name :: !objfiles
  sinon si Filename.check_suffix name ".cmi" && !make_package alors
    objfiles := name :: !objfiles
  sinon si Filename.check_suffix name ext_obj
       || Filename.check_suffix name ext_lib alors
    ccobjs := name :: !ccobjs
  sinon si Filename.check_suffix name ext_dll alors
    dllibs := name :: !dllibs
  sinon si Filename.check_suffix name ".c" alors début
    Compile.c_file name;
    ccobjs := (Filename.chop_suffix (Filename.basename name) ".c" ^ ext_obj)
              :: !ccobjs
  fin
  sinon
    raise(Arg.Bad("don't know what to do with " ^ name))

soit usage = "Usage: ocamlc <options> <files>\nOptions are:"

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

module Options = Main_args.Make_bytecomp_options (struct
  soit set r () = r := vrai
  soit unset r () = r := faux
  soit _a = set make_archive
  soit _absname = set Location.absname
  soit _annot = set annotations
  soit _binannot = set binary_annotations
  soit _c = set compile_only
  soit _cc s = c_compiler := Some s
  soit _cclib s = ccobjs := Misc.rev_split_words s @ !ccobjs
  soit _ccopt s = first_ccopts := s :: !first_ccopts
  soit _compat_32 = set bytecode_compatible_32
  soit _config = show_config
  soit _custom = set custom_runtime
  soit _dllib s = dllibs := Misc.rev_split_words s @ !dllibs
  soit _dllpath s = dllpaths := !dllpaths @ [s]
  soit _g = set debug
  soit _i () = print_types := vrai; compile_only := vrai
  soit _I s = include_dirs := s :: !include_dirs
  soit _impl = impl
  soit _intf = intf
  soit _intf_suffix s = Config.interface_suffix := s
  soit _keep_locs = set keep_locs
  soit _labels = unset classic
  soit _linkall = set link_everything
  soit _make_runtime () =
    custom_runtime := vrai; make_runtime := vrai; link_everything := vrai
  soit _no_app_funct = unset applicative_functors
  soit _noassert = set noassert
  soit _nolabels = set classic
  soit _noautolink = set no_auto_link
  soit _nostdlib = set no_std_include
  soit _o s = output_name := Some s
  soit _output_obj () = output_c_object := vrai; custom_runtime := vrai
  soit _pack = set make_package
  soit _pp s = preprocessor := Some s
  soit _ppx s = first_ppx := s :: !first_ppx
  soit _principal = set principal
  soit _rectypes = set recursive_types
  soit _runtime_variant s = runtime_variant := s
  soit _short_paths = unset real_paths
  soit _strict_sequence = set strict_sequence
  soit _thread = set use_threads
  soit _trans_mod = set transparent_modules
  soit _vmthread = set use_vmthreads
  soit _unsafe = set fast
  soit _use_prims s = use_prims := s
  soit _use_runtime s = use_runtime := s
  soit _v () = print_version_and_library "compiler"
  soit _version = print_version_string
  soit _vnum = print_version_string
  soit _w = (Warnings.parse_options faux)
  soit _warn_error = (Warnings.parse_options vrai)
  soit _warn_help = Warnings.help_warnings
  soit _where = print_standard_library
  soit _verbose = set verbose
  soit _nopervasives = set nopervasives
  soit _dsource = set dump_source
  soit _dparsetree = set dump_parsetree
  soit _dtypedtree = set dump_typedtree
  soit _drawlambda = set dump_rawlambda
  soit _dlambda = set dump_lambda
  soit _dinstr = set dump_instr
  soit _perfide_albion = set perfide_albion
  soit anonymous = anonymous
fin)

soit main () =
  essaie
    readenv ppf Before_args;
    Arg.parse Options.list anonymous usage;
    readenv ppf Before_link;
    si
      List.length (List.filter (fonc x -> !x)
                      [make_archive;make_package;compile_only;output_c_object])
        > 1
    alors
      si !print_types alors
        fatal "Option -i is incompatible with -pack, -a, -output-obj"
      sinon
        fatal "Please specify at most one of -pack, -a, -c, -output-obj";
    si !make_archive alors début
      Compmisc.init_path faux;

      Bytelibrarian.create_archive ppf  (Compenv.get_objfiles ())
                                   (extract_output !output_name);
      Warnings.check_fatal ();
    fin
    sinon si !make_package alors début
      Compmisc.init_path faux;
      soit extracted_output = extract_output !output_name dans
      soit revd = get_objfiles () dans
      Bytepackager.package_files ppf revd (extracted_output);
      Warnings.check_fatal ();
    fin
    sinon si not !compile_only && !objfiles <> [] alors début
      soit target =
        si !output_c_object alors
          soit s = extract_output !output_name dans
          si (Filename.check_suffix s Config.ext_obj
            || Filename.check_suffix s Config.ext_dll
            || Filename.check_suffix s ".c")
          alors s
          sinon
            fatal
              (Printf.sprintf
                 "The extension of the output file must be .c, %s or %s"
                 Config.ext_obj Config.ext_dll
              )
        sinon
          default_output !output_name
      dans
      Compmisc.init_path faux;
      Bytelink.link ppf (get_objfiles ()) target;
      Warnings.check_fatal ();
    fin;
    exit 0
  avec x ->
    Location.report_exception ppf x;
    exit 2

soit _ = main ()
