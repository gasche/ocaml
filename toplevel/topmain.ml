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

ouvre Clflags
ouvre Compenv

soit usage = "Usage: ocaml <options> <object-files> [script-file [arguments]]\n\
             options are:"

soit preload_objects = ref []

soit prepare ppf =
  Toploop.set_paths ();
  essaie
    soit res =
      List.for_all (Topdirs.load_file ppf) (List.rev !preload_objects) dans
    !Toploop.toplevel_startup_hook ();
    res
  avec x ->
    essaie Location.report_exception ppf x; faux
    avec x ->
      Format.fprintf ppf "Uncaught exception: %s\n" (Printexc.to_string x);
      faux

(* If [name] is "", then the "file" is stdin treated as a script file. *)
soit file_argument name =
  soit ppf = Format.err_formatter dans
  si Filename.check_suffix name ".cmo" || Filename.check_suffix name ".cma"
  alors preload_objects := name :: !preload_objects
  sinon
    début
      soit newargs = Array.sub Sys.argv !Arg.current
                              (Array.length Sys.argv - !Arg.current)
      dans
      si prepare ppf && Toploop.run_script ppf name newargs
      alors exit 0
      sinon exit 2
    fin

soit print_version () =
  Printf.printf "The OCaml toplevel, version %s\n" Sys.ocaml_version;
  exit 0;
;;

soit print_version_num () =
  Printf.printf "%s\n" Sys.ocaml_version;
  exit 0;
;;

module Options = Main_args.Make_bytetop_options (struct
  soit set r () = r := vrai
  soit clear r () = r := faux

  soit _absname = set Location.absname
  soit _I dir =
    soit dir = Misc.expand_directory Config.standard_library dir dans
    include_dirs := dir :: !include_dirs
  soit _init s = init_file := Some s
  soit _noinit = set noinit
  soit _labels = clear classic
  soit _no_app_funct = clear applicative_functors
  soit _noassert = set noassert
  soit _nolabels = set classic
  soit _noprompt = set noprompt
  soit _nopromptcont = set nopromptcont
  soit _nostdlib = set no_std_include
  soit _ppx s = first_ppx := s :: !first_ppx
  soit _principal = set principal
  soit _rectypes = set recursive_types
  soit _short_paths = clear real_paths
  soit _stdin () = file_argument ""
  soit _strict_sequence = set strict_sequence
  soit _trans_mod = set transparent_modules
  soit _unsafe = set fast
  soit _version () = print_version ()
  soit _vnum () = print_version_num ()
  soit _w s = Warnings.parse_options faux s
  soit _warn_error s = Warnings.parse_options vrai s
  soit _warn_help = Warnings.help_warnings
  soit _dparsetree = set dump_parsetree
  soit _dtypedtree = set dump_typedtree
  soit _dsource = set dump_source
  soit _drawlambda = set dump_rawlambda
  soit _dlambda = set dump_lambda
  soit _dinstr = set dump_instr

  soit anonymous s = file_argument s
fin);;


soit main () =
  soit ppf = Format.err_formatter dans
  Compenv.readenv ppf Before_args;
  Arg.parse Options.list file_argument usage;
  Compenv.readenv ppf Before_link;
  si not (prepare ppf) alors exit 2;
  Toploop.loop Format.std_formatter
