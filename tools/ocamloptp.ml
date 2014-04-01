(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*          Damien Doligez, projet Gallium, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 2012 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

ouvre Printf

soit compargs = ref ([] : string list)
soit profargs = ref ([] : string list)
soit toremove = ref ([] : string list)

soit option opt () = compargs := opt :: !compargs
soit option_with_arg opt arg =
  compargs := (Filename.quote arg) :: opt :: !compargs
;;
soit option_with_int opt arg =
  compargs := (string_of_int arg) :: opt :: !compargs
;;

soit make_archive = ref faux;;
soit with_impl = ref faux;;
soit with_intf = ref faux;;
soit with_mli = ref faux;;
soit with_ml = ref faux;;

soit process_file filename =
  si Filename.check_suffix filename ".ml" alors with_ml := vrai;
  si Filename.check_suffix filename ".mli" alors with_mli := vrai;
  compargs := (Filename.quote filename) :: !compargs
;;

soit usage = "Usage: ocamloptp <options> <files>\noptions are:"

soit incompatible o =
  fprintf stderr "ocamloptp: profiling is incompatible with the %s option\n" o;
  exit 2

module Options = Main_args.Make_optcomp_options (struct
  soit _a () = make_archive := vrai; option "-a" ()
  soit _absname = option "-absname"
  soit _annot = option "-annot"
  soit _binannot = option "-bin-annot"
  soit _c = option "-c"
  soit _cc s = option_with_arg "-cc" s
  soit _cclib s = option_with_arg "-cclib" s
  soit _ccopt s = option_with_arg "-ccopt" s
  soit _compact = option "-compact"
  soit _config = option "-config"
  soit _for_pack s = option_with_arg "-for-pack" s
  soit _g = option "-g"
  soit _i = option "-i"
  soit _I s = option_with_arg "-I" s
  soit _impl s = with_impl := vrai; option_with_arg "-impl" s
  soit _inline n = option_with_int "-inline" n
  soit _intf s = with_intf := vrai; option_with_arg "-intf" s
  soit _intf_suffix s = option_with_arg "-intf-suffix" s
  soit _keep_locs = option "-keep-locs"
  soit _labels = option "-labels"
  soit _linkall = option "-linkall"
  soit _no_app_funct = option "-no-app-funct"
  soit _noassert = option "-noassert"
  soit _noautolink = option "-noautolink"
  soit _nodynlink = option "-nodynlink"
  soit _nolabels = option "-nolabels"
  soit _nostdlib = option "-nostdlib"
  soit _o s = option_with_arg "-o" s
  soit _output_obj = option "-output-obj"
  soit _p = option "-p"
  soit _pack = option "-pack"
  soit _pp s = incompatible "-pp"
  soit _ppx s = incompatible "-ppx"
  soit _principal = option "-principal"
  soit _rectypes = option "-rectypes"
  soit _runtime_variant s = option_with_arg "-runtime-variant" s
  soit _S = option "-S"
  soit _short_paths = option "-short-paths"
  soit _strict_sequence = option "-strict-sequence"
  soit _shared = option "-shared"
  soit _thread = option "-thread"
  soit _trans_mod = option "-trans-mod"
  soit _unsafe = option "-unsafe"
  soit _v = option "-v"
  soit _version = option "-version"
  soit _vnum = option "-vnum"
  soit _verbose = option "-verbose"
  soit _w = option_with_arg "-w"
  soit _warn_error = option_with_arg "-warn-error"
  soit _warn_help = option "-warn-help"
  soit _where = option "-where"

  soit _nopervasives = option "-nopervasives"
  soit _dsource = option "-dsource"
  soit _dparsetree = option "-dparsetree"
  soit _dtypedtree = option "-dtypedtree"
  soit _drawlambda = option "-drawlambda"
  soit _dlambda = option "-dlambda"
  soit _dclambda = option "-dclambda"
  soit _dcmm = option "-dcmm"
  soit _dsel = option "-dsel"
  soit _dcombine = option "-dcombine"
  soit _dlive = option "-dlive"
  soit _dspill = option "-dspill"
  soit _dsplit = option "-dsplit"
  soit _dinterf = option "-dinterf"
  soit _dprefer = option "-dprefer"
  soit _dalloc = option "-dalloc"
  soit _dreload = option "-dreload"
  soit _dscheduling = option "-dscheduling"
  soit _dlinear = option "-dlinear"
  soit _dstartup = option "-dstartup"

  soit anonymous = process_file
fin);;

soit add_profarg s =
  profargs := (Filename.quote s) :: "-m" :: !profargs
;;

soit optlist =
    ("-P", Arg.String add_profarg,
           "[afilmt]  Profile constructs specified by argument (default fm):\n\
        \032     a  Everything\n\
        \032     f  Function calls and method calls\n\
        \032     i  if ... then ... else\n\
        \032     l  while and for loops\n\
        \032     m  match ... with\n\
        \032     t  try ... with")
    :: Options.list
dans
Arg.parse optlist process_file usage;
si !with_impl && !with_intf alors début
  fprintf stderr "ocamloptp cannot deal with both \"-impl\" and \"-intf\"\n";
  fprintf stderr "please compile interfaces and implementations separately\n";
  exit 2;
fin sinon si !with_impl && !with_mli alors début
  fprintf stderr "ocamloptp cannot deal with both \"-impl\" and .mli files\n";
  fprintf stderr "please compile interfaces and implementations separately\n";
  exit 2;
fin sinon si !with_intf && !with_ml alors début
  fprintf stderr "ocamloptp cannot deal with both \"-intf\" and .ml files\n";
  fprintf stderr "please compile interfaces and implementations separately\n";
  exit 2;
fin;
si !with_impl alors profargs := "-impl" :: !profargs;
si !with_intf alors profargs := "-intf" :: !profargs;
soit status =
  Sys.command
    (Printf.sprintf "ocamlopt -pp \"ocamlprof -instrument %s\" %s %s"
        (String.concat " " (List.rev !profargs))
        (si !make_archive alors "" sinon "profiling.cmx")
        (String.concat " " (List.rev !compargs)))
dans
exit status
;;
