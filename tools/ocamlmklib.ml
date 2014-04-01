(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 2001 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

ouvre Printf
ouvre Ocamlmklibconfig

(* PR#4783: under Windows, don't use absolute paths because we do
   not know where the binary distribution will be installed. *)
soit compiler_path name =
  si Sys.os_type = "Win32" alors name sinon Filename.concat bindir name

soit bytecode_objs = ref []  (* .cmo,.cma,.ml,.mli files to pass to ocamlc *)
et native_objs = ref []    (* .cmx,.cmxa,.ml,.mli files to pass to ocamlopt *)
et c_objs = ref []         (* .o, .a, .obj, .lib, .dll files to pass
                               to mksharedlib and ar *)
et caml_libs = ref []      (* -cclib to pass to ocamlc, ocamlopt *)
et caml_opts = ref []      (* -ccopt to pass to ocamlc, ocamlopt *)
et dynlink = ref supports_shared_libraries
et failsafe = ref faux    (* whether to fall back on static build only *)
et c_libs = ref []         (* libs to pass to mksharedlib and ocamlc -cclib *)
et c_Lopts = ref []      (* options to pass to mksharedlib and ocamlc -cclib *)
et c_opts = ref []      (* options to pass to mksharedlib and ocamlc -ccopt *)
et ld_opts = ref []        (* options to pass only to the linker *)
et ocamlc = ref (compiler_path "ocamlc")
et ocamlopt = ref (compiler_path "ocamlopt")
et output = ref "a"        (* Output name for OCaml part of library *)
et output_c = ref ""       (* Output name for C part of library *)
et rpath = ref []          (* rpath options *)
et verbose = ref faux

soit starts_with s pref =
  String.length s >= String.length pref &&
  String.sub s 0 (String.length pref) = pref
soit ends_with = Filename.check_suffix
soit chop_prefix s pref =
  String.sub s (String.length pref) (String.length s - String.length pref)
soit chop_suffix = Filename.chop_suffix

exception Bad_argument de string

soit print_version () =
  printf "ocamlmklib, version %s\n" Sys.ocaml_version;
  exit 0;
;;

soit print_version_num () =
  printf "%s\n" Sys.ocaml_version;
  exit 0;
;;

soit parse_arguments argv =
  soit i = ref 1 dans
  soit next_arg () =
    si !i + 1 >= Array.length argv
    alors raise (Bad_argument("Option " ^ argv.(!i) ^ " expects one argument"));
    incr i; argv.(!i) dans
  pendant_que !i < Array.length argv faire
    soit s = argv.(!i) dans
    si ends_with s ".cmo" || ends_with s ".cma" alors
      bytecode_objs := s :: !bytecode_objs
    sinon si ends_with s ".cmx" || ends_with s ".cmxa" alors
      native_objs := s :: !native_objs
    sinon si ends_with s ".ml" || ends_with s ".mli" alors
     (bytecode_objs := s :: !bytecode_objs;
      native_objs := s :: !native_objs)
    sinon si List.exists (ends_with s) [".o"; ".a"; ".obj"; ".lib"; ".dll"] alors
      c_objs := s :: !c_objs
    sinon si s = "-cclib" alors
      caml_libs := next_arg () :: "-cclib" :: !caml_libs
    sinon si s = "-ccopt" alors
      caml_opts := next_arg () :: "-ccopt" :: !caml_opts
    sinon si s = "-custom" alors
      dynlink := faux
    sinon si s = "-I" alors
      caml_opts := next_arg () :: "-I" :: !caml_opts
    sinon si s = "-failsafe" alors
      failsafe := vrai
    sinon si s = "-h" || s = "-help" || s = "--help" alors
      raise (Bad_argument "")
    sinon si s = "-ldopt" alors
      ld_opts := next_arg () :: !ld_opts
    sinon si s = "-linkall" alors
      caml_opts := s :: !caml_opts
    sinon si starts_with s "-l" alors
      c_libs := s :: !c_libs
    sinon si starts_with s "-L" alors
     (c_Lopts := s :: !c_Lopts;
      soit l = chop_prefix s "-L" dans
      si not (Filename.is_relative l) alors rpath := l :: !rpath)
    sinon si s = "-ocamlc" alors
      ocamlc := next_arg ()
    sinon si s = "-ocamlopt" alors
      ocamlopt := next_arg ()
    sinon si s = "-o" alors
      output := next_arg()
    sinon si s = "-oc" alors
      output_c := next_arg()
    sinon si s = "-dllpath" || s = "-R" || s = "-rpath" alors
      rpath := next_arg() :: !rpath
    sinon si starts_with s "-R" alors
      rpath := chop_prefix s "-R" :: !rpath
    sinon si s = "-Wl,-rpath" alors
     (soit a = next_arg() dans
      si starts_with a "-Wl,"
      alors rpath := chop_prefix a "-Wl," :: !rpath
      sinon raise (Bad_argument("Option -Wl,-rpath expects a -Wl, argument")))
    sinon si starts_with s "-Wl,-rpath," alors
      rpath := chop_prefix s "-Wl,-rpath," :: !rpath
    sinon si starts_with s "-Wl,-R" alors
      rpath := chop_prefix s "-Wl,-R" :: !rpath
    sinon si s = "-v" || s = "-verbose" alors
      verbose := vrai
    sinon si s = "-version" alors
      print_version ()
    sinon si s = "-vnum" alors
      print_version_num ()
    sinon si starts_with s "-F" alors
      c_opts := s :: !c_opts
    sinon si s = "-framework" alors
      (soit a = next_arg() dans c_opts := a :: s :: !c_opts)
    sinon si starts_with s "-" alors
      prerr_endline ("Unknown option " ^ s)
    sinon
      raise (Bad_argument("Don't know what to do with " ^ s));
    incr i
  fait;
  List.iter
    (fonc r -> r := List.rev !r)
    [ bytecode_objs; native_objs; caml_libs; caml_opts;
      c_libs; c_objs; c_opts; ld_opts; rpath ];
(* Put -L options in front of -l options in -cclib to mimic -ccopt behavior *)
  c_libs := !c_Lopts @ !c_libs;

  si !output_c = "" alors output_c := !output

soit usage = "\
Usage: ocamlmklib [options] <.cmo|.cma|.cmx|.cmxa|.ml|.mli|.o|.a|.obj|.lib|\
                             .dll files>\
\nOptions are:\
\n  -cclib <lib>   C library passed to ocamlc -a or ocamlopt -a only\
\n  -ccopt <opt>   C option passed to ocamlc -a or ocamlopt -a only\
\n  -custom        disable dynamic loading\
\n  -dllpath <dir> Add <dir> to the run-time search path for DLLs\
\n  -F<dir>        Specify a framework directory (MacOSX)\
\n  -framework <name>    Use framework <name> (MacOSX)\
\n  -help          Print this help message and exit\
\n  --help         Same as -help\
\n  -h             Same as -help\
\n  -I <dir>       Add <dir> to the path searched for OCaml object files\
\n  -failsafe      fall back to static linking if DLL construction failed\
\n  -ldopt <opt>   C option passed to the shared linker only\
\n  -linkall       Build OCaml archive with link-all behavior\
\n  -l<lib>        Specify a dependent C library\
\n  -L<dir>        Add <dir> to the path searched for C libraries\
\n  -ocamlc <cmd>  Use <cmd> in place of \"ocamlc\"\
\n  -ocamlopt <cmd> Use <cmd> in place of \"ocamlopt\"\
\n  -o <name>      Generated OCaml library is named <name>.cma or <name>.cmxa\
\n  -oc <name>     Generated C library is named dll<name>.so or lib<name>.a\
\n  -rpath <dir>   Same as -dllpath <dir>\
\n  -R<dir>        Same as -rpath\
\n  -verbose       Print commands before executing them\
\n  -v             same as -verbose\
\n  -version       Print version and exit\
\n  -vnum          Print version number and exit\
\n  -Wl,-rpath,<dir>     Same as -dllpath <dir>\
\n  -Wl,-rpath -Wl,<dir> Same as -dllpath <dir>\
\n  -Wl,-R<dir>          Same as -dllpath <dir>\
\n"

soit command cmd =
  si !verbose alors (print_string "+ "; print_string cmd; print_newline());
  Sys.command cmd

soit scommand cmd =
  si command cmd <> 0 alors exit 2

soit safe_remove s =
  essaie Sys.remove s avec Sys_error _ -> ()

soit make_set l =
  soit rec merge l = fonction
    []     -> List.rev l
  | p :: r -> si List.mem p l alors merge l r sinon merge (p::l) r
  dans
  merge [] l

soit make_rpath flag =
  si !rpath = [] || flag = ""
  alors ""
  sinon flag ^ String.concat ":" (make_set !rpath)

soit make_rpath_ccopt flag =
  si !rpath = [] || flag = ""
  alors ""
  sinon "-ccopt " ^ flag ^ String.concat ":" (make_set !rpath)

soit prefix_list pref l =
  List.map (fonc s -> pref ^ s) l

soit prepostfix pre name post =
  soit base = Filename.basename name dans
  soit dir = Filename.dirname name dans
  Filename.concat dir (pre ^ base ^ post)
;;

soit transl_path s =
  filtre Sys.os_type avec
    | "Win32" ->
        soit rec aux i =
          si i = String.length s || s.[i] = ' ' alors s
          sinon (si s.[i] = '/' alors s.[i] <- '\\'; aux (i + 1))
        dans aux 0
    | _ -> s

soit build_libs () =
  si !c_objs <> [] alors début
    si !dynlink alors début
      soit retcode = command
          (Printf.sprintf "%s -o %s %s %s %s %s %s"
             mkdll
             (prepostfix "dll" !output_c ext_dll)
             (String.concat " " !c_objs)
             (String.concat " " !c_opts)
             (String.concat " " !ld_opts)
             (make_rpath mksharedlibrpath)
             (String.concat " " !c_libs)
          )
      dans
      si retcode <> 0 alors si !failsafe alors dynlink := faux sinon exit 2
    fin;
    safe_remove (prepostfix "lib" !output_c ext_lib);
    scommand
      (mklib (prepostfix "lib" !output_c ext_lib)
             (String.concat " " !c_objs) "");
  fin;
  si !bytecode_objs <> [] alors
    scommand
      (sprintf "%s -a %s -o %s.cma %s %s -dllib -l%s -cclib -l%s %s %s %s %s"
                  (transl_path !ocamlc)
                  (si !dynlink alors "" sinon "-custom")
                  !output
                  (String.concat " " !caml_opts)
                  (String.concat " " !bytecode_objs)
                  (Filename.basename !output_c)
                  (Filename.basename !output_c)
                  (String.concat " " (prefix_list "-ccopt " !c_opts))
                  (make_rpath_ccopt byteccrpath)
                  (String.concat " " (prefix_list "-cclib " !c_libs))
                  (String.concat " " !caml_libs));
  si !native_objs <> [] alors
    scommand
      (sprintf "%s -a -o %s.cmxa %s %s -cclib -l%s %s %s %s %s"
                  (transl_path !ocamlopt)
                  !output
                  (String.concat " " !caml_opts)
                  (String.concat " " !native_objs)
                  (Filename.basename !output_c)
                  (String.concat " " (prefix_list "-ccopt " !c_opts))
                  (make_rpath_ccopt nativeccrpath)
                  (String.concat " " (prefix_list "-cclib " !c_libs))
                  (String.concat " " !caml_libs))

soit _ =
  essaie
    parse_arguments Sys.argv;
    build_libs()
  avec
  | Bad_argument "" ->
      prerr_string usage; exit 0
  | Bad_argument s ->
      prerr_endline s; prerr_string usage; exit 4
  | Sys_error s ->
      prerr_string "System error: "; prerr_endline s; exit 4
  | x ->
      raise x
