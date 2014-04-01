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

(* Compiling C files and building C libraries *)

soit command cmdline =
  si !Clflags.verbose alors début
    prerr_string "+ ";
    prerr_string cmdline;
    prerr_newline()
  fin;
  Sys.command cmdline

soit run_command cmdline = ignore(command cmdline)

(* Build @responsefile to work around Windows limitations on
   command-line length *)
soit build_diversion lst =
  soit (responsefile, oc) = Filename.open_temp_file "camlresp" "" dans
  List.iter (fonc f -> Printf.fprintf oc "%s\n" f) lst;
  close_out oc;
  at_exit (fonc () -> Misc.remove_file responsefile);
  "@" ^ responsefile

soit quote_files lst =
  soit lst = List.filter (fonc f -> f <> "") lst dans
  soit quoted = List.map Filename.quote lst dans
  soit s = String.concat " " quoted dans
  si String.length s >= 4096 && Sys.os_type = "Win32"
  alors build_diversion quoted
  sinon s

soit quote_prefixed pr lst =
  soit lst = List.filter (fonc f -> f <> "") lst dans
  soit lst = List.map (fonc f -> pr ^ f) lst dans
  quote_files lst

soit quote_optfile = fonction
  | None -> ""
  | Some f -> Filename.quote f

soit compile_file name =
  command
    (Printf.sprintf
       "%s -c %s %s %s %s"
       (filtre !Clflags.c_compiler avec
        | Some cc -> cc
        | None ->
            si !Clflags.native_code
            alors Config.native_c_compiler
            sinon Config.bytecomp_c_compiler)
       (String.concat " " (List.rev !Clflags.all_ccopts))
       (quote_prefixed "-I" (List.rev !Clflags.include_dirs))
       (Clflags.std_include_flag "-I")
       (Filename.quote name))

soit create_archive archive file_list =
  Misc.remove_file archive;
  soit quoted_archive = Filename.quote archive dans
  filtre Config.ccomp_type avec
    "msvc" ->
      command(Printf.sprintf "link /lib /nologo /out:%s %s"
                             quoted_archive (quote_files file_list))
  | _ ->
      affirme(String.length Config.ar > 0);
      soit r1 =
        command(Printf.sprintf "%s rc %s %s"
                Config.ar quoted_archive (quote_files file_list)) dans
      si r1 <> 0 || String.length Config.ranlib = 0
      alors r1
      sinon command(Config.ranlib ^ " " ^ quoted_archive)

soit expand_libname name =
  si String.length name < 2 || String.sub name 0 2 <> "-l"
  alors name
  sinon début
    soit libname =
      "lib" ^ String.sub name 2 (String.length name - 2) ^ Config.ext_lib dans
    essaie
      Misc.find_in_path !Config.load_path libname
    avec Not_found ->
      libname
  fin

type link_mode =
  | Exe
  | Dll
  | MainDll
  | Partial

soit call_linker mode output_name files extra =
  soit files = quote_files files dans
  soit cmd =
    si mode = Partial alors
      Printf.sprintf "%s%s %s %s"
        Config.native_pack_linker
        (Filename.quote output_name)
        files
        extra
    sinon
      Printf.sprintf "%s -o %s %s %s %s %s %s %s"
        (filtre !Clflags.c_compiler, mode avec
        | Some cc, _ -> cc
        | None, Exe -> Config.mkexe
        | None, Dll -> Config.mkdll
        | None, MainDll -> Config.mkmaindll
        | None, Partial -> affirme faux
        )
        (Filename.quote output_name)
        (si !Clflags.gprofile alors Config.cc_profile sinon "")
        ""  (*(Clflags.std_include_flag "-I")*)
        (quote_prefixed "-L" !Config.load_path)
        (String.concat " " (List.rev !Clflags.all_ccopts))
        files
        extra
  dans
  command cmd = 0
