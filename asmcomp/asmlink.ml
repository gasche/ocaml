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

(* Link a set of .cmx/.o files and produce an executable *)

ouvre Misc
ouvre Config
ouvre Cmx_format
ouvre Compilenv

type error =
    File_not_found de string
  | Not_an_object_file de string
  | Missing_implementations de (string * string list) list
  | Inconsistent_interface de string * string * string
  | Inconsistent_implementation de string * string * string
  | Assembler_error de string
  | Linking_error
  | Multiple_definition de string * string * string
  | Missing_cmx de string * string

exception Error de error

(* Consistency check between interfaces and implementations *)

soit crc_interfaces = Consistbl.create ()
soit crc_implementations = Consistbl.create ()
soit extra_implementations = ref ([] : string list)
soit implementations_defined = ref ([] : (string * string) list)
soit cmx_required = ref ([] : string list)

soit check_consistency file_name unit crc =
  début essaie
    List.iter
      (fonc (name, crc) ->
        si name = unit.ui_name
        alors Consistbl.set crc_interfaces name crc file_name
        sinon Consistbl.check crc_interfaces name crc file_name)
      unit.ui_imports_cmi
  avec Consistbl.Inconsistency(name, user, auth) ->
    raise(Error(Inconsistent_interface(name, user, auth)))
  fin;
  début essaie
    List.iter
      (fonc (name, crc) ->
        si crc <> cmx_not_found_crc alors
          Consistbl.check crc_implementations name crc file_name
        sinon si List.mem name !cmx_required alors
          raise(Error(Missing_cmx(file_name, name)))
        sinon
          extra_implementations := name :: !extra_implementations)
      unit.ui_imports_cmx
  avec Consistbl.Inconsistency(name, user, auth) ->
    raise(Error(Inconsistent_implementation(name, user, auth)))
  fin;
  début essaie
    soit source = List.assoc unit.ui_name !implementations_defined dans
    raise (Error(Multiple_definition(unit.ui_name, file_name, source)))
  avec Not_found -> ()
  fin;
  Consistbl.set crc_implementations unit.ui_name crc file_name;
  implementations_defined :=
    (unit.ui_name, file_name) :: !implementations_defined;
  si unit.ui_symbol <> unit.ui_name alors
    cmx_required := unit.ui_name :: !cmx_required

soit extract_crc_interfaces () =
  Consistbl.extract crc_interfaces
soit extract_crc_implementations () =
  List.fold_left
    (fonc ncl n ->
      si List.mem_assoc n ncl alors ncl sinon (n, cmx_not_found_crc) :: ncl)
    (Consistbl.extract crc_implementations)
    !extra_implementations

(* Add C objects and options and "custom" info from a library descriptor.
   See bytecomp/bytelink.ml for comments on the order of C objects. *)

soit lib_ccobjs = ref []
soit lib_ccopts = ref []

soit add_ccobjs l =
  si not !Clflags.no_auto_link alors début
    lib_ccobjs := l.lib_ccobjs @ !lib_ccobjs;
    lib_ccopts := l.lib_ccopts @ !lib_ccopts
  fin

soit runtime_lib () =
  soit libname =
    si !Clflags.gprofile
    alors "libasmrunp" ^ ext_lib
    sinon "libasmrun" ^ !Clflags.runtime_variant ^ ext_lib dans
  essaie
    si !Clflags.nopervasives alors []
    sinon [ find_in_path !load_path libname ]
  avec Not_found ->
    raise(Error(File_not_found libname))

soit object_file_name name =
  soit file_name =
    essaie
      find_in_path !load_path name
    avec Not_found ->
      fatal_error "Asmlink.object_file_name: introuvable" dans
  si Filename.check_suffix file_name ".cmx" alors
    Filename.chop_suffix file_name ".cmx" ^ ext_obj
  sinon si Filename.check_suffix file_name ".cmxa" alors
    Filename.chop_suffix file_name ".cmxa" ^ ext_lib
  sinon
    fatal_error "Asmlink.object_file_name: extension incorrecte"

(* First pass: determine which units are needed *)

soit missing_globals = (Hashtbl.create 17 : (string, string list ref) Hashtbl.t)

soit is_required name =
  essaie ignore (Hashtbl.find missing_globals name); vrai
  avec Not_found -> faux

soit add_required by (name, crc) =
  essaie
    soit rq = Hashtbl.find missing_globals name dans
    rq := by :: !rq
  avec Not_found ->
    Hashtbl.add missing_globals name (ref [by])

soit remove_required name =
  Hashtbl.remove missing_globals name

soit extract_missing_globals () =
  soit mg = ref [] dans
  Hashtbl.iter (fonc md rq -> mg := (md, !rq) :: !mg) missing_globals;
  !mg

type file =
  | Unit de string * unit_infos * Digest.t
  | Library de string * library_infos

soit read_file obj_name =
  soit file_name =
    essaie
      find_in_path !load_path obj_name
    avec Not_found ->
      raise(Error(File_not_found obj_name)) dans
  si Filename.check_suffix file_name ".cmx" alors début
    (* This is a .cmx file. It must be linked in any case.
       Read the infos to see which modules it requires. *)
    soit (info, crc) = read_unit_info file_name dans
    Unit (file_name,info,crc)
  fin
  sinon si Filename.check_suffix file_name ".cmxa" alors début
    soit infos =
      essaie read_library_info file_name
      avec Compilenv.Error(Not_a_unit_info _) ->
        raise(Error(Not_an_object_file file_name))
    dans
    Library (file_name,infos)
  fin
  sinon raise(Error(Not_an_object_file file_name))

soit scan_file obj_name tolink = filtre read_file obj_name avec
  | Unit (file_name,info,crc) ->
      (* This is a .cmx file. It must be linked in any case. *)
      remove_required info.ui_name;
      List.iter (add_required file_name) info.ui_imports_cmx;
      (info, file_name, crc) :: tolink
  | Library (file_name,infos) ->
      (* This is an archive file. Each unit contained in it will be linked
         in only if needed. *)
      add_ccobjs infos;
      List.fold_right
        (fonc (info, crc) reqd ->
           si info.ui_force_link
             || !Clflags.link_everything
             || is_required info.ui_name
           alors début
             remove_required info.ui_name;
             List.iter (add_required (Printf.sprintf "%s(%s)"
                                        file_name info.ui_name))
               info.ui_imports_cmx;
             (info, file_name, crc) :: reqd
           fin sinon
             reqd)
        infos.lib_units tolink

(* Second pass: generate the startup file and link it with everything else *)

soit make_startup_file ppf filename units_list =
  soit compile_phrase p = Asmgen.compile_phrase ppf p dans
  soit oc = open_out filename dans
  Emitaux.output_channel := oc;
  Location.input_name := "caml_startup"; (* set name of "current" input *)
  Compilenv.reset "_startup"; (* set the name of the "current" compunit *)
  Emit.begin_assembly();
  soit name_list =
    List.flatten (List.map (fonc (info,_,_) -> info.ui_defines) units_list) dans
  compile_phrase (Cmmgen.entry_point name_list);
  soit units = List.map (fonc (info,_,_) -> info) units_list dans
  List.iter compile_phrase (Cmmgen.generic_functions faux units);
  Array.iteri
    (fonc i name -> compile_phrase (Cmmgen.predef_exception i name))
    Runtimedef.builtin_exceptions;
  compile_phrase (Cmmgen.global_table name_list);
  compile_phrase
    (Cmmgen.globals_map
       (List.map
          (fonc (unit,_,crc) ->
             essaie (unit.ui_name, List.assoc unit.ui_name unit.ui_imports_cmi,
                  crc,
                  unit.ui_defines)
             avec Not_found -> affirme faux)
          units_list));
  compile_phrase(Cmmgen.data_segment_table ("_startup" :: name_list));
  compile_phrase(Cmmgen.code_segment_table ("_startup" :: name_list));
  compile_phrase
    (Cmmgen.frame_table("_startup" :: "_system" :: name_list));

  Emit.end_assembly();
  close_out oc

soit make_shared_startup_file ppf units filename =
  soit compile_phrase p = Asmgen.compile_phrase ppf p dans
  soit oc = open_out filename dans
  Emitaux.output_channel := oc;
  Location.input_name := "caml_startup";
  Compilenv.reset "_shared_startup";
  Emit.begin_assembly();
  List.iter compile_phrase
    (Cmmgen.generic_functions vrai (List.map fst units));
  compile_phrase (Cmmgen.plugin_header units);
  compile_phrase
    (Cmmgen.global_table
       (List.map (fonc (ui,_) -> ui.ui_symbol) units));
  (* this is to force a reference to all units, otherwise the linker
     might drop some of them (in case of libraries) *)

  Emit.end_assembly();
  close_out oc


soit call_linker_shared file_list output_name =
  si not (Ccomp.call_linker Ccomp.Dll output_name file_list "")
  alors raise(Error Linking_error)

soit link_shared ppf objfiles output_name =
  soit units_tolink = List.fold_right scan_file objfiles [] dans
  List.iter
    (fonc (info, file_name, crc) -> check_consistency file_name info crc)
    units_tolink;
  Clflags.ccobjs := !Clflags.ccobjs @ !lib_ccobjs;
  Clflags.all_ccopts := !lib_ccopts @ !Clflags.all_ccopts;
  soit objfiles = List.rev (List.map object_file_name objfiles) @
    (List.rev !Clflags.ccobjs) dans

  soit startup =
    si !Clflags.keep_startup_file
    alors output_name ^ ".startup" ^ ext_asm
    sinon Filename.temp_file "camlstartup" ext_asm dans
  make_shared_startup_file ppf
    (List.map (fonc (ui,_,crc) -> (ui,crc)) units_tolink) startup;
  soit startup_obj = output_name ^ ".startup" ^ ext_obj dans
  si Proc.assemble_file startup startup_obj <> 0
  alors raise(Error(Assembler_error startup));
  si not !Clflags.keep_startup_file alors remove_file startup;
  call_linker_shared (startup_obj :: objfiles) output_name;
  remove_file startup_obj

soit call_linker file_list startup_file output_name =
  soit main_dll = !Clflags.output_c_object
                 && Filename.check_suffix output_name Config.ext_dll
  dans
  soit files = startup_file :: (List.rev file_list) dans
  soit files, c_lib =
    si (not !Clflags.output_c_object) || main_dll alors
      files @ (List.rev !Clflags.ccobjs) @ runtime_lib (),
      (si !Clflags.nopervasives alors "" sinon Config.native_c_libraries)
    sinon
      files, ""
  dans
  soit mode =
    si main_dll alors Ccomp.MainDll
    sinon si !Clflags.output_c_object alors Ccomp.Partial
    sinon Ccomp.Exe
  dans
  si not (Ccomp.call_linker mode output_name files c_lib)
  alors raise(Error Linking_error)

(* Main entry point *)

soit link ppf objfiles output_name =
  soit stdlib =
    si !Clflags.gprofile alors "stdlib.p.cmxa" sinon "stdlib.cmxa" dans
  soit stdexit =
    si !Clflags.gprofile alors "std_exit.p.cmx" sinon "std_exit.cmx" dans
  soit objfiles =
    si !Clflags.nopervasives alors objfiles
    sinon si !Clflags.output_c_object alors stdlib :: objfiles
    sinon stdlib :: (objfiles @ [stdexit]) dans
  soit units_tolink = List.fold_right scan_file objfiles [] dans
  Array.iter remove_required Runtimedef.builtin_exceptions;
  début filtre extract_missing_globals() avec
    [] -> ()
  | mg -> raise(Error(Missing_implementations mg))
  fin;
  List.iter
    (fonc (info, file_name, crc) -> check_consistency file_name info crc)
    units_tolink;
  Clflags.ccobjs := !Clflags.ccobjs @ !lib_ccobjs;
  Clflags.all_ccopts := !lib_ccopts @ !Clflags.all_ccopts;
                                               (* put user's opts first *)
  soit startup =
    si !Clflags.keep_startup_file alors output_name ^ ".startup" ^ ext_asm
    sinon Filename.temp_file "camlstartup" ext_asm dans
  make_startup_file ppf startup units_tolink;
  soit startup_obj = Filename.temp_file "camlstartup" ext_obj dans
  si Proc.assemble_file startup startup_obj <> 0 alors
    raise(Error(Assembler_error startup));
  essaie
    call_linker (List.map object_file_name objfiles) startup_obj output_name;
    si not !Clflags.keep_startup_file alors remove_file startup;
    remove_file startup_obj
  avec x ->
    remove_file startup_obj;
    raise x

(* Error report *)

ouvre Format

soit report_error ppf = fonction
  | File_not_found name ->
      fprintf ppf "Cannot find file %s" name
  | Not_an_object_file name ->
      fprintf ppf "The file %a is not a compilation unit description"
        Location.print_filename name
  | Missing_implementations l ->
     soit print_references ppf = fonction
       | [] -> ()
       | r1 :: rl ->
           fprintf ppf "%s" r1;
           List.iter (fonc r -> fprintf ppf ",@ %s" r) rl dans
      soit print_modules ppf =
        List.iter
         (fonc (md, rq) ->
            fprintf ppf "@ @[<hov 2>%s referenced from %a@]" md
            print_references rq) dans
      fprintf ppf
       "@[<v 2>No implementations provided for the following modules:%a@]"
       print_modules l
  | Inconsistent_interface(intf, file1, file2) ->
      fprintf ppf
       "@[<hov>Files %a@ and %a@ make inconsistent assumptions \
              over interface %s@]"
       Location.print_filename file1
       Location.print_filename file2
       intf
  | Inconsistent_implementation(intf, file1, file2) ->
      fprintf ppf
       "@[<hov>Files %a@ and %a@ make inconsistent assumptions \
              over implementation %s@]"
       Location.print_filename file1
       Location.print_filename file2
       intf
  | Assembler_error file ->
      fprintf ppf "Error while assembling %a" Location.print_filename file
  | Linking_error ->
      fprintf ppf "Error during linking"
  | Multiple_definition(modname, file1, file2) ->
      fprintf ppf
        "@[<hov>Files %a@ and %a@ both define a module named %s@]"
        Location.print_filename file1
        Location.print_filename file2
        modname
  | Missing_cmx(filename, name) ->
      fprintf ppf
        "@[<hov>File %a@ was compiled without access@ \
         to the .cmx file@ for module %s,@ \
         which was produced by `ocamlopt -for-pack'.@ \
         Please recompile %a@ with the correct `-I' option@ \
         so that %s.cmx@ is found.@]"
        Location.print_filename filename name
        Location.print_filename  filename
        name

soit () =
  Location.register_error_of_exn
    (fonction
      | Error err -> Some (Location.error_of_printer_file report_error err)
      | _ -> None
    )
