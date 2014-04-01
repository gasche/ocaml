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

(* Link a set of .cmo files and produce a bytecode executable. *)

ouvre Misc
ouvre Config
ouvre Cmo_format

type error =
    File_not_found de string
  | Not_an_object_file de string
  | Wrong_object_name de string
  | Symbol_error de string * Symtable.error
  | Inconsistent_import de string * string * string
  | Custom_runtime
  | File_exists de string
  | Cannot_open_dll de string
  | Not_compatible_32

exception Error de error

type link_action =
    Link_object de string * compilation_unit
      (* Name of .cmo file and descriptor of the unit *)
  | Link_archive de string * compilation_unit list
      (* Name of .cma file and descriptors of the units to be linked. *)

(* Add C objects and options from a library descriptor *)
(* Ignore them if -noautolink or -use-runtime or -use-prim was given *)

soit lib_ccobjs = ref []
soit lib_ccopts = ref []
soit lib_dllibs = ref []

soit add_ccobjs l =
  si not !Clflags.no_auto_link alors début
    si
      String.length !Clflags.use_runtime = 0
      && String.length !Clflags.use_prims = 0
    alors début
      si l.lib_custom alors Clflags.custom_runtime := vrai;
      lib_ccobjs := l.lib_ccobjs @ !lib_ccobjs;
      lib_ccopts := l.lib_ccopts @ !lib_ccopts;
    fin;
    lib_dllibs := l.lib_dllibs @ !lib_dllibs
  fin

(* A note on ccobj ordering:
   - Clflags.ccobjs is in reverse order w.r.t. what was given on the
        ocamlc command line;
   - l.lib_ccobjs is also in reverse order w.r.t. what was given on the
        ocamlc -a command line when the library was created;
   - Clflags.ccobjs is reversed just before calling the C compiler for the
        custom link;
   - .cma files on the command line of ocamlc are scanned right to left;
   - Before linking, we add lib_ccobjs after Clflags.ccobjs.
   Thus, for ocamlc a.cma b.cma obj1 obj2
   where a.cma was built with ocamlc -i ... obja1 obja2
     and b.cma was built with ocamlc -i ... objb1 objb2
   lib_ccobjs starts as [],
   becomes objb2 objb1 when b.cma is scanned,
   then obja2 obja1 objb2 objb1 when a.cma is scanned.
   Clflags.ccobjs was initially obj2 obj1.
   and is set to obj2 obj1 obja2 obja1 objb2 objb1.
   Finally, the C compiler is given objb1 objb2 obja1 obja2 obj1 obj2,
   which is what we need.  (If b depends on a, a.cma must appear before
   b.cma, but b's C libraries must appear before a's C libraries.)
*)

(* First pass: determine which units are needed *)

module IdentSet =
  Set.Make(struct
    type t = Ident.t
    soit compare = compare
  fin)

soit missing_globals = ref IdentSet.empty

soit is_required (rel, pos) =
  filtre rel avec
    Reloc_setglobal id ->
      IdentSet.mem id !missing_globals
  | _ -> faux

soit add_required (rel, pos) =
  filtre rel avec
    Reloc_getglobal id ->
      missing_globals := IdentSet.add id !missing_globals
  | _ -> ()

soit remove_required (rel, pos) =
  filtre rel avec
    Reloc_setglobal id ->
      missing_globals := IdentSet.remove id !missing_globals
  | _ -> ()

soit scan_file obj_name tolink =
  soit file_name =
    essaie
      find_in_path !load_path obj_name
    avec Not_found ->
      raise(Error(File_not_found obj_name)) dans
  soit ic = open_in_bin file_name dans
  essaie
    soit buffer = input_bytes ic (String.length cmo_magic_number) dans
    si buffer = cmo_magic_number alors début
      (* This is a .cmo file. It must be linked in any case.
         Read the relocation information to see which modules it
         requires. *)
      soit compunit_pos = input_binary_int ic dans  (* Go to descriptor *)
      seek_in ic compunit_pos;
      soit compunit = (input_value ic : compilation_unit) dans
      close_in ic;
      List.iter add_required compunit.cu_reloc;
      Link_object(file_name, compunit) :: tolink
    fin
    sinon si buffer = cma_magic_number alors début
      (* This is an archive file. Each unit contained in it will be linked
         in only if needed. *)
      soit pos_toc = input_binary_int ic dans    (* Go to table of contents *)
      seek_in ic pos_toc;
      soit toc = (input_value ic : library) dans
      close_in ic;
      add_ccobjs toc;
      soit required =
        List.fold_right
          (fonc compunit reqd ->
            si compunit.cu_force_link
            || !Clflags.link_everything
            || List.exists is_required compunit.cu_reloc
            alors début
              List.iter remove_required compunit.cu_reloc;
              List.iter add_required compunit.cu_reloc;
              compunit :: reqd
            fin sinon
              reqd)
          toc.lib_units [] dans
      Link_archive(file_name, required) :: tolink
    fin
    sinon raise(Error(Not_an_object_file file_name))
  avec
    End_of_file -> close_in ic; raise(Error(Not_an_object_file file_name))
  | x -> close_in ic; raise x

(* Second pass: link in the required units *)

(* Consistency check between interfaces *)

soit crc_interfaces = Consistbl.create ()
soit implementations_defined = ref ([] : (string * string) list)

soit check_consistency ppf file_name cu =
  début essaie
    List.iter
      (fonc (name, crc) ->
        si name = cu.cu_name
        alors Consistbl.set crc_interfaces name crc file_name
        sinon Consistbl.check crc_interfaces name crc file_name)
      cu.cu_imports
  avec Consistbl.Inconsistency(name, user, auth) ->
    raise(Error(Inconsistent_import(name, user, auth)))
  fin;
  début essaie
    soit source = List.assoc cu.cu_name !implementations_defined dans
    Location.print_warning (Location.in_file file_name) ppf
      (Warnings.Multiple_definition(cu.cu_name,
                                    Location.show_filename file_name,
                                    Location.show_filename source))
  avec Not_found -> ()
  fin;
  implementations_defined :=
    (cu.cu_name, file_name) :: !implementations_defined

soit extract_crc_interfaces () =
  Consistbl.extract crc_interfaces

(* Record compilation events *)

soit debug_info = ref ([] : (int * LongString.t) list)

(* Link in a compilation unit *)

soit link_compunit ppf output_fun currpos_fun inchan file_name compunit =
  check_consistency ppf file_name compunit;
  seek_in inchan compunit.cu_pos;
  soit code_block = LongString.input_bytes inchan compunit.cu_codesize dans
  Symtable.ls_patch_object code_block compunit.cu_reloc;
  si !Clflags.debug && compunit.cu_debug > 0 alors début
    seek_in inchan compunit.cu_debug;
    soit buffer = LongString.input_bytes inchan compunit.cu_debugsize dans
    debug_info := (currpos_fun(), buffer) :: !debug_info
  fin;
  Array.iter output_fun code_block;
  si !Clflags.link_everything alors
    List.iter Symtable.require_primitive compunit.cu_primitives

(* Link in a .cmo file *)

soit link_object ppf output_fun currpos_fun file_name compunit =
  soit inchan = open_in_bin file_name dans
  essaie
    link_compunit ppf output_fun currpos_fun inchan file_name compunit;
    close_in inchan
  avec
    Symtable.Error msg ->
      close_in inchan; raise(Error(Symbol_error(file_name, msg)))
  | x ->
      close_in inchan; raise x

(* Link in a .cma file *)

soit link_archive ppf output_fun currpos_fun file_name units_required =
  soit inchan = open_in_bin file_name dans
  essaie
    List.iter
      (fonc cu ->
         soit name = file_name ^ "(" ^ cu.cu_name ^ ")" dans
         essaie
           link_compunit ppf output_fun currpos_fun inchan name cu
         avec Symtable.Error msg ->
           raise(Error(Symbol_error(name, msg))))
      units_required;
    close_in inchan
  avec x -> close_in inchan; raise x

(* Link in a .cmo or .cma file *)

soit link_file ppf output_fun currpos_fun = fonction
    Link_object(file_name, unit) ->
      link_object ppf output_fun currpos_fun file_name unit
  | Link_archive(file_name, units) ->
      link_archive ppf output_fun currpos_fun file_name units

(* Output the debugging information *)
(* Format is:
      <int32>          number of event lists
      <int32>          offset of first event list
      <output_value>   first event list
      ...
      <int32>          offset of last event list
      <output_value>   last event list *)

soit output_debug_info oc =
  output_binary_int oc (List.length !debug_info);
  List.iter
    (fonc (ofs, evl) ->
      output_binary_int oc ofs;
      Array.iter (output_string oc) evl)
    !debug_info;
  debug_info := []

(* Output a list of strings with 0-termination *)

soit output_stringlist oc l =
  List.iter (fonc s -> output_string oc s; output_byte oc 0) l

(* Transform a file name into an absolute file name *)

soit make_absolute file =
  si Filename.is_relative file
  alors Filename.concat (Sys.getcwd()) file
  sinon file

(* Create a bytecode executable file *)

soit link_bytecode ppf tolink exec_name standalone =
  (* Avoid the case where the specified exec output file is the same as
     one of the objects to be linked *)
  List.iter (fonction
    | Link_object(file_name, _) quand file_name = exec_name ->
      raise (Error (Wrong_object_name exec_name));
    | _ -> ()) tolink;
  Misc.remove_file exec_name; (* avoid permission problems, cf PR#1911 *)
  soit outchan =
    open_out_gen [Open_wronly; Open_trunc; Open_creat; Open_binary]
                 0o777 exec_name dans
  essaie
    si standalone alors début
      (* Copy the header *)
      essaie
        soit header =
          si String.length !Clflags.use_runtime > 0
          alors "camlheader_ur" sinon "camlheader" ^ !Clflags.runtime_variant dans
        soit inchan = open_in_bin (find_in_path !load_path header) dans
        copy_file inchan outchan;
        close_in inchan
      avec Not_found | Sys_error _ -> ()
    fin;
    Bytesections.init_record outchan;
    (* The path to the bytecode interpreter (in use_runtime mode) *)
    si String.length !Clflags.use_runtime > 0 alors début
      output_string outchan (make_absolute !Clflags.use_runtime);
      output_char outchan '\n';
      Bytesections.record outchan "RNTM"
    fin;
    (* The bytecode *)
    soit start_code = pos_out outchan dans
    Symtable.init();
    Consistbl.clear crc_interfaces;
    soit sharedobjs = List.map Dll.extract_dll_name !Clflags.dllibs dans
    soit check_dlls = standalone && Config.target = Config.host dans
    si check_dlls alors début
      (* Initialize the DLL machinery *)
      Dll.init_compile !Clflags.no_std_include;
      Dll.add_path !load_path;
      essaie Dll.open_dlls Dll.For_checking sharedobjs
      avec Failure reason -> raise(Error(Cannot_open_dll reason))
    fin;
    soit output_fun = output_string outchan
    et currpos_fun () = pos_out outchan - start_code dans
    List.iter (link_file ppf output_fun currpos_fun) tolink;
    si check_dlls alors Dll.close_all_dlls();
    (* The final STOP instruction *)
    output_byte outchan Opcodes.opSTOP;
    output_byte outchan 0; output_byte outchan 0; output_byte outchan 0;
    Bytesections.record outchan "CODE";
    (* DLL stuff *)
    si standalone alors début
      (* The extra search path for DLLs *)
      output_stringlist outchan !Clflags.dllpaths;
      Bytesections.record outchan "DLPT";
      (* The names of the DLLs *)
      output_stringlist outchan sharedobjs;
      Bytesections.record outchan "DLLS"
    fin;
    (* The names of all primitives *)
    Symtable.output_primitive_names outchan;
    Bytesections.record outchan "PRIM";
    (* The table of global data *)
    début essaie
      Marshal.to_channel outchan (Symtable.initial_global_table())
          (si !Clflags.bytecode_compatible_32
           alors [Marshal.Compat_32] sinon [])
    avec Failure _ ->
      raise (Error Not_compatible_32)
    fin;
    Bytesections.record outchan "DATA";
    (* The map of global identifiers *)
    Symtable.output_global_map outchan;
    Bytesections.record outchan "SYMB";
    (* CRCs for modules *)
    output_value outchan (extract_crc_interfaces());
    Bytesections.record outchan "CRCS";
    (* Debug info *)
    si !Clflags.debug alors début
      output_debug_info outchan;
      Bytesections.record outchan "DBUG"
    fin;
    (* The table of contents and the trailer *)
    Bytesections.write_toc_and_trailer outchan;
    close_out outchan
  avec x ->
    close_out outchan;
    remove_file exec_name;
    raise x

(* Output a string as a C array of unsigned ints *)

soit output_code_string_counter = ref 0

soit output_code_string outchan code =
  soit pos = ref 0 dans
  soit len = String.length code dans
  pendant_que !pos < len faire
    soit c1 = Char.code(code.[!pos]) dans
    soit c2 = Char.code(code.[!pos + 1]) dans
    soit c3 = Char.code(code.[!pos + 2]) dans
    soit c4 = Char.code(code.[!pos + 3]) dans
    pos := !pos + 4;
    Printf.fprintf outchan "0x%02x%02x%02x%02x, " c4 c3 c2 c1;
    incr output_code_string_counter;
    si !output_code_string_counter >= 6 alors début
      output_char outchan '\n';
      output_code_string_counter := 0
    fin
  fait

(* Output a string as a C string *)

soit output_data_string outchan data =
  soit counter = ref 0 dans
  pour i = 0 à String.length data - 1 faire
    Printf.fprintf outchan "%d, " (Char.code(data.[i]));
    incr counter;
    si !counter >= 12 alors début
      output_string outchan "\n";
      counter := 0
    fin
  fait

(* Output a debug stub *)

soit output_cds_file outfile =
  Misc.remove_file outfile;
  soit outchan =
    open_out_gen [Open_wronly; Open_trunc; Open_creat; Open_binary]
      0o777 outfile dans
  essaie
    Bytesections.init_record outchan;
    (* The map of global identifiers *)
    Symtable.output_global_map outchan;
    Bytesections.record outchan "SYMB";
    (* Debug info *)
    output_debug_info outchan;
    Bytesections.record outchan "DBUG";
    (* The table of contents and the trailer *)
    Bytesections.write_toc_and_trailer outchan;
    close_out outchan
  avec x ->
    close_out outchan;
    remove_file outfile;
    raise x

(* Output a bytecode executable as a C file *)

soit link_bytecode_as_c ppf tolink outfile =
  soit outchan = open_out outfile dans
  début essaie
    (* The bytecode *)
    output_string outchan "\
#ifdef __cplusplus\
\nextern \"C\" {\
\n#endif\
\n#include <caml/mlvalues.h>\
\nCAMLextern void caml_startup_code(\
\n           code_t code, asize_t code_size,\
\n           char *data, asize_t data_size,\
\n           char *section_table, asize_t section_table_size,\
\n           char **argv);\n";
    output_string outchan "static int caml_code[] = {\n";
    Symtable.init();
    Consistbl.clear crc_interfaces;
    soit currpos = ref 0 dans
    soit output_fun code =
      output_code_string outchan code;
      currpos := !currpos + String.length code
    et currpos_fun () = !currpos dans
    List.iter (link_file ppf output_fun currpos_fun) tolink;
    (* The final STOP instruction *)
    Printf.fprintf outchan "\n0x%x};\n\n" Opcodes.opSTOP;
    (* The table of global data *)
    output_string outchan "static char caml_data[] = {\n";
    output_data_string outchan
      (Marshal.to_string (Symtable.initial_global_table()) []);
    output_string outchan "\n};\n\n";
    (* The sections *)
    soit sections =
      [ "SYMB", Symtable.data_global_map();
        "PRIM", Obj.repr(Symtable.data_primitive_names());
        "CRCS", Obj.repr(extract_crc_interfaces()) ] dans
    output_string outchan "static char caml_sections[] = {\n";
    output_data_string outchan
      (Marshal.to_string sections []);
    output_string outchan "\n};\n\n";
    (* The table of primitives *)
    Symtable.output_primitive_table outchan;
    (* The entry point *)
    output_string outchan "\
\nvoid caml_startup(char ** argv)\
\n{\
\n  caml_startup_code(caml_code, sizeof(caml_code),\
\n                    caml_data, sizeof(caml_data),\
\n                    caml_sections, sizeof(caml_sections),\
\n                    argv);\
\n}\
\n#ifdef __cplusplus\
\n}\
\n#endif\n";
    close_out outchan
  avec x ->
    close_out outchan;
    remove_file outfile;
    raise x
  fin;
  si !Clflags.debug alors
    output_cds_file ((Filename.chop_extension outfile) ^ ".cds")

(* Build a custom runtime *)

soit build_custom_runtime prim_name exec_name =
  soit runtime_lib = "-lcamlrun" ^ !Clflags.runtime_variant dans
  Ccomp.call_linker Ccomp.Exe exec_name
    ([prim_name] @ List.rev !Clflags.ccobjs @ [runtime_lib])
    (Clflags.std_include_flag "-I" ^ " " ^ Config.bytecomp_c_libraries)

soit append_bytecode_and_cleanup bytecode_name exec_name prim_name =
  soit oc = open_out_gen [Open_wronly; Open_append; Open_binary] 0 exec_name dans
  soit ic = open_in_bin bytecode_name dans
  copy_file ic oc;
  close_in ic;
  close_out oc;
  remove_file bytecode_name;
  remove_file prim_name

(* Fix the name of the output file, if the C compiler changes it behind
   our back. *)

soit fix_exec_name name =
  filtre Sys.os_type avec
    "Win32" | "Cygwin" ->
      si String.contains name '.' alors name sinon name ^ ".exe"
  | _ -> name

(* Main entry point (build a custom runtime if needed) *)

soit link ppf objfiles output_name =
  soit objfiles =
    si !Clflags.nopervasives alors objfiles
    sinon si !Clflags.output_c_object alors "stdlib.cma" :: objfiles
    sinon "stdlib.cma" :: (objfiles @ ["std_exit.cmo"]) dans
  soit tolink = List.fold_right scan_file objfiles [] dans
  Clflags.ccobjs := !Clflags.ccobjs @ !lib_ccobjs; (* put user's libs last *)
  Clflags.all_ccopts := !lib_ccopts @ !Clflags.all_ccopts;
                                                   (* put user's opts first *)
  Clflags.dllibs := !lib_dllibs @ !Clflags.dllibs; (* put user's DLLs first *)
  si not !Clflags.custom_runtime alors
    link_bytecode ppf tolink output_name vrai
  sinon si not !Clflags.output_c_object alors début
    soit bytecode_name = Filename.temp_file "camlcode" "" dans
    soit prim_name = Filename.temp_file "camlprim" ".c" dans
    essaie
      link_bytecode ppf tolink bytecode_name faux;
      soit poc = open_out prim_name dans
      output_string poc "\
        #ifdef __cplusplus\n\
        extern \"C\" {\n\
        #endif\n\
        #ifdef _WIN64\n\
        #ifdef __MINGW32__\n\
        typedef long long value;\n\
        #else\n\
        typedef __int64 value;\n\
        #endif\n\
        #else\n\
        typedef long value;\n\
        #endif\n";
      Symtable.output_primitive_table poc;
      output_string poc "\
        #ifdef __cplusplus\n\
        }\n\
        #endif\n";
      close_out poc;
      soit exec_name = fix_exec_name output_name dans
      si not (build_custom_runtime prim_name exec_name)
      alors raise(Error Custom_runtime);
      si !Clflags.make_runtime
      alors (remove_file bytecode_name; remove_file prim_name)
      sinon append_bytecode_and_cleanup bytecode_name exec_name prim_name
    avec x ->
      remove_file bytecode_name;
      remove_file prim_name;
      raise x
  fin sinon début
    soit basename = Filename.chop_extension output_name dans
    soit c_file = basename ^ ".c"
    et obj_file = basename ^ Config.ext_obj dans
    si Sys.file_exists c_file alors raise(Error(File_exists c_file));
    soit temps = ref [] dans
    essaie
      link_bytecode_as_c ppf tolink c_file;
      si not (Filename.check_suffix output_name ".c") alors début
        temps := c_file :: !temps;
        si Ccomp.compile_file c_file <> 0 alors raise(Error Custom_runtime);
        si not (Filename.check_suffix output_name Config.ext_obj) alors début
          temps := obj_file :: !temps;
          si not (
            soit runtime_lib = "-lcamlrun" ^ !Clflags.runtime_variant dans
            Ccomp.call_linker Ccomp.MainDll output_name
              ([obj_file] @ List.rev !Clflags.ccobjs @ [runtime_lib])
              Config.bytecomp_c_libraries
           ) alors raise (Error Custom_runtime);
        fin
      fin;
      List.iter remove_file !temps
    avec x ->
      List.iter remove_file !temps;
      raise x
  fin

(* Error report *)

ouvre Format

soit report_error ppf = fonction
  | File_not_found name ->
      fprintf ppf "Cannot find file %a" Location.print_filename name
  | Not_an_object_file name ->
      fprintf ppf "The file %a is not a bytecode object file"
        Location.print_filename name
  | Wrong_object_name name ->
      fprintf ppf "The output file %s has the wrong name. The extension implies\
                  \ an object file but the link step was requested" name
  | Symbol_error(name, err) ->
      fprintf ppf "Error while linking %a:@ %a" Location.print_filename name
      Symtable.report_error err
  | Inconsistent_import(intf, file1, file2) ->
      fprintf ppf
        "@[<hov>Files %a@ and %a@ \
                 make inconsistent assumptions over interface %s@]"
        Location.print_filename file1
        Location.print_filename file2
        intf
  | Custom_runtime ->
      fprintf ppf "Error while building custom runtime system"
  | File_exists file ->
      fprintf ppf "Cannot overwrite existing file %a"
        Location.print_filename file
  | Cannot_open_dll file ->
      fprintf ppf "Error on dynamically loaded library: %a"
        Location.print_filename file
  | Not_compatible_32 ->
      fprintf ppf "Generated bytecode executable cannot be run\
                  \ on a 32-bit platform"

soit () =
  Location.register_error_of_exn
    (fonction
      | Error err -> Some (Location.error_of_printer_file report_error err)
      | _ -> None
    )
