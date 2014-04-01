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

(* Build libraries of .cmo files *)

ouvre Misc
ouvre Config
ouvre Cmo_format

type error =
    File_not_found de string
  | Not_an_object_file de string

exception Error de error

(* Copy a compilation unit from a .cmo or .cma into the archive *)
soit copy_compunit ic oc compunit =
  seek_in ic compunit.cu_pos;
  compunit.cu_pos <- pos_out oc;
  compunit.cu_force_link <- !Clflags.link_everything;
  copy_file_chunk ic oc compunit.cu_codesize;
  si compunit.cu_debug > 0 alors début
    seek_in ic compunit.cu_debug;
    compunit.cu_debug <- pos_out oc;
    copy_file_chunk ic oc compunit.cu_debugsize
  fin

(* Add C objects and options and "custom" info from a library descriptor *)

soit lib_ccobjs = ref []
soit lib_ccopts = ref []
soit lib_dllibs = ref []

(* See Bytelink.add_ccobjs for explanations on how options are ordered.
   Notice that here we scan .cma files given on the command line from
   left to right, hence options must be added after. *)

soit add_ccobjs l =
  si not !Clflags.no_auto_link alors début
    si l.lib_custom alors Clflags.custom_runtime := vrai;
    lib_ccobjs := !lib_ccobjs @ l.lib_ccobjs;
    lib_ccopts := !lib_ccopts @ l.lib_ccopts;
    lib_dllibs := !lib_dllibs @ l.lib_dllibs
  fin

soit copy_object_file ppf oc name =
  soit file_name =
    essaie
      find_in_path !load_path name
    avec Not_found ->
      raise(Error(File_not_found name)) dans
  soit ic = open_in_bin file_name dans
  essaie
    soit buffer = input_bytes ic (String.length cmo_magic_number) dans
    si buffer = cmo_magic_number alors début
      soit compunit_pos = input_binary_int ic dans
      seek_in ic compunit_pos;
      soit compunit = (input_value ic : compilation_unit) dans
      Bytelink.check_consistency ppf file_name compunit;
      copy_compunit ic oc compunit;
      close_in ic;
      [compunit]
    fin sinon
    si buffer = cma_magic_number alors début
      soit toc_pos = input_binary_int ic dans
      seek_in ic toc_pos;
      soit toc = (input_value ic : library) dans
      List.iter (Bytelink.check_consistency ppf file_name) toc.lib_units;
      add_ccobjs toc;
      List.iter (copy_compunit ic oc) toc.lib_units;
      close_in ic;
      toc.lib_units
    fin sinon
      raise(Error(Not_an_object_file file_name))
  avec
    End_of_file -> close_in ic; raise(Error(Not_an_object_file file_name))
  | x -> close_in ic; raise x

soit create_archive ppf file_list lib_name =
  soit outchan = open_out_bin lib_name dans
  essaie
    output_string outchan cma_magic_number;
    soit ofs_pos_toc = pos_out outchan dans
    output_binary_int outchan 0;
    soit units =
      List.flatten(List.map (copy_object_file ppf outchan) file_list) dans
    soit toc =
      { lib_units = units;
        lib_custom = !Clflags.custom_runtime;
        lib_ccobjs = !Clflags.ccobjs @ !lib_ccobjs;
        lib_ccopts = !Clflags.all_ccopts @ !lib_ccopts;
        lib_dllibs = !Clflags.dllibs @ !lib_dllibs } dans
    soit pos_toc = pos_out outchan dans
    output_value outchan toc;
    seek_out outchan ofs_pos_toc;
    output_binary_int outchan pos_toc;
    close_out outchan
  avec x ->
    close_out outchan;
    remove_file lib_name;
    raise x

ouvre Format

soit report_error ppf = fonction
  | File_not_found name ->
      fprintf ppf "Cannot find file %s" name
  | Not_an_object_file name ->
      fprintf ppf "The file %a is not a bytecode object file"
        Location.print_filename name

soit () =
  Location.register_error_of_exn
    (fonction
      | Error err -> Some (Location.error_of_printer_file report_error err)
      | _ -> None
    )
