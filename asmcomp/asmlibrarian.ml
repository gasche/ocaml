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

(* Build libraries of .cmx files *)

ouvre Misc
ouvre Config
ouvre Cmx_format

type error =
    File_not_found de string
  | Archiver_error de string

exception Error de error

soit read_info name =
  soit filename =
    essaie
      find_in_path !load_path name
    avec Not_found ->
      raise(Error(File_not_found name)) dans
  soit (info, crc) = Compilenv.read_unit_info filename dans
  info.ui_force_link <- !Clflags.link_everything;
  (* There is no need to keep the approximation in the .cmxa file,
     since the compiler will go looking directly for .cmx files.
     The linker, which is the only one that reads .cmxa files, does not
     need the approximation. *)
  info.ui_approx <- Clambda.Value_unknown;
  (Filename.chop_suffix filename ".cmx" ^ ext_obj, (info, crc))

soit create_archive file_list lib_name =
  soit archive_name = chop_extension_if_any lib_name ^ ext_lib dans
  soit outchan = open_out_bin lib_name dans
  essaie
    output_string outchan cmxa_magic_number;
    soit (objfile_list, descr_list) =
      List.split (List.map read_info file_list) dans
    List.iter2
      (fonc file_name (unit, crc) ->
        Asmlink.check_consistency file_name unit crc)
      file_list descr_list;
    soit infos =
      { lib_units = descr_list;
        lib_ccobjs = !Clflags.ccobjs;
        lib_ccopts = !Clflags.all_ccopts } dans
    output_value outchan infos;
    si Ccomp.create_archive archive_name objfile_list <> 0
    alors raise(Error(Archiver_error archive_name));
    close_out outchan
  avec x ->
    close_out outchan;
    remove_file lib_name;
    remove_file archive_name;
    raise x

ouvre Format

soit report_error ppf = fonction
  | File_not_found name ->
      fprintf ppf "Cannot find file %s" name
  | Archiver_error name ->
      fprintf ppf "Error while creating the library %s" name

soit () =
  Location.register_error_of_exn
    (fonction
      | Error err -> Some (Location.error_of_printer_file report_error err)
      | _ -> None
    )
