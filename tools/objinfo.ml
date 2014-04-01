(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*        Mehdi Dogguy, PPS laboratory, University Paris Diderot       *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.   Modifications Copyright 2010 Mehdi Dogguy,       *)
(*  used and distributed as part of OCaml by permission from           *)
(*  the author.   This file is distributed under the terms of the      *)
(*  Q Public License version 1.0.                                      *)
(*                                                                     *)
(***********************************************************************)

(* Dump info on .cmi, .cmo, .cmx, .cma, .cmxa, .cmxs files
   and on bytecode executables. *)

ouvre Printf
ouvre Misc
ouvre Config
ouvre Cmo_format

soit input_stringlist ic len =
  soit get_string_list sect len =
    soit rec fold s e acc =
      si e != len alors
        si sect.[e] = '\000' alors
          fold (e+1) (e+1) (String.sub sect s (e-s) :: acc)
        sinon fold s (e+1) acc
      sinon acc
    dans fold 0 0 []
  dans
  soit sect = Misc.input_bytes ic len dans
  get_string_list sect len

soit print_name_crc (name, crc) =
  printf "\t%s\t%s\n" (Digest.to_hex crc) name

soit print_line name =
  printf "\t%s\n" name

soit print_cmo_infos cu =
  printf "Unit name: %s\n" cu.cu_name;
  print_string "Interfaces imported:\n";
  List.iter print_name_crc cu.cu_imports;
  printf "Uses unsafe features: ";
  (filtre cu.cu_primitives avec
    | [] -> printf "no\n"
    | l  ->
        printf "YES\n";
        printf "Primitives declared in this module:\n";
        List.iter print_line l);
  printf "Force link: %s\n" (si cu.cu_force_link alors "YES" sinon "no")

soit print_spaced_string s =
  printf " %s" s

soit print_cma_infos (lib : Cmo_format.library) =
  printf "Force custom: %s\n" (si lib.lib_custom alors "YES" sinon "no");
  printf "Extra C object files:";
  (* PR#4949: print in linking order *)
  List.iter print_spaced_string (List.rev lib.lib_ccobjs);
  printf "\nExtra C options:";
  List.iter print_spaced_string lib.lib_ccopts;
  printf "\n";
  print_string "Extra dynamically-loaded libraries:";
  List.iter print_spaced_string lib.lib_dllibs;
  printf "\n";
  List.iter print_cmo_infos lib.lib_units

soit print_cmi_infos name sign crcs =
  printf "Unit name: %s\n" name;
  printf "Interfaces imported:\n";
  List.iter print_name_crc crcs

soit print_general_infos name crc defines cmi cmx =
  printf "Name: %s\n" name;
  printf "CRC of implementation: %s\n" (Digest.to_hex crc);
  printf "Globals defined:\n";
  List.iter print_line defines;
  printf "Interfaces imported:\n";
  List.iter print_name_crc cmi;
  printf "Implementations imported:\n";
  List.iter print_name_crc cmx

ouvre Cmx_format

soit print_cmx_infos (ui, crc) =
  print_general_infos
    ui.ui_name crc ui.ui_defines ui.ui_imports_cmi ui.ui_imports_cmx;
  printf "Approximation:\n";
  Format.fprintf Format.std_formatter "  %a@." Printclambda.approx ui.ui_approx;
  soit pr_funs _ fns =
    List.iter (fonc arity -> printf " %d" arity) fns dans
  printf "Currying functions:%a\n" pr_funs ui.ui_curry_fun;
  printf "Apply functions:%a\n" pr_funs ui.ui_apply_fun;
  printf "Send functions:%a\n" pr_funs ui.ui_send_fun;
  printf "Force link: %s\n" (si ui.ui_force_link alors "YES" sinon "no")

soit print_cmxa_infos (lib : Cmx_format.library_infos) =
  printf "Extra C object files:";
  List.iter print_spaced_string (List.rev lib.lib_ccobjs);
  printf "\nExtra C options:";
  List.iter print_spaced_string lib.lib_ccopts;
  printf "\n";
  List.iter print_cmx_infos lib.lib_units

soit print_cmxs_infos header =
  List.iter
    (fonc ui ->
       print_general_infos
         ui.dynu_name
         ui.dynu_crc
         ui.dynu_defines
         ui.dynu_imports_cmi
         ui.dynu_imports_cmx)
    header.dynu_units

soit p_title title = printf "%s:\n" title

soit p_section title = fonction
  | [] -> ()
  | l ->
      p_title title;
      List.iter print_name_crc l

soit p_list title print = fonction
  | [] -> ()
  | l ->
      p_title title;
      List.iter print l

soit dump_byte ic =
  Bytesections.read_toc ic;
  soit toc = Bytesections.toc () dans
  soit toc = List.sort Pervasives.compare toc dans
  List.iter
    (fonc (section, _) ->
       essaie
         soit len = Bytesections.seek_section ic section dans
         si len > 0 alors filtre section avec
           | "CRCS" ->
               p_section
                 "Imported units"
                 (input_value ic : (string * Digest.t) list)
           | "DLLS" ->
               p_list
                 "Used DLLs"
                 print_line
                 (input_stringlist ic len)
           | "DLPT" ->
               p_list
                 "Additional DLL paths"
                 print_line
                 (input_stringlist ic len)
           | "PRIM" ->
               p_list
                 "Primitives used"
                 print_line
                 (input_stringlist ic len)
           | _ -> ()
       avec _ -> ()
    )
    toc

soit read_dyn_header filename ic =
  soit tempfile = Filename.temp_file "objinfo" ".out" dans
  soit helper = Filename.concat Config.standard_library "objinfo_helper" dans
  essaie
    try_finally
      (fonc () ->
        soit rc = Sys.command (sprintf "%s %s > %s"
                                (Filename.quote helper)
                                (Filename.quote filename)
                                tempfile) dans
        si rc <> 0 alors failwith "impossible de lire";
        soit tc = open_in tempfile dans
        try_finally
          (fonc () ->
            soit ofs = Scanf.fscanf tc "%Ld" (fonc x -> x) dans
            LargeFile.seek_in ic ofs;
            Some(input_value ic : dynheader))
          (fonc () -> close_in tc))
      (fonc () -> remove_file tempfile)
  avec Failure _ | Sys_error _ -> None

soit dump_obj filename =
  printf "File %s\n" filename;
  soit ic = open_in_bin filename dans
  soit len_magic_number = String.length cmo_magic_number dans
  soit magic_number = Misc.input_bytes ic len_magic_number dans
  si magic_number = cmo_magic_number alors début
    soit cu_pos = input_binary_int ic dans
    seek_in ic cu_pos;
    soit cu = (input_value ic : compilation_unit) dans
    close_in ic;
    print_cmo_infos cu
  fin sinon si magic_number = cma_magic_number alors début
    soit toc_pos = input_binary_int ic dans
    seek_in ic toc_pos;
    soit toc = (input_value ic : library) dans
    close_in ic;
    print_cma_infos toc
  fin sinon si magic_number = cmi_magic_number alors début
    soit cmi = Cmi_format.input_cmi ic dans
    close_in ic;
    print_cmi_infos cmi.Cmi_format.cmi_name cmi.Cmi_format.cmi_sign
      cmi.Cmi_format.cmi_crcs
  fin sinon si magic_number = cmx_magic_number alors début
    soit ui = (input_value ic : unit_infos) dans
    soit crc = Digest.input ic dans
    close_in ic;
    print_cmx_infos (ui, crc)
  fin sinon si magic_number = cmxa_magic_number alors début
    soit li = (input_value ic : library_infos) dans
    close_in ic;
    print_cmxa_infos li
  fin sinon début
    soit pos_trailer = in_channel_length ic - len_magic_number dans
    soit _ = seek_in ic pos_trailer dans
    soit _ = really_input ic magic_number 0 len_magic_number dans
    si magic_number = Config.exec_magic_number alors début
      dump_byte ic;
      close_in ic
    fin sinon si Filename.check_suffix filename ".cmxs" alors début
      flush stdout;
      filtre read_dyn_header filename ic avec
      | None ->
          printf "Impossible de lire les informations sur le fichier %s\n" filename;
          exit 2
      | Some header ->
          si header.dynu_magic = Config.cmxs_magic_number alors
            print_cmxs_infos header
          sinon début
            printf "Mauvais nombre magique\n"; exit 2
          fin;
          close_in ic
    fin sinon début
      printf "Ce n'est pas un fichier objet Chamelle\n"; exit 2
    fin
  fin

soit arg_list = []
soit arg_usage =
   Printf.sprintf "%s [OPTIONS] FILES : donne des informations sur les fichiers" Sys.argv.(0)

soit main() =
  Arg.parse arg_list dump_obj arg_usage;
  exit 0

soit _ = main ()
