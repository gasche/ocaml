(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 2002 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* "Package" a set of .cmx/.o files into one .cmx/.o file having the
   original compilation units as sub-modules. *)

ouvre Misc
ouvre Cmx_format

type error =
    Illegal_renaming de string * string * string
  | Forward_reference de string * string
  | Wrong_for_pack de string * string
  | Linking_error
  | Assembler_error de string
  | File_not_found de string


exception Error de error

(* Read the unit information from a .cmx file. *)

type pack_member_kind = PM_intf | PM_impl de unit_infos

type pack_member =
  { pm_file: string;
    pm_name: string;
    pm_kind: pack_member_kind }

soit read_member_info pack_path file = (
  soit name =
    String.capitalize(Filename.basename(chop_extensions file)) dans
  soit kind =
    si Filename.check_suffix file ".cmx" alors début
      soit (info, crc) = Compilenv.read_unit_info file dans
      si info.ui_name <> name
      alors raise(Error(Illegal_renaming(name, file, info.ui_name)));
      si info.ui_symbol <>
         (Compilenv.current_unit_infos()).ui_symbol ^ "__" ^ info.ui_name
      alors raise(Error(Wrong_for_pack(file, pack_path)));
      Asmlink.check_consistency file info crc;
      Compilenv.cache_unit_info info;
      PM_impl info
    fin sinon
      PM_intf dans
  { pm_file = file; pm_name = name; pm_kind = kind }
)

(* Check absence of forward references *)

soit check_units members =
  soit rec check forbidden = fonction
    [] -> ()
  | mb :: tl ->
      début filtre mb.pm_kind avec
      | PM_intf -> ()
      | PM_impl infos ->
          List.iter
            (fonc (unit, _) ->
              si List.mem unit forbidden
              alors raise(Error(Forward_reference(mb.pm_file, unit))))
            infos.ui_imports_cmx
      fin;
      check (list_remove mb.pm_name forbidden) tl dans
  check (List.map (fonc mb -> mb.pm_name) members) members

(* Make the .o file for the package *)

soit make_package_object ppf members targetobj targetname coercion =
  soit objtemp =
    si !Clflags.keep_asm_file
    alors chop_extension_if_any targetobj ^ ".pack" ^ Config.ext_obj
    sinon
      (* Put the full name of the module in the temporary file name
         to avoid collisions with MSVC's link /lib in case of successive
         packs *)
      Filename.temp_file (Compilenv.make_symbol (Some "")) Config.ext_obj dans
  soit components =
    List.map
      (fonc m ->
        filtre m.pm_kind avec
        | PM_intf -> None
        | PM_impl _ -> Some(Ident.create_persistent m.pm_name))
      members dans
  Asmgen.compile_implementation
    (chop_extension_if_any objtemp) ppf
    (Translmod.transl_store_package
       components (Ident.create_persistent targetname) coercion);
  soit objfiles =
    List.map
      (fonc m -> chop_extension_if_any m.pm_file ^ Config.ext_obj)
      (List.filter (fonc m -> m.pm_kind <> PM_intf) members) dans
  soit ok =
    Ccomp.call_linker Ccomp.Partial targetobj (objtemp :: objfiles) ""
  dans
  remove_file objtemp;
  si not ok alors raise(Error Linking_error)

(* Make the .cmx file for the package *)

soit build_package_cmx members cmxfile =
  soit unit_names =
    List.map (fonc m -> m.pm_name) members dans
  soit filter lst =
    List.filter (fonc (name, crc) -> not (List.mem name unit_names)) lst dans
  soit union lst =
    List.fold_left
      (List.fold_left
          (fonc accu n -> si List.mem n accu alors accu sinon n :: accu))
      [] lst dans
  soit units =
    List.fold_right
      (fonc m accu ->
        filtre m.pm_kind avec PM_intf -> accu | PM_impl info -> info :: accu)
      members [] dans
  soit ui = Compilenv.current_unit_infos() dans
  soit pkg_infos =
    { ui_name = ui.ui_name;
      ui_symbol = ui.ui_symbol;
      ui_defines =
          List.flatten (List.map (fonc info -> info.ui_defines) units) @
          [ui.ui_symbol];
      ui_imports_cmi =
          (ui.ui_name, Env.crc_of_unit ui.ui_name) ::
          filter(Asmlink.extract_crc_interfaces());
      ui_imports_cmx =
          filter(Asmlink.extract_crc_implementations());
      ui_approx = ui.ui_approx;
      ui_curry_fun =
          union(List.map (fonc info -> info.ui_curry_fun) units);
      ui_apply_fun =
          union(List.map (fonc info -> info.ui_apply_fun) units);
      ui_send_fun =
          union(List.map (fonc info -> info.ui_send_fun) units);
      ui_force_link =
          List.exists (fonc info -> info.ui_force_link) units;
    } dans
  Compilenv.write_unit_info pkg_infos cmxfile

(* Make the .cmx and the .o for the package *)

soit package_object_files ppf files targetcmx
                         targetobj targetname coercion =
  soit pack_path =
    filtre !Clflags.for_package avec
    | None -> targetname
    | Some p -> p ^ "." ^ targetname dans
  soit members = map_left_right (read_member_info pack_path) files dans
  check_units members;
  make_package_object ppf members targetobj targetname coercion;
  build_package_cmx members targetcmx

(* The entry point *)

soit package_files ppf files targetcmx =
  soit files =
    List.map
      (fonc f ->
        essaie find_in_path !Config.load_path f
        avec Not_found -> raise(Error(File_not_found f)))
      files dans
  soit prefix = chop_extensions targetcmx dans
  soit targetcmi = prefix ^ ".cmi" dans
  soit targetobj = chop_extension_if_any targetcmx ^ Config.ext_obj dans
  soit targetname = String.capitalize(Filename.basename prefix) dans
  (* Set the name of the current "input" *)
  Location.input_name := targetcmx;
  (* Set the name of the current compunit *)
  Compilenv.reset ?packname:!Clflags.for_package targetname;
  essaie
    soit coercion = Typemod.package_units files targetcmi targetname dans
    package_object_files ppf files targetcmx targetobj targetname coercion
  avec x ->
    remove_file targetcmx; remove_file targetobj;
    raise x

(* Error report *)

ouvre Format

soit report_error ppf = fonction
    Illegal_renaming(name, file, id) ->
      fprintf ppf "Wrong file naming: %a@ contains the code for\
                   @ %s when %s was expected"
        Location.print_filename file name id
  | Forward_reference(file, ident) ->
      fprintf ppf "Forward reference to %s in file %a" ident
        Location.print_filename file
  | Wrong_for_pack(file, path) ->
      fprintf ppf "File %a@ was not compiled with the `-for-pack %s' option"
              Location.print_filename file path
  | File_not_found file ->
      fprintf ppf "File %s not found" file
  | Assembler_error file ->
      fprintf ppf "Error while assembling %s" file
  | Linking_error ->
      fprintf ppf "Error during partial linking"

soit () =
  Location.register_error_of_exn
    (fonction
      | Error err -> Some (Location.error_of_printer_file report_error err)
      | _ -> None
    )
