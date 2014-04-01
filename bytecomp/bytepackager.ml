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

(* "Package" a set of .cmo files into one .cmo file having the
   original compilation units as sub-modules. *)

ouvre Misc
ouvre Instruct
ouvre Cmo_format

type error =
    Forward_reference de string * Ident.t
  | Multiple_definition de string * Ident.t
  | Not_an_object_file de string
  | Illegal_renaming de string * string * string
  | File_not_found de string

exception Error de error

(* References accumulating information on the .cmo files *)

soit relocs = ref ([] : (reloc_info * int) list)
soit events = ref ([] : debug_event list)
soit primitives = ref ([] : string list)
soit force_link = ref faux

(* Record a relocation.  Update its offset, and rename GETGLOBAL and
   SETGLOBAL relocations that correspond to one of the units being
   consolidated. *)

soit rename_relocation packagename objfile mapping defined base (rel, ofs) =
  soit rel' =
    filtre rel avec
      Reloc_getglobal id ->
        début essaie
          soit id' = List.assoc id mapping dans
          si List.mem id defined
          alors Reloc_getglobal id'
          sinon raise(Error(Forward_reference(objfile, id)))
        avec Not_found ->
          (* PR#5276: unique-ize dotted global names, which appear
             if one of the units being consolidated is itself a packed
             module. *)
          soit name = Ident.name id dans
          si String.contains name '.' alors
            Reloc_getglobal (Ident.create_persistent (packagename ^ "." ^ name))
          sinon
            rel
        fin
    | Reloc_setglobal id ->
        début essaie
          soit id' = List.assoc id mapping dans
          si List.mem id defined
          alors raise(Error(Multiple_definition(objfile, id)))
          sinon Reloc_setglobal id'
        avec Not_found ->
          (* PR#5276, as above *)
          soit name = Ident.name id dans
          si String.contains name '.' alors
            Reloc_setglobal (Ident.create_persistent (packagename ^ "." ^ name))
          sinon
            rel
        fin
    | _ ->
        rel dans
  relocs := (rel', base + ofs) :: !relocs

(* Record and relocate a debugging event *)

soit relocate_debug base prefix subst ev =
  soit ev' = { ev avec ev_pos = base + ev.ev_pos;
                      ev_module = prefix ^ "." ^ ev.ev_module;
                      ev_typsubst = Subst.compose ev.ev_typsubst subst } dans
  events := ev' :: !events

(* Read the unit information from a .cmo file. *)

type pack_member_kind = PM_intf | PM_impl de compilation_unit

type pack_member =
  { pm_file: string;
    pm_name: string;
    pm_kind: pack_member_kind }

soit read_member_info file = (
  soit name =
    String.capitalize(Filename.basename(chop_extensions file)) dans
  soit kind =
    si Filename.check_suffix file ".cmo" alors début
    soit ic = open_in_bin file dans
    essaie
      soit buffer = input_bytes ic (String.length Config.cmo_magic_number) dans
      si buffer <> Config.cmo_magic_number alors
        raise(Error(Not_an_object_file file));
      soit compunit_pos = input_binary_int ic dans
      seek_in ic compunit_pos;
      soit compunit = (input_value ic : compilation_unit) dans
      si compunit.cu_name <> name
      alors raise(Error(Illegal_renaming(name, file, compunit.cu_name)));
      close_in ic;
      PM_impl compunit
    avec x ->
      close_in ic;
      raise x
    fin sinon
      PM_intf dans
  { pm_file = file; pm_name = name; pm_kind = kind }
)

(* Read the bytecode from a .cmo file.
   Write bytecode to channel [oc].
   Rename globals as indicated by [mapping] in reloc info.
   Accumulate relocs, debug info, etc.
   Return size of bytecode. *)

soit rename_append_bytecode ppf packagename oc mapping defined ofs prefix subst
                           objfile compunit =
  soit ic = open_in_bin objfile dans
  essaie
    Bytelink.check_consistency ppf objfile compunit;
    List.iter
      (rename_relocation packagename objfile mapping defined ofs)
      compunit.cu_reloc;
    primitives := compunit.cu_primitives @ !primitives;
    si compunit.cu_force_link alors force_link := vrai;
    seek_in ic compunit.cu_pos;
    Misc.copy_file_chunk ic oc compunit.cu_codesize;
    si !Clflags.debug && compunit.cu_debug > 0 alors début
      seek_in ic compunit.cu_debug;
      List.iter (relocate_debug ofs prefix subst) (input_value ic);
    fin;
    close_in ic;
    compunit.cu_codesize
  avec x ->
    close_in ic;
    raise x

(* Same, for a list of .cmo and .cmi files.
   Return total size of bytecode. *)

soit rec rename_append_bytecode_list ppf packagename oc mapping defined ofs
                                    prefix subst =
  fonction
    [] ->
      ofs
  | m :: rem ->
      filtre m.pm_kind avec
      | PM_intf ->
          rename_append_bytecode_list ppf packagename oc mapping defined ofs
                                      prefix subst rem
      | PM_impl compunit ->
          soit size =
            rename_append_bytecode ppf packagename oc mapping defined ofs
                                   prefix subst m.pm_file compunit dans
          soit id = Ident.create_persistent m.pm_name dans
          soit root = Path.Pident (Ident.create_persistent prefix) dans
          rename_append_bytecode_list ppf packagename oc mapping (id :: defined)
            (ofs + size) prefix
            (Subst.add_module id (Path.Pdot (root, Ident.name id, Path.nopos))
                              subst)
            rem

(* Generate the code that builds the tuple representing the package module *)

soit build_global_target oc target_name members mapping pos coercion =
  soit components =
    List.map2
      (fonc m (id1, id2) ->
        filtre m.pm_kind avec
        | PM_intf -> None
        | PM_impl _ -> Some id2)
      members mapping dans
  soit lam =
    Translmod.transl_package
      components (Ident.create_persistent target_name) coercion dans
  si !Clflags.dump_lambda alors
    Format.printf "%a@." Printlambda.lambda lam;
  soit instrs =
    Bytegen.compile_implementation target_name lam dans
  soit rel =
    Emitcode.to_packed_file oc instrs dans
  relocs := List.map (fonc (r, ofs) -> (r, pos + ofs)) rel @ !relocs

(* Build the .cmo file obtained by packaging the given .cmo files. *)

soit package_object_files ppf files targetfile targetname coercion =
  soit members =
    map_left_right read_member_info files dans
  soit unit_names =
    List.map (fonc m -> m.pm_name) members dans
  soit mapping =
    List.map
      (fonc name ->
          (Ident.create_persistent name,
           Ident.create_persistent(targetname ^ "." ^ name)))
      unit_names dans
  soit oc = open_out_bin targetfile dans
  essaie
    output_string oc Config.cmo_magic_number;
    soit pos_depl = pos_out oc dans
    output_binary_int oc 0;
    soit pos_code = pos_out oc dans
    soit ofs = rename_append_bytecode_list ppf targetname oc mapping [] 0
                                          targetname Subst.identity members dans
    build_global_target oc targetname members mapping ofs coercion;
    soit pos_debug = pos_out oc dans
    si !Clflags.debug && !events <> [] alors
      output_value oc (List.rev !events);
    soit pos_final = pos_out oc dans
    soit imports =
      List.filter
        (fonc (name, crc) -> not (List.mem name unit_names))
        (Bytelink.extract_crc_interfaces()) dans
    soit compunit =
      { cu_name = targetname;
        cu_pos = pos_code;
        cu_codesize = pos_debug - pos_code;
        cu_reloc = List.rev !relocs;
        cu_imports = (targetname, Env.crc_of_unit targetname) :: imports;
        cu_primitives = !primitives;
        cu_force_link = !force_link;
        cu_debug = si pos_final > pos_debug alors pos_debug sinon 0;
        cu_debugsize = pos_final - pos_debug } dans
    output_value oc compunit;
    seek_out oc pos_depl;
    output_binary_int oc pos_final;
    close_out oc
  avec x ->
    close_out oc;
    raise x

(* The entry point *)

soit package_files ppf files targetfile =
    soit files =
    List.map
        (fonc f ->
        essaie find_in_path !Config.load_path f
        avec Not_found -> raise(Error(File_not_found f)))
        files dans
    soit prefix = chop_extensions targetfile dans
    soit targetcmi = prefix ^ ".cmi" dans
    soit targetname = String.capitalize(Filename.basename prefix) dans
    essaie
      soit coercion = Typemod.package_units files targetcmi targetname dans
    soit ret = package_object_files ppf files targetfile targetname coercion dans
    ret
  avec x ->
    remove_file targetfile; raise x

(* Error report *)

ouvre Format

soit report_error ppf = fonction
    Forward_reference(file, ident) ->
      fprintf ppf "Forward reference to %s in file %a" (Ident.name ident)
        Location.print_filename file
  | Multiple_definition(file, ident) ->
      fprintf ppf "File %a redefines %s"
        Location.print_filename file
        (Ident.name ident)
  | Not_an_object_file file ->
      fprintf ppf "%a is not a bytecode object file"
        Location.print_filename file
  | Illegal_renaming(name, file, id) ->
      fprintf ppf "Wrong file naming: %a@ contains the code for\
                   @ %s when %s was expected"
        Location.print_filename file name id
  | File_not_found file ->
      fprintf ppf "File %s not found" file

soit () =
  Location.register_error_of_exn
    (fonction
      | Error err -> Some (Location.error_of_printer_file report_error err)
      | _ -> None
    )
