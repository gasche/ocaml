(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../../LICENSE.  *)
(*                                                                     *)
(***********************************************************************)

(* Dynamic loading of .cmo files *)

ouvre Dynlinkaux  (* REMOVE_ME for ../../debugger/dynlink.ml *)
ouvre Cmo_format

type linking_error =
    Undefined_global de string
  | Unavailable_primitive de string
  | Uninitialized_global de string

type error =
    Not_a_bytecode_file de string
  | Inconsistent_import de string
  | Unavailable_unit de string
  | Unsafe_file
  | Linking_error de string * linking_error
  | Corrupted_interface de string
  | File_not_found de string
  | Cannot_open_dll de string
  | Inconsistent_implementation de string

exception Error de error

soit () =
  Printexc.register_printer
    (fonction
      | Error err ->
          soit msg = filtre err avec
          | Not_a_bytecode_file s ->
              Printf.sprintf "Not_a_bytecode_file %S" s
          | Inconsistent_import s ->
              Printf.sprintf "Inconsistent_import %S" s
          | Unavailable_unit s ->
              Printf.sprintf "Unavailable_unit %S" s
          | Unsafe_file ->
              "Unsafe_file"
          | Linking_error (s, Undefined_global s') ->
              Printf.sprintf "Linking_error (%S, Dynlink.Undefined_global %S)"
                             s s'
          | Linking_error (s, Unavailable_primitive s') ->
              Printf.sprintf "Linking_error (%S, Dynlink.Unavailable_primitive \
                              %S)" s s'
          | Linking_error (s, Uninitialized_global s') ->
              Printf.sprintf "Linking_error (%S, Dynlink.Uninitialized_global \
                              %S)" s s'
          | Corrupted_interface s ->
              Printf.sprintf "Corrupted_interface %S" s
          | File_not_found s ->
              Printf.sprintf "File_not_found %S" s
          | Cannot_open_dll s ->
              Printf.sprintf "Cannot_open_dll %S" s
          | Inconsistent_implementation s ->
              Printf.sprintf "Inconsistent_implementation %S" s dans
          Some (Printf.sprintf "Dynlink.Error(Dynlink.%s)" msg)
      | _ -> None)

(* Management of interface CRCs *)

soit crc_interfaces = ref (Consistbl.create ())
soit allow_extension = ref vrai

(* Check that the object file being loaded has been compiled against
   the same interfaces as the program itself. In addition, check that
   only authorized compilation units are referenced. *)

soit check_consistency file_name cu =
  essaie
    List.iter
      (fonc (name, crc) ->
        si name = cu.cu_name alors
          Consistbl.set !crc_interfaces name crc file_name
        sinon si !allow_extension alors
          Consistbl.check !crc_interfaces name crc file_name
        sinon
          Consistbl.check_noadd !crc_interfaces name crc file_name)
      cu.cu_imports
  avec Consistbl.Inconsistency(name, user, auth) ->
         raise(Error(Inconsistent_import name))
     | Consistbl.Not_available(name) ->
         raise(Error(Unavailable_unit name))

(* Empty the crc_interfaces table *)

soit clear_available_units () =
  Consistbl.clear !crc_interfaces;
  allow_extension := faux

(* Allow only access to the units with the given names *)

soit allow_only names =
  Consistbl.filter (fonc name -> List.mem name names) !crc_interfaces;
  allow_extension := faux

(* Prohibit access to the units with the given names *)

soit prohibit names =
  Consistbl.filter (fonc name -> not (List.mem name names)) !crc_interfaces;
  allow_extension := faux

(* Initialize the crc_interfaces table with a list of units with fixed CRCs *)

soit add_available_units units =
  List.iter (fonc (unit, crc) -> Consistbl.set !crc_interfaces unit crc "")
            units

(* Default interface CRCs: those found in the current executable *)
soit default_crcs = ref []

soit default_available_units () =
  clear_available_units();
  add_available_units !default_crcs;
  allow_extension := vrai

(* Initialize the linker tables and everything *)

soit inited = ref faux

soit init () =
  si not !inited alors début
    default_crcs := Symtable.init_toplevel();
    default_available_units ();
    inited := vrai;
  fin

soit clear_available_units () = init(); clear_available_units ()
soit allow_only l = init(); allow_only l
soit prohibit l = init(); prohibit l
soit add_available_units l = init(); add_available_units l
soit default_available_units () = init(); default_available_units ()

(* Read the CRC of an interface from its .cmi file *)

soit digest_interface unit loadpath =
  soit filename =
    soit shortname = unit ^ ".cmi" dans
    essaie
      Misc.find_in_path_uncap loadpath shortname
    avec Not_found ->
      raise (Error(File_not_found shortname)) dans
  soit ic = open_in_bin filename dans
  essaie
    soit buffer = Misc.input_bytes ic (String.length Config.cmi_magic_number) dans
    si buffer <> Config.cmi_magic_number alors début
      close_in ic;
      raise(Error(Corrupted_interface filename))
    fin;
    soit cmi = Cmi_format.input_cmi ic dans
    close_in ic;
    soit crc =
      filtre cmi.Cmi_format.cmi_crcs avec
        (_, crc) :: _ -> crc
      | _             -> raise(Error(Corrupted_interface filename))
    dans
    crc
  avec End_of_file | Failure _ ->
    close_in ic;
    raise(Error(Corrupted_interface filename))

(* Initialize the crc_interfaces table with a list of units.
   Their CRCs are read from their interfaces. *)

soit add_interfaces units loadpath =
  add_available_units
    (List.map (fonc unit -> (unit, digest_interface unit loadpath)) units)

(* Check whether the object file being loaded was compiled in unsafe mode *)

soit unsafe_allowed = ref faux

soit allow_unsafe_modules b =
  unsafe_allowed := b

soit check_unsafe_module cu =
  si (not !unsafe_allowed) && cu.cu_primitives <> []
  alors raise(Error(Unsafe_file))

(* Load in-core and execute a bytecode object file *)

dehors register_code_fragment: string -> int -> string -> unit
                               = "caml_register_code_fragment"

soit load_compunit ic file_name file_digest compunit =
  check_consistency file_name compunit;
  check_unsafe_module compunit;
  seek_in ic compunit.cu_pos;
  soit code_size = compunit.cu_codesize + 8 dans
  soit code = Meta.static_alloc code_size dans
  unsafe_really_input ic code 0 compunit.cu_codesize;
  String.unsafe_set code compunit.cu_codesize (Char.chr Opcodes.opRETURN);
  String.unsafe_set code (compunit.cu_codesize + 1) '\000';
  String.unsafe_set code (compunit.cu_codesize + 2) '\000';
  String.unsafe_set code (compunit.cu_codesize + 3) '\000';
  String.unsafe_set code (compunit.cu_codesize + 4) '\001';
  String.unsafe_set code (compunit.cu_codesize + 5) '\000';
  String.unsafe_set code (compunit.cu_codesize + 6) '\000';
  String.unsafe_set code (compunit.cu_codesize + 7) '\000';
  soit initial_symtable = Symtable.current_state() dans
  début essaie
    Symtable.patch_object code compunit.cu_reloc;
    Symtable.check_global_initialized compunit.cu_reloc;
    Symtable.update_global_table()
  avec Symtable.Error error ->
    soit new_error =
      filtre error avec
        Symtable.Undefined_global s -> Undefined_global s
      | Symtable.Unavailable_primitive s -> Unavailable_primitive s
      | Symtable.Uninitialized_global s -> Uninitialized_global s
      | _ -> affirme faux dans
    raise(Error(Linking_error (file_name, new_error)))
  fin;
  (* PR#5215: identify this code fragment by
     digest of file contents + unit name.
     Unit name is needed for .cma files, which produce several code fragments.*)
  soit digest = Digest.string (file_digest ^ compunit.cu_name) dans
  register_code_fragment code code_size digest;
  début essaie
    ignore((Meta.reify_bytecode code code_size) ())
  avec exn ->
    Symtable.restore_state initial_symtable;
    raise exn
  fin

soit loadfile file_name =
  init();
  si not (Sys.file_exists file_name)
    alors raise (Error (File_not_found file_name));
  soit ic = open_in_bin file_name dans
  soit file_digest = Digest.channel ic (-1) dans
  seek_in ic 0;
  essaie
    soit buffer =
      essaie Misc.input_bytes ic (String.length Config.cmo_magic_number)
      avec End_of_file -> raise (Error (Not_a_bytecode_file file_name))
    dans
    si buffer = Config.cmo_magic_number alors début
      soit compunit_pos = input_binary_int ic dans  (* Go to descriptor *)
      seek_in ic compunit_pos;
      soit cu = (input_value ic : compilation_unit) dans
      load_compunit ic file_name file_digest cu
    fin sinon
    si buffer = Config.cma_magic_number alors début
      soit toc_pos = input_binary_int ic dans  (* Go to table of contents *)
      seek_in ic toc_pos;
      soit lib = (input_value ic : library) dans
      début essaie
        Dll.open_dlls Dll.For_execution
                      (List.map Dll.extract_dll_name lib.lib_dllibs)
      avec Failure reason ->
        raise(Error(Cannot_open_dll reason))
      fin;
      List.iter (load_compunit ic file_name file_digest) lib.lib_units
    fin sinon
      raise(Error(Not_a_bytecode_file file_name));
    close_in ic
  avec exc ->
    close_in ic; raise exc

soit loadfile_private file_name =
  init();
  soit initial_symtable = Symtable.current_state()
  et initial_crc = !crc_interfaces dans
  essaie
    loadfile file_name;
    Symtable.hide_additions initial_symtable;
    crc_interfaces := initial_crc
  avec exn ->
    Symtable.hide_additions initial_symtable;
    crc_interfaces := initial_crc;
    raise exn

(* Error report *)

soit error_message = fonction
    Not_a_bytecode_file name ->
      name ^ " is not a bytecode object file"
  | Inconsistent_import name ->
      "interface mismatch on " ^ name
  | Unavailable_unit name ->
      "no implementation available for " ^ name
  | Unsafe_file ->
      "this object file uses unsafe features"
  | Linking_error (name, Undefined_global s) ->
      "error while linking " ^ name ^ ".\n" ^
      "Reference to undefined global `" ^ s ^ "'"
  | Linking_error (name, Unavailable_primitive s) ->
      "error while linking " ^ name ^ ".\n" ^
      "The external function `" ^ s ^ "' is not available"
  | Linking_error (name, Uninitialized_global s) ->
      "error while linking " ^ name ^ ".\n" ^
      "The module `" ^ s ^ "' is not yet initialized"
  | Corrupted_interface name ->
      "corrupted interface file " ^ name
  | File_not_found name ->
      "cannot find file " ^ name ^ " in search path"
  | Cannot_open_dll reason ->
      "error loading shared library: " ^ reason
  | Inconsistent_implementation name ->
      "implementation mismatch on " ^ name

soit is_native = faux
soit adapt_filename f = f
