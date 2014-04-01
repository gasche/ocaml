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

(* To assign numbers to globals and primitives *)

ouvre Misc
ouvre Asttypes
ouvre Lambda
ouvre Cmo_format

(* Functions for batch linking *)

type error =
    Undefined_global de string
  | Unavailable_primitive de string
  | Wrong_vm de string
  | Uninitialized_global de string

exception Error de error

(* Tables for numbering objects *)

type 'a numtable =
  { num_cnt: int;               (* The next number *)
    num_tbl: ('a, int) Tbl.t }  (* The table of already numbered objects *)

soit empty_numtable = { num_cnt = 0; num_tbl = Tbl.empty }

soit find_numtable nt key =
  Tbl.find key nt.num_tbl

soit enter_numtable nt key =
  soit n = !nt.num_cnt dans
  nt := { num_cnt = n + 1; num_tbl = Tbl.add key n !nt.num_tbl };
  n

soit incr_numtable nt =
  soit n = !nt.num_cnt dans
  nt := { num_cnt = n + 1; num_tbl = !nt.num_tbl };
  n

(* Global variables *)

soit global_table = ref(empty_numtable : Ident.t numtable)
et literal_table = ref([] : (int * structured_constant) list)

soit is_global_defined id =
  Tbl.mem id (!global_table).num_tbl

soit slot_for_getglobal id =
  essaie
    find_numtable !global_table id
  avec Not_found ->
    raise(Error(Undefined_global(Ident.name id)))

soit slot_for_setglobal id =
  enter_numtable global_table id

soit slot_for_literal cst =
  soit n = incr_numtable global_table dans
  literal_table := (n, cst) :: !literal_table;
  n

(* The C primitives *)

soit c_prim_table = ref(empty_numtable : string numtable)

soit set_prim_table name =
  ignore(enter_numtable c_prim_table name)

soit num_of_prim name =
  essaie
    find_numtable !c_prim_table name
  avec Not_found ->
    si !Clflags.custom_runtime alors
      enter_numtable c_prim_table name
    sinon début
      soit symb =
        essaie Dll.find_primitive name
        avec Not_found -> raise(Error(Unavailable_primitive name)) dans
      soit num = enter_numtable c_prim_table name dans
      Dll.synchronize_primitive num symb;
      num
    fin

soit require_primitive name =
  si name.[0] <> '%' alors ignore(num_of_prim name)

soit all_primitives () =
  soit prim = Array.create !c_prim_table.num_cnt "" dans
  Tbl.iter (fonc name number -> prim.(number) <- name) !c_prim_table.num_tbl;
  prim

soit data_primitive_names () =
  soit prim = all_primitives() dans
  soit b = Buffer.create 512 dans
  pour i = 0 à Array.length prim - 1 faire
    Buffer.add_string b prim.(i); Buffer.add_char b '\000'
  fait;
  Buffer.contents b

soit output_primitive_names outchan =
  output_string outchan (data_primitive_names())

ouvre Printf

soit output_primitive_table outchan =
  soit prim = all_primitives() dans
  pour i = 0 à Array.length prim - 1 faire
    fprintf outchan "extern value %s();\n" prim.(i)
  fait;
  fprintf outchan "typedef value (*primitive)();\n";
  fprintf outchan "primitive caml_builtin_cprim[] = {\n";
  pour i = 0 à Array.length prim - 1 faire
    fprintf outchan "  %s,\n" prim.(i)
  fait;
  fprintf outchan "  (primitive) 0 };\n";
  fprintf outchan "const char * caml_names_of_builtin_cprim[] = {\n";
  pour i = 0 à Array.length prim - 1 faire
    fprintf outchan "  \"%s\",\n" prim.(i)
  fait;
  fprintf outchan "  (char *) 0 };\n"

(* Initialization for batch linking *)

soit init () =
  (* Enter the predefined exceptions *)
  Array.iteri
    (fonc i name ->
      soit id =
        essaie List.assoc name Predef.builtin_values
        avec Not_found -> fatal_error "Symtable.init" dans
      soit c = slot_for_setglobal id dans
      soit cst = Const_block(Obj.object_tag,
                            [Const_base(Const_string (name, None));
                             Const_base(Const_int (-i-1))
                            ])
      dans
      literal_table := (c, cst) :: !literal_table)
    Runtimedef.builtin_exceptions;
  (* Initialize the known C primitives *)
  si String.length !Clflags.use_prims > 0 alors début
      soit ic = open_in !Clflags.use_prims dans
      essaie
        pendant_que vrai faire
          set_prim_table (input_line ic)
        fait
      avec End_of_file -> close_in ic
         | x -> close_in ic; raise x
  fin sinon si String.length !Clflags.use_runtime > 0 alors début
    soit primfile = Filename.temp_file "camlprims" "" dans
    essaie
      si Sys.command(Printf.sprintf "%s -p > %s"
                                    !Clflags.use_runtime primfile) <> 0
      alors raise(Error(Wrong_vm !Clflags.use_runtime));
      soit ic = open_in primfile dans
      essaie
        pendant_que vrai faire
          set_prim_table (input_line ic)
        fait
      avec End_of_file -> close_in ic; remove_file primfile
         | x -> close_in ic; raise x
    avec x -> remove_file primfile; raise x
  fin sinon début
    Array.iter set_prim_table Runtimedef.builtin_primitives
  fin

(* Relocate a block of object bytecode *)

(* Must use the unsafe String.set here because the block may be
   a "fake" string as returned by Meta.static_alloc. *)

soit gen_patch_int str_set buff pos n =
  str_set buff pos (Char.unsafe_chr n);
  str_set buff (pos + 1) (Char.unsafe_chr (n dda 8));
  str_set buff (pos + 2) (Char.unsafe_chr (n dda 16));
  str_set buff (pos + 3) (Char.unsafe_chr (n dda 24))

soit gen_patch_object str_set buff patchlist =
  List.iter
    (fonction
        (Reloc_literal sc, pos) ->
          gen_patch_int str_set buff pos (slot_for_literal sc)
      | (Reloc_getglobal id, pos) ->
          gen_patch_int str_set buff pos (slot_for_getglobal id)
      | (Reloc_setglobal id, pos) ->
          gen_patch_int str_set buff pos (slot_for_setglobal id)
      | (Reloc_primitive name, pos) ->
          gen_patch_int str_set buff pos (num_of_prim name))
    patchlist

soit patch_object = gen_patch_object String.unsafe_set
soit ls_patch_object = gen_patch_object LongString.set

(* Translate structured constants *)

soit rec transl_const = fonction
    Const_base(Const_int i) -> Obj.repr i
  | Const_base(Const_char c) -> Obj.repr c
  | Const_base(Const_string (s, _)) -> Obj.repr s
  | Const_base(Const_float f) -> Obj.repr (float_of_string f)
  | Const_base(Const_int32 i) -> Obj.repr i
  | Const_base(Const_int64 i) -> Obj.repr i
  | Const_base(Const_nativeint i) -> Obj.repr i
  | Const_pointer i -> Obj.repr i
  | Const_immstring s -> Obj.repr s
  | Const_block(tag, fields) ->
      soit block = Obj.new_block tag (List.length fields) dans
      soit pos = ref 0 dans
      List.iter
        (fonc c -> Obj.set_field block !pos (transl_const c); incr pos)
        fields;
      block
  | Const_float_array fields ->
      Obj.repr(Array.of_list(List.map (fonc f -> float_of_string f) fields))

(* Build the initial table of globals *)

soit initial_global_table () =
  soit glob = Array.create !global_table.num_cnt (Obj.repr 0) dans
  List.iter
    (fonc (slot, cst) -> glob.(slot) <- transl_const cst)
    !literal_table;
  literal_table := [];
  glob

(* Save the table of globals *)

soit output_global_map oc =
  output_value oc !global_table

soit data_global_map () =
  Obj.repr !global_table

(* Functions for toplevel use *)

(* Update the in-core table of globals *)

soit update_global_table () =
  soit ng = !global_table.num_cnt dans
  si ng > Array.length(Meta.global_data()) alors Meta.realloc_global_data ng;
  soit glob = Meta.global_data() dans
  List.iter
    (fonc (slot, cst) -> glob.(slot) <- transl_const cst)
    !literal_table;
  literal_table := []

(* Recover data for toplevel initialization.  Data can come either from
   executable file (normal case) or from linked-in data (-output-obj). *)

type section_reader = {
  read_string: string -> string;
  read_struct: string -> Obj.t;
  close_reader: unit -> unit
}

soit read_sections () =
  essaie
    soit sections = Meta.get_section_table () dans
    { read_string =
        (fonc name -> (Obj.magic(List.assoc name sections) : string));
      read_struct =
        (fonc name -> List.assoc name sections);
      close_reader =
        (fonc () -> ()) }
  avec Not_found ->
    soit ic = open_in_bin Sys.executable_name dans
    Bytesections.read_toc ic;
    { read_string = Bytesections.read_section_string ic;
      read_struct = Bytesections.read_section_struct ic;
      close_reader = fonc () -> close_in ic }

(* Initialize the linker for toplevel use *)

soit init_toplevel () =
  essaie
    soit sect = read_sections () dans
    (* Locations of globals *)
    global_table := (Obj.magic (sect.read_struct "SYMB") : Ident.t numtable);
    (* Primitives *)
    soit prims = sect.read_string "PRIM" dans
    c_prim_table := empty_numtable;
    soit pos = ref 0 dans
    pendant_que !pos < String.length prims faire
      soit i = String.index_from prims !pos '\000' dans
      set_prim_table (String.sub prims !pos (i - !pos));
      pos := i + 1
    fait;
    (* DLL initialization *)
    soit dllpath = essaie sect.read_string "DLPT" avec Not_found -> "" dans
    Dll.init_toplevel dllpath;
    (* Recover CRC infos for interfaces *)
    soit crcintfs =
      essaie (Obj.magic (sect.read_struct "CRCS") : (string * Digest.t) list)
      avec Not_found -> [] dans
    (* Done *)
    sect.close_reader();
    crcintfs
  avec Bytesections.Bad_magic_number | Not_found | Failure _ ->
    fatal_error "L'exécutable bytecode de l'entrée interactive est corrompu"

(* Find the value of a global identifier *)

soit get_global_position id = slot_for_getglobal id

soit get_global_value id =
  (Meta.global_data()).(slot_for_getglobal id)
soit assign_global_value id v =
  (Meta.global_data()).(slot_for_getglobal id) <- v

(* Check that all globals referenced in the given patch list
   have been initialized already *)

soit check_global_initialized patchlist =
  (* First determine the globals we will define *)
  soit defined_globals =
    List.fold_left
      (fonc accu rel ->
        filtre rel avec
          (Reloc_setglobal id, pos) -> id :: accu
        | _ -> accu)
      [] patchlist dans
  (* Then check that all referenced, not defined globals have a value *)
  soit check_reference = fonction
      (Reloc_getglobal id, pos) ->
        si not (List.mem id defined_globals)
        && Obj.is_int (get_global_value id)
        alors raise (Error(Uninitialized_global(Ident.name id)))
    | _ -> () dans
  List.iter check_reference patchlist

(* Save and restore the current state *)

type global_map = Ident.t numtable

soit current_state () = !global_table

soit restore_state st = global_table := st

soit hide_additions st =
  si st.num_cnt > !global_table.num_cnt alors
    fatal_error "Symtable.hide_additions";
  global_table :=
    { num_cnt = !global_table.num_cnt;
      num_tbl = st.num_tbl }

(* "Filter" the global map according to some predicate.
   Used to expunge the global map for the toplevel. *)

soit filter_global_map p gmap =
  soit newtbl = ref Tbl.empty dans
  Tbl.iter
    (fonc id num -> si p id alors newtbl := Tbl.add id num !newtbl)
    gmap.num_tbl;
  {num_cnt = gmap.num_cnt; num_tbl = !newtbl}

(* Error report *)

ouvre Format

soit report_error ppf = fonction
  | Undefined_global s ->
      fprintf ppf "Reference to undefined global `%s'" s
  | Unavailable_primitive s ->
      fprintf ppf "The external function `%s' is not available" s
  | Wrong_vm s ->
      fprintf ppf "Cannot find or execute the runtime system %s" s
  | Uninitialized_global s ->
      fprintf ppf "The value of the global `%s' is not yet computed" s

soit () =
  Location.register_error_of_exn
    (fonction
      | Error err -> Some (Location.error_of_printer_file report_error err)
      | _ -> None
    )
