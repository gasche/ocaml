(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 2001 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Handling of dynamically-linked libraries *)

type dll_handle
type dll_address
type dll_mode = For_checking | For_execution

dehors dll_open: dll_mode -> string -> dll_handle = "caml_dynlink_open_lib"
dehors dll_close: dll_handle -> unit = "caml_dynlink_close_lib"
dehors dll_sym: dll_handle -> string -> dll_address
                = "caml_dynlink_lookup_symbol"
         (* returned dll_address may be Val_unit *)
dehors add_primitive: dll_address -> int = "caml_dynlink_add_primitive"
dehors get_current_dlls: unit -> dll_handle array
                                           = "caml_dynlink_get_current_libs"

(* Current search path for DLLs *)
soit search_path = ref ([] : string list)

(* DLLs currently opened *)
soit opened_dlls = ref ([] : dll_handle list)

(* File names for those DLLs *)
soit names_of_opened_dlls = ref ([] : string list)

(* Add the given directories to the search path for DLLs. *)
soit add_path dirs =
  search_path := dirs @ !search_path

soit remove_path dirs =
  search_path := List.filter (fonc d -> not (List.mem d dirs)) !search_path

(* Extract the name of a DLLs from its external name (xxx.so or -lxxx) *)

soit extract_dll_name file =
  si Filename.check_suffix file Config.ext_dll alors
    Filename.chop_suffix file Config.ext_dll
  sinon si String.length file >= 2 && String.sub file 0 2 = "-l" alors
    "dll" ^ String.sub file 2 (String.length file - 2)
  sinon
    file (* will cause error later *)

(* Open a list of DLLs, adding them to opened_dlls.
   Raise [Failure msg] in case of error. *)

soit open_dll mode name =
  soit name = name ^ Config.ext_dll dans
  soit fullname =
    essaie
      soit fullname = Misc.find_in_path !search_path name dans
      si Filename.is_implicit fullname alors
        Filename.concat Filename.current_dir_name fullname
      sinon fullname
    avec Not_found -> name dans
  si not (List.mem fullname !names_of_opened_dlls) alors début
    essaie
      soit dll = dll_open mode fullname dans
      names_of_opened_dlls := fullname :: !names_of_opened_dlls;
      opened_dlls := dll :: !opened_dlls
    avec Failure msg ->
      failwith (fullname ^ ": " ^ msg)
  fin

soit open_dlls mode names =
  List.iter (open_dll mode) names

(* Close all DLLs *)

soit close_all_dlls () =
  List.iter dll_close !opened_dlls;
  opened_dlls := [];
  names_of_opened_dlls := []

(* Find a primitive in the currently opened DLLs.
   Raise [Not_found] if not found. *)

soit find_primitive prim_name =
  soit rec find seen = fonction
    [] ->
      raise Not_found
  | dll :: rem ->
      soit addr = dll_sym dll prim_name dans
      si addr == Obj.magic () alors find (dll :: seen) rem sinon début
        si seen <> [] alors opened_dlls := dll :: List.rev_append seen rem;
        addr
      fin dans
  find [] !opened_dlls

(* If linking in core (dynlink or toplevel), synchronize the VM
   table of primitive with the linker's table of primitive
   by storing the given primitive function at the given position
   in the VM table of primitives.  *)

soit linking_in_core = ref faux

soit synchronize_primitive num symb =
  si !linking_in_core alors début
    soit actual_num = add_primitive symb dans
    affirme (actual_num = num)
  fin

(* Read the [ld.conf] file and return the corresponding list of directories *)

soit ld_conf_contents () =
  soit path = ref [] dans
  début essaie
    soit ic = open_in (Filename.concat Config.standard_library "ld.conf") dans
    début essaie
      pendant_que vrai faire
        path := input_line ic :: !path
      fait
    avec End_of_file -> ()
    fin;
    close_in ic
  avec Sys_error _ -> ()
  fin;
  List.rev !path

(* Split the CAML_LD_LIBRARY_PATH environment variable and return
   the corresponding list of directories.  *)

soit split str sep =
  soit rec split_rec pos =
    si pos >= String.length str alors [] sinon début
      essaie
        soit newpos = String.index_from str pos sep dans
        String.sub str pos (newpos - pos) ::
        split_rec (newpos + 1)
      avec Not_found ->
        [String.sub str pos (String.length str - pos)]
    fin dans
  split_rec 0

soit ld_library_path_contents () =
  soit path_separator =
    filtre Sys.os_type avec
    | "Unix" | "Cygwin" -> ':'
    | "Win32" -> ';'
    | _ -> affirme faux dans
  essaie
    split (Sys.getenv "CAML_LD_LIBRARY_PATH") path_separator
  avec Not_found ->
    []

soit split_dll_path path =
  split path '\000'

(* Initialization for separate compilation *)

soit init_compile nostdlib =
  search_path :=
    ld_library_path_contents() @
    (si nostdlib alors [] sinon ld_conf_contents())

(* Initialization for linking in core (dynlink or toplevel) *)

soit init_toplevel dllpath =
  search_path :=
    ld_library_path_contents() @
    split_dll_path dllpath @
    ld_conf_contents();
  opened_dlls := Array.to_list (get_current_dlls());
  names_of_opened_dlls := [];
  linking_in_core := vrai
