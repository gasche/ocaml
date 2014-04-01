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

(* Toplevel directives *)

ouvre Format
ouvre Misc
ouvre Longident
ouvre Types
ouvre Cmo_format
ouvre Trace
ouvre Toploop

(* The standard output formatter *)
soit std_out = std_formatter

(* To quit *)

soit dir_quit () = exit 0

soit _ = Hashtbl.add directive_table "quit" (Directive_none dir_quit)

(* To add a directory to the load path *)

soit dir_directory s =
  soit d = expand_directory Config.standard_library s dans
  Config.load_path := d :: !Config.load_path;
  Dll.add_path [d]

soit _ = Hashtbl.add directive_table "directory" (Directive_string dir_directory)

(* To remove a directory from the load path *)
soit dir_remove_directory s =
  soit d = expand_directory Config.standard_library s dans
  Config.load_path := List.filter (fonc d' -> d' <> d) !Config.load_path;
  Dll.remove_path [d]

soit _ =
  Hashtbl.add directive_table "remove_directory"
    (Directive_string dir_remove_directory)

(* To change the current directory *)

soit dir_cd s = Sys.chdir s

soit _ = Hashtbl.add directive_table "cd" (Directive_string dir_cd)

(* Load in-core a .cmo file *)

exception Load_failed

soit check_consistency ppf filename cu =
  essaie
    List.iter
      (fonc (name, crc) -> Consistbl.check Env.crc_units name crc filename)
      cu.cu_imports
  avec Consistbl.Inconsistency(name, user, auth) ->
    fprintf ppf "@[<hv 0>The files %s@ and %s@ \
                 disagree over interface %s@]@."
            user auth name;
    raise Load_failed

soit load_compunit ic filename ppf compunit =
  check_consistency ppf filename compunit;
  seek_in ic compunit.cu_pos;
  soit code_size = compunit.cu_codesize + 8 dans
  soit code = Meta.static_alloc code_size dans
  unsafe_really_input ic code 0 compunit.cu_codesize;
  String.unsafe_set code compunit.cu_codesize (Char.chr Opcodes.opRETURN);
  String.unsafe_blit "\000\000\000\001\000\000\000" 0
                     code (compunit.cu_codesize + 1) 7;
  soit initial_symtable = Symtable.current_state() dans
  Symtable.patch_object code compunit.cu_reloc;
  Symtable.update_global_table();
  début essaie
    may_trace := vrai;
    ignore((Meta.reify_bytecode code code_size) ());
    may_trace := faux;
  avec exn ->
    may_trace := faux;
    Symtable.restore_state initial_symtable;
    print_exception_outcome ppf exn;
    raise Load_failed
  fin

soit rec load_file recursive ppf name =
  soit filename =
    essaie Some (find_in_path !Config.load_path name) avec Not_found -> None
  dans
  filtre filename avec
  | None -> fprintf ppf "Cannot find file %s.@." name; faux
  | Some filename ->
      soit ic = open_in_bin filename dans
      essaie
        soit success = really_load_file recursive ppf name filename ic dans
        close_in ic;
        success
      avec exn ->
        close_in ic;
        raise exn

et really_load_file recursive ppf name filename ic =
  soit ic = open_in_bin filename dans
  soit buffer = Misc.input_bytes ic (String.length Config.cmo_magic_number) dans
  essaie
    si buffer = Config.cmo_magic_number alors début
      soit compunit_pos = input_binary_int ic dans  (* Go to descriptor *)
      seek_in ic compunit_pos;
      soit cu : compilation_unit = input_value ic dans
      si recursive alors
        List.iter
          (fonction
            | (Reloc_getglobal id, _)
              quand not (Symtable.is_global_defined id) ->
                soit file = Ident.name id ^ ".cmo" dans
                début filtre essaie Some (Misc.find_in_path_uncap !Config.load_path
                                        file)
                      avec Not_found -> None
                avec
                | None -> ()
                | Some file ->
                    si not (load_file recursive ppf file) alors raise Load_failed
                fin
            | _ -> ()
          )
          cu.cu_reloc;
      load_compunit ic filename ppf cu;
      vrai
    fin sinon
      si buffer = Config.cma_magic_number alors début
        soit toc_pos = input_binary_int ic dans  (* Go to table of contents *)
        seek_in ic toc_pos;
        soit lib = (input_value ic : library) dans
        List.iter
          (fonc dllib ->
            soit name = Dll.extract_dll_name dllib dans
            essaie Dll.open_dlls Dll.For_execution [name]
            avec Failure reason ->
              fprintf ppf
                "Cannot load required shared library %s.@.Reason: %s.@."
                name reason;
              raise Load_failed)
          lib.lib_dllibs;
        List.iter (load_compunit ic filename ppf) lib.lib_units;
        vrai
      fin sinon début
        fprintf ppf "File %s is not a bytecode object file.@." name;
        faux
      fin
  avec Load_failed -> faux

soit dir_load ppf name = ignore (load_file faux ppf name)

soit _ = Hashtbl.add directive_table "load" (Directive_string (dir_load std_out))

soit dir_load_rec ppf name = ignore (load_file vrai ppf name)

soit _ = Hashtbl.add directive_table "load_rec"
                    (Directive_string (dir_load_rec std_out))

soit load_file = load_file faux

(* Load commands from a file *)

soit dir_use ppf name = ignore(Toploop.use_file ppf name)
soit dir_mod_use ppf name = ignore(Toploop.mod_use_file ppf name)

soit _ = Hashtbl.add directive_table "use" (Directive_string (dir_use std_out))
soit _ = Hashtbl.add directive_table "mod_use"
                    (Directive_string (dir_mod_use std_out))

(* Install, remove a printer *)

type 'a printer_type_new = Format.formatter -> 'a -> unit
type 'a printer_type_old = 'a -> unit

soit match_printer_type ppf desc typename =
  soit (printer_type, _) =
    essaie
      Env.lookup_type (Ldot(Lident "Topdirs", typename)) !toplevel_env
    avec Not_found ->
      fprintf ppf "Cannot find type Topdirs.%s.@." typename;
      raise Exit dans
  Ctype.init_def(Ident.current_time());
  Ctype.begin_def();
  soit ty_arg = Ctype.newvar() dans
  Ctype.unify !toplevel_env
    (Ctype.newconstr printer_type [ty_arg])
    (Ctype.instance_def desc.val_type);
  Ctype.end_def();
  Ctype.generalize ty_arg;
  ty_arg

soit find_printer_type ppf lid =
  essaie
    soit (path, desc) = Env.lookup_value lid !toplevel_env dans
    soit (ty_arg, is_old_style) =
      essaie
        (match_printer_type ppf desc "printer_type_new", faux)
      avec Ctype.Unify _ ->
        (match_printer_type ppf desc "printer_type_old", vrai) dans
    (ty_arg, path, is_old_style)
  avec
  | Not_found ->
      fprintf ppf "Unbound value %a.@." Printtyp.longident lid;
      raise Exit
  | Ctype.Unify _ ->
      fprintf ppf "%a has a wrong type for a printing function.@."
      Printtyp.longident lid;
      raise Exit

soit dir_install_printer ppf lid =
  essaie
    soit (ty_arg, path, is_old_style) = find_printer_type ppf lid dans
    soit v = eval_path !toplevel_env path dans
    soit print_function =
      si is_old_style alors
        (fonc formatter repr -> Obj.obj v (Obj.obj repr))
      sinon
        (fonc formatter repr -> Obj.obj v formatter (Obj.obj repr)) dans
    install_printer path ty_arg print_function
  avec Exit -> ()

soit dir_remove_printer ppf lid =
  essaie
    soit (ty_arg, path, is_old_style) = find_printer_type ppf lid dans
    début essaie
      remove_printer path
    avec Not_found ->
      fprintf ppf "No printer named %a.@." Printtyp.longident lid
    fin
  avec Exit -> ()

soit _ = Hashtbl.add directive_table "install_printer"
             (Directive_ident (dir_install_printer std_out))
soit _ = Hashtbl.add directive_table "remove_printer"
             (Directive_ident (dir_remove_printer std_out))

(* The trace *)

dehors current_environment: unit -> Obj.t = "caml_get_current_environment"

soit tracing_function_ptr =
  get_code_pointer
    (Obj.repr (fonc arg -> Trace.print_trace (current_environment()) arg))

soit dir_trace ppf lid =
  essaie
    soit (path, desc) = Env.lookup_value lid !toplevel_env dans
    (* Check if this is a primitive *)
    filtre desc.val_kind avec
    | Val_prim p ->
        fprintf ppf "%a is an external function and cannot be traced.@."
        Printtyp.longident lid
    | _ ->
        soit clos = eval_path !toplevel_env path dans
        (* Nothing to do if it's not a closure *)
        si Obj.is_block clos
        && (Obj.tag clos = Obj.closure_tag || Obj.tag clos = Obj.infix_tag)
        alors début
        filtre is_traced clos avec
        | Some opath ->
            fprintf ppf "%a is already traced (under the name %a).@."
            Printtyp.path path
            Printtyp.path opath
        | None ->
            (* Instrument the old closure *)
            traced_functions :=
              { path = path;
                closure = clos;
                actual_code = get_code_pointer clos;
                instrumented_fun =
                  instrument_closure !toplevel_env lid ppf desc.val_type }
              :: !traced_functions;
            (* Redirect the code field of the closure to point
               to the instrumentation function *)
            set_code_pointer clos tracing_function_ptr;
            fprintf ppf "%a is now traced.@." Printtyp.longident lid
        fin sinon fprintf ppf "%a is not a function.@." Printtyp.longident lid
  avec
  | Not_found -> fprintf ppf "Unbound value %a.@." Printtyp.longident lid

soit dir_untrace ppf lid =
  essaie
    soit (path, desc) = Env.lookup_value lid !toplevel_env dans
    soit rec remove = fonction
    | [] ->
        fprintf ppf "%a was not traced.@." Printtyp.longident lid;
        []
    | f :: rem ->
        si Path.same f.path path alors début
          set_code_pointer f.closure f.actual_code;
          fprintf ppf "%a is no longer traced.@." Printtyp.longident lid;
          rem
        fin sinon f :: remove rem dans
    traced_functions := remove !traced_functions
  avec
  | Not_found -> fprintf ppf "Unbound value %a.@." Printtyp.longident lid

soit dir_untrace_all ppf () =
  List.iter
    (fonc f ->
      set_code_pointer f.closure f.actual_code;
      fprintf ppf "%a is no longer traced.@." Printtyp.path f.path)
    !traced_functions;
  traced_functions := []

soit parse_warnings ppf iserr s =
  essaie Warnings.parse_options iserr s
  avec Arg.Bad err -> fprintf ppf "%s.@." err

soit _ =
  Hashtbl.add directive_table "trace" (Directive_ident (dir_trace std_out));
  Hashtbl.add directive_table "untrace" (Directive_ident (dir_untrace std_out));
  Hashtbl.add directive_table
    "untrace_all" (Directive_none (dir_untrace_all std_out));

(* Control the printing of values *)

  Hashtbl.add directive_table "print_depth"
             (Directive_int(fonc n -> max_printer_depth := n));
  Hashtbl.add directive_table "print_length"
             (Directive_int(fonc n -> max_printer_steps := n));

(* Set various compiler flags *)

  Hashtbl.add directive_table "labels"
             (Directive_bool(fonc b -> Clflags.classic := not b));

  Hashtbl.add directive_table "principal"
             (Directive_bool(fonc b -> Clflags.principal := b));

  Hashtbl.add directive_table "rectypes"
             (Directive_none(fonc () -> Clflags.recursive_types := vrai));

  Hashtbl.add directive_table "warnings"
             (Directive_string (parse_warnings std_out faux));

  Hashtbl.add directive_table "warn_error"
             (Directive_string (parse_warnings std_out vrai))
