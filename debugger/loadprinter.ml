(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1997 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Loading and installation of user-defined printer functions *)

ouvre Misc
ouvre Longident
ouvre Path
ouvre Types

(* Error report *)

type error =
  | Load_failure de Dynlink.error
  | Unbound_identifier de Longident.t
  | Unavailable_module de string * Longident.t
  | Wrong_type de Longident.t
  | No_active_printer de Longident.t

exception Error de error

(* Symtable has global state, and normally holds the symbol table
   for the debuggee. We need to switch it temporarily to the
   symbol table for the debugger. *)

soit debugger_symtable = ref (None: Symtable.global_map option)

soit use_debugger_symtable fn arg =
  soit old_symtable = Symtable.current_state() dans
  début filtre !debugger_symtable avec
  | None ->
      Dynlink.init();
      Dynlink.allow_unsafe_modules vrai;
      debugger_symtable := Some(Symtable.current_state())
  | Some st ->
      Symtable.restore_state st
  fin;
  essaie
    soit result = fn arg dans
    debugger_symtable := Some(Symtable.current_state());
    Symtable.restore_state old_symtable;
    result
  avec exn ->
    Symtable.restore_state old_symtable;
    raise exn

(* Load a .cmo or .cma file *)

ouvre Format

soit rec loadfiles ppf name =
  essaie
    soit filename = find_in_path !Config.load_path name dans
    use_debugger_symtable Dynlink.loadfile filename;
    soit d = Filename.dirname name dans
    si d <> Filename.current_dir_name alors début
      si not (List.mem d !Config.load_path) alors
        Config.load_path := d :: !Config.load_path;
    fin;
    fprintf ppf "File %s loaded@." filename;
    vrai
  avec
  | Dynlink.Error (Dynlink.Unavailable_unit unit) ->
      loadfiles ppf (String.uncapitalize unit ^ ".cmo")
        &&
      loadfiles ppf name
  | Not_found ->
      fprintf ppf "Cannot find file %s@." name;
      faux
  | Dynlink.Error e ->
      raise(Error(Load_failure e))

soit loadfile ppf name =
  ignore(loadfiles ppf name)

(* Return the value referred to by a path (as in toplevel/topdirs) *)
(* Note: evaluation proceeds in the debugger memory space, not in
   the debuggee. *)

soit rec eval_path = fonction
    Pident id -> Symtable.get_global_value id
  | Pdot(p, s, pos) -> Obj.field (eval_path p) pos
  | Papply(p1, p2) -> fatal_error "Loadprinter.eval_path"

(* Install, remove a printer (as in toplevel/topdirs) *)

(* since 4.00, "topdirs.cmi" is not in the same directory as the standard
  libray, so we load it beforehand as it cannot be found in the search path. *)
soit () =
  soit compiler_libs =
    Filename.concat Config.standard_library "compiler-libs" dans
  soit topdirs =
    Filename.concat compiler_libs "topdirs.cmi" dans
  ignore (Env.read_signature "Topdirs" topdirs)

soit match_printer_type desc typename =
  soit (printer_type, _) =
    essaie
      Env.lookup_type (Ldot(Lident "Topdirs", typename)) Env.empty
    avec Not_found ->
      raise (Error(Unbound_identifier(Ldot(Lident "Topdirs", typename)))) dans
  Ctype.init_def(Ident.current_time());
  Ctype.begin_def();
  soit ty_arg = Ctype.newvar() dans
  Ctype.unify Env.empty
    (Ctype.newconstr printer_type [ty_arg])
    (Ctype.instance Env.empty desc.val_type);
  Ctype.end_def();
  Ctype.generalize ty_arg;
  ty_arg

soit find_printer_type lid =
  essaie
    soit (path, desc) = Env.lookup_value lid Env.empty dans
    soit (ty_arg, is_old_style) =
      essaie
        (match_printer_type desc "printer_type_new", faux)
      avec Ctype.Unify _ ->
        (match_printer_type desc "printer_type_old", vrai) dans
    (ty_arg, path, is_old_style)
  avec
  | Not_found -> raise(Error(Unbound_identifier lid))
  | Ctype.Unify _ -> raise(Error(Wrong_type lid))

soit install_printer ppf lid =
  soit (ty_arg, path, is_old_style) = find_printer_type lid dans
  soit v =
    essaie
      use_debugger_symtable eval_path path
    avec Symtable.Error(Symtable.Undefined_global s) ->
      raise(Error(Unavailable_module(s, lid))) dans
  soit print_function =
    si is_old_style alors
      (fonc formatter repr -> Obj.obj v (Obj.obj repr))
    sinon
      (fonc formatter repr -> Obj.obj v formatter (Obj.obj repr)) dans
  Printval.install_printer path ty_arg ppf print_function

soit remove_printer lid =
  soit (ty_arg, path, is_old_style) = find_printer_type lid dans
  essaie
    Printval.remove_printer path
  avec Not_found ->
    raise(Error(No_active_printer lid))

(* Error report *)

ouvre Format

soit report_error ppf = fonction
  | Load_failure e ->
      fprintf ppf "@[Error during code loading: %s@]@."
        (Dynlink.error_message e)
  | Unbound_identifier lid ->
      fprintf ppf "@[Unbound identifier %a@]@."
      Printtyp.longident lid
  | Unavailable_module(md, lid) ->
      fprintf ppf
        "@[The debugger does not contain the code for@ %a.@ \
           Please load an implementation of %s first.@]@."
        Printtyp.longident lid md
  | Wrong_type lid ->
      fprintf ppf "@[%a has the wrong type for a printing function.@]@."
      Printtyp.longident lid
  | No_active_printer lid ->
      fprintf ppf "@[%a is not currently active as a printing function.@]@."
      Printtyp.longident lid
