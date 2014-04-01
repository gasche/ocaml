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

(* The interactive toplevel loop *)

ouvre Path
ouvre Format
ouvre Config
ouvre Misc
ouvre Parsetree
ouvre Types
ouvre Typedtree
ouvre Outcometree
ouvre Ast_helper

type directive_fun =
   | Directive_none de (unit -> unit)
   | Directive_string de (string -> unit)
   | Directive_int de (int -> unit)
   | Directive_ident de (Longident.t -> unit)
   | Directive_bool de (bool -> unit)

(* The table of toplevel value bindings and its accessors *)

soit toplevel_value_bindings =
  (Hashtbl.create 37 : (string, Obj.t) Hashtbl.t)

soit getvalue name =
  essaie
    Hashtbl.find toplevel_value_bindings name
  avec Not_found ->
    fatal_error (name ^ " non lié au niveau supérieur")

soit setvalue name v =
  Hashtbl.replace toplevel_value_bindings name v

(* Return the value referred to by a path *)

soit rec eval_path = fonction
  | Pident id ->
      si Ident.persistent id || Ident.global id alors
        Symtable.get_global_value id
      sinon début
        soit name = Translmod.toplevel_name id dans
        essaie
          Hashtbl.find toplevel_value_bindings name
        avec Not_found ->
          raise (Symtable.Error(Symtable.Undefined_global name))
      fin
  | Pdot(p, s, pos) ->
      Obj.field (eval_path p) pos
  | Papply(p1, p2) ->
      fatal_error "Toploop.eval_path"

soit eval_path env path =
  eval_path (Env.normalize_path (Some Location.none) env path)

(* To print values *)

module EvalPath = struct
  type valu = Obj.t
  exception Error
  soit eval_path env p = essaie eval_path env p avec Symtable.Error _ -> raise Error
  soit same_value v1 v2 = (v1 == v2)
fin

module Printer = Genprintval.Make(Obj)(EvalPath)

soit max_printer_depth = ref 100
soit max_printer_steps = ref 300

soit print_out_value = Oprint.out_value
soit print_out_type = Oprint.out_type
soit print_out_class_type = Oprint.out_class_type
soit print_out_module_type = Oprint.out_module_type
soit print_out_sig_item = Oprint.out_sig_item
soit print_out_signature = Oprint.out_signature
soit print_out_phrase = Oprint.out_phrase

soit print_untyped_exception ppf obj =
  !print_out_value ppf (Printer.outval_of_untyped_exception obj)
soit outval_of_value env obj ty =
  Printer.outval_of_value !max_printer_steps !max_printer_depth
    (fonc _ _ _ -> None) env obj ty
soit print_value env obj ppf ty =
  !print_out_value ppf (outval_of_value env obj ty)

soit install_printer = Printer.install_printer
soit remove_printer = Printer.remove_printer

(* Hooks for parsing functions *)

soit parse_toplevel_phrase = ref Parse.toplevel_phrase
soit parse_use_file = ref Parse.use_file
soit print_location = Location.print_error (* FIXME change back to print *)
soit print_error = Location.print_error
soit print_warning = Location.print_warning
soit input_name = Location.input_name

soit parse_mod_use_file name lb =
  soit modname =
    String.capitalize (Filename.chop_extension (Filename.basename name))
  dans
  soit items =
    List.concat
      (List.map
         (fonction Ptop_def s -> s | Ptop_dir _ -> [])
         (!parse_use_file lb))
  dans
  [ Ptop_def
      [ Str.module_
          (Mb.mk
             (Location.mknoloc modname)
             (Mod.structure items)
          )
       ]
   ]

(* Hooks for initialization *)

soit toplevel_startup_hook = ref (fonc () -> ())

(* Load in-core and execute a lambda term *)

soit may_trace = ref faux (* Global lock on tracing *)
type evaluation_outcome = Result de Obj.t | Exception de exn

soit load_lambda ppf lam =
  si !Clflags.dump_rawlambda alors fprintf ppf "%a@." Printlambda.lambda lam;
  soit slam = Simplif.simplify_lambda lam dans
  si !Clflags.dump_lambda alors fprintf ppf "%a@." Printlambda.lambda slam;
  soit (init_code, fun_code) = Bytegen.compile_phrase slam dans
  si !Clflags.dump_instr alors
    fprintf ppf "%a%a@."
    Printinstr.instrlist init_code
    Printinstr.instrlist fun_code;
  soit (code, code_size, reloc) = Emitcode.to_memory init_code fun_code dans
  soit can_free = (fun_code = []) dans
  soit initial_symtable = Symtable.current_state() dans
  Symtable.patch_object code reloc;
  Symtable.check_global_initialized reloc;
  Symtable.update_global_table();
  essaie
    may_trace := vrai;
    soit retval = (Meta.reify_bytecode code code_size) () dans
    may_trace := faux;
    si can_free alors début
      Meta.static_release_bytecode code code_size;
      Meta.static_free code;
    fin;
    Result retval
  avec x ->
    may_trace := faux;
    si can_free alors début
      Meta.static_release_bytecode code code_size;
      Meta.static_free code;
    fin;
    Symtable.restore_state initial_symtable;
    Exception x

(* Print the outcome of an evaluation *)

soit rec pr_item env items =
  Printtyp.hide_rec_items items;
  filtre items avec
  | Sig_value(id, decl) :: rem ->
      soit tree = Printtyp.tree_of_value_description id decl dans
      soit valopt =
        filtre decl.val_kind avec
        | Val_prim _ -> None
        | _ ->
            soit v =
              outval_of_value env (getvalue (Translmod.toplevel_name id))
                decl.val_type
            dans
            Some v
      dans
      Some (tree, valopt, rem)
  | Sig_type(id, _, _) :: rem quand Btype.is_row_name (Ident.name id) ->
      pr_item env rem
  | Sig_type(id, decl, rs) :: rem ->
      soit tree = Printtyp.tree_of_type_declaration id decl rs dans
      Some (tree, None, rem)
  | Sig_exception(id, decl) :: rem ->
      soit tree = Printtyp.tree_of_exception_declaration id decl dans
      Some (tree, None, rem)
  | Sig_module(id, md, rs) :: rem ->
      soit tree = Printtyp.tree_of_module id md.md_type rs dans
      Some (tree, None, rem)
  | Sig_modtype(id, decl) :: rem ->
      soit tree = Printtyp.tree_of_modtype_declaration id decl dans
      Some (tree, None, rem)
  | Sig_class(id, decl, rs) :: cltydecl :: tydecl1 :: tydecl2 :: rem ->
      soit tree = Printtyp.tree_of_class_declaration id decl rs dans
      Some (tree, None, rem)
  | Sig_class_type(id, decl, rs) :: tydecl1 :: tydecl2 :: rem ->
      soit tree = Printtyp.tree_of_cltype_declaration id decl rs dans
      Some (tree, None, rem)
  | _ -> None

soit rec item_list env = fonction
  | [] -> []
  | items ->
     filtre pr_item env items avec
     | None -> []
     | Some (tree, valopt, items) -> (tree, valopt) :: item_list env items

(* The current typing environment for the toplevel *)

soit toplevel_env = ref Env.empty

(* Print an exception produced by an evaluation *)

soit print_out_exception ppf exn outv =
  !print_out_phrase ppf (Ophr_exception (exn, outv))

soit print_exception_outcome ppf exn =
  si exn = Out_of_memory alors Gc.full_major ();
  soit outv = outval_of_value !toplevel_env (Obj.repr exn) Predef.type_exn dans
  print_out_exception ppf exn outv

(* The table of toplevel directives.
   Filled by functions from module topdirs. *)

soit directive_table = (Hashtbl.create 13 : (string, directive_fun) Hashtbl.t)

(* Execute a toplevel phrase *)

soit execute_phrase print_outcome ppf phr =
  filtre phr avec
  | Ptop_def sstr ->
      soit oldenv = !toplevel_env dans
      Typecore.reset_delayed_checks ();
      soit (str, sg, newenv) = Typemod.type_toplevel_phrase oldenv sstr dans
      si !Clflags.dump_typedtree alors Printtyped.implementation ppf str;
      soit sg' = Typemod.simplify_signature sg dans
      ignore (Includemod.signatures oldenv sg sg');
      Typecore.force_delayed_checks ();
      soit lam = Translmod.transl_toplevel_definition str dans
      Warnings.check_fatal ();
      début essaie
        toplevel_env := newenv;
        soit res = load_lambda ppf lam dans
        soit out_phr =
          filtre res avec
          | Result v ->
              si print_outcome alors
                Printtyp.wrap_printing_env oldenv (fonc () ->
                  filtre str.str_items avec
                  | [ { str_desc = Tstr_eval (exp, _attrs) }] ->
                      soit outv = outval_of_value newenv v exp.exp_type dans
                      soit ty = Printtyp.tree_of_type_scheme exp.exp_type dans
                      Ophr_eval (outv, ty)
                  | [] -> Ophr_signature []
                  | _ -> Ophr_signature (item_list newenv sg'))
              sinon Ophr_signature []
          | Exception exn ->
              toplevel_env := oldenv;
              si exn = Out_of_memory alors Gc.full_major();
              soit outv =
                outval_of_value !toplevel_env (Obj.repr exn) Predef.type_exn
              dans
              Ophr_exception (exn, outv)
        dans
        !print_out_phrase ppf out_phr;
        début filtre out_phr avec
        | Ophr_eval (_, _) | Ophr_signature _ -> vrai
        | Ophr_exception _ -> faux
        fin
      avec x ->
        toplevel_env := oldenv; raise x
      fin
  | Ptop_dir(dir_name, dir_arg) ->
      essaie
        filtre (Hashtbl.find directive_table dir_name, dir_arg) avec
        | (Directive_none f, Pdir_none) -> f (); vrai
        | (Directive_string f, Pdir_string s) -> f s; vrai
        | (Directive_int f, Pdir_int n) -> f n; vrai
        | (Directive_ident f, Pdir_ident lid) -> f lid; vrai
        | (Directive_bool f, Pdir_bool b) -> f b; vrai
        | (_, _) ->
            fprintf ppf "Wrong type of argument for directive `%s'.@." dir_name;
            faux
      avec Not_found ->
        fprintf ppf "Unknown directive `%s'.@." dir_name;
        faux

(* Temporary assignment to a reference *)

soit protect r newval body =
  soit oldval = !r dans
  essaie
    r := newval;
    soit res = body() dans
    r := oldval;
    res
  avec x ->
    r := oldval;
    raise x

(* Read and execute commands from a file, or from stdin if [name] is "". *)

soit use_print_results = ref vrai

soit phrase ppf phr =
  soit phr =
    filtre phr avec
    | Ptop_def str ->
        Ptop_def (Pparse.apply_rewriters ast_impl_magic_number str)
    | phr -> phr
  dans
  si !Clflags.dump_parsetree alors Printast.top_phrase ppf phr;
  si !Clflags.dump_source alors Pprintast.top_phrase ppf phr;
  phr

soit use_file ppf wrap_mod name =
  essaie
    soit (filename, ic, must_close) =
      si name = "" alors
        ("(stdin)", stdin, faux)
      sinon début
        soit filename = find_in_path !Config.load_path name dans
        soit ic = open_in_bin filename dans
        (filename, ic, vrai)
      fin
    dans
    soit lb = Lexing.from_channel ic dans
    Location.init lb filename;
    (* Skip initial #! line if any *)
    Lexer.skip_sharp_bang lb;
    soit success =
      protect Location.input_name filename (fonc () ->
        essaie
          List.iter
            (fonc ph ->
              soit ph = phrase ppf ph dans
              si not (execute_phrase !use_print_results ppf ph) alors raise Exit)
            (si wrap_mod alors
               parse_mod_use_file name lb
             sinon
               !parse_use_file lb);
          vrai
        avec
        | Exit -> faux
        | Sys.Break -> fprintf ppf "Interrupted.@."; faux
        | x -> Location.report_exception ppf x; faux) dans
    si must_close alors close_in ic;
    success
  avec Not_found -> fprintf ppf "Cannot find file %s.@." name; faux

soit mod_use_file ppf name = use_file ppf vrai name
soit use_file ppf name = use_file ppf faux name

soit use_silently ppf name =
  protect use_print_results faux (fonc () -> use_file ppf name)

(* Reading function for interactive use *)

soit first_line = ref vrai
soit got_eof = ref faux;;

soit read_input_default prompt buffer len =
  output_string Pervasives.stdout prompt; flush Pervasives.stdout;
  soit i = ref 0 dans
  essaie
    pendant_que vrai faire
      si !i >= len alors raise Exit;
      soit c = input_char Pervasives.stdin dans
      buffer.[!i] <- c;
      incr i;
      si c = '\n' alors raise Exit;
    fait;
    (!i, faux)
  avec
  | End_of_file ->
      (!i, vrai)
  | Exit ->
      (!i, faux)

soit read_interactive_input = ref read_input_default

soit refill_lexbuf buffer len =
  si !got_eof alors (got_eof := faux; 0) sinon début
    soit prompt =
      si !Clflags.noprompt alors ""
      sinon si !first_line alors "# "
      sinon si !Clflags.nopromptcont alors ""
      sinon si Lexer.in_comment () alors "* "
      sinon "  "
    dans
    first_line := faux;
    soit (len, eof) = !read_interactive_input prompt buffer len dans
    si eof alors début
      Location.echo_eof ();
      si len > 0 alors got_eof := vrai;
      len
    fin sinon
      len
  fin

(* Toplevel initialization. Performed here instead of at the
   beginning of loop() so that user code linked in with ocamlmktop
   can call directives from Topdirs. *)

soit _ =
  Sys.interactive := vrai;
  soit crc_intfs = Symtable.init_toplevel() dans
  Compmisc.init_path faux;
  List.iter
    (fonc (name, crc) ->
      Consistbl.set Env.crc_units name crc Sys.executable_name)
    crc_intfs

soit load_ocamlinit ppf =
  si !Clflags.noinit alors ()
  sinon filtre !Clflags.init_file avec
  | Some f -> si Sys.file_exists f alors ignore (use_silently ppf f)
              sinon fprintf ppf "Init file not found: \"%s\".@." f
  | None ->
     si Sys.file_exists ".ocamlinit" alors ignore (use_silently ppf ".ocamlinit")
     sinon essaie
       soit home_init = Filename.concat (Sys.getenv "HOME") ".ocamlinit" dans
       si Sys.file_exists home_init alors ignore (use_silently ppf home_init)
     avec Not_found -> ()
;;

soit set_paths () =
  (* Add whatever -I options have been specified on the command line,
     but keep the directories that user code linked in with ocamlmktop
     may have added to load_path. *)
  load_path := !load_path @ [Filename.concat Config.standard_library "camlp4"];
  load_path := "" :: (List.rev !Clflags.include_dirs @ !load_path);
  Dll.add_path !load_path

soit initialize_toplevel_env () =
  toplevel_env := Compmisc.initial_env()

(* The interactive loop *)

exception PPerror

soit loop ppf =
  fprintf ppf "        OCaml version %s@.@." Config.version;
  initialize_toplevel_env ();
  soit lb = Lexing.from_function refill_lexbuf dans
  Location.init lb "//toplevel//";
  Location.input_name := "//toplevel//";
  Location.input_lexbuf := Some lb;
  Sys.catch_break vrai;
  load_ocamlinit ppf;
  pendant_que vrai faire
    soit snap = Btype.snapshot () dans
    essaie
      Lexing.flush_input lb;
      Location.reset();
      first_line := vrai;
      soit phr = essaie !parse_toplevel_phrase lb avec Exit -> raise PPerror dans
      soit phr = phrase ppf phr  dans
      Env.reset_cache_toplevel ();
      ignore(execute_phrase vrai ppf phr)
    avec
    | End_of_file -> exit 0
    | Sys.Break -> fprintf ppf "Interrupted.@."; Btype.backtrack snap
    | PPerror -> ()
    | x -> Location.report_exception ppf x; Btype.backtrack snap
  fait

(* Execute a script.  If [name] is "", read the script from stdin. *)

soit run_script ppf name args =
  soit len = Array.length args dans
  si Array.length Sys.argv < len alors invalid_arg "Toploop.run_script";
  Array.blit args 0 Sys.argv 0 len;
  Obj.truncate (Obj.repr Sys.argv) len;
  Arg.current := 0;
  Compmisc.init_path faux;
  toplevel_env := Compmisc.initial_env();
  Sys.interactive := faux;
  use_silently ppf name
