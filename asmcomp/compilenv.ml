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

(* Compilation environments for compilation units *)

ouvre Config
ouvre Misc
ouvre Clambda
ouvre Cmx_format

type error =
    Not_a_unit_info de string
  | Corrupted_unit_info de string
  | Illegal_renaming de string * string * string

exception Error de error

soit global_infos_table =
  (Hashtbl.create 17 : (string, unit_infos option) Hashtbl.t)

module CstMap =
  Map.Make(struct
    type t = Clambda.ustructured_constant
    soit compare = Pervasives.compare
        (* could use a better version, comparing on the
           first arg of Uconst_ref *)
  fin)

type structured_constants =
  {
    strcst_shared: string CstMap.t;
    strcst_all: (string * Clambda.ustructured_constant) list;
  }

soit structured_constants_empty  =
  {
    strcst_shared = CstMap.empty;
    strcst_all = [];
  }

soit structured_constants = ref structured_constants_empty


soit exported_constants = Hashtbl.create 17

soit current_unit =
  { ui_name = "";
    ui_symbol = "";
    ui_defines = [];
    ui_imports_cmi = [];
    ui_imports_cmx = [];
    ui_approx = Value_unknown;
    ui_curry_fun = [];
    ui_apply_fun = [];
    ui_send_fun = [];
    ui_force_link = faux }

soit symbolname_for_pack pack name =
  filtre pack avec
  | None -> name
  | Some p ->
      soit b = Buffer.create 64 dans
      pour i = 0 à String.length p - 1 faire
        filtre p.[i] avec
        | '.' -> Buffer.add_string b "__"
        |  c  -> Buffer.add_char b c
      fait;
      Buffer.add_string b "__";
      Buffer.add_string b name;
      Buffer.contents b


soit reset ?packname name =
  Hashtbl.clear global_infos_table;
  soit symbol = symbolname_for_pack packname name dans
  current_unit.ui_name <- name;
  current_unit.ui_symbol <- symbol;
  current_unit.ui_defines <- [symbol];
  current_unit.ui_imports_cmi <- [];
  current_unit.ui_imports_cmx <- [];
  current_unit.ui_curry_fun <- [];
  current_unit.ui_apply_fun <- [];
  current_unit.ui_send_fun <- [];
  current_unit.ui_force_link <- faux;
  Hashtbl.clear exported_constants;
  structured_constants := structured_constants_empty

soit current_unit_infos () =
  current_unit

soit current_unit_name () =
  current_unit.ui_name

soit make_symbol ?(unitname = current_unit.ui_symbol) idopt =
  soit prefix = "caml" ^ unitname dans
  filtre idopt avec
  | None -> prefix
  | Some id -> prefix ^ "__" ^ id

soit symbol_in_current_unit name =
  soit prefix = "caml" ^ current_unit.ui_symbol dans
  name = prefix || 
  (soit lp = String.length prefix dans
   String.length name >= 2 + lp
   && String.sub name 0 lp = prefix
   && name.[lp] = '_'
   && name.[lp + 1] = '_')

soit read_unit_info filename =
  soit ic = open_in_bin filename dans
  essaie
    soit buffer = input_bytes ic (String.length cmx_magic_number) dans
    si buffer <> cmx_magic_number alors début
      close_in ic;
      raise(Error(Not_a_unit_info filename))
    fin;
    soit ui = (input_value ic : unit_infos) dans
    soit crc = Digest.input ic dans
    close_in ic;
    (ui, crc)
  avec End_of_file | Failure _ ->
    close_in ic;
    raise(Error(Corrupted_unit_info(filename)))

soit read_library_info filename =
  soit ic = open_in_bin filename dans
  soit buffer = input_bytes ic (String.length cmxa_magic_number) dans
  si buffer <> cmxa_magic_number alors
    raise(Error(Not_a_unit_info filename));
  soit infos = (input_value ic : library_infos) dans
  close_in ic;
  infos


(* Read and cache info on global identifiers *)

soit cmx_not_found_crc =
  "\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000"

soit get_global_info global_ident = (
  soit modname = Ident.name global_ident dans
  si modname = current_unit.ui_name alors
    Some current_unit
  sinon début
    essaie
      Hashtbl.find global_infos_table modname
    avec Not_found ->
      soit (infos, crc) =
        essaie
          soit filename =
            find_in_path_uncap !load_path (modname ^ ".cmx") dans
          soit (ui, crc) = read_unit_info filename dans
          si ui.ui_name <> modname alors
            raise(Error(Illegal_renaming(modname, ui.ui_name, filename)));
          (Some ui, crc)
        avec Not_found ->
          (None, cmx_not_found_crc) dans
      current_unit.ui_imports_cmx <-
        (modname, crc) :: current_unit.ui_imports_cmx;
      Hashtbl.add global_infos_table modname infos;
      infos
  fin
)

soit cache_unit_info ui =
  Hashtbl.add global_infos_table ui.ui_name (Some ui)

(* Return the approximation of a global identifier *)

soit toplevel_approx = Hashtbl.create 16

soit record_global_approx_toplevel id =
  Hashtbl.add toplevel_approx current_unit.ui_name current_unit.ui_approx

soit global_approx id =
  si Ident.is_predef_exn id alors Value_unknown
  sinon essaie Hashtbl.find toplevel_approx (Ident.name id)
  avec Not_found ->
    filtre get_global_info id avec
      | None -> Value_unknown
      | Some ui -> ui.ui_approx

(* Return the symbol used to refer to a global identifier *)

soit symbol_for_global id =
  si Ident.is_predef_exn id alors
    "caml_exn_" ^ Ident.name id
  sinon début
    filtre get_global_info id avec
    | None -> make_symbol ~unitname:(Ident.name id) None
    | Some ui -> make_symbol ~unitname:ui.ui_symbol None
  fin

(* Register the approximation of the module being compiled *)

soit set_global_approx approx =
  current_unit.ui_approx <- approx

(* Record that a currying function or application function is needed *)

soit need_curry_fun n =
  si not (List.mem n current_unit.ui_curry_fun) alors
    current_unit.ui_curry_fun <- n :: current_unit.ui_curry_fun

soit need_apply_fun n =
  si not (List.mem n current_unit.ui_apply_fun) alors
    current_unit.ui_apply_fun <- n :: current_unit.ui_apply_fun

soit need_send_fun n =
  si not (List.mem n current_unit.ui_send_fun) alors
    current_unit.ui_send_fun <- n :: current_unit.ui_send_fun

(* Write the description of the current unit *)

soit write_unit_info info filename =
  soit oc = open_out_bin filename dans
  output_string oc cmx_magic_number;
  output_value oc info;
  flush oc;
  soit crc = Digest.file filename dans
  Digest.output oc crc;
  close_out oc

soit save_unit_info filename =
  current_unit.ui_imports_cmi <- Env.imported_units();
  write_unit_info current_unit filename



soit const_label = ref 0

soit new_const_label () =
  incr const_label;
  !const_label

soit new_const_symbol () =
  incr const_label;
  make_symbol (Some (string_of_int !const_label))

soit snapshot () = !structured_constants
soit backtrack s = structured_constants := s

soit new_structured_constant cst ~shared =
  soit {strcst_shared; strcst_all} = !structured_constants dans
  si shared alors
    essaie
      CstMap.find cst strcst_shared
    avec Not_found ->
      soit lbl = new_const_symbol() dans
      structured_constants :=
        {
          strcst_shared = CstMap.add cst lbl strcst_shared;
          strcst_all = (lbl, cst) :: strcst_all;
        };
      lbl
  sinon
    soit lbl = new_const_symbol() dans
    structured_constants :=
      {
        strcst_shared;
        strcst_all = (lbl, cst) :: strcst_all;
      };
    lbl

soit add_exported_constant s =
  Hashtbl.replace exported_constants s ()

soit structured_constants () =
  List.map
    (fonc (lbl, cst) ->
       (lbl, Hashtbl.mem exported_constants lbl, cst)
    ) (!structured_constants).strcst_all

(* Error report *)

ouvre Format

soit report_error ppf = fonction
  | Not_a_unit_info filename ->
      fprintf ppf "%a@ is not a compilation unit description."
        Location.print_filename filename
  | Corrupted_unit_info filename ->
      fprintf ppf "Corrupted compilation unit description@ %a"
        Location.print_filename filename
  | Illegal_renaming(name, modname, filename) ->
      fprintf ppf "%a@ contains the description for unit\
                   @ %s when %s was expected"
        Location.print_filename filename name modname

soit () =
  Location.register_error_of_exn
    (fonction
      | Error err -> Some (Location.error_of_printer_file report_error err)
      | _ -> None
    )
