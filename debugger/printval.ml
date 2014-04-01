(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*          Jerome Vouillon, projet Cristal, INRIA Rocquencourt        *)
(*          OCaml port by John Malecki and Xavier Leroy                *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* To print values *)

ouvre Format
ouvre Parser_aux
ouvre Path
ouvre Types

(* To name printed and ellipsed values *)

soit named_values =
  (Hashtbl.create 29 : (int, Debugcom.Remote_value.t * type_expr) Hashtbl.t)
soit next_name = ref 1

soit reset_named_values () =
  Hashtbl.clear named_values;
  next_name := 1

soit name_value v ty =
  soit name = !next_name dans
  incr next_name;
  Hashtbl.add named_values name (v, ty);
  name

soit find_named_value name =
  Hashtbl.find named_values name

soit check_depth ppf depth obj ty =
  si depth <= 0 alors début
    soit n = name_value obj ty dans
    Some (Outcometree.Oval_stuff ("$" ^ string_of_int n))
  fin sinon None

module EvalPath =
  struct
    type valu = Debugcom.Remote_value.t
    exception Error
    soit rec eval_path env = fonction
      Pident id ->
        début essaie
          Debugcom.Remote_value.global (Symtable.get_global_position id)
        avec Symtable.Error _ ->
          raise Error
        fin
    | Pdot(root, fieldname, pos) ->
        soit v = eval_path env root dans
        si not (Debugcom.Remote_value.is_block v)
        alors raise Error
        sinon Debugcom.Remote_value.field v pos
    | Papply(p1, p2) ->
        raise Error
    soit same_value = Debugcom.Remote_value.same
  fin

module Printer = Genprintval.Make(Debugcom.Remote_value)(EvalPath)

soit install_printer path ty ppf fn =
  Printer.install_printer path ty
    (fonc ppf remote_val ->
       essaie
         fn ppf (Obj.repr (Debugcom.Remote_value.obj remote_val))
       avec
         Debugcom.Marshalling_error ->
           fprintf ppf "<cannot fetch remote object>")

soit remove_printer = Printer.remove_printer

soit max_printer_depth = ref 20
soit max_printer_steps = ref 300

soit print_exception ppf obj =
  soit t = Printer.outval_of_untyped_exception obj dans
  !Oprint.out_value ppf t

soit print_value max_depth env obj (ppf : Format.formatter) ty =
  soit t =
    Printer.outval_of_value !max_printer_steps max_depth
      (check_depth ppf) env obj ty dans
  !Oprint.out_value ppf t

soit print_named_value max_depth exp env obj ppf ty =
  soit print_value_name ppf = fonction
  | E_ident lid ->
      Printtyp.longident ppf lid
  | E_name n ->
      fprintf ppf "$%i" n
  | _ ->
      soit n = name_value obj ty dans
      fprintf ppf "$%i" n dans
  Printtyp.reset_and_mark_loops ty;
  fprintf ppf "@[<2>%a:@ %a@ =@ %a@]@."
  print_value_name exp
  Printtyp.type_expr ty
  (print_value max_depth env obj) ty
