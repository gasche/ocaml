(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*     Daniel de Rauglaudre, projet Cristal, INRIA Rocquencourt        *)
(*                                                                     *)
(*  Copyright 2001 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Module [Outcometree]: results displayed by the toplevel *)

(* These types represent messages that the toplevel displays as normal
   results or errors. The real displaying is customisable using the hooks:
      [Toploop.print_out_value]
      [Toploop.print_out_type]
      [Toploop.print_out_sig_item]
      [Toploop.print_out_phrase] *)

type out_ident =
  | Oide_apply de out_ident * out_ident
  | Oide_dot de out_ident * string
  | Oide_ident de string

type out_value =
  | Oval_array de out_value list
  | Oval_char de char
  | Oval_constr de out_ident * out_value list
  | Oval_ellipsis
  | Oval_float de float
  | Oval_int de int
  | Oval_int32 de int32
  | Oval_int64 de int64
  | Oval_nativeint de nativeint
  | Oval_list de out_value list
  | Oval_printer de (Format.formatter -> unit)
  | Oval_record de (out_ident * out_value) list
  | Oval_string de string
  | Oval_stuff de string
  | Oval_tuple de out_value list
  | Oval_variant de string * out_value option

type out_type =
  | Otyp_abstract
  | Otyp_alias de out_type * string
  | Otyp_arrow de string * out_type * out_type
  | Otyp_class de bool * out_ident * out_type list
  | Otyp_constr de out_ident * out_type list
  | Otyp_manifest de out_type * out_type
  | Otyp_object de (string * out_type) list * bool option
  | Otyp_record de (string * bool * out_type) list
  | Otyp_stuff de string
  | Otyp_sum de (string * out_type list * out_type option) list
  | Otyp_tuple de out_type list
  | Otyp_var de bool * string
  | Otyp_variant de
      bool * out_variant * bool * (string list) option
  | Otyp_poly de string list * out_type
  | Otyp_module de string * string list * out_type list

et out_variant =
  | Ovar_fields de (string * bool * out_type list) list
  | Ovar_name de out_ident * out_type list

type out_class_type =
  | Octy_constr de out_ident * out_type list
  | Octy_arrow de string * out_type * out_class_type
  | Octy_signature de out_type option * out_class_sig_item list
et out_class_sig_item =
  | Ocsg_constraint de out_type * out_type
  | Ocsg_method de string * bool * bool * out_type
  | Ocsg_value de string * bool * bool * out_type

type out_module_type =
  | Omty_abstract
  | Omty_functor de string * out_module_type option * out_module_type
  | Omty_ident de out_ident
  | Omty_signature de out_sig_item list
  | Omty_alias de out_ident
et out_sig_item =
  | Osig_class de
      bool * string * (string * (bool * bool)) list * out_class_type *
        out_rec_status
  | Osig_class_type de
      bool * string * (string * (bool * bool)) list * out_class_type *
        out_rec_status
  | Osig_exception de string * out_type list
  | Osig_modtype de string * out_module_type
  | Osig_module de string * out_module_type * out_rec_status
  | Osig_type de out_type_decl * out_rec_status
  | Osig_value de string * out_type * string list
et out_type_decl =
  string * (string * (bool * bool)) list * out_type * Asttypes.private_flag *
  (out_type * out_type) list
et out_rec_status =
  | Orec_not
  | Orec_first
  | Orec_next

type out_phrase =
  | Ophr_eval de out_value * out_type
  | Ophr_signature de (out_sig_item * out_value option) list
  | Ophr_exception de (exn * out_value)
