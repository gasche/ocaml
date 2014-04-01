(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Pierre Weis && Damien Doligez, INRIA Rocquencourt        *)
(*                                                                     *)
(*  Copyright 1998 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

ouvre Format

type t =
  | Comment_start                           (*  1 *)
  | Comment_not_end                         (*  2 *)
  | Deprecated de string                    (*  3 *)
  | Fragile_match de string                 (*  4 *)
  | Partial_application                     (*  5 *)
  | Labels_omitted                          (*  6 *)
  | Method_override de string list          (*  7 *)
  | Partial_match de string                 (*  8 *)
  | Non_closed_record_pattern de string     (*  9 *)
  | Statement_type                          (* 10 *)
  | Unused_match                            (* 11 *)
  | Unused_pat                              (* 12 *)
  | Instance_variable_override de string list (* 13 *)
  | Illegal_backslash                       (* 14 *)
  | Implicit_public_methods de string list  (* 15 *)
  | Unerasable_optional_argument            (* 16 *)
  | Undeclared_virtual_method de string     (* 17 *)
  | Not_principal de string                 (* 18 *)
  | Without_principality de string          (* 19 *)
  | Unused_argument                         (* 20 *)
  | Nonreturning_statement                  (* 21 *)
  | Camlp4 de string                        (* 22 *)
  | Useless_record_with                     (* 23 *)
  | Bad_module_name de string               (* 24 *)
  | All_clauses_guarded                     (* 25 *)
  | Unused_var de string                    (* 26 *)
  | Unused_var_strict de string             (* 27 *)
  | Wildcard_arg_to_constant_constr         (* 28 *)
  | Eol_in_string                           (* 29 *)
  | Duplicate_definitions de string * string * string * string (* 30 *)
  | Multiple_definition de string * string * string (* 31 *)
  | Unused_value_declaration de string      (* 32 *)
  | Unused_open de string                   (* 33 *)
  | Unused_type_declaration de string       (* 34 *)
  | Unused_for_index de string              (* 35 *)
  | Unused_ancestor de string               (* 36 *)
  | Unused_constructor de string * bool * bool (* 37 *)
  | Unused_exception de string * bool       (* 38 *)
  | Unused_rec_flag                         (* 39 *)
  | Name_out_of_scope de string * string list * bool   (* 40 *)
  | Ambiguous_name de string list * string list * bool (* 41 *)
  | Disambiguated_name de string            (* 42 *)
  | Nonoptional_label de string             (* 43 *)
  | Open_shadow_identifier de string * string (* 44 *)
  | Open_shadow_label_constructor de string * string (* 45 *)
  | Bad_env_variable de string * string     (* 46 *)
  | Attribute_payload de string * string    (* 47 *)
  | Eliminated_optional_arguments de string list (* 48 *)
;;

val parse_options : bool -> string -> unit;;

val is_active : t -> bool;;
val is_error : t -> bool;;

val defaults_w : string;;
val defaults_warn_error : string;;

val print : formatter -> t -> int;;
  (* returns the number of newlines in the printed string *)


exception Errors de int;;

val check_fatal : unit -> unit;;

val help_warnings: unit -> unit

type state
val backup: unit -> state
val restore: state -> unit
