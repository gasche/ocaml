(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*         Jerome Vouillon, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

ouvre Asttypes
ouvre Types
ouvre Format

val class_declarations:
  Env.t -> Parsetree.class_declaration list ->
  (Ident.t * string loc * class_declaration *
   Ident.t * class_type_declaration *
   Ident.t * type_declaration *
   Ident.t * type_declaration *
   int * string list * Typedtree.class_declaration) list * Env.t

(*
and class_declaration =
  (class_expr, Types.class_declaration) class_infos
*)

val class_descriptions:
  Env.t -> Parsetree.class_description list ->
  (Ident.t * string loc * class_declaration *
   Ident.t * class_type_declaration *
   Ident.t * type_declaration *
   Ident.t * type_declaration *
   int * string list * Typedtree.class_description) list * Env.t

(*
and class_description =
  (class_type, unit) class_infos
*)

val class_type_declarations:
  Env.t -> Parsetree.class_description list ->
  (Ident.t * string loc * class_type_declaration *
   Ident.t * type_declaration *
   Ident.t * type_declaration *
  Typedtree.class_type_declaration) list * Env.t

(*
and class_type_declaration =
  (class_type, Types.class_type_declaration) class_infos
*)

val approx_class_declarations:
  Env.t -> Parsetree.class_description list ->
  (Ident.t * string loc * class_type_declaration *
   Ident.t * type_declaration *
   Ident.t * type_declaration *
  Typedtree.class_type_declaration) list

val virtual_methods: Types.class_signature -> label list

(*
val type_classes :
           bool ->
           ('a -> Types.type_expr) ->
           (Env.t -> 'a -> 'b * Types.class_type) ->
           Env.t ->
           'a Parsetree.class_infos list ->
  (  Ident.t * Types.class_declaration *
     Ident.t * Types.class_type_declaration *
     Ident.t * Types.type_declaration *
     Ident.t * Types.type_declaration *
     int * string list * 'b * 'b Typedtree.class_infos)
           list * Env.t
*)

type error =
    Unconsistent_constraint de (type_expr * type_expr) list
  | Field_type_mismatch de string * string * (type_expr * type_expr) list
  | Structure_expected de class_type
  | Cannot_apply de class_type
  | Apply_wrong_label de label
  | Pattern_type_clash de type_expr
  | Repeated_parameter
  | Unbound_class_2 de Longident.t
  | Unbound_class_type_2 de Longident.t
  | Abbrev_type_clash de type_expr * type_expr * type_expr
  | Constructor_type_mismatch de string * (type_expr * type_expr) list
  | Virtual_class de bool * bool * string list * string list
  | Parameter_arity_mismatch de Longident.t * int * int
  | Parameter_mismatch de (type_expr * type_expr) list
  | Bad_parameters de Ident.t * type_expr * type_expr
  | Class_match_failure de Ctype.class_match_failure list
  | Unbound_val de string
  | Unbound_type_var de (formatter -> unit) * Ctype.closed_class_failure
  | Make_nongen_seltype de type_expr
  | Non_generalizable_class de Ident.t * Types.class_declaration
  | Cannot_coerce_self de type_expr
  | Non_collapsable_conjunction de
      Ident.t * Types.class_declaration * (type_expr * type_expr) list
  | Final_self_clash de (type_expr * type_expr) list
  | Mutability_mismatch de string * mutable_flag
  | No_overriding de string * string
  | Duplicate de string * string
  | Extension de string

exception Error de Location.t * Env.t * error

val report_error : Env.t -> formatter -> error -> unit
