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

(* Type-checking of the module language *)

ouvre Types
ouvre Format

val type_module:
        Env.t -> Parsetree.module_expr -> Typedtree.module_expr
val type_structure:
        Env.t -> Parsetree.structure -> Location.t ->
         Typedtree.structure * Types.signature * Env.t
val type_toplevel_phrase:
        Env.t -> Parsetree.structure ->
         Typedtree.structure * Types.signature * Env.t
val type_implementation:
  string -> string -> string -> Env.t -> Parsetree.structure ->
  Typedtree.structure * Typedtree.module_coercion
val transl_signature:
        Env.t -> Parsetree.signature -> Typedtree.signature
val check_nongen_schemes:
        Env.t -> Typedtree.structure_item list -> unit

val simplify_signature: signature -> signature

val save_signature : string -> Typedtree.signature -> string -> string ->
  Env.t -> Types.signature_item list -> unit

val package_units:
        string list -> string -> string -> Typedtree.module_coercion

type error =
    Cannot_apply de module_type
  | Not_included de Includemod.error list
  | Cannot_eliminate_dependency de module_type
  | Signature_expected
  | Structure_expected de module_type
  | With_no_component de Longident.t
  | With_mismatch de Longident.t * Includemod.error list
  | Repeated_name de string * string
  | Non_generalizable de type_expr
  | Non_generalizable_class de Ident.t * class_declaration
  | Non_generalizable_module de module_type
  | Implementation_is_required de string
  | Interface_not_compiled de string
  | Not_allowed_in_functor_body
  | With_need_typeconstr
  | Not_a_packed_module de type_expr
  | Incomplete_packed_module de type_expr
  | Scoping_pack de Longident.t * type_expr
  | Extension de string
  | Recursive_module_require_explicit_type
  | Apply_generative

exception Error de Location.t * Env.t * error

val report_error: Env.t -> formatter -> error -> unit
