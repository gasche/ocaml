(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*                        Alain Frisch, LexiFi                         *)
(*                                                                     *)
(*  Copyright 2012 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

ouvre Asttypes
ouvre Typedtree

classe iter: objet
  méthode binding: value_binding -> unit
  méthode bindings: (rec_flag * value_binding list) -> unit
  méthode case: case -> unit
  méthode cases: case list -> unit
  méthode class_description: class_description -> unit
  méthode class_expr: class_expr -> unit
  méthode class_field: class_field -> unit
  méthode class_signature: class_signature -> unit
  méthode class_structure: class_structure -> unit
  méthode class_type: class_type -> unit
  méthode class_type_declaration: class_type_declaration -> unit
  méthode class_type_field: class_type_field -> unit
  méthode core_type: core_type -> unit
  méthode expression: expression -> unit
  méthode module_binding: module_binding -> unit
  méthode module_expr: module_expr -> unit
  méthode module_type: module_type -> unit
  méthode package_type: package_type -> unit
  méthode pattern: pattern -> unit
  méthode row_field: row_field -> unit
  méthode signature: signature -> unit
  méthode signature_item: signature_item -> unit
  méthode structure: structure -> unit
  méthode structure_item: structure_item -> unit
  méthode type_declaration: type_declaration -> unit
  méthode value_description: value_description -> unit
  méthode with_constraint: with_constraint -> unit
fin
(** Recursive iterator class. By inheriting from it and
    overriding selected methods, it is possible to implement
    custom behavior for specific kinds of nodes. *)

(** {2 One-level iterators} *)

(** The following functions apply the provided iterator to each
    sub-component of the argument. *)

val binding: iter -> value_binding -> unit
val bindings: iter -> (rec_flag * value_binding list) -> unit
val class_description: iter -> class_description -> unit
val class_expr: iter -> class_expr -> unit
val class_field: iter -> class_field -> unit
val class_signature: iter -> class_signature -> unit
val class_structure: iter -> class_structure -> unit
val class_type: iter -> class_type -> unit
val class_type_declaration: iter -> class_type_declaration -> unit
val class_type_field: iter -> class_type_field -> unit
val core_type: iter -> core_type -> unit
val expression: iter -> expression -> unit
val module_binding: iter -> module_binding -> unit
val module_expr: iter -> module_expr -> unit
val module_type: iter -> module_type -> unit
val package_type: iter -> package_type -> unit
val pattern: iter -> pattern -> unit
val row_field: iter -> row_field -> unit
val signature: iter -> signature -> unit
val signature_item: iter -> signature_item -> unit
val structure: iter -> structure -> unit
val structure_item: iter -> structure_item -> unit
val type_declaration: iter -> type_declaration -> unit
val value_description: iter -> value_description -> unit
val with_constraint: iter -> with_constraint -> unit
