(***********************************************************************)
(*                                                                     *)
(*                           Objective Caml                            *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  Automatique.  Distributed only by permission.                      *)
(*                                                                     *)
(***********************************************************************)

(* $Id$ *)

(* Environment handling *)

open Types

type t

val empty: t
val initial: t

(* Lookup by paths *)

val find_value: Path.t -> t -> value_description
val find_type: Path.t -> t -> type_declaration
val find_module: Path.t -> t -> module_type
val find_modtype: Path.t -> t -> modtype_declaration
val find_class: Path.t -> t -> class_type

(* Lookup by long identifiers *)

val lookup_value: Longident.t -> t -> Path.t * value_description
val lookup_constructor: Longident.t -> t -> constructor_description
val lookup_label: Longident.t -> t -> label_description
val lookup_type: Longident.t -> t -> Path.t * type_declaration
val lookup_module: Longident.t -> t -> Path.t * module_type
val lookup_modtype: Longident.t -> t -> Path.t * modtype_declaration
val lookup_class: Longident.t -> t -> Path.t * class_type

(* Insertion by identifier *)

val add_value: Ident.t -> value_description -> t -> t
val add_type: Ident.t -> type_declaration -> t -> t
val add_exception: Ident.t -> exception_declaration -> t -> t
val add_module: Ident.t -> module_type -> t -> t
val add_modtype: Ident.t -> modtype_declaration -> t -> t
val add_class: Ident.t -> class_type -> t -> t

(* Insertion of all fields of a signature. *)

val add_item: signature_item -> t -> t
val add_signature: signature -> t -> t

(* Insertion of all fields of a signature, relative to the given path.
   Used to implement open. *)

val open_signature: Path.t -> signature -> t -> t
val open_pers_signature: string -> t -> t

(* Insertion by name *)

val enter_value: string -> value_description -> t -> Ident.t * t
val enter_type: string -> type_declaration -> t -> Ident.t * t
val enter_exception: string -> exception_declaration -> t -> Ident.t * t
val enter_module: string -> module_type -> t -> Ident.t * t
val enter_modtype: string -> modtype_declaration -> t -> Ident.t * t
val enter_class: string -> class_type -> t -> Ident.t * t

(* Reset the cache of in-core module interfaces.
   To be called in particular when load_path changes. *)

val reset_cache: unit -> unit

(* Read, save a signature to/from a file *)

val read_signature: string -> string -> signature * Digest.t
        (* Arguments: module name, file name.
           Results: signature, CRC. *)
val save_signature: signature -> string -> string -> Digest.t
        (* Arguments: signature, module name, file name.
           Result: CRC. *)

(* Return the set of compilation units imported, with their CRC *)

val imported_units: unit -> (string * Digest.t) list

(* Summaries -- compact representation of an environment, to be
   exported in debugging information. *)

type summary =
    Env_empty
  | Env_value of summary * Ident.t * value_description
  | Env_type of summary * Ident.t * type_declaration
  | Env_exception of summary * Ident.t * exception_declaration
  | Env_module of summary * Ident.t * module_type
  | Env_modtype of summary * Ident.t * modtype_declaration
  | Env_class of summary * Ident.t * class_type
  | Env_open of summary * Path.t

val summary: t -> summary

(* Error report *)

type error =
    Not_an_interface of string
  | Corrupted_interface of string
  | Illegal_renaming of string * string

exception Error of error

val report_error: error -> unit

(* Forward declaration to break mutual recursion with includemod. *)

val check_modtype_inclusion: (t -> module_type -> module_type -> unit) ref
