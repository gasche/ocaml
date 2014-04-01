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

(* Link a set of .cmx/.o files and produce an executable or a plugin *)

ouvre Format

val link: formatter -> string list -> string -> unit

val link_shared: formatter -> string list -> string -> unit

val call_linker_shared: string list -> string -> unit

val check_consistency: string -> Cmx_format.unit_infos -> Digest.t -> unit
val extract_crc_interfaces: unit -> (string * Digest.t) list
val extract_crc_implementations: unit -> (string * Digest.t) list

type error =
    File_not_found de string
  | Not_an_object_file de string
  | Missing_implementations de (string * string list) list
  | Inconsistent_interface de string * string * string
  | Inconsistent_implementation de string * string * string
  | Assembler_error de string
  | Linking_error
  | Multiple_definition de string * string * string
  | Missing_cmx de string * string

exception Error de error

val report_error: formatter -> error -> unit
