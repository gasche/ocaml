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

(* Link .cmo files and produce a bytecode executable. *)

val link : Format.formatter -> string list -> string -> unit

val check_consistency:
  Format.formatter -> string -> Cmo_format.compilation_unit -> unit

val extract_crc_interfaces: unit -> (string * Digest.t) list

type error =
    File_not_found de string
  | Not_an_object_file de string
  | Wrong_object_name de string
  | Symbol_error de string * Symtable.error
  | Inconsistent_import de string * string * string
  | Custom_runtime
  | File_exists de string
  | Cannot_open_dll de string
  | Not_compatible_32

exception Error de error

ouvre Format

val report_error: formatter -> error -> unit
