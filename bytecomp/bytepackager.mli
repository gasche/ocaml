(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 2002 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* "Package" a set of .cmo files into one .cmo file having the
   original compilation units as sub-modules. *)

val package_files: Format.formatter -> string list -> string -> unit

type error =
    Forward_reference de string * Ident.t
  | Multiple_definition de string * Ident.t
  | Not_an_object_file de string
  | Illegal_renaming de string * string * string
  | File_not_found de string

exception Error de error

val report_error: Format.formatter -> error -> unit
