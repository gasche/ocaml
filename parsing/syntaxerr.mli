(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1997 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Auxiliary type for reporting syntax errors *)

ouvre Format

type error =
    Unclosed de Location.t * string * Location.t * string
  | Expecting de Location.t * string
  | Not_expecting de Location.t * string
  | Applicative_path de Location.t
  | Variable_in_scope de Location.t * string
  | Other de Location.t

exception Error de error
exception Escape_error

val report_error: formatter -> error -> unit
 (* Deprecated.  Use Location.{error_of_exn, report_error}. *)

val location_of_error: error -> Location.t
