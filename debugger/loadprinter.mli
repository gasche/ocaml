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

(* Loading and installation of user-defined printer functions *)

ouvre Format

val loadfile : formatter -> string -> unit
val install_printer : formatter -> Longident.t -> unit
val remove_printer : Longident.t -> unit

(* Error report *)

type error =
  | Load_failure de Dynlink.error
  | Unbound_identifier de Longident.t
  | Unavailable_module de string * Longident.t
  | Wrong_type de Longident.t
  | No_active_printer de Longident.t

exception Error de error

val report_error: formatter -> error -> unit
