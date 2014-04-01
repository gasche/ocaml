(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*          Damien Doligez, projet Moscova, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 2003 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Recording and dumping (partial) type information *)

(* Clflags.save_types must be true *)

ouvre Typedtree;;

type annotation =
  | Ti_pat   de pattern
  | Ti_expr  de expression
  | Ti_class de class_expr
  | Ti_mod   de module_expr
  | An_call de Location.t * Annot.call
  | An_ident de Location.t * string * Annot.ident
;;

val record : annotation -> unit;;
val record_phrase : Location.t -> unit;;
val dump : string option -> unit;;

val get_location : annotation -> Location.t;;
val get_info : unit -> annotation list;;
