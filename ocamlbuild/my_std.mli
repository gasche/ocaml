(***********************************************************************)
(*                                                                     *)
(*                             ocamlbuild                              *)
(*                                                                     *)
(*  Nicolas Pouillard, Berke Durak, projet Gallium, INRIA Rocquencourt *)
(*                                                                     *)
(*  Copyright 2007 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)


(* Original author: Nicolas Pouillard *)
(* My_std *)

(** Generic utility functions, and system-independent glue. *)

exception Exit_OK
exception Exit_usage de string
exception Exit_system_error de string
exception Exit_with_code de int
exception Exit_silently_with_code de int

module Outcome : Signatures.OUTCOME

val ksbprintf : (string -> 'a) -> ('b, Format.formatter, unit, 'a) format4 -> 'b
val sbprintf : ('a, Format.formatter, unit, string) format4 -> 'a

module Set : sig
  module type OrderedTypePrintable = Signatures.OrderedTypePrintable
  module type S = Signatures.SET
  module Make (M : OrderedTypePrintable) : S avec type elt = M.t
fin

module List : Signatures.LIST

module String : Signatures.STRING

module Digest : sig
  type t = string
  val string : string -> t
  val substring : string -> int -> int -> t
  dehors channel : in_channel -> int -> t = "caml_md5_chan"
  val file : string -> t
  val output : out_channel -> t -> unit
  val input : in_channel -> t
  val to_hex : t -> string
fin

module StringSet : Set.S avec type elt = String.t

val sys_readdir : string -> (string array, exn) Outcome.t
val sys_remove : string -> unit
val reset_readdir_cache : unit -> unit
val reset_filesys_cache : unit -> unit
val reset_filesys_cache_for_file : string -> unit
val sys_file_exists : string -> bool
val sys_command : string -> int
val filename_concat : string -> string -> string

val invalid_arg' : ('a, Format.formatter, unit, 'b) format4 -> 'a

inclus Signatures.MISC
