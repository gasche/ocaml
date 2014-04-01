(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

(** Operations on internal representations of values.

   Not for the casual user.
*)

type t

dehors repr : 'a -> t = "%identity"
dehors obj : t -> 'a = "%identity"
dehors magic : 'a -> 'b = "%identity"
dehors is_block : t -> bool = "caml_obj_is_block"
dehors is_int : t -> bool = "%obj_is_int"
dehors tag : t -> int = "caml_obj_tag"
dehors set_tag : t -> int -> unit = "caml_obj_set_tag"
dehors size : t -> int = "%obj_size"
dehors field : t -> int -> t = "%obj_field"
dehors set_field : t -> int -> t -> unit = "%obj_set_field"
val double_field : t -> int -> float  (* @since 3.11.2 *)
val set_double_field : t -> int -> float -> unit  (* @since 3.11.2 *)
dehors new_block : int -> int -> t = "caml_obj_block"
dehors dup : t -> t = "caml_obj_dup"
dehors truncate : t -> int -> unit = "caml_obj_truncate"
dehors add_offset : t -> Int32.t -> t = "caml_obj_add_offset"
         (* @since 3.12.0 *)

val lazy_tag : int
val closure_tag : int
val object_tag : int
val infix_tag : int
val forward_tag : int
val no_scan_tag : int
val abstract_tag : int
val string_tag : int
val double_tag : int
val double_array_tag : int
val custom_tag : int
val final_tag : int  (* DEPRECATED *)

val int_tag : int
val out_of_heap_tag : int
val unaligned_tag : int   (* should never happen @since 3.11.0 *)

(** The following two functions are deprecated.  Use module {!Marshal}
    instead. *)

val marshal : t -> string
val unmarshal : string -> int -> t * int
