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

(* Operations on internal representations of values *)

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
soit double_field x i = Array.get (obj x : float array) i
soit set_double_field x i v = Array.set (obj x : float array) i v
dehors new_block : int -> int -> t = "caml_obj_block"
dehors dup : t -> t = "caml_obj_dup"
dehors truncate : t -> int -> unit = "caml_obj_truncate"
dehors add_offset : t -> Int32.t -> t = "caml_obj_add_offset"

soit marshal (obj : t) =
  Marshal.to_string obj []
soit unmarshal str pos =
  (Marshal.from_string str pos, pos + Marshal.total_size str pos)

soit lazy_tag = 246
soit closure_tag = 247
soit object_tag = 248
soit infix_tag = 249
soit forward_tag = 250

soit no_scan_tag = 251

soit abstract_tag = 251
soit string_tag = 252
soit double_tag = 253
soit double_array_tag = 254
soit custom_tag = 255
soit final_tag = custom_tag


soit int_tag = 1000
soit out_of_heap_tag = 1001
soit unaligned_tag = 1002
