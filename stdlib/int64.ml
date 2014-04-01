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

(* Module [Int64]: 64-bit integers *)

dehors neg : int64 -> int64 = "%int64_neg"
dehors add : int64 -> int64 -> int64 = "%int64_add"
dehors sub : int64 -> int64 -> int64 = "%int64_sub"
dehors mul : int64 -> int64 -> int64 = "%int64_mul"
dehors div : int64 -> int64 -> int64 = "%int64_div"
dehors rem : int64 -> int64 -> int64 = "%int64_mod"
dehors logand : int64 -> int64 -> int64 = "%int64_and"
dehors logor : int64 -> int64 -> int64 = "%int64_or"
dehors logxor : int64 -> int64 -> int64 = "%int64_xor"
dehors shift_left : int64 -> int -> int64 = "%int64_lsl"
dehors shift_right : int64 -> int -> int64 = "%int64_asr"
dehors shift_right_logical : int64 -> int -> int64 = "%int64_lsr"
dehors of_int : int -> int64 = "%int64_of_int"
dehors to_int : int64 -> int = "%int64_to_int"
dehors of_float : float -> int64 = "caml_int64_of_float"
dehors to_float : int64 -> float = "caml_int64_to_float"
dehors of_int32 : int32 -> int64 = "%int64_of_int32"
dehors to_int32 : int64 -> int32 = "%int64_to_int32"
dehors of_nativeint : nativeint -> int64 = "%int64_of_nativeint"
dehors to_nativeint : int64 -> nativeint = "%int64_to_nativeint"

soit zero = 0L
soit one = 1L
soit minus_one = -1L
soit succ n = add n 1L
soit pred n = sub n 1L
soit abs n = si n >= 0L alors n sinon neg n
soit min_int = 0x8000000000000000L
soit max_int = 0x7FFFFFFFFFFFFFFFL
soit lognot n = logxor n (-1L)

dehors format : string -> int64 -> string = "caml_int64_format"
soit to_string n = format "%d" n

dehors of_string : string -> int64 = "caml_int64_of_string"

dehors bits_of_float : float -> int64 = "caml_int64_bits_of_float"
dehors float_of_bits : int64 -> float = "caml_int64_float_of_bits"

type t = int64

soit compare (x: t) (y: t) = Pervasives.compare x y
