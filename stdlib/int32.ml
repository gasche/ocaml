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

(* Module [Int32]: 32-bit integers *)

dehors neg : int32 -> int32 = "%int32_neg"
dehors add : int32 -> int32 -> int32 = "%int32_add"
dehors sub : int32 -> int32 -> int32 = "%int32_sub"
dehors mul : int32 -> int32 -> int32 = "%int32_mul"
dehors div : int32 -> int32 -> int32 = "%int32_div"
dehors rem : int32 -> int32 -> int32 = "%int32_mod"
dehors logand : int32 -> int32 -> int32 = "%int32_and"
dehors logor : int32 -> int32 -> int32 = "%int32_or"
dehors logxor : int32 -> int32 -> int32 = "%int32_xor"
dehors shift_left : int32 -> int -> int32 = "%int32_lsl"
dehors shift_right : int32 -> int -> int32 = "%int32_asr"
dehors shift_right_logical : int32 -> int -> int32 = "%int32_lsr"
dehors of_int : int -> int32 = "%int32_of_int"
dehors to_int : int32 -> int = "%int32_to_int"
dehors of_float : float -> int32 = "caml_int32_of_float"
dehors to_float : int32 -> float = "caml_int32_to_float"
dehors bits_of_float : float -> int32 = "caml_int32_bits_of_float"
dehors float_of_bits : int32 -> float = "caml_int32_float_of_bits"

soit zero = 0l
soit one = 1l
soit minus_one = -1l
soit succ n = add n 1l
soit pred n = sub n 1l
soit abs n = si n >= 0l alors n sinon neg n
soit min_int = 0x80000000l
soit max_int = 0x7FFFFFFFl
soit lognot n = logxor n (-1l)

dehors format : string -> int32 -> string = "caml_int32_format"
soit to_string n = format "%d" n

dehors of_string : string -> int32 = "caml_int32_of_string"

type t = int32

soit compare (x: t) (y: t) = Pervasives.compare x y
