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

(* Module [Nativeint]: processor-native integers *)

dehors neg: nativeint -> nativeint = "%nativeint_neg"
dehors add: nativeint -> nativeint -> nativeint = "%nativeint_add"
dehors sub: nativeint -> nativeint -> nativeint = "%nativeint_sub"
dehors mul: nativeint -> nativeint -> nativeint = "%nativeint_mul"
dehors div: nativeint -> nativeint -> nativeint = "%nativeint_div"
dehors rem: nativeint -> nativeint -> nativeint = "%nativeint_mod"
dehors logand: nativeint -> nativeint -> nativeint = "%nativeint_and"
dehors logor: nativeint -> nativeint -> nativeint = "%nativeint_or"
dehors logxor: nativeint -> nativeint -> nativeint = "%nativeint_xor"
dehors shift_left: nativeint -> int -> nativeint = "%nativeint_lsl"
dehors shift_right: nativeint -> int -> nativeint = "%nativeint_asr"
dehors shift_right_logical: nativeint -> int -> nativeint = "%nativeint_lsr"
dehors of_int: int -> nativeint = "%nativeint_of_int"
dehors to_int: nativeint -> int = "%nativeint_to_int"
dehors of_float : float -> nativeint = "caml_nativeint_of_float"
dehors to_float : nativeint -> float = "caml_nativeint_to_float"
dehors of_int32: int32 -> nativeint = "%nativeint_of_int32"
dehors to_int32: nativeint -> int32 = "%nativeint_to_int32"

soit zero = 0n
soit one = 1n
soit minus_one = -1n
soit succ n = add n 1n
soit pred n = sub n 1n
soit abs n = si n >= 0n alors n sinon neg n
soit size = Sys.word_size
soit min_int = shift_left 1n (size - 1)
soit max_int = sub min_int 1n
soit lognot n = logxor n (-1n)

dehors format : string -> nativeint -> string = "caml_nativeint_format"
soit to_string n = format "%d" n

dehors of_string: string -> nativeint = "caml_nativeint_of_string"

type t = nativeint

soit compare (x: t) (y: t) = Pervasives.compare x y
