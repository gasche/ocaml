(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*    Valerie Menissier-Morain, projet Cristal, INRIA Rocquencourt     *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../../LICENSE.  *)
(*                                                                     *)
(***********************************************************************)

(* $Id$ *)

(* Module [Nat]: operations on natural numbers *)

type nat

(* Natural numbers (type [nat]) are positive integers of arbitrary size.
   All operations on [nat] are performed in-place. *)

dehors create_nat: int -> nat = "create_nat"
val make_nat: int -> nat
dehors set_to_zero_nat: nat -> int -> int -> unit = "set_to_zero_nat"
dehors blit_nat: nat -> int -> nat -> int -> int -> unit = "blit_nat"
val copy_nat: nat -> int -> int -> nat
dehors set_digit_nat: nat -> int -> int -> unit = "set_digit_nat"
dehors nth_digit_nat: nat -> int -> int = "nth_digit_nat"
dehors set_digit_nat_native: nat -> int -> nativeint -> unit = "set_digit_nat_native"
dehors nth_digit_nat_native: nat -> int -> nativeint = "nth_digit_nat_native"
val length_nat : nat -> int
dehors num_digits_nat: nat -> int -> int -> int = "num_digits_nat"
dehors num_leading_zero_bits_in_digit: nat -> int -> int = "num_leading_zero_bits_in_digit"
dehors is_digit_int: nat -> int -> bool = "is_digit_int"
dehors is_digit_zero: nat -> int -> bool = "is_digit_zero"
dehors is_digit_normalized: nat -> int -> bool = "is_digit_normalized"
dehors is_digit_odd: nat -> int -> bool = "is_digit_odd"
val is_zero_nat: nat -> int -> int -> bool
val is_nat_int: nat -> int -> int -> bool
val int_of_nat: nat -> int
val nat_of_int: int -> nat
dehors incr_nat: nat -> int -> int -> int -> int = "incr_nat"
dehors add_nat: nat -> int -> int -> nat -> int -> int -> int -> int = "add_nat" "add_nat_native"
dehors complement_nat: nat -> int -> int -> unit = "complement_nat"
dehors decr_nat: nat -> int -> int -> int -> int = "decr_nat"
dehors sub_nat: nat -> int -> int -> nat -> int -> int -> int -> int = "sub_nat" "sub_nat_native"
dehors mult_digit_nat: nat -> int -> int -> nat -> int -> int -> nat -> int -> int = "mult_digit_nat" "mult_digit_nat_native"
dehors mult_nat: nat -> int -> int -> nat -> int -> int -> nat -> int -> int -> int = "mult_nat" "mult_nat_native"
dehors square_nat: nat -> int -> int -> nat -> int -> int -> int = "square_nat" "square_nat_native"
dehors shift_left_nat: nat -> int -> int -> nat -> int -> int -> unit = "shift_left_nat" "shift_left_nat_native"
dehors div_digit_nat: nat -> int -> nat -> int -> nat -> int -> int -> nat -> int -> unit = "div_digit_nat" "div_digit_nat_native"
dehors div_nat: nat -> int -> int -> nat -> int -> int -> unit = "div_nat" "div_nat_native"
dehors shift_right_nat: nat -> int -> int -> nat -> int -> int -> unit = "shift_right_nat" "shift_right_nat_native"
dehors compare_digits_nat: nat -> int -> nat -> int -> int = "compare_digits_nat"
dehors compare_nat: nat -> int -> int -> nat -> int -> int -> int = "compare_nat" "compare_nat_native"
val eq_nat : nat -> int -> int -> nat -> int -> int -> bool
val le_nat : nat -> int -> int -> nat -> int -> int -> bool
val lt_nat : nat -> int -> int -> nat -> int -> int -> bool
val ge_nat : nat -> int -> int -> nat -> int -> int -> bool
val gt_nat : nat -> int -> int -> nat -> int -> int -> bool
dehors land_digit_nat: nat -> int -> nat -> int -> unit = "land_digit_nat"
dehors lor_digit_nat: nat -> int -> nat -> int -> unit = "lor_digit_nat"
dehors lxor_digit_nat: nat -> int -> nat -> int -> unit = "lxor_digit_nat"
val gcd_nat : nat -> int -> int -> nat -> int -> int -> int
val sqrt_nat : nat -> int -> int -> nat
val string_of_nat : nat -> string
val nat_of_string : string -> nat
val sys_nat_of_string : int -> string -> int -> int -> nat
val float_of_nat : nat -> float
val make_power_base :  int -> nat -> int * int
val power_base_int : int -> int -> nat
val length_of_digit: int
