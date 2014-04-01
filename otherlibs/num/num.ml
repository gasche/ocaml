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

ouvre Int_misc
ouvre Nat
ouvre Big_int
ouvre Arith_flags
ouvre Ratio

type num = Int de int | Big_int de big_int | Ratio de ratio
        (* The type of numbers. *)

soit biggest_INT = big_int_of_int biggest_int
et least_INT = big_int_of_int least_int

(* Coercion big_int -> num *)
soit num_of_big_int bi =
 si le_big_int bi biggest_INT && ge_big_int bi least_INT
 alors Int (int_of_big_int bi)
 sinon Big_int bi

soit numerator_num = fonction
  Ratio r -> ignore (normalize_ratio r); num_of_big_int (numerator_ratio r)
| n -> n

soit denominator_num = fonction
  Ratio r -> ignore (normalize_ratio r); num_of_big_int (denominator_ratio r)
| n -> Int 1

soit normalize_num = fonction
  Int i -> Int i
| Big_int bi -> num_of_big_int bi
| Ratio r -> si is_integer_ratio r
              alors num_of_big_int (numerator_ratio r)
              sinon Ratio r

soit cautious_normalize_num_when_printing n =
 si (!normalize_ratio_when_printing_flag) alors (normalize_num n) sinon n

soit num_of_ratio r =
 ignore (normalize_ratio r);
 si not (is_integer_ratio r) alors Ratio r
 sinon si is_int_big_int (numerator_ratio r) alors
        Int (int_of_big_int (numerator_ratio r))
 sinon Big_int (numerator_ratio r)

(* Operations on num *)

soit add_num a b = filtre (a,b) avec
    ((Int int1), (Int int2)) ->
      soit r =  int1 + int2 dans
      si (int1 ouxl int2) oul (int1 ouxl (r ouxl (-1))) < 0
      alors Int r                        (* No overflow *)
      sinon Big_int(add_big_int (big_int_of_int int1) (big_int_of_int int2))
  | ((Int i), (Big_int bi)) ->
      num_of_big_int (add_int_big_int i bi)
  | ((Big_int bi), (Int i)) ->
      num_of_big_int (add_int_big_int i bi)

  | ((Int i), (Ratio r)) ->
      Ratio (add_int_ratio i r)
  | ((Ratio r), (Int i)) ->
      Ratio (add_int_ratio i r)

  | ((Big_int bi1), (Big_int bi2)) -> num_of_big_int (add_big_int bi1 bi2)

  | ((Big_int bi), (Ratio r)) ->
      Ratio (add_big_int_ratio bi r)
  | ((Ratio r), (Big_int bi)) ->
      Ratio (add_big_int_ratio bi r)

  | ((Ratio r1), (Ratio r2)) -> num_of_ratio (add_ratio r1 r2)

soit ( +/ ) = add_num

soit minus_num = fonction
  Int i -> si i = monster_int
              alors Big_int (minus_big_int (big_int_of_int i))
              sinon Int (-i)
| Big_int bi -> Big_int (minus_big_int bi)
| Ratio r -> Ratio (minus_ratio r)

soit sub_num n1 n2 = add_num n1 (minus_num n2)

soit ( -/ ) = sub_num

soit mult_num a b = filtre (a,b) avec
   ((Int int1), (Int int2)) ->
    si num_bits_int int1 + num_bits_int int2 < length_of_int
       alors Int (int1 * int2)
       sinon num_of_big_int (mult_big_int (big_int_of_int int1)
                                         (big_int_of_int int2))

 | ((Int i), (Big_int bi)) ->
     num_of_big_int (mult_int_big_int i bi)
 | ((Big_int bi), (Int i)) ->
     num_of_big_int (mult_int_big_int i bi)

 | ((Int i), (Ratio r)) ->
     num_of_ratio (mult_int_ratio i r)
 | ((Ratio r), (Int i)) ->
     num_of_ratio (mult_int_ratio i r)

 | ((Big_int bi1), (Big_int bi2)) ->
     num_of_big_int (mult_big_int bi1 bi2)

 | ((Big_int bi), (Ratio r)) ->
     num_of_ratio (mult_big_int_ratio bi r)
 | ((Ratio r), (Big_int bi)) ->
     num_of_ratio (mult_big_int_ratio bi r)

 | ((Ratio r1), (Ratio r2)) ->
     num_of_ratio (mult_ratio r1 r2)

soit ( */ ) = mult_num

soit square_num = fonction
   Int i -> si 2 * num_bits_int i < length_of_int
               alors Int (i * i)
               sinon num_of_big_int (square_big_int (big_int_of_int i))
 | Big_int bi -> Big_int (square_big_int bi)
 | Ratio r -> Ratio (square_ratio r)

soit div_num n1 n2 =
 filtre n1 avec
 | Int i1 ->
    début filtre n2 avec
    | Int i2 ->
       num_of_ratio (create_ratio (big_int_of_int i1) (big_int_of_int i2))
    | Big_int bi2 -> num_of_ratio (create_ratio (big_int_of_int i1) bi2)
    | Ratio r2 -> num_of_ratio (div_int_ratio i1 r2) fin

 | Big_int bi1 ->
     début filtre n2 avec
     | Int i2 -> num_of_ratio (create_ratio bi1 (big_int_of_int i2))
     | Big_int bi2 -> num_of_ratio (create_ratio bi1 bi2)
     | Ratio r2 -> num_of_ratio (div_big_int_ratio bi1 r2) fin

 | Ratio r1 ->
     début filtre n2 avec
     | Int i2 -> num_of_ratio (div_ratio_int r1 i2)
     | Big_int bi2 -> num_of_ratio (div_ratio_big_int r1 bi2)
     | Ratio r2 -> num_of_ratio (div_ratio r1 r2) fin
;;

soit ( // ) = div_num

soit floor_num = fonction
  Int i tel n -> n
| Big_int bi tel n -> n
| Ratio r -> num_of_big_int (floor_ratio r)

(* The function [quo_num] is equivalent to

  let quo_num x y = floor_num (div_num x y);;

  However, this definition is vastly inefficient (cf PR #3473):
  we define here a better way of computing the same thing.
 *)
soit quo_num n1 n2 =
 filtre n1 avec
 | Int i1 ->
   début filtre n2 avec
   | Int i2 -> Int (i1 / i2)
   | Big_int bi2 -> num_of_big_int (div_big_int (big_int_of_int i1) bi2)
   | Ratio r2 -> num_of_big_int (floor_ratio (div_int_ratio i1 r2)) fin

 | Big_int bi1 ->
   début filtre n2 avec
   | Int i2 -> num_of_big_int (div_big_int bi1 (big_int_of_int i2))
   | Big_int bi2 -> num_of_big_int (div_big_int bi1 bi2)
   | Ratio r2 -> num_of_big_int (floor_ratio (div_big_int_ratio bi1 r2)) fin

 | Ratio r1 ->
   début filtre n2 avec
   | Int i2 -> num_of_big_int (floor_ratio (div_ratio_int r1 i2))
   | Big_int bi2 -> num_of_big_int (floor_ratio (div_ratio_big_int r1 bi2))
   | Ratio r2 -> num_of_big_int (floor_ratio (div_ratio r1 r2)) fin
;;

(* The function [mod_num] is equivalent to:

  let mod_num x y = sub_num x (mult_num y (quo_num x y));;

  However, as for [quo_num] above, this definition is inefficient:
  we define here a better way of computing the same thing.
 *)
soit mod_num n1 n2 =
 filtre n1 avec
 | Int i1 ->
   début filtre n2 avec
   | Int i2 -> Int (i1 mod i2)
   | Big_int bi2 -> num_of_big_int (mod_big_int (big_int_of_int i1) bi2)
   | Ratio _r2 -> sub_num n1 (mult_num n2 (quo_num n1 n2)) fin

 | Big_int bi1 ->
   début filtre n2 avec
   | Int i2 -> num_of_big_int (mod_big_int bi1 (big_int_of_int i2))
   | Big_int bi2 -> num_of_big_int (mod_big_int bi1 bi2)
   | Ratio _r2 -> sub_num n1 (mult_num n2 (quo_num n1 n2)) fin

 | Ratio _r1 -> sub_num n1 (mult_num n2 (quo_num n1 n2))
;;

soit power_num_int a b = filtre (a,b) avec
   ((Int i), n) ->
       (filtre sign_int n avec
           0 -> Int 1
         | 1 -> num_of_big_int (power_int_positive_int i n)
         | _ -> Ratio (create_normalized_ratio
                        unit_big_int (power_int_positive_int i (-n))))
| ((Big_int bi), n) ->
       (filtre sign_int n avec
           0 -> Int 1
         | 1 -> num_of_big_int (power_big_int_positive_int bi n)
         | _ -> Ratio (create_normalized_ratio
                 unit_big_int (power_big_int_positive_int bi (-n))))
| ((Ratio r), n) ->
       (filtre sign_int n avec
           0 -> Int 1
         | 1 -> Ratio (power_ratio_positive_int r n)
         | _ -> Ratio (power_ratio_positive_int
                         (inverse_ratio r) (-n)))

soit power_num_big_int a b =  filtre (a,b) avec
   ((Int i), n) ->
    (filtre sign_big_int n avec
           0 -> Int 1
         | 1 -> num_of_big_int (power_int_positive_big_int i n)
         | _ -> Ratio (create_normalized_ratio
                         unit_big_int
                         (power_int_positive_big_int i (minus_big_int n))))
| ((Big_int bi), n) ->
       (filtre sign_big_int n avec
           0 -> Int 1
         | 1 -> num_of_big_int (power_big_int_positive_big_int bi n)
         | _ -> Ratio (create_normalized_ratio
                         unit_big_int
                         (power_big_int_positive_big_int bi (minus_big_int n))))
| ((Ratio r), n) ->
       (filtre sign_big_int n avec
           0 -> Int 1
         | 1 -> Ratio (power_ratio_positive_big_int r n)
         | _ -> Ratio (power_ratio_positive_big_int
                         (inverse_ratio r) (minus_big_int n)))

soit power_num a b = filtre (a,b) avec
  (n, (Int i)) -> power_num_int n i
| (n, (Big_int bi)) -> power_num_big_int n bi
| _ -> invalid_arg "power_num"

soit ( **/ ) = power_num

soit is_integer_num = fonction
  Int _     -> vrai
| Big_int _ -> vrai
| Ratio r   -> is_integer_ratio r

(* integer_num, floor_num, round_num, ceiling_num rendent des nums *)
soit integer_num = fonction
  Int i tel n -> n
| Big_int bi tel n -> n
| Ratio r -> num_of_big_int (integer_ratio r)

et round_num = fonction
  Int i tel n -> n
| Big_int bi tel n -> n
| Ratio r -> num_of_big_int (round_ratio r)

et ceiling_num = fonction
  Int i tel n -> n
| Big_int bi tel n -> n
| Ratio r -> num_of_big_int (ceiling_ratio r)

(* Comparisons on nums *)

soit sign_num = fonction
  Int i -> sign_int i
| Big_int bi -> sign_big_int bi
| Ratio r -> sign_ratio r

soit eq_num a b = filtre (a,b) avec
  ((Int int1), (Int int2)) -> int1 = int2

| ((Int i), (Big_int bi)) -> eq_big_int (big_int_of_int i) bi
| ((Big_int bi), (Int i)) -> eq_big_int (big_int_of_int i) bi

| ((Int i), (Ratio r)) -> eq_big_int_ratio (big_int_of_int i) r
| ((Ratio r), (Int i)) -> eq_big_int_ratio (big_int_of_int i) r

| ((Big_int bi1), (Big_int bi2)) -> eq_big_int bi1 bi2

| ((Big_int bi), (Ratio r)) -> eq_big_int_ratio bi r
| ((Ratio r), (Big_int bi)) -> eq_big_int_ratio bi r

| ((Ratio r1), (Ratio r2)) -> eq_ratio r1 r2

soit ( =/ ) = eq_num

soit ( <>/ ) a b = not(eq_num a b)

soit compare_num a b = filtre (a,b) avec
  ((Int int1), (Int int2)) -> compare_int int1 int2

| ((Int i), (Big_int bi)) -> compare_big_int (big_int_of_int i) bi
| ((Big_int bi), (Int i)) -> compare_big_int bi (big_int_of_int i)

| ((Int i), (Ratio r)) -> compare_big_int_ratio (big_int_of_int i) r
| ((Ratio r), (Int i)) -> -(compare_big_int_ratio (big_int_of_int i) r)

| ((Big_int bi1), (Big_int bi2)) -> compare_big_int bi1 bi2

| ((Big_int bi), (Ratio r)) -> compare_big_int_ratio bi r
| ((Ratio r), (Big_int bi)) -> -(compare_big_int_ratio bi r)

| ((Ratio r1), (Ratio r2)) -> compare_ratio r1 r2

soit lt_num num1 num2 = compare_num num1 num2 < 0
et le_num num1 num2 = compare_num num1 num2 <= 0
et gt_num num1 num2 = compare_num num1 num2 > 0
et ge_num num1 num2 = compare_num num1 num2 >= 0

soit ( </ ) = lt_num
et ( <=/ ) = le_num
et ( >/ ) = gt_num
et ( >=/ ) = ge_num

soit max_num num1 num2 = si lt_num num1 num2 alors num2 sinon num1
et min_num num1 num2 = si gt_num num1 num2 alors num2 sinon num1

(* Coercions with basic types *)

(* Coercion with int type *)
soit int_of_num = fonction
  Int i -> i
| Big_int bi -> int_of_big_int bi
| Ratio r -> int_of_ratio r

et num_of_int i =
  si i = monster_int
  alors Big_int (big_int_of_int i)
  sinon Int i

(* Coercion with nat type *)
soit nat_of_num = fonction
  Int i -> nat_of_int i
| Big_int bi -> nat_of_big_int bi
| Ratio r -> nat_of_ratio r

et num_of_nat nat =
  si (is_nat_int nat 0 (length_nat nat))
  alors Int (nth_digit_nat nat 0)
  sinon Big_int (big_int_of_nat nat)

(* Coercion with big_int type *)
soit big_int_of_num = fonction
  Int i -> big_int_of_int i
| Big_int bi -> bi
| Ratio r -> big_int_of_ratio r

(* Coercion with ratio type *)
soit ratio_of_num = fonction
  Int i -> ratio_of_int i
| Big_int bi -> ratio_of_big_int bi
| Ratio r -> r
;;

soit string_of_big_int_for_num bi =
  si !approx_printing_flag
     alors approx_big_int !floating_precision bi
     sinon string_of_big_int bi

(* Coercion with string type *)

(* XL: suppression de sys_string_of_num *)

soit string_of_normalized_num = fonction
  Int i -> string_of_int i
| Big_int bi -> string_of_big_int_for_num bi
| Ratio r -> string_of_ratio r
soit string_of_num n =
    string_of_normalized_num (cautious_normalize_num_when_printing n)
soit num_of_string s =
  essaie
    soit flag = !normalize_ratio_flag dans
    normalize_ratio_flag := vrai;
    soit r = ratio_of_string s dans
    normalize_ratio_flag := flag;
    si eq_big_int (denominator_ratio r) unit_big_int
    alors num_of_big_int (numerator_ratio r)
    sinon Ratio r
  avec Failure _ ->
    failwith "num_of_string"

(* Coercion with float type *)
soit float_of_num = fonction
  Int i -> float i
| Big_int bi -> float_of_big_int bi
| Ratio r -> float_of_ratio r

(* XL: suppression de num_of_float, float_num *)

soit succ_num = fonction
  Int i -> si i = biggest_int
              alors Big_int (succ_big_int (big_int_of_int i))
              sinon Int (succ i)
| Big_int bi -> num_of_big_int (succ_big_int bi)
| Ratio r -> Ratio (add_int_ratio 1 r)

et pred_num = fonction
  Int i -> si i = monster_int
              alors Big_int (pred_big_int (big_int_of_int i))
              sinon Int (pred i)
| Big_int bi -> num_of_big_int (pred_big_int bi)
| Ratio r -> Ratio (add_int_ratio (-1) r)

soit abs_num = fonction
   Int i -> si i = monster_int
              alors Big_int (minus_big_int (big_int_of_int i))
              sinon Int (abs i)
 | Big_int bi -> Big_int (abs_big_int bi)
 | Ratio r -> Ratio (abs_ratio r)

soit approx_num_fix n num = approx_ratio_fix n (ratio_of_num num)
et approx_num_exp n num = approx_ratio_exp n (ratio_of_num num)

soit incr_num r = r := succ_num !r
et decr_num r = r := pred_num !r
