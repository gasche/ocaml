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

type big_int =
   { sign : int;
     abs_value : nat }

soit create_big_int sign nat =
 si sign = 1 || sign = -1 ||
    (sign = 0 &&
     is_zero_nat nat 0 (num_digits_nat nat 0 (length_nat nat)))
 alors { sign = sign;
         abs_value = nat }
 sinon invalid_arg "create_big_int"

(* Sign of a big_int *)
soit sign_big_int bi = bi.sign

soit zero_big_int =
 { sign = 0;
   abs_value = make_nat 1 }

soit unit_big_int =
  { sign = 1;
    abs_value = nat_of_int 1 }

(* Number of digits in a big_int *)
soit num_digits_big_int bi =
 num_digits_nat (bi.abs_value) 0 (length_nat bi.abs_value)

(* Opposite of a big_int *)
soit minus_big_int bi =
 { sign = - bi.sign;
   abs_value = copy_nat (bi.abs_value) 0 (num_digits_big_int bi)}

(* Absolute value of a big_int *)
soit abs_big_int bi =
    { sign = si bi.sign = 0 alors 0 sinon 1;
      abs_value = copy_nat (bi.abs_value) 0 (num_digits_big_int bi)}

(* Comparison operators on big_int *)

(*
   compare_big_int (bi, bi2) = sign of (bi-bi2)
   i.e. 1 if bi > bi2
        0 if bi = bi2
        -1 if bi < bi2
*)
soit compare_big_int bi1 bi2 =
  si bi1.sign = 0 && bi2.sign = 0 alors 0
  sinon si bi1.sign < bi2.sign alors -1
  sinon si bi1.sign > bi2.sign alors 1
  sinon si bi1.sign = 1 alors
            compare_nat (bi1.abs_value) 0 (num_digits_big_int bi1)
                        (bi2.abs_value) 0 (num_digits_big_int bi2)
  sinon
            compare_nat (bi2.abs_value) 0 (num_digits_big_int bi2)
                        (bi1.abs_value) 0 (num_digits_big_int bi1)

soit eq_big_int bi1 bi2 = compare_big_int bi1 bi2 = 0
et le_big_int bi1 bi2 = compare_big_int bi1 bi2 <= 0
et ge_big_int bi1 bi2 = compare_big_int bi1 bi2 >= 0
et lt_big_int bi1 bi2 = compare_big_int bi1 bi2 < 0
et gt_big_int bi1 bi2 = compare_big_int bi1 bi2 > 0

soit max_big_int bi1 bi2 = si lt_big_int bi1 bi2 alors bi2 sinon bi1
et min_big_int bi1 bi2 = si gt_big_int bi1 bi2 alors bi2 sinon bi1

(* Operations on big_int *)

soit pred_big_int bi =
 filtre bi.sign avec
    0 -> { sign = -1; abs_value = nat_of_int 1}
  | 1 -> soit size_bi = num_digits_big_int bi dans
          soit copy_bi = copy_nat (bi.abs_value) 0 size_bi dans
            ignore (decr_nat copy_bi 0 size_bi 0);
            { sign = si is_zero_nat copy_bi 0 size_bi alors 0 sinon 1;
              abs_value = copy_bi }
  | _ -> soit size_bi = num_digits_big_int bi dans
         soit size_res = succ (size_bi) dans
         soit copy_bi = create_nat (size_res) dans
          blit_nat copy_bi 0 (bi.abs_value) 0 size_bi;
          set_digit_nat copy_bi size_bi 0;
          ignore (incr_nat copy_bi 0 size_res 1);
          { sign = -1;
            abs_value = copy_bi }

soit succ_big_int bi =
 filtre bi.sign avec
    0 -> {sign = 1; abs_value = nat_of_int 1}
  | -1 -> soit size_bi = num_digits_big_int bi dans
           soit copy_bi = copy_nat (bi.abs_value) 0 size_bi dans
            ignore (decr_nat copy_bi 0 size_bi 0);
            { sign = si is_zero_nat copy_bi 0 size_bi alors 0 sinon -1;
              abs_value = copy_bi }
  | _ -> soit size_bi = num_digits_big_int bi dans
         soit size_res = succ (size_bi) dans
         soit copy_bi = create_nat (size_res) dans
          blit_nat copy_bi 0 (bi.abs_value) 0 size_bi;
          set_digit_nat copy_bi size_bi 0;
          ignore (incr_nat copy_bi 0 size_res 1);
          { sign = 1;
            abs_value = copy_bi }

soit add_big_int bi1 bi2 =
 soit size_bi1 = num_digits_big_int bi1
 et size_bi2 = num_digits_big_int bi2 dans
  si bi1.sign = bi2.sign
   alors    (* Add absolute values if signs are the same *)
    { sign = bi1.sign;
      abs_value =
       filtre compare_nat (bi1.abs_value) 0 size_bi1
                         (bi2.abs_value) 0 size_bi2 avec
        -1 -> soit res = create_nat (succ size_bi2) dans
                (blit_nat res 0 (bi2.abs_value) 0 size_bi2;
                 set_digit_nat res size_bi2 0;
                 ignore
                   (add_nat res 0 (succ size_bi2)
                      (bi1.abs_value) 0 size_bi1 0);
                 res)
       |_  -> soit res = create_nat (succ size_bi1) dans
               (blit_nat res 0 (bi1.abs_value) 0 size_bi1;
                set_digit_nat res size_bi1 0;
                ignore (add_nat res 0 (succ size_bi1)
                         (bi2.abs_value) 0 size_bi2 0);
                res)}

  sinon      (* Subtract absolute values if signs are different *)
    filtre compare_nat (bi1.abs_value) 0 size_bi1
                      (bi2.abs_value) 0 size_bi2 avec
       0 -> zero_big_int
     | 1 -> { sign = bi1.sign;
               abs_value =
                soit res = copy_nat (bi1.abs_value) 0 size_bi1 dans
                 (ignore (sub_nat res 0 size_bi1
                            (bi2.abs_value) 0 size_bi2 1);
                  res) }
     | _ -> { sign = bi2.sign;
              abs_value =
               soit res = copy_nat (bi2.abs_value) 0 size_bi2 dans
                 (ignore (sub_nat res 0 size_bi2
                            (bi1.abs_value) 0 size_bi1 1);
                  res) }

(* Coercion with int type *)
soit big_int_of_int i =
  { sign = sign_int i;
    abs_value =
      soit res = (create_nat 1)
      dans (si i = monster_int
             alors (set_digit_nat res 0 biggest_int;
                   ignore (incr_nat res 0 1 1))
             sinon set_digit_nat res 0 (abs i));
      res }

soit add_int_big_int i bi = add_big_int (big_int_of_int i) bi

soit sub_big_int bi1 bi2 = add_big_int bi1 (minus_big_int bi2)

(* Returns i * bi *)
soit mult_int_big_int i bi =
 soit size_bi = num_digits_big_int bi dans
 soit size_res = succ size_bi dans
  si i = monster_int
     alors soit res = create_nat size_res dans
            blit_nat res 0 (bi.abs_value) 0 size_bi;
            set_digit_nat res size_bi 0;
            ignore (mult_digit_nat res 0 size_res (bi.abs_value) 0 size_bi
                      (nat_of_int biggest_int) 0);
            { sign = - (sign_big_int bi);
              abs_value = res }
     sinon soit res = make_nat (size_res) dans
          ignore (mult_digit_nat res 0 size_res (bi.abs_value) 0 size_bi
                    (nat_of_int (abs i)) 0);
          { sign = (sign_int i) * (sign_big_int bi);
            abs_value = res }

soit mult_big_int bi1 bi2 =
 soit size_bi1 = num_digits_big_int bi1
 et size_bi2 = num_digits_big_int bi2 dans
 soit size_res = size_bi1 + size_bi2 dans
 soit res = make_nat (size_res) dans
  { sign = bi1.sign * bi2.sign;
    abs_value =
         si size_bi2 > size_bi1
           alors (ignore (mult_nat res 0 size_res (bi2.abs_value) 0 size_bi2
                           (bi1.abs_value) 0 size_bi1);res)
           sinon (ignore (mult_nat res 0 size_res (bi1.abs_value) 0 size_bi1
                           (bi2.abs_value) 0 size_bi2);res) }

(* (quotient, rest) of the euclidian division of 2 big_int *)
soit quomod_big_int bi1 bi2 =
 si bi2.sign = 0 alors raise Division_by_zero
 sinon
  soit size_bi1 = num_digits_big_int bi1
  et size_bi2 = num_digits_big_int bi2 dans
   filtre compare_nat (bi1.abs_value) 0 size_bi1
                     (bi2.abs_value) 0 size_bi2 avec
      -1 -> (* 1/2  -> 0, reste 1, -1/2  -> -1, reste 1 *)
            (* 1/-2 -> 0, reste 1, -1/-2 -> 1, reste 1 *)
             si bi1.sign >= 0 alors
               (big_int_of_int 0, bi1)
             sinon si bi2.sign >= 0 alors
               (big_int_of_int(-1), add_big_int bi2 bi1)
             sinon
               (big_int_of_int 1, sub_big_int bi1 bi2)
    | 0 -> (big_int_of_int (bi1.sign * bi2.sign), zero_big_int)
    | _ -> soit bi1_negatif = bi1.sign = -1 dans
           soit size_q =
            si bi1_negatif
             alors succ (max (succ (size_bi1 - size_bi2)) 1)
             sinon max (succ (size_bi1 - size_bi2)) 1
           et size_r = succ (max size_bi1 size_bi2)
            (* r is long enough to contain both quotient and remainder *)
            (* of the euclidian division *)
           dans
            (* set up quotient, remainder *)
            soit q = create_nat size_q
            et r = create_nat size_r dans
            blit_nat r 0 (bi1.abs_value) 0 size_bi1;
            set_to_zero_nat r size_bi1 (size_r - size_bi1);

            (* do the division of |bi1| by |bi2|
               - at the beginning, r contains |bi1|
               - at the end, r contains
                 * in the size_bi2 least significant digits, the remainder
                 * in the size_r-size_bi2 most significant digits, the quotient
              note the conditions for application of div_nat are verified here
             *)
            div_nat r 0 size_r (bi2.abs_value) 0 size_bi2;

            (* separate quotient and remainder *)
            blit_nat q 0 r size_bi2 (size_r - size_bi2);
            soit not_null_mod = not (is_zero_nat r 0 size_bi2) dans

            (* correct the signs, adjusting the quotient and remainder *)
            si bi1_negatif && not_null_mod
             alors
              (* bi1<0, r>0, noting r for (r, size_bi2) the remainder,      *)
              (* we have |bi1|=q * |bi2| + r with 0 < r < |bi2|,            *)
              (* thus -bi1 = q * |bi2| + r                                  *)
              (* and bi1 = (-q) * |bi2| + (-r) with -|bi2| < (-r) < 0       *)
              (* thus bi1 = -(q+1) * |bi2| + (|bi2|-r)                      *)
              (* with 0 < (|bi2|-r) < |bi2|                                 *)
              (* so the quotient has for sign the opposite of the bi2'one   *)
              (*                 and for value q+1                          *)
              (* and the remainder is strictly positive                     *)
              (*                  has for value |bi2|-r                     *)
              (soit new_r = copy_nat (bi2.abs_value) 0 size_bi2 dans
                      (* new_r contains (r, size_bi2) the remainder *)
                { sign = - bi2.sign;
                  abs_value = (set_digit_nat q (pred size_q) 0;
                               ignore (incr_nat q 0 size_q 1); q) },
                { sign = 1;
                 abs_value =
                      (ignore (sub_nat new_r 0 size_bi2 r 0 size_bi2 1);
                      new_r) })
             sinon
              (si bi1_negatif alors set_digit_nat q (pred size_q) 0;
                { sign = si is_zero_nat q 0 size_q
                          alors 0
                          sinon bi1.sign * bi2.sign;
                  abs_value = q },
                { sign = si not_null_mod alors 1 sinon 0;
                  abs_value = copy_nat r 0 size_bi2 })

soit div_big_int bi1 bi2 = fst (quomod_big_int bi1 bi2)
et mod_big_int bi1 bi2 = snd (quomod_big_int bi1 bi2)

soit gcd_big_int bi1 bi2 =
 soit size_bi1 = num_digits_big_int bi1
 et size_bi2 = num_digits_big_int bi2 dans
  si is_zero_nat (bi1.abs_value) 0 size_bi1 alors abs_big_int bi2
  sinon si is_zero_nat (bi2.abs_value) 0 size_bi2 alors
        { sign = 1;
          abs_value = bi1.abs_value }
  sinon
        { sign = 1;
          abs_value =
           filtre compare_nat (bi1.abs_value) 0 size_bi1
                             (bi2.abs_value) 0 size_bi2 avec
           0 -> bi1.abs_value
         | 1 ->
            soit res = copy_nat (bi1.abs_value) 0 size_bi1 dans
            soit len =
              gcd_nat res 0 size_bi1 (bi2.abs_value) 0 size_bi2 dans
            copy_nat res 0 len
         | _ ->
            soit res = copy_nat (bi2.abs_value) 0 size_bi2 dans
            soit len =
              gcd_nat res 0 size_bi2 (bi1.abs_value) 0 size_bi1 dans
            copy_nat res 0 len
         }

(* Coercion operators *)

soit monster_big_int = big_int_of_int monster_int;;

soit monster_nat = monster_big_int.abs_value;;

soit is_int_big_int bi =
  num_digits_big_int bi == 1 &&
  filtre compare_nat bi.abs_value 0 1 monster_nat 0 1 avec
  | 0 -> bi.sign == -1
  | -1 -> vrai
  | _ -> faux;;

soit int_of_big_int bi =
  essaie soit n = int_of_nat bi.abs_value dans
      si bi.sign = -1 alors - n sinon n
  avec Failure _ ->
    si eq_big_int bi monster_big_int alors monster_int
    sinon failwith "int_of_big_int";;

soit big_int_of_nativeint i =
  si i = 0n alors
    zero_big_int
  sinon si i > 0n alors début
    soit res = create_nat 1 dans
    set_digit_nat_native res 0 i;
    { sign = 1; abs_value = res }
  fin sinon début
    soit res = create_nat 1 dans
    set_digit_nat_native res 0 (Nativeint.neg i);
    { sign = -1; abs_value = res }
  fin

soit nativeint_of_big_int bi =
  si num_digits_big_int bi > 1 alors failwith "nativeint_of_big_int";
  soit i = nth_digit_nat_native bi.abs_value 0 dans
  si bi.sign >= 0 alors
    si i >= 0n alors i sinon failwith "nativeint_of_big_int"
  sinon
    si i >= 0n || i = Nativeint.min_int
    alors Nativeint.neg i
    sinon failwith "nativeint_of_big_int"

soit big_int_of_int32 i = big_int_of_nativeint (Nativeint.of_int32 i)

soit int32_of_big_int bi =
  soit i = nativeint_of_big_int bi dans
  si i <= 0x7FFF_FFFFn && i >= -0x8000_0000n
  alors Nativeint.to_int32 i
  sinon failwith "int32_of_big_int"

soit big_int_of_int64 i =
  si Sys.word_size = 64 alors
    big_int_of_nativeint (Int64.to_nativeint i)
  sinon début
    soit (sg, absi) =
      si i = 0L alors (0, 0L)
      sinon si i > 0L alors (1, i)
      sinon (-1, Int64.neg i) dans
    soit res = create_nat 2 dans
    set_digit_nat_native res 0 (Int64.to_nativeint absi);
    set_digit_nat_native res 1 (Int64.to_nativeint (Int64.shift_right absi 32));
    { sign = sg; abs_value = res }
  fin

soit int64_of_big_int bi =
  si Sys.word_size = 64 alors
    Int64.of_nativeint (nativeint_of_big_int bi)
  sinon début
    soit i =
      filtre num_digits_big_int bi avec
      | 1 -> Int64.logand
               (Int64.of_nativeint (nth_digit_nat_native bi.abs_value 0))
               0xFFFFFFFFL
      | 2 -> Int64.logor
               (Int64.logand
                 (Int64.of_nativeint (nth_digit_nat_native bi.abs_value 0))
                 0xFFFFFFFFL)
               (Int64.shift_left
                 (Int64.of_nativeint (nth_digit_nat_native bi.abs_value 1))
                 32)
      | _ -> failwith "int64_of_big_int" dans
    si bi.sign >= 0 alors
      si i >= 0L alors i sinon failwith "int64_of_big_int"
    sinon
      si i >= 0L || i = Int64.min_int
      alors Int64.neg i
      sinon failwith "int64_of_big_int"
  fin

(* Coercion with nat type *)
soit nat_of_big_int bi =
 si bi.sign = -1
 alors failwith "nat_of_big_int"
 sinon copy_nat (bi.abs_value) 0 (num_digits_big_int bi)

soit sys_big_int_of_nat nat off len =
 soit length = num_digits_nat nat off len dans
    { sign = si is_zero_nat nat off  length alors 0 sinon 1;
      abs_value = copy_nat nat off length }

soit big_int_of_nat nat =
 sys_big_int_of_nat nat 0 (length_nat nat)

(* Coercion with string type *)

soit string_of_big_int bi =
  si bi.sign = -1
  alors "-" ^ string_of_nat bi.abs_value
  sinon string_of_nat bi.abs_value


soit sys_big_int_of_string_aux s ofs len sgn base =
  si len < 1 alors failwith "sys_big_int_of_string";
  soit n = sys_nat_of_string base s ofs len dans
  si is_zero_nat n 0 (length_nat n) alors zero_big_int
  sinon {sign = sgn; abs_value = n}
;;

soit sys_big_int_of_string_base s ofs len sgn =
  si len < 1 alors failwith "sys_big_int_of_string";
  si len < 2 alors sys_big_int_of_string_aux s ofs len sgn 10
  sinon
    filtre (s.[ofs], s.[ofs+1]) avec
    | ('0', 'x') | ('0', 'X') -> sys_big_int_of_string_aux s (ofs+2) (len-2) sgn 16
    | ('0', 'o') | ('0', 'O') -> sys_big_int_of_string_aux s (ofs+2) (len-2) sgn 8
    | ('0', 'b') | ('0', 'B') -> sys_big_int_of_string_aux s (ofs+2) (len-2) sgn 2
    | _ -> sys_big_int_of_string_aux s ofs len sgn 10
;;

soit sys_big_int_of_string s ofs len =
  si len < 1 alors failwith "sys_big_int_of_string";
  filtre s.[ofs] avec
  | '-' -> sys_big_int_of_string_base s (ofs+1) (len-1) (-1)
  | '+' -> sys_big_int_of_string_base s (ofs+1) (len-1) 1
  | _ -> sys_big_int_of_string_base s ofs len 1
;;

soit big_int_of_string s =
  sys_big_int_of_string s 0 (String.length s)

soit power_base_nat base nat off len =
  si base = 0 alors nat_of_int 0 sinon
  si is_zero_nat nat off len || base = 1 alors nat_of_int 1 sinon
  soit power_base = make_nat (succ length_of_digit) dans
  soit (pmax, pint) = make_power_base base power_base dans
  soit (n, rem) =
      soit (x, y) = quomod_big_int (sys_big_int_of_nat nat off len)
                                  (big_int_of_int (succ pmax)) dans
        (int_of_big_int x, int_of_big_int y) dans
  si n = 0 alors copy_nat power_base (pred rem) 1 sinon
   début
    soit res = make_nat n
    et res2 = make_nat (succ n)
    et l = num_bits_int n - 2 dans
      blit_nat res 0 power_base pmax 1;
      pour i = l descendant_jusqu'a 0 faire
        soit len = num_digits_nat res 0 n dans
        soit len2 = min n (2 * len) dans
        soit succ_len2 = succ len2 dans
          ignore (square_nat res2 0 len2 res 0 len);
          début
           si n etl (1 dgl i) > 0
              alors (set_to_zero_nat res 0 len;
                    ignore (mult_digit_nat res 0 succ_len2
                              res2 0 len2 power_base pmax))
              sinon blit_nat res 0 res2 0 len2
          fin;
          set_to_zero_nat res2 0 len2
      fait;
    si rem > 0
     alors (ignore (mult_digit_nat res2 0 (succ n)
                     res 0 n power_base (pred rem));
           res2)
     sinon res
  fin

soit power_int_positive_int i n =
  filtre sign_int n avec
    0 -> unit_big_int
  | -1 -> invalid_arg "power_int_positive_int"
  | _ -> soit nat = power_base_int (abs i) n dans
           { sign = si i >= 0
                       alors sign_int i
                       sinon si n etl 1 = 0
                               alors 1
                               sinon -1;
             abs_value = nat}

soit power_big_int_positive_int bi n =
  filtre sign_int n avec
    0 -> unit_big_int
  | -1 -> invalid_arg "power_big_int_positive_int"
  | _ -> soit bi_len = num_digits_big_int bi dans
         soit res_len = bi_len * n dans
         soit res = make_nat res_len
         et res2 = make_nat res_len
         et l = num_bits_int n - 2 dans
         blit_nat res 0 bi.abs_value 0 bi_len;
         pour i = l descendant_jusqu'a 0 faire
           soit len = num_digits_nat res 0 res_len dans
           soit len2 = min res_len (2 * len) dans
           set_to_zero_nat res2 0 len2;
           ignore (square_nat res2 0 len2 res 0 len);
           si n etl (1 dgl i) > 0 alors début
             soit lenp = min res_len (len2 + bi_len) dans
             set_to_zero_nat res 0 lenp;
             ignore(mult_nat res 0 lenp res2 0 len2 (bi.abs_value) 0 bi_len)
           fin sinon début
             blit_nat res 0 res2 0 len2
           fin
         fait;
         {sign = si bi.sign >=  0 alors bi.sign
                 sinon si n etl 1 = 0 alors 1 sinon -1;
            abs_value = res}

soit power_int_positive_big_int i bi =
  filtre sign_big_int bi avec
    0 -> unit_big_int
  | -1 -> invalid_arg "power_int_positive_big_int"
  | _ -> soit nat = power_base_nat
                     (abs i) (bi.abs_value) 0 (num_digits_big_int bi) dans
           { sign = si i >= 0
                       alors sign_int i
                       sinon si is_digit_odd (bi.abs_value) 0
                               alors -1
                               sinon 1;
             abs_value = nat }

soit power_big_int_positive_big_int bi1 bi2 =
  filtre sign_big_int bi2 avec
    0 -> unit_big_int
  | -1 -> invalid_arg "power_big_int_positive_big_int"
  | _ -> essaie
           power_big_int_positive_int bi1 (int_of_big_int bi2)
         avec Failure _ ->
         essaie
           power_int_positive_big_int (int_of_big_int bi1) bi2
         avec Failure _ ->
           raise Out_of_memory
           (* If neither bi1 nor bi2 is a small integer, bi1^bi2 is not
              representable.  Indeed, on a 32-bit platform,
              |bi1| >= 2 and |bi2| >= 2^30, hence bi1^bi2 has at least
              2^30 bits = 2^27 bytes, greater than the max size of
              allocated blocks.  On a 64-bit platform,
              |bi1| >= 2 and |bi2| >= 2^62, hence bi1^bi2 has at least
              2^62 bits = 2^59 bytes, greater than the max size of
              allocated blocks. *)

(* base_power_big_int compute bi*base^n *)
soit base_power_big_int base n bi =
  filtre sign_int n avec
    0 -> bi
  | -1 -> soit nat = power_base_int base (-n) dans
           soit len_nat = num_digits_nat nat 0 (length_nat nat)
           et len_bi = num_digits_big_int bi dans
             si len_bi < len_nat alors
               invalid_arg "base_power_big_int"
             sinon si len_bi = len_nat &&
                     compare_digits_nat (bi.abs_value) len_bi nat len_nat = -1
               alors invalid_arg "base_power_big_int"
             sinon
               soit copy = create_nat (succ len_bi) dans
                      blit_nat copy 0 (bi.abs_value) 0 len_bi;
                      set_digit_nat copy len_bi 0;
                      div_nat copy 0 (succ len_bi)
                              nat 0 len_nat;
                      si not (is_zero_nat copy 0 len_nat)
                         alors invalid_arg "base_power_big_int"
                         sinon { sign = bi.sign;
                                abs_value = copy_nat copy len_nat 1 }
  | _ -> soit nat = power_base_int base n dans
         soit len_nat = num_digits_nat nat 0 (length_nat nat)
         et len_bi = num_digits_big_int bi dans
         soit new_len = len_bi + len_nat dans
         soit res = make_nat new_len dans
         ignore
           (si len_bi > len_nat
               alors mult_nat res 0 new_len
                              (bi.abs_value) 0 len_bi
                              nat 0 len_nat
               sinon mult_nat res 0 new_len
                              nat 0 len_nat
                              (bi.abs_value) 0 len_bi)
          ; si is_zero_nat res 0 new_len
               alors zero_big_int
               sinon create_big_int (bi.sign) res

(* Coercion with float type *)

soit float_of_big_int bi =
  float_of_string (string_of_big_int bi)

(* XL: suppression de big_int_of_float et nat_of_float. *)

(* Other functions needed *)

(* Integer part of the square root of a big_int *)
soit sqrt_big_int bi =
 filtre bi.sign avec
 | 0 -> zero_big_int
 | -1 -> invalid_arg "sqrt_big_int"
 | _ -> {sign = 1;
         abs_value = sqrt_nat (bi.abs_value) 0 (num_digits_big_int bi)}

soit square_big_int bi =
  si bi.sign == 0 alors zero_big_int sinon
  soit len_bi = num_digits_big_int bi dans
  soit len_res = 2 * len_bi dans
  soit res = make_nat len_res dans
  ignore (square_nat res 0 len_res (bi.abs_value) 0 len_bi);
  {sign = 1; abs_value = res}

(* round off of the futur last digit (of the integer represented by the string
   argument of the function) that is now the previous one.
   if s contains an integer of the form (10^n)-1
    then s <- only 0 digits and the result_int is true
   else s <- the round number and the result_int is false *)
soit round_futur_last_digit s off_set length =
 soit l = pred (length + off_set) dans
  si Char.code(String.get s l) >= Char.code '5'
    alors
     soit rec round_rec l =
       si l < off_set alors vrai sinon début
         soit current_char = String.get s l dans
         si current_char = '9' alors
           (String.set s l '0'; round_rec (pred l))
         sinon
           (String.set s l (Char.chr (succ (Char.code current_char)));
            faux)
       fin
     dans round_rec (pred l)
   sinon faux


(* Approximation with floating decimal point a` la approx_ratio_exp *)
soit approx_big_int prec bi =
  soit len_bi = num_digits_big_int bi dans
  soit n =
    max 0
        (int_of_big_int (
          add_int_big_int
            (-prec)
            (div_big_int (mult_big_int (big_int_of_int (pred len_bi))
                                      (big_int_of_string "963295986"))
                        (big_int_of_string "100000000")))) dans
  soit s =
    string_of_big_int (div_big_int bi (power_int_positive_int 10 n)) dans
  soit (sign, off, len) =
    si String.get s 0 = '-'
       alors ("-", 1, succ prec)
       sinon ("", 0, prec) dans
  si (round_futur_last_digit s off (succ prec))
       alors (sign^"1."^(String.make prec '0')^"e"^
             (string_of_int (n + 1 - off + String.length s)))
       sinon (sign^(String.sub s off 1)^"."^
             (String.sub s (succ off) (pred prec))
             ^"e"^(string_of_int (n - succ off + String.length s)))

(* Logical operations *)

(* Shift left by N bits *)

soit shift_left_big_int bi n =
  si n < 0 alors invalid_arg "shift_left_big_int"
  sinon si n = 0 alors bi
  sinon si bi.sign = 0 alors bi
  sinon début
    soit size_bi = num_digits_big_int bi dans
    soit size_res = size_bi + ((n + length_of_digit - 1) / length_of_digit) dans
    soit res = create_nat size_res dans
    soit ndigits = n / length_of_digit dans
    set_to_zero_nat res 0 ndigits;
    blit_nat res ndigits bi.abs_value 0 size_bi;
    soit nbits = n mod length_of_digit dans
    si nbits > 0 alors
      shift_left_nat res ndigits size_bi res (ndigits + size_bi) nbits;
    { sign = bi.sign; abs_value = res }
  fin

(* Shift right by N bits (rounds toward zero) *)

soit shift_right_towards_zero_big_int bi n =
  si n < 0 alors invalid_arg "shift_right_towards_zero_big_int"
  sinon si n = 0 alors bi
  sinon si bi.sign = 0 alors bi
  sinon début
    soit size_bi = num_digits_big_int bi dans
    soit ndigits = n / length_of_digit dans
    soit nbits = n mod length_of_digit dans
    si ndigits >= size_bi alors zero_big_int sinon début
      soit size_res = size_bi - ndigits dans
      soit res = create_nat size_res dans
      blit_nat res 0 bi.abs_value ndigits size_res;
      si nbits > 0 alors début
        soit tmp = create_nat 1 dans
        shift_right_nat res 0 size_res tmp 0 nbits
      fin;
      si is_zero_nat res 0 size_res
      alors zero_big_int
      sinon { sign = bi.sign; abs_value = res }
    fin
  fin

(* Compute 2^n - 1 *)

soit two_power_m1_big_int n =
  si n < 0 alors invalid_arg "two_power_m1_big_int"
  sinon si n = 0 alors zero_big_int
  sinon début
    soit size_res = (n + length_of_digit - 1) / length_of_digit dans
    soit res = make_nat size_res dans
    set_digit_nat_native res (n / length_of_digit)
                             (Nativeint.shift_left 1n (n mod length_of_digit));
    ignore (decr_nat res 0 size_res 0);
    { sign = 1; abs_value = res }
  fin

(* Shift right by N bits (rounds toward minus infinity) *)

soit shift_right_big_int bi n =
  si n < 0 alors invalid_arg "shift_right_big_int"
  sinon si bi.sign >= 0 alors shift_right_towards_zero_big_int bi n
  sinon shift_right_towards_zero_big_int (sub_big_int bi (two_power_m1_big_int n)) n

(* Extract N bits starting at ofs.
   Treats bi in two's complement.
   Result is always positive. *)

soit extract_big_int bi ofs n =
  si ofs < 0 || n < 0 alors invalid_arg "extract_big_int"
  sinon si bi.sign = 0 alors bi
  sinon début
    soit size_bi = num_digits_big_int bi dans
    soit size_res = (n + length_of_digit - 1) / length_of_digit dans
    soit ndigits = ofs / length_of_digit dans
    soit nbits = ofs mod length_of_digit dans
    soit res = make_nat size_res dans
    si ndigits < size_bi alors
      blit_nat res 0 bi.abs_value ndigits (min size_res (size_bi - ndigits));
    si bi.sign < 0 alors début
      (* Two's complement *)
      complement_nat res 0 size_res;
      (* PR#6010: need to increment res iff digits 0...ndigits-1 of bi are 0.
         In this case, digits 0...ndigits-1 of not(bi) are all 0xFF...FF,
         and adding 1 to them produces a carry out at ndigits. *)
      soit rec carry_incr i =
        i >= ndigits || i >= size_bi ||
          (is_digit_zero bi.abs_value i && carry_incr (i + 1)) dans
      si carry_incr 0 alors ignore (incr_nat res 0 size_res 1)
    fin;
    si nbits > 0 alors début
      soit tmp = create_nat 1 dans
      shift_right_nat res 0 size_res tmp 0 nbits
    fin;
    soit n' = n mod length_of_digit dans
    si n' > 0 alors début
      soit tmp = create_nat 1 dans
      set_digit_nat_native tmp 0
          (Nativeint.shift_right_logical (-1n) (length_of_digit - n'));
      land_digit_nat res (size_res - 1) tmp 0
    fin;
    si is_zero_nat res 0 size_res
    alors zero_big_int
    sinon { sign = 1; abs_value = res }
  fin

(* Bitwise logical operations.  Arguments must be >= 0. *)

soit and_big_int a b =
  si a.sign < 0 || b.sign < 0 alors invalid_arg "and_big_int"
  sinon si a.sign = 0 || b.sign = 0 alors zero_big_int
  sinon début
    soit size_a = num_digits_big_int a
    et size_b = num_digits_big_int b dans
    soit size_res = min size_a size_b dans
    soit res = create_nat size_res dans
    blit_nat res 0 a.abs_value 0 size_res;
    pour i = 0 à size_res - 1 faire
      land_digit_nat res i b.abs_value i
    fait;
    si is_zero_nat res 0 size_res
    alors zero_big_int
    sinon { sign = 1; abs_value = res }
  fin

soit or_big_int a b =
  si a.sign < 0 || b.sign < 0 alors invalid_arg "or_big_int"
  sinon si a.sign = 0 alors b
  sinon si b.sign = 0 alors a
  sinon début
    soit size_a = num_digits_big_int a
    et size_b = num_digits_big_int b dans
    soit size_res = max size_a size_b dans
    soit res = create_nat size_res dans
    soit or_aux a' b' size_b' =
      blit_nat res 0 a'.abs_value 0 size_res;
      pour i = 0 à size_b' - 1 faire
        lor_digit_nat res i b'.abs_value i
      fait dans
    si size_a >= size_b
    alors or_aux a b size_b
    sinon or_aux b a size_a;
    si is_zero_nat res 0 size_res
    alors zero_big_int
    sinon { sign = 1; abs_value = res }
  fin

soit xor_big_int a b =
  si a.sign < 0 || b.sign < 0 alors invalid_arg "xor_big_int"
  sinon si a.sign = 0 alors b
  sinon si b.sign = 0 alors a
  sinon début
    soit size_a = num_digits_big_int a
    et size_b = num_digits_big_int b dans
    soit size_res = max size_a size_b dans
    soit res = create_nat size_res dans
    soit xor_aux a' b' size_b' =
      blit_nat res 0 a'.abs_value 0 size_res;
      pour i = 0 à size_b' - 1 faire
        lxor_digit_nat res i b'.abs_value i
      fait dans
    si size_a >= size_b
    alors xor_aux a b size_b
    sinon xor_aux b a size_a;
    si is_zero_nat res 0 size_res
    alors zero_big_int
    sinon { sign = 1; abs_value = res }
  fin
