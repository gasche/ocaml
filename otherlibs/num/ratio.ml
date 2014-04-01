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

ouvre Int_misc
ouvre Nat
ouvre Big_int
ouvre Arith_flags

(* Definition of the type ratio :
   Conventions :
   - the denominator is always a positive number
   - the sign of n/0 is the sign of n
These convention is automatically respected when a ratio is created with
the create_ratio primitive
*)

type ratio = { modifiable numerator : big_int;
               modifiable denominator : big_int;
               modifiable normalized : bool}

soit failwith_zero name =
    soit s = "infinite or undefined rational number" dans
    failwith (si String.length name = 0 alors s sinon name ^ " " ^ s)

soit numerator_ratio r = r.numerator
et denominator_ratio r = r.denominator

soit null_denominator r = sign_big_int r.denominator = 0

soit verify_null_denominator r =
  si sign_big_int r.denominator = 0
     alors (si !error_when_null_denominator_flag
           alors (failwith_zero "")
           sinon vrai)
     sinon faux

soit sign_ratio r = sign_big_int r.numerator

(* Physical normalization of rational numbers *)
(* 1/0, 0/0 and -1/0 are the normalized forms for n/0 numbers *)
soit normalize_ratio r =
  si r.normalized alors r
  sinon si verify_null_denominator r alors début
    r.numerator <- big_int_of_int (sign_big_int r.numerator);
    r.normalized <- vrai;
    r
  fin sinon début
    soit p = gcd_big_int r.numerator r.denominator dans
    si eq_big_int p unit_big_int
    alors début
      r.normalized <- vrai; r
    fin sinon début
      r.numerator <- div_big_int (r.numerator) p;
      r.denominator <- div_big_int (r.denominator) p;
      r.normalized <- vrai; r
    fin
  fin

soit cautious_normalize_ratio r =
 si (!normalize_ratio_flag) alors (normalize_ratio r) sinon r

soit cautious_normalize_ratio_when_printing r =
 si (!normalize_ratio_when_printing_flag) alors (normalize_ratio r) sinon r

soit create_ratio bi1 bi2 =
 filtre sign_big_int bi2 avec
       -1 -> cautious_normalize_ratio
               { numerator = minus_big_int bi1;
                 denominator = minus_big_int bi2;
                 normalized = faux }
     | 0 -> si !error_when_null_denominator_flag
                alors (failwith_zero "create_ratio")
                sinon cautious_normalize_ratio
                    { numerator = bi1; denominator = bi2; normalized = faux }
     | _ ->  cautious_normalize_ratio
              { numerator = bi1; denominator = bi2; normalized = faux }

soit create_normalized_ratio bi1 bi2 =
 filtre sign_big_int bi2 avec
  -1 -> { numerator = minus_big_int bi1;
          denominator = minus_big_int bi2;
          normalized = vrai }
|  0 -> si !error_when_null_denominator_flag
            alors failwith_zero "create_normalized_ratio"
            sinon { numerator = bi1; denominator = bi2; normalized = vrai }
|  _  -> { numerator = bi1; denominator = bi2; normalized = vrai }

soit is_normalized_ratio r = r.normalized

soit report_sign_ratio r bi =
  si sign_ratio r = -1
  alors minus_big_int bi
  sinon bi

soit abs_ratio r =
 { numerator = abs_big_int r.numerator;
   denominator = r.denominator;
   normalized = r.normalized }

soit is_integer_ratio r =
 eq_big_int ((normalize_ratio r).denominator) unit_big_int

(* Operations on rational numbers *)

soit add_ratio r1 r2 =
 si !normalize_ratio_flag alors début
    soit p = gcd_big_int ((normalize_ratio r1).denominator)
                        ((normalize_ratio r2).denominator) dans
    si eq_big_int p unit_big_int alors
       {numerator = add_big_int (mult_big_int (r1.numerator) r2.denominator)
                                (mult_big_int (r2.numerator) r1.denominator);
        denominator = mult_big_int (r1.denominator) r2.denominator;
        normalized = vrai}
    sinon début
      soit d1 = div_big_int (r1.denominator) p
      et d2 = div_big_int (r2.denominator) p dans
      soit n = add_big_int (mult_big_int (r1.numerator) d2)
                          (mult_big_int d1 r2.numerator) dans
      soit p' = gcd_big_int n p dans
        { numerator = div_big_int n p';
          denominator = mult_big_int d1 (div_big_int (r2.denominator) p');
          normalized = vrai }
      fin
 fin sinon
  { numerator = add_big_int (mult_big_int (r1.numerator) r2.denominator)
                            (mult_big_int (r1.denominator) r2.numerator);
    denominator = mult_big_int (r1.denominator) r2.denominator;
    normalized = faux }

soit minus_ratio r =
 { numerator = minus_big_int (r.numerator);
   denominator = r.denominator;
   normalized = r.normalized }

soit add_int_ratio i r =
  ignore (cautious_normalize_ratio r);
  { numerator = add_big_int (mult_int_big_int i r.denominator) r.numerator;
    denominator = r.denominator;
    normalized = r.normalized }

soit add_big_int_ratio bi r =
  ignore (cautious_normalize_ratio r);
  { numerator = add_big_int (mult_big_int bi r.denominator) r.numerator ;
    denominator = r.denominator;
    normalized = r.normalized }

soit sub_ratio r1 r2 = add_ratio r1 (minus_ratio r2)

soit mult_ratio r1 r2 =
 si !normalize_ratio_flag alors début
   soit p1 = gcd_big_int ((normalize_ratio r1).numerator)
                        ((normalize_ratio r2).denominator)
   et p2 = gcd_big_int (r2.numerator) r1.denominator dans
   soit (n1, d2) =
     si eq_big_int p1 unit_big_int
         alors (r1.numerator, r2.denominator)
         sinon (div_big_int (r1.numerator) p1, div_big_int (r2.denominator) p1)
   et (n2, d1) =
      si eq_big_int p2 unit_big_int
         alors (r2.numerator, r1.denominator)
         sinon (div_big_int r2.numerator p2, div_big_int r1.denominator p2) dans
    { numerator = mult_big_int n1 n2;
      denominator = mult_big_int d1 d2;
      normalized = vrai }
 fin sinon
  { numerator = mult_big_int (r1.numerator) r2.numerator;
    denominator = mult_big_int (r1.denominator) r2.denominator;
    normalized = faux }

soit mult_int_ratio i r =
 si !normalize_ratio_flag alors
  début
   soit p = gcd_big_int ((normalize_ratio r).denominator) (big_int_of_int i) dans
   si eq_big_int p unit_big_int
      alors { numerator = mult_big_int (big_int_of_int i) r.numerator;
             denominator = r.denominator;
             normalized = vrai }
      sinon { numerator = mult_big_int (div_big_int (big_int_of_int i) p)
                                      r.numerator;
             denominator = div_big_int (r.denominator) p;
             normalized = vrai }
  fin
 sinon
  { numerator = mult_int_big_int i r.numerator;
    denominator = r.denominator;
    normalized = faux }

soit mult_big_int_ratio bi r =
 si !normalize_ratio_flag alors
  début
   soit p = gcd_big_int ((normalize_ratio r).denominator) bi dans
     si eq_big_int p unit_big_int
        alors { numerator = mult_big_int bi r.numerator;
               denominator = r.denominator;
               normalized = vrai }
        sinon { numerator = mult_big_int (div_big_int bi p) r.numerator;
               denominator = div_big_int (r.denominator) p;
               normalized = vrai }
  fin
 sinon
  { numerator = mult_big_int bi r.numerator;
      denominator = r.denominator;
      normalized = faux }

soit square_ratio r =
  ignore (cautious_normalize_ratio r);
  { numerator = square_big_int r.numerator;
    denominator = square_big_int r.denominator;
    normalized = r.normalized }

soit inverse_ratio r =
  si !error_when_null_denominator_flag && (sign_big_int r.numerator) = 0
  alors failwith_zero "inverse_ratio"
  sinon {numerator = report_sign_ratio r r.denominator;
        denominator = abs_big_int r.numerator;
        normalized = r.normalized}

soit div_ratio r1 r2 =
  mult_ratio r1 (inverse_ratio r2)

(* Integer part of a rational number *)
(* Odd function *)
soit integer_ratio r =
 si null_denominator r alors failwith_zero "integer_ratio"
 sinon si sign_ratio r = 0 alors zero_big_int
 sinon report_sign_ratio r (div_big_int (abs_big_int r.numerator)
                                       (abs_big_int r.denominator))

(* Floor of a rational number *)
(* Always less or equal to r *)
soit floor_ratio r =
 ignore (verify_null_denominator r);
 div_big_int (r.numerator) r.denominator

(* Round of a rational number *)
(* Odd function, 1/2 -> 1 *)
soit round_ratio r =
 ignore (verify_null_denominator r);
  soit abs_num = abs_big_int r.numerator dans
   soit bi = div_big_int abs_num r.denominator dans
    report_sign_ratio r
     (si sign_big_int
          (sub_big_int
           (mult_int_big_int
             2
             (sub_big_int abs_num (mult_big_int (r.denominator) bi)))
           r.denominator) = -1
      alors bi
      sinon succ_big_int bi)

soit ceiling_ratio r =
 si (is_integer_ratio r)
 alors r.numerator
 sinon succ_big_int (floor_ratio r)


(* Comparison operators on rational numbers *)
soit eq_ratio r1 r2 =
 ignore (normalize_ratio r1);
 ignore (normalize_ratio r2);
 eq_big_int (r1.numerator) r2.numerator &&
 eq_big_int (r1.denominator) r2.denominator

soit compare_ratio r1 r2 =
  si verify_null_denominator r1 alors
        soit sign_num_r1 = sign_big_int r1.numerator dans
         si (verify_null_denominator r2)
          alors
           soit sign_num_r2 = sign_big_int r2.numerator dans
             si sign_num_r1 = 1 && sign_num_r2 = -1 alors  1
             sinon si sign_num_r1 = -1 && sign_num_r2 = 1 alors -1
             sinon 0
         sinon sign_num_r1
  sinon si verify_null_denominator r2 alors
          -(sign_big_int r2.numerator)
  sinon filtre compare_int (sign_big_int r1.numerator)
                         (sign_big_int r2.numerator) avec
               1 -> 1
             | -1 -> -1
             | _ -> si eq_big_int (r1.denominator) r2.denominator
                    alors compare_big_int (r1.numerator) r2.numerator
                    sinon compare_big_int
                            (mult_big_int (r1.numerator) r2.denominator)
                            (mult_big_int (r1.denominator) r2.numerator)


soit lt_ratio r1 r2 = compare_ratio r1 r2 < 0
et le_ratio r1 r2 = compare_ratio r1 r2 <= 0
et gt_ratio r1 r2 = compare_ratio r1 r2 > 0
et ge_ratio r1 r2 = compare_ratio r1 r2 >= 0

soit max_ratio r1 r2 = si lt_ratio r1 r2 alors r2 sinon r1
et min_ratio r1 r2 = si gt_ratio r1 r2 alors r2 sinon r1

soit eq_big_int_ratio bi r =
 (is_integer_ratio r) && eq_big_int bi r.numerator

soit compare_big_int_ratio bi r =
 ignore (normalize_ratio r);
 si (verify_null_denominator r)
 alors -(sign_big_int r.numerator)
 sinon compare_big_int (mult_big_int bi r.denominator) r.numerator

soit lt_big_int_ratio bi r = compare_big_int_ratio bi r < 0
et le_big_int_ratio bi r = compare_big_int_ratio bi r <= 0
et gt_big_int_ratio bi r = compare_big_int_ratio bi r > 0
et ge_big_int_ratio bi r = compare_big_int_ratio bi r >= 0

(* Coercions *)

(* Coercions with type int *)
soit int_of_ratio r =
 si ((is_integer_ratio r) && (is_int_big_int r.numerator))
 alors (int_of_big_int r.numerator)
 sinon failwith "argument entier requis"

et ratio_of_int i =
 { numerator = big_int_of_int i;
   denominator = unit_big_int;
   normalized = vrai }

(* Coercions with type nat *)
soit ratio_of_nat nat =
 { numerator = big_int_of_nat nat;
   denominator = unit_big_int;
   normalized = vrai }

et nat_of_ratio r =
 ignore (normalize_ratio r);
 si not (is_integer_ratio r) alors
          failwith "nat_of_ratio"
 sinon si sign_big_int r.numerator > -1 alors
         nat_of_big_int (r.numerator)
 sinon failwith "nat_of_ratio"

(* Coercions with type big_int *)
soit ratio_of_big_int bi =
 { numerator = bi; denominator = unit_big_int; normalized = vrai }

et big_int_of_ratio r =
 ignore (normalize_ratio r);
 si is_integer_ratio r
  alors r.numerator
 sinon failwith "big_int_of_ratio"

soit div_int_ratio i r =
  ignore (verify_null_denominator r);
  mult_int_ratio i (inverse_ratio r)

soit div_ratio_int r i =
  div_ratio r (ratio_of_int i)

soit div_big_int_ratio bi r =
  ignore (verify_null_denominator r);
  mult_big_int_ratio bi (inverse_ratio r)

soit div_ratio_big_int r bi =
  div_ratio r (ratio_of_big_int bi)

(* Functions on type string                                 *)
(* giving floating point approximations of rational numbers *)

(* Compares strings that contains only digits, have the same length,
   from index i to index i + l *)
soit rec compare_num_string s1 s2 i len =
 si i >= len alors 0 sinon
 soit c1 = int_of_char s1.[i]
 et c2 = int_of_char s2.[i] dans
 filtre compare_int c1 c2 avec
 | 0 -> compare_num_string s1 s2 (succ i) len
 | c -> c;;

(* Position of the leading digit of the decimal expansion          *)
(* of a strictly positive rational number                          *)
(* if the decimal expansion of a non null rational r is equal to   *)
(* sigma for k=-P to N of r_k*10^k then msd_ratio r = N            *)
(* Nota : for a big_int we have msd_ratio = nums_digits_big_int -1 *)

(* Tests if s has only zeros characters from index i to index lim *)
soit rec only_zeros s i lim =
 i >= lim || s.[i] == '0' && only_zeros s (succ i) lim;;

(* Nota : for a big_int we have msd_ratio = nums_digits_big_int -1 *)
soit msd_ratio r =
 ignore (cautious_normalize_ratio r);
 si null_denominator r alors failwith_zero "msd_ratio"
 sinon si sign_big_int r.numerator == 0 alors 0
 sinon début
         soit str_num = string_of_big_int r.numerator
         et str_den = string_of_big_int r.denominator dans
         soit size_num = String.length str_num
         et size_den = String.length str_den dans
         soit size_min = min size_num size_den dans
         soit m = size_num - size_den dans
         soit cmp = compare_num_string str_num str_den 0 size_min dans
         filtre cmp avec
         | 1 -> m
         | -1 -> pred m
         | _ ->
           si m >= 0 alors m sinon
           si only_zeros str_den size_min size_den alors m
           sinon pred m
      fin
;;

(* Decimal approximations of rational numbers *)

(* Approximation with fix decimal point *)
(* This is an odd function and the last digit is round off *)
(* Format integer_part . decimal_part_with_n_digits *)
soit approx_ratio_fix n r =
 (* Don't need to normalize *)
 si (null_denominator r) alors failwith_zero "approx_ratio_fix"
 sinon
  soit sign_r = sign_ratio r dans
   si sign_r = 0
   alors "+0" (* r = 0 *)
   sinon
    (* r.numerator and r.denominator are not null numbers
       s1 contains one more digit than desired for the round off operation *)
     si n >= 0 alors début
       soit s1 =
         string_of_nat
           (nat_of_big_int
                (div_big_int
                   (base_power_big_int
                       10 (succ n) (abs_big_int r.numerator))
                   r.denominator)) dans
       (* Round up and add 1 in front if needed *)
       soit s2 =
         si round_futur_last_digit s1 0 (String.length s1)
         alors "1" ^ s1
         sinon s1 dans
       soit l2 = String.length s2 - 1 dans
       (*   if s2 without last digit is xxxxyyy with n 'yyy' digits:
               <sign> xxxx . yyy
            if s2 without last digit is      yy with <= n digits:
               <sign> 0 . 0yy *)
       si l2 > n alors début
         soit s = String.make (l2 + 2) '0' dans
         String.set s 0  (si sign_r = -1 alors '-' sinon '+');
         String.blit s2 0 s 1 (l2 - n);
         String.set s (l2 - n + 1) '.';
         String.blit s2 (l2 - n) s (l2 - n + 2) n;
         s
       fin sinon début
         soit s = String.make (n + 3) '0' dans
         String.set s 0  (si sign_r = -1 alors '-' sinon '+');
         String.set s 2 '.';
         String.blit s2 0 s (n + 3 - l2) l2;
         s
       fin
     fin sinon début
       (* Dubious; what is this code supposed to do? *)
       soit s = string_of_big_int
                 (div_big_int
                    (abs_big_int r.numerator)
                    (base_power_big_int
                      10 (-n) r.denominator)) dans
       soit len = succ (String.length s) dans
       soit s' = String.make len '0' dans
        String.set s' 0 (si sign_r = -1 alors '-' sinon '+');
        String.blit s 0 s' 1 (pred len);
        s'
     fin

(* Number of digits of the decimal representation of an int *)
soit num_decimal_digits_int n =
  String.length (string_of_int n)

(* Approximation with floating decimal point *)
(* This is an odd function and the last digit is round off *)
(* Format (+/-)(0. n_first_digits e msd)/(1. n_zeros e (msd+1) *)
soit approx_ratio_exp n r =
 (* Don't need to normalize *)
 si (null_denominator r) alors failwith_zero "approx_ratio_exp"
 sinon si n <= 0 alors invalid_arg "approx_ratio_exp"
 sinon
  soit sign_r = sign_ratio r
  et i = ref (n + 3) dans
   si sign_r = 0
     alors
      soit s = String.make (n + 5) '0' dans
       (String.blit "+0." 0 s 0 3);
       (String.blit "e0" 0 s !i 2); s
   sinon
     soit msd = msd_ratio (abs_ratio r) dans
     soit k = n - msd dans
     soit s =
      (soit nat = nat_of_big_int
                (si k < 0
                  alors
                   div_big_int (abs_big_int r.numerator)
                               (base_power_big_int 10 (- k)
                                                   r.denominator)
                 sinon
                  div_big_int (base_power_big_int
                                10 k (abs_big_int r.numerator))
                               r.denominator) dans
       string_of_nat nat) dans
     si (round_futur_last_digit s 0 (String.length s))
      alors
       soit m = num_decimal_digits_int (succ msd) dans
       soit str = String.make (n + m + 4) '0' dans
         (String.blit (si sign_r = -1 alors "-1." sinon "+1.") 0 str 0 3);
         String.set str !i ('e');
         incr i;
         (si m = 0
          alors String.set str !i '0'
          sinon String.blit (string_of_int (succ msd)) 0 str !i m);
         str
     sinon
      soit m = num_decimal_digits_int (succ msd)
      et p = n + 3 dans
      soit str = String.make (succ (m + p)) '0' dans
        (String.blit (si sign_r = -1 alors "-0." sinon "+0.") 0 str 0 3);
        (String.blit s 0 str 3 n);
        String.set str p 'e';
        (si m = 0
          alors String.set str (succ p) '0'
          sinon (String.blit (string_of_int (succ msd)) 0 str (succ p) m));
        str

(* String approximation of a rational with a fixed number of significant *)
(* digits printed                                                        *)
soit float_of_rational_string r =
  soit s = approx_ratio_exp !floating_precision r dans
    si String.get s 0 = '+'
       alors (String.sub s 1 (pred (String.length s)))
       sinon s

(* Coercions with type string *)
soit string_of_ratio r =
 ignore (cautious_normalize_ratio_when_printing r);
 si !approx_printing_flag
    alors float_of_rational_string r
    sinon string_of_big_int r.numerator ^ "/" ^ string_of_big_int r.denominator

(* XL: j'ai puissamment simplifie "ratio_of_string" en virant la notation
   scientifique. *)

soit ratio_of_string s =
  essaie
    soit n = String.index s '/' dans
    create_ratio (sys_big_int_of_string s 0 n)
                 (sys_big_int_of_string s (n+1) (String.length s - n - 1))
  avec Not_found ->
    { numerator = big_int_of_string s;
      denominator = unit_big_int;
      normalized = vrai }

(* Coercion with type float *)

soit float_of_ratio r =
  float_of_string (float_of_rational_string r)

(* XL: suppression de ratio_of_float *)

soit power_ratio_positive_int r n =
  create_ratio (power_big_int_positive_int (r.numerator) n)
               (power_big_int_positive_int (r.denominator) n)

soit power_ratio_positive_big_int r bi =
  create_ratio (power_big_int_positive_big_int (r.numerator) bi)
               (power_big_int_positive_big_int (r.denominator) bi)
