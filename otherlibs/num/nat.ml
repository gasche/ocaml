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

type nat;;

dehors create_nat: int -> nat = "create_nat"
dehors set_to_zero_nat: nat -> int -> int -> unit = "set_to_zero_nat"
dehors blit_nat: nat -> int -> nat -> int -> int -> unit = "blit_nat"
dehors set_digit_nat: nat -> int -> int -> unit = "set_digit_nat"
dehors nth_digit_nat: nat -> int -> int = "nth_digit_nat"
dehors set_digit_nat_native: nat -> int -> nativeint -> unit = "set_digit_nat_native"
dehors nth_digit_nat_native: nat -> int -> nativeint = "nth_digit_nat_native"
dehors num_digits_nat: nat -> int -> int -> int = "num_digits_nat"
dehors num_leading_zero_bits_in_digit: nat -> int -> int = "num_leading_zero_bits_in_digit"
dehors is_digit_int: nat -> int -> bool = "is_digit_int"
dehors is_digit_zero: nat -> int -> bool = "is_digit_zero"
dehors is_digit_normalized: nat -> int -> bool = "is_digit_normalized"
dehors is_digit_odd: nat -> int -> bool = "is_digit_odd"
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
dehors land_digit_nat: nat -> int -> nat -> int -> unit = "land_digit_nat"
dehors lor_digit_nat: nat -> int -> nat -> int -> unit = "lor_digit_nat"
dehors lxor_digit_nat: nat -> int -> nat -> int -> unit = "lxor_digit_nat"

dehors initialize_nat: unit -> unit = "initialize_nat"
soit _ = initialize_nat()

soit length_nat (n : nat) = Obj.size (Obj.repr n) - 1

soit length_of_digit = Sys.word_size;;

soit make_nat len =
  si len < 0 alors invalid_arg "make_nat" sinon
    soit res = create_nat len dans set_to_zero_nat res 0 len; res

(* Nat temporaries *)
soit a_2 = make_nat 2
et a_1 = make_nat 1
et b_2 = make_nat 2

soit copy_nat nat off_set length =
 soit res = create_nat (length) dans
  blit_nat res 0 nat off_set length;
  res

soit is_zero_nat n off len =
  compare_nat (make_nat 1) 0 1 n off (num_digits_nat n off len) = 0

soit is_nat_int nat off len =
  num_digits_nat nat off len = 1 && is_digit_int nat off

soit sys_int_of_nat nat off len =
  si is_nat_int nat off len
  alors nth_digit_nat nat off
  sinon failwith "int_of_nat"

soit int_of_nat nat =
  sys_int_of_nat nat 0 (length_nat nat)

soit nat_of_int i =
  si i < 0 alors invalid_arg "nat_of_int" sinon
    soit res = make_nat 1 dans
    si i = 0 alors res sinon dÃ©but set_digit_nat res 0 i; res fin

soit eq_nat nat1 off1 len1 nat2 off2 len2 =
  compare_nat nat1 off1 (num_digits_nat nat1 off1 len1)
              nat2 off2 (num_digits_nat nat2 off2 len2) = 0
et le_nat nat1 off1 len1 nat2 off2 len2 =
  compare_nat nat1 off1 (num_digits_nat nat1 off1 len1)
              nat2 off2 (num_digits_nat nat2 off2 len2) <= 0
et lt_nat nat1 off1 len1 nat2 off2 len2 =
  compare_nat nat1 off1 (num_digits_nat nat1 off1 len1)
              nat2 off2 (num_digits_nat nat2 off2 len2) < 0
et ge_nat nat1 off1 len1 nat2 off2 len2 =
  compare_nat nat1 off1 (num_digits_nat nat1 off1 len1)
              nat2 off2 (num_digits_nat nat2 off2 len2) >= 0
et gt_nat nat1 off1 len1 nat2 off2 len2 =
  compare_nat nat1 off1 (num_digits_nat nat1 off1 len1)
              nat2 off2 (num_digits_nat nat2 off2 len2) > 0

(* XL: now implemented in C for better performance.
   The code below doesn't handle carries correctly.
   Fortunately, the carry is never used. *)
(***
let square_nat nat1 off1 len1 nat2 off2 len2 =
  let c = ref 0
  and trash = make_nat 1 in
    (* Double product *)
    for i = 0 to len2 - 2 do
        c := !c + mult_digit_nat
                         nat1
                         (succ (off1 + 2 * i))
                         (2 * (pred (len2 - i)))
                         nat2
                         (succ (off2 + i))
                         (pred (len2 - i))
                         nat2
                         (off2 + i)
    done;
    shift_left_nat nat1 0 len1 trash 0 1;
    (* Square of digit *)
    for i = 0 to len2 - 1 do
        c := !c + mult_digit_nat
                         nat1
                         (off1 + 2 * i)
                         (len1 - 2 * i)
                         nat2
                         (off2 + i)
                         1
                         nat2
                         (off2 + i)
    done;
  !c
***)

soit gcd_int_nat i nat off len =
  si i = 0 alors 1 sinon
  si is_nat_int nat off len alors dÃ©but
    set_digit_nat nat off (gcd_int (nth_digit_nat nat off) i); 0
  fin sinon dÃ©but
    soit len_copy = succ len dans
    soit copy = create_nat len_copy
    et quotient = create_nat 1
    et remainder = create_nat 1 dans
    blit_nat copy 0 nat off len;
    set_digit_nat copy len 0;
    div_digit_nat quotient 0 remainder 0 copy 0 len_copy (nat_of_int i) 0;
    set_digit_nat nat off (gcd_int (nth_digit_nat remainder 0) i);
    0
  fin

soit exchange r1 r2 =
  soit old1 = !r1 dans r1 := !r2; r2 := old1

soit gcd_nat nat1 off1 len1 nat2 off2 len2 =
  si is_zero_nat nat1 off1 len1 alors dÃ©but
    blit_nat nat1 off1 nat2 off2 len2; len2
  fin sinon dÃ©but
    soit copy1 = ref (create_nat (succ len1))
    et copy2 = ref (create_nat (succ len2)) dans
      blit_nat !copy1 0 nat1 off1 len1;
      blit_nat !copy2 0 nat2 off2 len2;
      set_digit_nat !copy1 len1 0;
      set_digit_nat !copy2 len2 0;
      si lt_nat !copy1 0 len1 !copy2 0 len2
         alors exchange copy1 copy2;
      soit real_len1 =
            ref (num_digits_nat !copy1 0 (length_nat !copy1))
      et real_len2 =
            ref (num_digits_nat !copy2 0 (length_nat !copy2)) dans
      pendant_que not (is_zero_nat !copy2 0 !real_len2) faire
        set_digit_nat !copy1 !real_len1 0;
        div_nat !copy1 0 (succ !real_len1) !copy2 0 !real_len2;
        exchange copy1 copy2;
        real_len1 := !real_len2;
        real_len2 := num_digits_nat !copy2 0 !real_len2
      fait;
      blit_nat nat1 off1 !copy1 0 !real_len1;
      !real_len1
  fin

(* Racine carrée entière par la méthode de Newton (entière par défaut). *)

(* Théorème: la suite xn+1 = (xn + a/xn) / 2 converge vers la racine *)
(* carrée entière de a par défaut, si on part d'une valeur x0 *)
(* strictement plus grande que la racine de a, sauf quand a est un *)
(* carré - 1, cas auquel la suite alterne entre la racine par défaut *)
(* et par excès. Dans tous les cas, le dernier terme de la partie *)
(* strictement décroissante de la suite est le résultat cherché. *)

soit sqrt_nat rad off len =
 soit len = num_digits_nat rad off len dans
 (* Copie de travail du radicande *)
 soit len_parity = len mod 2 dans
 soit rad_len = len + 1 + len_parity dans
 soit rad =
   soit res = create_nat rad_len dans
   blit_nat res 0 rad off len;
   set_digit_nat res len 0;
   set_digit_nat res (rad_len - 1) 0;
   res dans
 soit cand_len = (len + 1) / 2 dans  (* ceiling len / 2 *)
 soit cand_rest = rad_len - cand_len dans
 (* Racine carrée supposée cand = "|FFFF .... |" *)
 soit cand = make_nat cand_len dans
 (* Amélioration de la racine de départ:
    on calcule nbb le nombre de bits significatifs du premier digit du candidat
    (la moitié du nombre de bits significatifs dans les deux premiers
     digits du radicande étendu à une longueur paire).
    shift_cand est word_size - nbb *)
 soit shift_cand =
   ((num_leading_zero_bits_in_digit rad (len-1)) +
     Sys.word_size * len_parity) / 2 dans
 (* Tous les bits du radicande sont à 0, on rend 0. *)
 si shift_cand = Sys.word_size alors cand sinon
 dÃ©but
  complement_nat cand 0 cand_len;
  shift_right_nat cand 0 1 a_1 0 shift_cand;
  soit next_cand = create_nat rad_len dans
  (* Repeat until *)
  soit rec loop () =
           (* next_cand := rad *)
   blit_nat next_cand 0 rad 0 rad_len;
           (* next_cand <- next_cand / cand *)
   div_nat next_cand 0 rad_len cand 0 cand_len;
           (* next_cand (poids fort) <- next_cand (poids fort) + cand,
              i.e. next_cand <- cand + rad / cand *)
   ignore (add_nat next_cand cand_len cand_rest cand 0 cand_len 0);
        (* next_cand <- next_cand / 2 *)
   shift_right_nat next_cand cand_len cand_rest a_1 0 1;
   si lt_nat next_cand cand_len cand_rest cand 0 cand_len alors
    dÃ©but  (* cand <- next_cand *)
     blit_nat cand 0 next_cand cand_len cand_len; loop ()
    fin
   sinon cand dans
  loop ()
 fin;;

soit power_base_max = make_nat 2;;

filtre length_of_digit avec
  | 64 ->
      set_digit_nat power_base_max 0 (Int64.to_int 1000000000000000000L);
      ignore
        (mult_digit_nat power_base_max 0 2
           power_base_max 0 1 (nat_of_int 9) 0)
  | 32 -> set_digit_nat power_base_max 0 1000000000
  | _ -> affirme faux
;;

soit pmax =
  filtre length_of_digit avec
  | 64 -> 19
  | 32 -> 9
  | _ -> affirme faux
;;

soit max_superscript_10_power_in_int =
  filtre length_of_digit avec
  | 64 -> 18
  | 32 -> 9
  | _ -> affirme faux
;;
soit max_power_10_power_in_int =
  filtre length_of_digit avec
  | 64 -> nat_of_int (Int64.to_int 1000000000000000000L)
  | 32 -> nat_of_int 1000000000
  | _ -> affirme faux
;;

soit raw_string_of_digit nat off =
  si is_nat_int nat off 1
     alors dÃ©but string_of_int (nth_digit_nat nat off) fin
  sinon dÃ©but
       blit_nat b_2 0 nat off 1;
       div_digit_nat a_2 0 a_1 0 b_2 0 2 max_power_10_power_in_int 0;
       soit leading_digits = nth_digit_nat a_2 0
       et s1 = string_of_int (nth_digit_nat a_1 0) dans
       soit len = String.length s1 dans
       si leading_digits < 10 alors dÃ©but
            soit result = String.make (max_superscript_10_power_in_int+1) '0' dans
            String.set result 0
                         (Char.chr (48 + leading_digits));
            String.blit s1 0
                 result (String.length result - len) len;
            result
       fin sinon dÃ©but
            soit result = String.make (max_superscript_10_power_in_int+2) '0' dans
            String.blit (string_of_int leading_digits) 0 result 0 2;
            String.blit s1 0
                 result (String.length result - len) len;
            result
       fin
  fin

(* XL: suppression de string_of_digit et de sys_string_of_digit.
   La copie est de toute facon faite dans string_of_nat, qui est le
   seul point d entree public dans ce code. *)

(******
let sys_string_of_digit nat off =
    let s = raw_string_of_digit nat off in
    let result = String.create (String.length s) in
    String.blit s 0 result 0 (String.length s);
    s

let string_of_digit nat =
    sys_string_of_digit nat 0

*******)

soit digits = "0123456789ABCDEF"

(*
   make_power_base affecte power_base des puissances successives de base a
   partir de la puissance 1-ieme.
   A la fin de la boucle i-1 est la plus grande puissance de la base qui tient
   sur un seul digit et j est la plus grande puissance de la base qui tient
   sur un int.
*)
soit make_power_base base power_base =
  soit i = ref 0
  et j = ref 0 dans
   set_digit_nat power_base 0 base;
   pendant_que incr i; is_digit_zero power_base !i faire
     ignore
       (mult_digit_nat power_base !i 2
          power_base (pred !i) 1
          power_base 0)
   fait;
   pendant_que !j <= !i && is_digit_int power_base !j faire incr j fait;
  (!i - 2, !j)

(*
   int_to_string place la representation de l entier int en base base
   dans la chaine s en le rangeant de la fin indiquee par pos vers le
   debut, sur times places et affecte a pos sa nouvelle valeur.
*)
soit int_to_string int s pos_ref base times =
  soit i = ref int
  et j = ref times dans
     pendant_que ((!i != 0) || (!j != 0)) && (!pos_ref != -1) faire
        String.set s !pos_ref (String.get digits (!i mod base));
        decr pos_ref;
        decr j;
        i := !i / base
     fait

(* XL: suppression de adjust_string *)

soit power_base_int base i =
  si i = 0 || base = 1 alors
    nat_of_int 1
  sinon si base = 0 alors
    nat_of_int 0
  sinon si i < 0 alors
    invalid_arg "power_base_int"
  sinon dÃ©but
         soit power_base = make_nat (succ length_of_digit) dans
         soit (pmax, pint) = make_power_base base power_base dans
         soit n = i / (succ pmax)
         et rem = i mod (succ pmax) dans
           si n > 0 alors dÃ©but
               soit newn =
                 si i = biggest_int alors n sinon (succ n) dans
               soit res = make_nat newn
               et res2 = make_nat newn
               et l = num_bits_int n - 2 dans
                 blit_nat res 0 power_base pmax 1;
                 pour i = l descendant_jusqu'a 0 faire
                   soit len = num_digits_nat res 0 newn dans
                   soit len2 = min n (2 * len) dans
                   soit succ_len2 = succ len2 dans
                     ignore (square_nat res2 0 len2 res 0 len);
                     si n etl (1 dgl i) > 0 alors dÃ©but
                       set_to_zero_nat res 0 len;
                       ignore
                         (mult_digit_nat res 0 succ_len2
                            res2 0 len2  power_base pmax)
                     fin sinon
                       blit_nat res 0 res2 0 len2;
                     set_to_zero_nat res2 0 len2
                 fait;
               si rem > 0 alors dÃ©but
                 ignore
                   (mult_digit_nat res2 0 newn
                      res 0 n power_base (pred rem));
                 res2
               fin sinon res
            fin sinon
              copy_nat power_base (pred rem) 1
  fin

(* the ith element (i >= 2) of num_digits_max_vector is :
    |                                 |
    | biggest_string_length * log (i) |
    | ------------------------------- | + 1
    |      length_of_digit * log (2)  |
    --                               --
*)

(* XL: ai specialise le code d origine a length_of_digit = 32. *)
(* Puis suppression (inutile?) *)

(******
let num_digits_max_vector =
  [|0; 0; 1024; 1623; 2048; 2378; 2647; 2875; 3072; 3246; 3402;
              3543; 3671; 3789; 3899; 4001; 4096|]

let num_digits_max_vector =
   match length_of_digit with
     16 -> [|0; 0; 2048; 3246; 4096; 4755; 5294; 5749; 6144; 6492; 6803;
              7085; 7342; 7578; 7797; 8001; 8192|]
(* If really exotic machines !!!!
   | 17 -> [|0; 0; 1928; 3055; 3855; 4476; 4983; 5411; 5783; 6110; 6403;
              6668; 6910; 7133; 7339; 7530; 7710|]
   | 18 -> [|0; 0; 1821; 2886; 3641; 4227; 4706; 5111; 5461; 5771; 6047;
              6298; 6526; 6736; 6931; 7112; 7282|]
   | 19 -> [|0; 0; 1725; 2734; 3449; 4005; 4458; 4842; 5174; 5467; 5729;
              5966; 6183; 6382; 6566; 6738; 6898|]
   | 20 -> [|0; 0; 1639; 2597; 3277; 3804; 4235; 4600; 4915; 5194; 5443;
              5668; 5874; 6063; 6238; 6401; 6553|]
   | 21 -> [|0; 0; 1561; 2473; 3121; 3623; 4034; 4381; 4681; 4946; 5183;
              5398; 5594; 5774; 5941; 6096; 6241|]
   | 22 -> [|0; 0; 1490; 2361; 2979; 3459; 3850; 4182; 4468; 4722; 4948;
              5153; 5340; 5512; 5671; 5819; 5958|]
   | 23 -> [|0; 0; 1425; 2258; 2850; 3308; 3683; 4000; 4274; 4516; 4733;
              4929; 5108; 5272; 5424; 5566; 5699|]
   | 24 -> [|0; 0; 1366; 2164; 2731; 3170; 3530; 3833; 4096; 4328; 4536;
              4723; 4895; 5052; 5198; 5334; 5461|]
   | 25 -> [|0; 0; 1311; 2078; 2622; 3044; 3388; 3680; 3932; 4155; 4354;
              4534; 4699; 4850; 4990; 5121; 5243|]
   | 26 -> [|0; 0; 1261; 1998; 2521; 2927; 3258; 3538; 3781; 3995; 4187;
              4360; 4518; 4664; 4798; 4924; 5041|]
   | 27 -> [|0; 0; 1214; 1924; 2428; 2818; 3137; 3407; 3641; 3847; 4032;
              4199; 4351; 4491; 4621; 4742; 4855|]
   | 28 -> [|0; 0; 1171; 1855; 2341; 2718; 3025; 3286; 3511; 3710; 3888;
              4049; 4196; 4331; 4456; 4572; 4681|]
   | 29 -> [|0; 0; 1130; 1791; 2260; 2624; 2921; 3172; 3390; 3582; 3754;
              3909; 4051; 4181; 4302; 4415; 4520|]
   | 30 -> [|0; 0; 1093; 1732; 2185; 2536; 2824; 3067; 3277; 3463; 3629;
              3779; 3916; 4042; 4159; 4267; 4369|]
   | 31 -> [|0; 0; 1057; 1676; 2114; 2455; 2733; 2968; 3171; 3351; 3512;
              3657; 3790; 3912; 4025; 4130; 4228|]
*)
   | 32 -> [|0; 0; 1024; 1623; 2048; 2378; 2647; 2875; 3072; 3246; 3402;
              3543; 3671; 3789; 3899; 4001; 4096|]
   | n -> failwith "num_digits_max_vector"
******)

(* XL: suppression de string_list_of_nat *)

soit unadjusted_string_of_nat nat off len_nat =
  soit len = num_digits_nat nat off len_nat dans
  si len = 1 alors
       raw_string_of_digit nat off
  sinon
       soit len_copy = ref (succ len) dans
       soit copy1 = create_nat !len_copy
       et copy2 = make_nat !len_copy
       et rest_digit = make_nat 2 dans
         si len > biggest_int / (succ pmax)
            alors failwith "le nombre est trop long"
            sinon soit len_s = (succ pmax) * len dans
                 soit s = String.make len_s '0'
                 et pos_ref = ref len_s dans
                   len_copy := pred !len_copy;
                   blit_nat copy1 0 nat off len;
                   set_digit_nat copy1 len 0;
                   pendant_que not (is_zero_nat copy1 0 !len_copy) faire
                      div_digit_nat copy2 0
                                     rest_digit 0
                                     copy1 0 (succ !len_copy)
                                     power_base_max 0;
                      soit str = raw_string_of_digit rest_digit 0 dans
                      String.blit str 0
                                  s (!pos_ref - String.length str)
                                  (String.length str);
                      (* XL: il y avait pmax a la place de String.length str
                         mais ca ne marche pas avec le blit de Caml Light,
                         qui ne verifie pas les debordements *)
                      pos_ref := !pos_ref - pmax;
                      len_copy := num_digits_nat copy2 0 !len_copy;
                      blit_nat copy1 0 copy2 0 !len_copy;
                      set_digit_nat copy1 !len_copy 0
                   fait;
                   s

soit string_of_nat nat =
  soit s = unadjusted_string_of_nat nat 0 (length_nat nat)
  et index = ref 0 dans
    dÃ©but essaie
      pour i = 0 Ã  String.length s - 2 faire
       si String.get s i <> '0' alors (index:= i; raise Exit)
      fait
    avec Exit -> ()
    fin;
    String.sub s !index (String.length s - !index)

(* XL: suppression de sys_string_of_nat *)

(* XL: suppression de debug_string_nat *)

soit base_digit_of_char c base =
  soit n = Char.code c dans
    si n >= 48 && n <= 47 + min base 10 alors n - 48
    sinon si n >= 65 && n <= 65 + base - 11 alors n - 55
    sinon si n >= 97 && n <= 97 + base - 11 alors n - 87
    sinon failwith "chiffre invalide"

(*
   La sous-chaine (s, off, len) represente un nat en base base que
   on determine ici
*)
soit sys_nat_of_string base s off len =
  soit power_base = make_nat (succ length_of_digit) dans
  soit (pmax, pint) = make_power_base base power_base dans
  soit new_len = ref (1 + len / (pmax + 1))
  et current_len = ref 1 dans
  soit possible_len = ref (min 2 !new_len) dans

  soit nat1 = make_nat !new_len
  et nat2 = make_nat !new_len

  et digits_read = ref 0
  et bound = off + len - 1
  et int = ref 0 dans

  pour i = off Ã  bound faire
    (*
       on lit pint (au maximum) chiffres, on en fait un int
       et on l integre au nombre
     *)
      soit c = String.get s i  dans
        dÃ©but filtre c avec
          ' ' | '\t' | '\n' | '\r' | '\\' -> ()
        | '_' quand i > off -> ()
        | _ -> int := !int * base + base_digit_of_char c base;
               incr digits_read
        fin;
        si (!digits_read = pint || i = bound) && not (!digits_read = 0) alors
          dÃ©but
           set_digit_nat nat1 0 !int;
           soit erase_len = si !new_len = !current_len alors !current_len - 1
                           sinon !current_len dans
           pour j = 1 Ã  erase_len faire
             set_digit_nat nat1 j 0
           fait;
           ignore
             (mult_digit_nat nat1 0 !possible_len
                nat2 0 !current_len power_base (pred !digits_read));
           blit_nat nat2 0 nat1 0 !possible_len;
           current_len := num_digits_nat nat1 0 !possible_len;
           possible_len := min !new_len (succ !current_len);
           int := 0;
           digits_read := 0
           fin
  fait;
  (*
     On recadre le nat
  *)
  soit nat = create_nat !current_len dans
    blit_nat nat 0 nat1 0 !current_len;
    nat

soit nat_of_string s = sys_nat_of_string 10 s 0 (String.length s)

soit float_of_nat nat = float_of_string(string_of_nat nat)
