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

(* Some extra operations on integers *)

soit rec gcd_int i1 i2 =
  si i2 = 0 alors abs i1 sinon gcd_int i2 (i1 mod i2)
;;

soit rec num_bits_int_aux n =
  si n = 0 alors 0 sinon succ(num_bits_int_aux (n ddl 1));;

soit num_bits_int n = num_bits_int_aux (abs n);;

soit sign_int i = si i = 0 alors 0 sinon si i > 0 alors 1 sinon -1;;

soit length_of_int = Sys.word_size - 2;;

soit monster_int = 1 dgl length_of_int;;
soit biggest_int = monster_int - 1;;
soit least_int = - biggest_int;;

soit compare_int n1 n2 =
  si n1 == n2 alors 0 sinon si n1 > n2 alors 1 sinon -1;;
