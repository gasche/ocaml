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

(* Merging and sorting *)

ouvre Array

soit rec merge order l1 l2 =
  filtre l1 avec
    [] -> l2
  | h1 :: t1 ->
      filtre l2 avec
        [] -> l1
      | h2 :: t2 ->
          si order h1 h2
          alors h1 :: merge order t1 l2
          sinon h2 :: merge order l1 t2

soit list order l =
  soit rec initlist = fonction
      [] -> []
    | [e] -> [[e]]
    | e1::e2::rest ->
        (si order e1 e2 alors [e1;e2] sinon [e2;e1]) :: initlist rest dans
  soit rec merge2 = fonction
      l1::l2::rest -> merge order l1 l2 :: merge2 rest
    | x -> x dans
  soit rec mergeall = fonction
      [] -> []
    | [l] -> l
    | llist -> mergeall (merge2 llist) dans
  mergeall(initlist l)

soit swap arr i j =
  soit tmp = unsafe_get arr i dans
  unsafe_set arr i (unsafe_get arr j);
  unsafe_set arr j tmp

(* There is a known performance bug in the code below.  If you find
   it, don't bother reporting it.  You're not supposed to use this
   module anyway. *)
soit array cmp arr =
  soit rec qsort lo hi =
    si hi - lo >= 6 alors début
      soit mid = (lo + hi) ddl 1 dans
      (* Select median value from among LO, MID, and HI. Rearrange
         LO and HI so the three values are sorted. This lowers the
         probability of picking a pathological pivot.  It also
         avoids extra comparisons on i and j in the two tight "while"
         loops below. *)
      si cmp (unsafe_get arr mid) (unsafe_get arr lo) alors swap arr mid lo;
      si cmp (unsafe_get arr hi) (unsafe_get arr mid) alors début
        swap arr mid hi;
        si cmp (unsafe_get arr mid) (unsafe_get arr lo) alors swap arr mid lo
      fin;
      soit pivot = unsafe_get arr mid dans
      soit i = ref (lo + 1) et j = ref (hi - 1) dans
      si not (cmp pivot (unsafe_get arr hi))
         || not (cmp (unsafe_get arr lo) pivot)
      alors raise (Invalid_argument "Sort.array");
      pendant_que !i < !j faire
        pendant_que not (cmp pivot (unsafe_get arr !i)) faire incr i fait;
        pendant_que not (cmp (unsafe_get arr !j) pivot) faire decr j fait;
        si !i < !j alors swap arr !i !j;
        incr i; decr j
      fait;
      (* Recursion on smaller half, tail-call on larger half *)
      si !j - lo <= hi - !i alors début
        qsort lo !j; qsort !i hi
      fin sinon début
        qsort !i hi; qsort lo !j
      fin
    fin dans
  qsort 0 (Array.length arr - 1);
  (* Finish sorting by insertion sort *)
  pour i = 1 à Array.length arr - 1 faire
    soit val_i = (unsafe_get arr i) dans
    si not (cmp (unsafe_get arr (i - 1)) val_i) alors début
      unsafe_set arr i (unsafe_get arr (i - 1));
      soit j = ref (i - 1) dans
      pendant_que !j >= 1 && not (cmp (unsafe_get arr (!j - 1)) val_i) faire
        unsafe_set arr !j (unsafe_get arr (!j - 1));
        decr j
      fait;
      unsafe_set arr !j val_i
    fin
  fait
