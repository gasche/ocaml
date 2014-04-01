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

(* List operations *)

soit rec length_aux len = fonction
    [] -> len
  | a::l -> length_aux (len + 1) l

soit length l = length_aux 0 l

soit hd = fonction
    [] -> failwith "hd"
  | a::l -> a

soit tl = fonction
    [] -> failwith "tl"
  | a::l -> l

soit nth l n =
  si n < 0 alors invalid_arg "List.nth" sinon
  soit rec nth_aux l n =
    filtre l avec
    | [] -> failwith "nth"
    | a::l -> si n = 0 alors a sinon nth_aux l (n-1)
  dans nth_aux l n

soit append = (@)

soit rec rev_append l1 l2 =
  filtre l1 avec
    [] -> l2
  | a :: l -> rev_append l (a :: l2)

soit rev l = rev_append l []

soit rec flatten = fonction
    [] -> []
  | l::r -> l @ flatten r

soit concat = flatten

soit rec map f = fonction
    [] -> []
  | a::l -> soit r = f a dans r :: map f l

soit rec mapi i f = fonction
    [] -> []
  | a::l -> soit r = f i a dans r :: mapi (i + 1) f l

soit mapi f l = mapi 0 f l

soit rev_map f l =
  soit rec rmap_f accu = fonction
    | [] -> accu
    | a::l -> rmap_f (f a :: accu) l
  dans
  rmap_f [] l
;;

soit rec iter f = fonction
    [] -> ()
  | a::l -> f a; iter f l

soit rec iteri i f = fonction
    [] -> ()
  | a::l -> f i a; iteri (i + 1) f l

soit iteri f l = iteri 0 f l

soit rec fold_left f accu l =
  filtre l avec
    [] -> accu
  | a::l -> fold_left f (f accu a) l

soit rec fold_right f l accu =
  filtre l avec
    [] -> accu
  | a::l -> f a (fold_right f l accu)

soit rec map2 f l1 l2 =
  filtre (l1, l2) avec
    ([], []) -> []
  | (a1::l1, a2::l2) -> soit r = f a1 a2 dans r :: map2 f l1 l2
  | (_, _) -> invalid_arg "List.map2"

soit rev_map2 f l1 l2 =
  soit rec rmap2_f accu l1 l2 =
    filtre (l1, l2) avec
    | ([], []) -> accu
    | (a1::l1, a2::l2) -> rmap2_f (f a1 a2 :: accu) l1 l2
    | (_, _) -> invalid_arg "List.rev_map2"
  dans
  rmap2_f [] l1 l2
;;

soit rec iter2 f l1 l2 =
  filtre (l1, l2) avec
    ([], []) -> ()
  | (a1::l1, a2::l2) -> f a1 a2; iter2 f l1 l2
  | (_, _) -> invalid_arg "List.iter2"

soit rec fold_left2 f accu l1 l2 =
  filtre (l1, l2) avec
    ([], []) -> accu
  | (a1::l1, a2::l2) -> fold_left2 f (f accu a1 a2) l1 l2
  | (_, _) -> invalid_arg "List.fold_left2"

soit rec fold_right2 f l1 l2 accu =
  filtre (l1, l2) avec
    ([], []) -> accu
  | (a1::l1, a2::l2) -> f a1 a2 (fold_right2 f l1 l2 accu)
  | (_, _) -> invalid_arg "List.fold_right2"

soit rec for_all p = fonction
    [] -> vrai
  | a::l -> p a && for_all p l

soit rec exists p = fonction
    [] -> faux
  | a::l -> p a || exists p l

soit rec for_all2 p l1 l2 =
  filtre (l1, l2) avec
    ([], []) -> vrai
  | (a1::l1, a2::l2) -> p a1 a2 && for_all2 p l1 l2
  | (_, _) -> invalid_arg "List.for_all2"

soit rec exists2 p l1 l2 =
  filtre (l1, l2) avec
    ([], []) -> faux
  | (a1::l1, a2::l2) -> p a1 a2 || exists2 p l1 l2
  | (_, _) -> invalid_arg "List.exists2"

soit rec mem x = fonction
    [] -> faux
  | a::l -> compare a x = 0 || mem x l

soit rec memq x = fonction
    [] -> faux
  | a::l -> a == x || memq x l

soit rec assoc x = fonction
    [] -> raise Not_found
  | (a,b)::l -> si compare a x = 0 alors b sinon assoc x l

soit rec assq x = fonction
    [] -> raise Not_found
  | (a,b)::l -> si a == x alors b sinon assq x l

soit rec mem_assoc x = fonction
  | [] -> faux
  | (a, b) :: l -> compare a x = 0 || mem_assoc x l

soit rec mem_assq x = fonction
  | [] -> faux
  | (a, b) :: l -> a == x || mem_assq x l

soit rec remove_assoc x = fonction
  | [] -> []
  | (a, b tel pair) :: l ->
      si compare a x = 0 alors l sinon pair :: remove_assoc x l

soit rec remove_assq x = fonction
  | [] -> []
  | (a, b tel pair) :: l -> si a == x alors l sinon pair :: remove_assq x l

soit rec find p = fonction
  | [] -> raise Not_found
  | x :: l -> si p x alors x sinon find p l

soit find_all p =
  soit rec find accu = fonction
  | [] -> rev accu
  | x :: l -> si p x alors find (x :: accu) l sinon find accu l dans
  find []

soit filter = find_all

soit partition p l =
  soit rec part yes no = fonction
  | [] -> (rev yes, rev no)
  | x :: l -> si p x alors part (x :: yes) no l sinon part yes (x :: no) l dans
  part [] [] l

soit rec split = fonction
    [] -> ([], [])
  | (x,y)::l ->
      soit (rx, ry) = split l dans (x::rx, y::ry)

soit rec combine l1 l2 =
  filtre (l1, l2) avec
    ([], []) -> []
  | (a1::l1, a2::l2) -> (a1, a2) :: combine l1 l2
  | (_, _) -> invalid_arg "List.combine"

(** sorting *)

soit rec merge cmp l1 l2 =
  filtre l1, l2 avec
  | [], l2 -> l2
  | l1, [] -> l1
  | h1 :: t1, h2 :: t2 ->
      si cmp h1 h2 <= 0
      alors h1 :: merge cmp t1 l2
      sinon h2 :: merge cmp l1 t2
;;

soit rec chop k l =
  si k = 0 alors l sinon début
    filtre l avec
    | x::t -> chop (k-1) t
    | _ -> affirme faux
  fin
;;

soit stable_sort cmp l =
  soit rec rev_merge l1 l2 accu =
    filtre l1, l2 avec
    | [], l2 -> rev_append l2 accu
    | l1, [] -> rev_append l1 accu
    | h1::t1, h2::t2 ->
        si cmp h1 h2 <= 0
        alors rev_merge t1 l2 (h1::accu)
        sinon rev_merge l1 t2 (h2::accu)
  dans
  soit rec rev_merge_rev l1 l2 accu =
    filtre l1, l2 avec
    | [], l2 -> rev_append l2 accu
    | l1, [] -> rev_append l1 accu
    | h1::t1, h2::t2 ->
        si cmp h1 h2 > 0
        alors rev_merge_rev t1 l2 (h1::accu)
        sinon rev_merge_rev l1 t2 (h2::accu)
  dans
  soit rec sort n l =
    filtre n, l avec
    | 2, x1 :: x2 :: _ ->
       si cmp x1 x2 <= 0 alors [x1; x2] sinon [x2; x1]
    | 3, x1 :: x2 :: x3 :: _ ->
       si cmp x1 x2 <= 0 alors début
         si cmp x2 x3 <= 0 alors [x1; x2; x3]
         sinon si cmp x1 x3 <= 0 alors [x1; x3; x2]
         sinon [x3; x1; x2]
       fin sinon début
         si cmp x1 x3 <= 0 alors [x2; x1; x3]
         sinon si cmp x2 x3 <= 0 alors [x2; x3; x1]
         sinon [x3; x2; x1]
       fin
    | n, l ->
       soit n1 = n dda 1 dans
       soit n2 = n - n1 dans
       soit l2 = chop n1 l dans
       soit s1 = rev_sort n1 l dans
       soit s2 = rev_sort n2 l2 dans
       rev_merge_rev s1 s2 []
  et rev_sort n l =
    filtre n, l avec
    | 2, x1 :: x2 :: _ ->
       si cmp x1 x2 > 0 alors [x1; x2] sinon [x2; x1]
    | 3, x1 :: x2 :: x3 :: _ ->
       si cmp x1 x2 > 0 alors début
         si cmp x2 x3 > 0 alors [x1; x2; x3]
         sinon si cmp x1 x3 > 0 alors [x1; x3; x2]
         sinon [x3; x1; x2]
       fin sinon début
         si cmp x1 x3 > 0 alors [x2; x1; x3]
         sinon si cmp x2 x3 > 0 alors [x2; x3; x1]
         sinon [x3; x2; x1]
       fin
    | n, l ->
       soit n1 = n dda 1 dans
       soit n2 = n - n1 dans
       soit l2 = chop n1 l dans
       soit s1 = sort n1 l dans
       soit s2 = sort n2 l2 dans
       rev_merge s1 s2 []
  dans
  soit len = length l dans
  si len < 2 alors l sinon sort len l
;;

soit sort = stable_sort;;
soit fast_sort = stable_sort;;

(* Note: on a list of length between about 100000 (depending on the minor
   heap size and the type of the list) and Sys.max_array_size, it is
   actually faster to use the following, but it might also use more memory
   because the argument list cannot be deallocated incrementally.

   Also, there seems to be a bug in this code or in the
   implementation of obj_truncate.

external obj_truncate : 'a array -> int -> unit = "caml_obj_truncate"

let array_to_list_in_place a =
  let l = Array.length a in
  let rec loop accu n p =
    if p <= 0 then accu else begin
      if p = n then begin
        obj_truncate a p;
        loop (a.(p-1) :: accu) (n-1000) (p-1)
      end else begin
        loop (a.(p-1) :: accu) n (p-1)
      end
    end
  in
  loop [] (l-1000) l
;;

let stable_sort cmp l =
  let a = Array.of_list l in
  Array.stable_sort cmp a;
  array_to_list_in_place a
;;
*)


(** sorting + removing duplicates *)

soit sort_uniq cmp l =
  soit rec rev_merge l1 l2 accu =
    filtre l1, l2 avec
    | [], l2 -> rev_append l2 accu
    | l1, [] -> rev_append l1 accu
    | h1::t1, h2::t2 ->
        soit c = cmp h1 h2 dans
        si c = 0 alors rev_merge t1 t2 (h1::accu)
        sinon si c < 0
        alors rev_merge t1 l2 (h1::accu)
        sinon rev_merge l1 t2 (h2::accu)
  dans
  soit rec rev_merge_rev l1 l2 accu =
    filtre l1, l2 avec
    | [], l2 -> rev_append l2 accu
    | l1, [] -> rev_append l1 accu
    | h1::t1, h2::t2 ->
        soit c = cmp h1 h2 dans
        si c = 0 alors rev_merge_rev t1 t2 (h1::accu)
        sinon si c > 0
        alors rev_merge_rev t1 l2 (h1::accu)
        sinon rev_merge_rev l1 t2 (h2::accu)
  dans
  soit rec sort n l =
    filtre n, l avec
    | 2, x1 :: x2 :: _ ->
       soit c = cmp x1 x2 dans
       si c = 0 alors [x1]
       sinon si c < 0 alors [x1; x2] sinon [x2; x1]
    | 3, x1 :: x2 :: x3 :: _ ->
       soit c = cmp x1 x2 dans
       si c = 0 alors début
         soit c = cmp x2 x3 dans
         si c = 0 alors [x2]
         sinon si c < 0 alors [x2; x3] sinon [x3; x2]
       fin sinon si c < 0 alors début
         soit c = cmp x2 x3 dans
         si c = 0 alors [x1; x2]
         sinon si c < 0 alors [x1; x2; x3]
         sinon soit c = cmp x1 x3 dans
         si c = 0 alors [x1; x2]
         sinon si c < 0 alors [x1; x3; x2]
         sinon [x3; x1; x2]
       fin sinon début
         soit c = cmp x1 x3 dans
         si c = 0 alors [x2; x1]
         sinon si c < 0 alors [x2; x1; x3]
         sinon soit c = cmp x2 x3 dans
         si c = 0 alors [x2; x1]
         sinon si c < 0 alors [x2; x3; x1]
         sinon [x3; x2; x1]
       fin
    | n, l ->
       soit n1 = n dda 1 dans
       soit n2 = n - n1 dans
       soit l2 = chop n1 l dans
       soit s1 = rev_sort n1 l dans
       soit s2 = rev_sort n2 l2 dans
       rev_merge_rev s1 s2 []
  et rev_sort n l =
    filtre n, l avec
    | 2, x1 :: x2 :: _ ->
       soit c = cmp x1 x2 dans
       si c = 0 alors [x1]
       sinon si c > 0 alors [x1; x2] sinon [x2; x1]
    | 3, x1 :: x2 :: x3 :: _ ->
       soit c = cmp x1 x2 dans
       si c = 0 alors début
         soit c = cmp x2 x3 dans
         si c = 0 alors [x2]
         sinon si c > 0 alors [x2; x3] sinon [x3; x2]
       fin sinon si c > 0 alors début
         soit c = cmp x2 x3 dans
         si c = 0 alors [x1; x2]
         sinon si c > 0 alors [x1; x2; x3]
         sinon soit c = cmp x1 x3 dans
         si c = 0 alors [x1; x2]
         sinon si c > 0 alors [x1; x3; x2]
         sinon [x3; x1; x2]
       fin sinon début
         soit c = cmp x1 x3 dans
         si c = 0 alors [x2; x1]
         sinon si c > 0 alors [x2; x1; x3]
         sinon soit c = cmp x2 x3 dans
         si c = 0 alors [x2; x1]
         sinon si c > 0 alors [x2; x3; x1]
         sinon [x3; x2; x1]
       fin
    | n, l ->
       soit n1 = n dda 1 dans
       soit n2 = n - n1 dans
       soit l2 = chop n1 l dans
       soit s1 = sort n1 l dans
       soit s2 = sort n2 l2 dans
       rev_merge s1 s2 []
  dans
  soit len = length l dans
  si len < 2 alors l sinon sort len l
;;
