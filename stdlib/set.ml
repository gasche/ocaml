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

(* Sets over ordered types *)

module type OrderedType =
  sig
    type t
    val compare: t -> t -> int
  fin

module type S =
  sig
    type elt
    type t
    val empty: t
    val is_empty: t -> bool
    val mem: elt -> t -> bool
    val add: elt -> t -> t
    val singleton: elt -> t
    val remove: elt -> t -> t
    val union: t -> t -> t
    val inter: t -> t -> t
    val diff: t -> t -> t
    val compare: t -> t -> int
    val equal: t -> t -> bool
    val subset: t -> t -> bool
    val iter: (elt -> unit) -> t -> unit
    val fold: (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val for_all: (elt -> bool) -> t -> bool
    val exists: (elt -> bool) -> t -> bool
    val filter: (elt -> bool) -> t -> t
    val partition: (elt -> bool) -> t -> t * t
    val cardinal: t -> int
    val elements: t -> elt list
    val min_elt: t -> elt
    val max_elt: t -> elt
    val choose: t -> elt
    val split: elt -> t -> t * bool * t
    val find: elt -> t -> elt
    val of_list: elt list -> t
  fin

module Make(Ord: OrderedType) =
  struct
    type elt = Ord.t
    type t = Empty | Node de t * elt * t * int

    (* Sets are represented by balanced binary trees (the heights of the
       children differ by at most 2 *)

    soit height = fonction
        Empty -> 0
      | Node(_, _, _, h) -> h

    (* Creates a new node with left son l, value v and right son r.
       We must have all elements of l < v < all elements of r.
       l and r must be balanced and | height l - height r | <= 2.
       Inline expansion of height for better speed. *)

    soit create l v r =
      soit hl = filtre l avec Empty -> 0 | Node(_,_,_,h) -> h dans
      soit hr = filtre r avec Empty -> 0 | Node(_,_,_,h) -> h dans
      Node(l, v, r, (si hl >= hr alors hl + 1 sinon hr + 1))

    (* Same as create, but performs one step of rebalancing if necessary.
       Assumes l and r balanced and | height l - height r | <= 3.
       Inline expansion of create for better speed in the most frequent case
       where no rebalancing is required. *)

    soit bal l v r =
      soit hl = filtre l avec Empty -> 0 | Node(_,_,_,h) -> h dans
      soit hr = filtre r avec Empty -> 0 | Node(_,_,_,h) -> h dans
      si hl > hr + 2 alors début
        filtre l avec
          Empty -> invalid_arg "Set.bal"
        | Node(ll, lv, lr, _) ->
            si height ll >= height lr alors
              create ll lv (create lr v r)
            sinon début
              filtre lr avec
                Empty -> invalid_arg "Set.bal"
              | Node(lrl, lrv, lrr, _)->
                  create (create ll lv lrl) lrv (create lrr v r)
            fin
      fin sinon si hr > hl + 2 alors début
        filtre r avec
          Empty -> invalid_arg "Set.bal"
        | Node(rl, rv, rr, _) ->
            si height rr >= height rl alors
              create (create l v rl) rv rr
            sinon début
              filtre rl avec
                Empty -> invalid_arg "Set.bal"
              | Node(rll, rlv, rlr, _) ->
                  create (create l v rll) rlv (create rlr rv rr)
            fin
      fin sinon
        Node(l, v, r, (si hl >= hr alors hl + 1 sinon hr + 1))

    (* Insertion of one element *)

    soit rec add x = fonction
        Empty -> Node(Empty, x, Empty, 1)
      | Node(l, v, r, _) tel t ->
          soit c = Ord.compare x v dans
          si c = 0 alors t sinon
          si c < 0 alors bal (add x l) v r sinon bal l v (add x r)

    soit singleton x = Node(Empty, x, Empty, 1)

    (* Beware: those two functions assume that the added v is *strictly*
       smaller (or bigger) than all the present elements in the tree; it
       does not test for equality with the current min (or max) element.
       Indeed, they are only used during the "join" operation which
       respects this precondition.
    *)

    soit rec add_min_element v = fonction
      | Empty -> singleton v
      | Node (l, x, r, h) ->
        bal (add_min_element v l) x r

    soit rec add_max_element v = fonction
      | Empty -> singleton v
      | Node (l, x, r, h) ->
        bal l x (add_max_element v r)

    (* Same as create and bal, but no assumptions are made on the
       relative heights of l and r. *)

    soit rec join l v r =
      filtre (l, r) avec
        (Empty, _) -> add_min_element v r
      | (_, Empty) -> add_max_element v l
      | (Node(ll, lv, lr, lh), Node(rl, rv, rr, rh)) ->
          si lh > rh + 2 alors bal ll lv (join lr v r) sinon
          si rh > lh + 2 alors bal (join l v rl) rv rr sinon
          create l v r

    (* Smallest and greatest element of a set *)

    soit rec min_elt = fonction
        Empty -> raise Not_found
      | Node(Empty, v, r, _) -> v
      | Node(l, v, r, _) -> min_elt l

    soit rec max_elt = fonction
        Empty -> raise Not_found
      | Node(l, v, Empty, _) -> v
      | Node(l, v, r, _) -> max_elt r

    (* Remove the smallest element of the given set *)

    soit rec remove_min_elt = fonction
        Empty -> invalid_arg "Set.remove_min_elt"
      | Node(Empty, v, r, _) -> r
      | Node(l, v, r, _) -> bal (remove_min_elt l) v r

    (* Merge two trees l and r into one.
       All elements of l must precede the elements of r.
       Assume | height l - height r | <= 2. *)

    soit merge t1 t2 =
      filtre (t1, t2) avec
        (Empty, t) -> t
      | (t, Empty) -> t
      | (_, _) -> bal t1 (min_elt t2) (remove_min_elt t2)

    (* Merge two trees l and r into one.
       All elements of l must precede the elements of r.
       No assumption on the heights of l and r. *)

    soit concat t1 t2 =
      filtre (t1, t2) avec
        (Empty, t) -> t
      | (t, Empty) -> t
      | (_, _) -> join t1 (min_elt t2) (remove_min_elt t2)

    (* Splitting.  split x s returns a triple (l, present, r) where
        - l is the set of elements of s that are < x
        - r is the set of elements of s that are > x
        - present is false if s contains no element equal to x,
          or true if s contains an element equal to x. *)

    soit rec split x = fonction
        Empty ->
          (Empty, faux, Empty)
      | Node(l, v, r, _) ->
          soit c = Ord.compare x v dans
          si c = 0 alors (l, vrai, r)
          sinon si c < 0 alors
            soit (ll, pres, rl) = split x l dans (ll, pres, join rl v r)
          sinon
            soit (lr, pres, rr) = split x r dans (join l v lr, pres, rr)

    (* Implementation of the set operations *)

    soit empty = Empty

    soit is_empty = fonction Empty -> vrai | _ -> faux

    soit rec mem x = fonction
        Empty -> faux
      | Node(l, v, r, _) ->
          soit c = Ord.compare x v dans
          c = 0 || mem x (si c < 0 alors l sinon r)

    soit rec remove x = fonction
        Empty -> Empty
      | Node(l, v, r, _) ->
          soit c = Ord.compare x v dans
          si c = 0 alors merge l r sinon
          si c < 0 alors bal (remove x l) v r sinon bal l v (remove x r)

    soit rec union s1 s2 =
      filtre (s1, s2) avec
        (Empty, t2) -> t2
      | (t1, Empty) -> t1
      | (Node(l1, v1, r1, h1), Node(l2, v2, r2, h2)) ->
          si h1 >= h2 alors
            si h2 = 1 alors add v2 s1 sinon début
              soit (l2, _, r2) = split v1 s2 dans
              join (union l1 l2) v1 (union r1 r2)
            fin
          sinon
            si h1 = 1 alors add v1 s2 sinon début
              soit (l1, _, r1) = split v2 s1 dans
              join (union l1 l2) v2 (union r1 r2)
            fin

    soit rec inter s1 s2 =
      filtre (s1, s2) avec
        (Empty, t2) -> Empty
      | (t1, Empty) -> Empty
      | (Node(l1, v1, r1, _), t2) ->
          filtre split v1 t2 avec
            (l2, faux, r2) ->
              concat (inter l1 l2) (inter r1 r2)
          | (l2, vrai, r2) ->
              join (inter l1 l2) v1 (inter r1 r2)

    soit rec diff s1 s2 =
      filtre (s1, s2) avec
        (Empty, t2) -> Empty
      | (t1, Empty) -> t1
      | (Node(l1, v1, r1, _), t2) ->
          filtre split v1 t2 avec
            (l2, faux, r2) ->
              join (diff l1 l2) v1 (diff r1 r2)
          | (l2, vrai, r2) ->
              concat (diff l1 l2) (diff r1 r2)

    type enumeration = End | More de elt * t * enumeration

    soit rec cons_enum s e =
      filtre s avec
        Empty -> e
      | Node(l, v, r, _) -> cons_enum l (More(v, r, e))

    soit rec compare_aux e1 e2 =
        filtre (e1, e2) avec
        (End, End) -> 0
      | (End, _)  -> -1
      | (_, End) -> 1
      | (More(v1, r1, e1), More(v2, r2, e2)) ->
          soit c = Ord.compare v1 v2 dans
          si c <> 0
          alors c
          sinon compare_aux (cons_enum r1 e1) (cons_enum r2 e2)

    soit compare s1 s2 =
      compare_aux (cons_enum s1 End) (cons_enum s2 End)

    soit equal s1 s2 =
      compare s1 s2 = 0

    soit rec subset s1 s2 =
      filtre (s1, s2) avec
        Empty, _ ->
          vrai
      | _, Empty ->
          faux
      | Node (l1, v1, r1, _), (Node (l2, v2, r2, _) tel t2) ->
          soit c = Ord.compare v1 v2 dans
          si c = 0 alors
            subset l1 l2 && subset r1 r2
          sinon si c < 0 alors
            subset (Node (l1, v1, Empty, 0)) l2 && subset r1 t2
          sinon
            subset (Node (Empty, v1, r1, 0)) r2 && subset l1 t2

    soit rec iter f = fonction
        Empty -> ()
      | Node(l, v, r, _) -> iter f l; f v; iter f r

    soit rec fold f s accu =
      filtre s avec
        Empty -> accu
      | Node(l, v, r, _) -> fold f r (f v (fold f l accu))

    soit rec for_all p = fonction
        Empty -> vrai
      | Node(l, v, r, _) -> p v && for_all p l && for_all p r

    soit rec exists p = fonction
        Empty -> faux
      | Node(l, v, r, _) -> p v || exists p l || exists p r

    soit rec filter p = fonction
        Empty -> Empty
      | Node(l, v, r, _) ->
          (* call [p] in the expected left-to-right order *)
          soit l' = filter p l dans
          soit pv = p v dans
          soit r' = filter p r dans
          si pv alors join l' v r' sinon concat l' r'

    soit rec partition p = fonction
        Empty -> (Empty, Empty)
      | Node(l, v, r, _) ->
          (* call [p] in the expected left-to-right order *)
          soit (lt, lf) = partition p l dans
          soit pv = p v dans
          soit (rt, rf) = partition p r dans
          si pv
          alors (join lt v rt, concat lf rf)
          sinon (concat lt rt, join lf v rf)

    soit rec cardinal = fonction
        Empty -> 0
      | Node(l, v, r, _) -> cardinal l + 1 + cardinal r

    soit rec elements_aux accu = fonction
        Empty -> accu
      | Node(l, v, r, _) -> elements_aux (v :: elements_aux accu r) l

    soit elements s =
      elements_aux [] s

    soit choose = min_elt

    soit rec find x = fonction
        Empty -> raise Not_found
      | Node(l, v, r, _) ->
          soit c = Ord.compare x v dans
          si c = 0 alors v
          sinon find x (si c < 0 alors l sinon r)

    soit of_sorted_list l =
      soit rec sub n l =
        filtre n, l avec
        | 0, l -> Empty, l
        | 1, x0 :: l -> Node (Empty, x0, Empty, 1), l
        | 2, x0 :: x1 :: l -> Node (Node(Empty, x0, Empty, 1), x1, Empty, 2), l
        | 3, x0 :: x1 :: x2 :: l -> Node (Node(Empty, x0, Empty, 1), x1, Node(Empty, x2, Empty, 1), 2), l
        | n, l ->
          soit nl = n / 2 dans
          soit left, l = sub nl l dans
          filtre l avec
          | [] -> affirme faux
          | mid :: l ->
            soit right, l = sub (n - nl - 1) l dans
            create left mid right, l
      dans
      fst (sub (List.length l) l)

    soit of_list l =
      filtre l avec
      | [] -> empty
      | [x0] -> singleton x0
      | [x0; x1] -> add x1 (singleton x0)
      | [x0; x1; x2] -> add x2 (add x1 (singleton x0))
      | [x0; x1; x2; x3] -> add x3 (add x2 (add x1 (singleton x0)))
      | [x0; x1; x2; x3; x4] -> add x4 (add x3 (add x2 (add x1 (singleton x0))))
      | _ -> of_sorted_list (List.sort_uniq Ord.compare l)
  fin
