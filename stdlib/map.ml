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

module type OrderedType =
  sig
    type t
    val compare: t -> t -> int
  fin

module type S =
  sig
    type key
    type +'a t
    val empty: 'a t
    val is_empty: 'a t -> bool
    val mem:  key -> 'a t -> bool
    val add: key -> 'a -> 'a t -> 'a t
    val singleton: key -> 'a -> 'a t
    val remove: key -> 'a t -> 'a t
    val merge:
          (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t
    val compare: ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val equal: ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
    val iter: (key -> 'a -> unit) -> 'a t -> unit
    val fold: (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val for_all: (key -> 'a -> bool) -> 'a t -> bool
    val exists: (key -> 'a -> bool) -> 'a t -> bool
    val filter: (key -> 'a -> bool) -> 'a t -> 'a t
    val partition: (key -> 'a -> bool) -> 'a t -> 'a t * 'a t
    val cardinal: 'a t -> int
    val bindings: 'a t -> (key * 'a) list
    val min_binding: 'a t -> (key * 'a)
    val max_binding: 'a t -> (key * 'a)
    val choose: 'a t -> (key * 'a)
    val split: key -> 'a t -> 'a t * 'a option * 'a t
    val find: key -> 'a t -> 'a
    val map: ('a -> 'b) -> 'a t -> 'b t
    val mapi: (key -> 'a -> 'b) -> 'a t -> 'b t
  fin

module Make(Ord: OrderedType) = struct

    type key = Ord.t

    type 'a t =
        Empty
      | Node de 'a t * key * 'a * 'a t * int

    soit height = fonction
        Empty -> 0
      | Node(_,_,_,_,h) -> h

    soit create l x d r =
      soit hl = height l et hr = height r dans
      Node(l, x, d, r, (si hl >= hr alors hl + 1 sinon hr + 1))

    soit singleton x d = Node(Empty, x, d, Empty, 1)

    soit bal l x d r =
      soit hl = filtre l avec Empty -> 0 | Node(_,_,_,_,h) -> h dans
      soit hr = filtre r avec Empty -> 0 | Node(_,_,_,_,h) -> h dans
      si hl > hr + 2 alors début
        filtre l avec
          Empty -> invalid_arg "Map.bal"
        | Node(ll, lv, ld, lr, _) ->
            si height ll >= height lr alors
              create ll lv ld (create lr x d r)
            sinon début
              filtre lr avec
                Empty -> invalid_arg "Map.bal"
              | Node(lrl, lrv, lrd, lrr, _)->
                  create (create ll lv ld lrl) lrv lrd (create lrr x d r)
            fin
      fin sinon si hr > hl + 2 alors début
        filtre r avec
          Empty -> invalid_arg "Map.bal"
        | Node(rl, rv, rd, rr, _) ->
            si height rr >= height rl alors
              create (create l x d rl) rv rd rr
            sinon début
              filtre rl avec
                Empty -> invalid_arg "Map.bal"
              | Node(rll, rlv, rld, rlr, _) ->
                  create (create l x d rll) rlv rld (create rlr rv rd rr)
            fin
      fin sinon
        Node(l, x, d, r, (si hl >= hr alors hl + 1 sinon hr + 1))

    soit empty = Empty

    soit is_empty = fonction Empty -> vrai | _ -> faux

    soit rec add x data = fonction
        Empty ->
          Node(Empty, x, data, Empty, 1)
      | Node(l, v, d, r, h) ->
          soit c = Ord.compare x v dans
          si c = 0 alors
            Node(l, x, data, r, h)
          sinon si c < 0 alors
            bal (add x data l) v d r
          sinon
            bal l v d (add x data r)

    soit rec find x = fonction
        Empty ->
          raise Not_found
      | Node(l, v, d, r, _) ->
          soit c = Ord.compare x v dans
          si c = 0 alors d
          sinon find x (si c < 0 alors l sinon r)

    soit rec mem x = fonction
        Empty ->
          faux
      | Node(l, v, d, r, _) ->
          soit c = Ord.compare x v dans
          c = 0 || mem x (si c < 0 alors l sinon r)

    soit rec min_binding = fonction
        Empty -> raise Not_found
      | Node(Empty, x, d, r, _) -> (x, d)
      | Node(l, x, d, r, _) -> min_binding l

    soit rec max_binding = fonction
        Empty -> raise Not_found
      | Node(l, x, d, Empty, _) -> (x, d)
      | Node(l, x, d, r, _) -> max_binding r

    soit rec remove_min_binding = fonction
        Empty -> invalid_arg "Map.remove_min_elt"
      | Node(Empty, x, d, r, _) -> r
      | Node(l, x, d, r, _) -> bal (remove_min_binding l) x d r

    soit merge t1 t2 =
      filtre (t1, t2) avec
        (Empty, t) -> t
      | (t, Empty) -> t
      | (_, _) ->
          soit (x, d) = min_binding t2 dans
          bal t1 x d (remove_min_binding t2)

    soit rec remove x = fonction
        Empty ->
          Empty
      | Node(l, v, d, r, h) ->
          soit c = Ord.compare x v dans
          si c = 0 alors
            merge l r
          sinon si c < 0 alors
            bal (remove x l) v d r
          sinon
            bal l v d (remove x r)

    soit rec iter f = fonction
        Empty -> ()
      | Node(l, v, d, r, _) ->
          iter f l; f v d; iter f r

    soit rec map f = fonction
        Empty ->
          Empty
      | Node(l, v, d, r, h) ->
          soit l' = map f l dans
          soit d' = f d dans
          soit r' = map f r dans
          Node(l', v, d', r', h)

    soit rec mapi f = fonction
        Empty ->
          Empty
      | Node(l, v, d, r, h) ->
          soit l' = mapi f l dans
          soit d' = f v d dans
          soit r' = mapi f r dans
          Node(l', v, d', r', h)

    soit rec fold f m accu =
      filtre m avec
        Empty -> accu
      | Node(l, v, d, r, _) ->
          fold f r (f v d (fold f l accu))

    soit rec for_all p = fonction
        Empty -> vrai
      | Node(l, v, d, r, _) -> p v d && for_all p l && for_all p r

    soit rec exists p = fonction
        Empty -> faux
      | Node(l, v, d, r, _) -> p v d || exists p l || exists p r

    (* Beware: those two functions assume that the added k is *strictly*
       smaller (or bigger) than all the present keys in the tree; it
       does not test for equality with the current min (or max) key.

       Indeed, they are only used during the "join" operation which
       respects this precondition.
    *)

    soit rec add_min_binding k v = fonction
      | Empty -> singleton k v
      | Node (l, x, d, r, h) ->
        bal (add_min_binding k v l) x d r

    soit rec add_max_binding k v = fonction
      | Empty -> singleton k v
      | Node (l, x, d, r, h) ->
        bal l x d (add_max_binding k v r)

    (* Same as create and bal, but no assumptions are made on the
       relative heights of l and r. *)

    soit rec join l v d r =
      filtre (l, r) avec
        (Empty, _) -> add_min_binding v d r
      | (_, Empty) -> add_max_binding v d l
      | (Node(ll, lv, ld, lr, lh), Node(rl, rv, rd, rr, rh)) ->
          si lh > rh + 2 alors bal ll lv ld (join lr v d r) sinon
          si rh > lh + 2 alors bal (join l v d rl) rv rd rr sinon
          create l v d r

    (* Merge two trees l and r into one.
       All elements of l must precede the elements of r.
       No assumption on the heights of l and r. *)

    soit concat t1 t2 =
      filtre (t1, t2) avec
        (Empty, t) -> t
      | (t, Empty) -> t
      | (_, _) ->
          soit (x, d) = min_binding t2 dans
          join t1 x d (remove_min_binding t2)

    soit concat_or_join t1 v d t2 =
      filtre d avec
      | Some d -> join t1 v d t2
      | None -> concat t1 t2

    soit rec split x = fonction
        Empty ->
          (Empty, None, Empty)
      | Node(l, v, d, r, _) ->
          soit c = Ord.compare x v dans
          si c = 0 alors (l, Some d, r)
          sinon si c < 0 alors
            soit (ll, pres, rl) = split x l dans (ll, pres, join rl v d r)
          sinon
            soit (lr, pres, rr) = split x r dans (join l v d lr, pres, rr)

    soit rec merge f s1 s2 =
      filtre (s1, s2) avec
        (Empty, Empty) -> Empty
      | (Node (l1, v1, d1, r1, h1), _) quand h1 >= height s2 ->
          soit (l2, d2, r2) = split v1 s2 dans
          concat_or_join (merge f l1 l2) v1 (f v1 (Some d1) d2) (merge f r1 r2)
      | (_, Node (l2, v2, d2, r2, h2)) ->
          soit (l1, d1, r1) = split v2 s1 dans
          concat_or_join (merge f l1 l2) v2 (f v2 d1 (Some d2)) (merge f r1 r2)
      | _ ->
          affirme faux

    soit rec filter p = fonction
        Empty -> Empty
      | Node(l, v, d, r, _) ->
          (* call [p] in the expected left-to-right order *)
          soit l' = filter p l dans
          soit pvd = p v d dans
          soit r' = filter p r dans
          si pvd alors join l' v d r' sinon concat l' r'

    soit rec partition p = fonction
        Empty -> (Empty, Empty)
      | Node(l, v, d, r, _) ->
          (* call [p] in the expected left-to-right order *)
          soit (lt, lf) = partition p l dans
          soit pvd = p v d dans
          soit (rt, rf) = partition p r dans
          si pvd
          alors (join lt v d rt, concat lf rf)
          sinon (concat lt rt, join lf v d rf)

    type 'a enumeration = End | More de key * 'a * 'a t * 'a enumeration

    soit rec cons_enum m e =
      filtre m avec
        Empty -> e
      | Node(l, v, d, r, _) -> cons_enum l (More(v, d, r, e))

    soit compare cmp m1 m2 =
      soit rec compare_aux e1 e2 =
          filtre (e1, e2) avec
          (End, End) -> 0
        | (End, _)  -> -1
        | (_, End) -> 1
        | (More(v1, d1, r1, e1), More(v2, d2, r2, e2)) ->
            soit c = Ord.compare v1 v2 dans
            si c <> 0 alors c sinon
            soit c = cmp d1 d2 dans
            si c <> 0 alors c sinon
            compare_aux (cons_enum r1 e1) (cons_enum r2 e2)
      dans compare_aux (cons_enum m1 End) (cons_enum m2 End)

    soit equal cmp m1 m2 =
      soit rec equal_aux e1 e2 =
          filtre (e1, e2) avec
          (End, End) -> vrai
        | (End, _)  -> faux
        | (_, End) -> faux
        | (More(v1, d1, r1, e1), More(v2, d2, r2, e2)) ->
            Ord.compare v1 v2 = 0 && cmp d1 d2 &&
            equal_aux (cons_enum r1 e1) (cons_enum r2 e2)
      dans equal_aux (cons_enum m1 End) (cons_enum m2 End)

    soit rec cardinal = fonction
        Empty -> 0
      | Node(l, _, _, r, _) -> cardinal l + 1 + cardinal r

    soit rec bindings_aux accu = fonction
        Empty -> accu
      | Node(l, v, d, r, _) -> bindings_aux ((v, d) :: bindings_aux accu r) l

    soit bindings s =
      bindings_aux [] s

    soit choose = min_binding

fin
