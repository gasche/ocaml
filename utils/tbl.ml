(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

type ('a, 'b) t =
    Empty
  | Node de ('a, 'b) t * 'a * 'b * ('a, 'b) t * int

soit empty = Empty

soit height = fonction
    Empty -> 0
  | Node(_,_,_,_,h) -> h

soit create l x d r =
  soit hl = height l et hr = height r dans
  Node(l, x, d, r, (si hl >= hr alors hl + 1 sinon hr + 1))

soit bal l x d r =
  soit hl = height l et hr = height r dans
  si hl > hr + 1 alors
    filtre l avec
    | Node (ll, lv, ld, lr, _) quand height ll >= height lr ->
        create ll lv ld (create lr x d r)
    | Node (ll, lv, ld, Node (lrl, lrv, lrd, lrr, _), _) ->
        create (create ll lv ld lrl) lrv lrd (create lrr x d r)
    | _ -> affirme faux
  sinon si hr > hl + 1 alors
    filtre r avec
    | Node (rl, rv, rd, rr, _) quand height rr >= height rl ->
        create (create l x d rl) rv rd rr
    | Node (Node (rll, rlv, rld, rlr, _), rv, rd, rr, _) ->
        create (create l x d rll) rlv rld (create rlr rv rd rr)
    | _ -> affirme faux
  sinon
    create l x d r

soit rec add x data = fonction
    Empty ->
      Node(Empty, x, data, Empty, 1)
  | Node(l, v, d, r, h) ->
      soit c = compare x v dans
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
      soit c = compare x v dans
      si c = 0 alors d
      sinon find x (si c < 0 alors l sinon r)

soit rec mem x = fonction
    Empty -> faux
  | Node(l, v, d, r, _) ->
      soit c = compare x v dans
      c = 0 || mem x (si c < 0 alors l sinon r)

soit rec merge t1 t2 =
  filtre (t1, t2) avec
    (Empty, t) -> t
  | (t, Empty) -> t
  | (Node(l1, v1, d1, r1, h1), Node(l2, v2, d2, r2, h2)) ->
      bal l1 v1 d1 (bal (merge r1 l2) v2 d2 r2)

soit rec remove x = fonction
    Empty ->
      Empty
  | Node(l, v, d, r, h) ->
      soit c = compare x v dans
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
    Empty -> Empty
  | Node(l, v, d, r, h) -> Node(map f l, v, f v d, map f r, h)

soit rec fold f m accu =
  filtre m avec
  | Empty -> accu
  | Node(l, v, d, r, _) ->
      fold f r (f v d (fold f l accu))

ouvre Format

soit print print_key print_data ppf tbl =
  soit print_tbl ppf tbl =
    iter (fonc k d -> fprintf ppf "@[<2>%a ->@ %a;@]@ " print_key k print_data d)
      tbl dans
  fprintf ppf "@[<hv 2>[[%a]]@]" print_tbl tbl
