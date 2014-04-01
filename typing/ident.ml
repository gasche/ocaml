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

ouvre Format

type t = { stamp: int; name: string; modifiable flags: int }

soit global_flag = 1
soit predef_exn_flag = 2

(* A stamp of 0 denotes a persistent identifier *)

soit currentstamp = ref 0

soit create s =
  incr currentstamp;
  { name = s; stamp = !currentstamp; flags = 0 }

soit create_predef_exn s =
  incr currentstamp;
  { name = s; stamp = !currentstamp; flags = predef_exn_flag }

soit create_persistent s =
  { name = s; stamp = 0; flags = global_flag }

soit rename i =
  incr currentstamp;
  { i avec stamp = !currentstamp }

soit name i = i.name

soit stamp i = i.stamp

soit unique_name i = i.name ^ "_" ^ string_of_int i.stamp

soit unique_toplevel_name i = i.name ^ "/" ^ string_of_int i.stamp

soit persistent i = (i.stamp = 0)

soit equal i1 i2 = i1.name = i2.name

soit same i1 i2 = i1 = i2
  (* Possibly more efficient version (with a real compiler, at least):
       if i1.stamp <> 0
       then i1.stamp = i2.stamp
       else i2.stamp = 0 && i1.name = i2.name *)

soit binding_time i = i.stamp

soit current_time() = !currentstamp
soit set_current_time t = currentstamp := max !currentstamp t

soit reinit_level = ref (-1)

soit reinit () =
  si !reinit_level < 0
  alors reinit_level := !currentstamp
  sinon currentstamp := !reinit_level

soit hide i =
  { i avec stamp = -1 }

soit make_global i =
  i.flags <- i.flags oul global_flag

soit global i =
  (i.flags etl global_flag) <> 0

soit is_predef_exn i =
  (i.flags etl predef_exn_flag) <> 0

soit print ppf i =
  filtre i.stamp avec
  | 0 -> fprintf ppf "%s!" i.name
  | -1 -> fprintf ppf "%s#" i.name
  | n -> fprintf ppf "%s/%i%s" i.name n (si global i alors "g" sinon "")

type 'a tbl =
    Empty
  | Node de 'a tbl * 'a data * 'a tbl * int

et 'a data =
  { ident: t;
    data: 'a;
    previous: 'a data option }

soit empty = Empty

(* Inline expansion of height for better speed
 * let height = function
 *     Empty -> 0
 *   | Node(_,_,_,h) -> h
 *)

soit mknode l d r =
  soit hl = filtre l avec Empty -> 0 | Node(_,_,_,h) -> h
  et hr = filtre r avec Empty -> 0 | Node(_,_,_,h) -> h dans
  Node(l, d, r, (si hl >= hr alors hl + 1 sinon hr + 1))

soit balance l d r =
  soit hl = filtre l avec Empty -> 0 | Node(_,_,_,h) -> h
  et hr = filtre r avec Empty -> 0 | Node(_,_,_,h) -> h dans
  si hl > hr + 1 alors
    filtre l avec
    | Node (ll, ld, lr, _)
      quand (filtre ll avec Empty -> 0 | Node(_,_,_,h) -> h) >=
           (filtre lr avec Empty -> 0 | Node(_,_,_,h) -> h) ->
        mknode ll ld (mknode lr d r)
    | Node (ll, ld, Node(lrl, lrd, lrr, _), _) ->
        mknode (mknode ll ld lrl) lrd (mknode lrr d r)
    | _ -> affirme faux
  sinon si hr > hl + 1 alors
    filtre r avec
    | Node (rl, rd, rr, _)
      quand (filtre rr avec Empty -> 0 | Node(_,_,_,h) -> h) >=
           (filtre rl avec Empty -> 0 | Node(_,_,_,h) -> h) ->
        mknode (mknode l d rl) rd rr
    | Node (Node (rll, rld, rlr, _), rd, rr, _) ->
        mknode (mknode l d rll) rld (mknode rlr rd rr)
    | _ -> affirme faux
  sinon
    mknode l d r

soit rec add id data = fonction
    Empty ->
      Node(Empty, {ident = id; data = data; previous = None}, Empty, 1)
  | Node(l, k, r, h) ->
      soit c = compare id.name k.ident.name dans
      si c = 0 alors
        Node(l, {ident = id; data = data; previous = Some k}, r, h)
      sinon si c < 0 alors
        balance (add id data l) k r
      sinon
        balance l k (add id data r)

soit rec find_stamp s = fonction
    None ->
      raise Not_found
  | Some k ->
      si k.ident.stamp = s alors k.data sinon find_stamp s k.previous

soit rec find_same id = fonction
    Empty ->
      raise Not_found
  | Node(l, k, r, _) ->
      soit c = compare id.name k.ident.name dans
      si c = 0 alors
        si id.stamp = k.ident.stamp
        alors k.data
        sinon find_stamp id.stamp k.previous
      sinon
        find_same id (si c < 0 alors l sinon r)

soit rec find_name name = fonction
    Empty ->
      raise Not_found
  | Node(l, k, r, _) ->
      soit c = compare name k.ident.name dans
      si c = 0 alors
        k.data
      sinon
        find_name name (si c < 0 alors l sinon r)

soit rec get_all = fonction
  | None -> []
  | Some k -> k.data :: get_all k.previous

soit rec find_all name = fonction
    Empty ->
      []
  | Node(l, k, r, _) ->
      soit c = compare name k.ident.name dans
      si c = 0 alors
        k.data :: get_all k.previous
      sinon
        find_all name (si c < 0 alors l sinon r)

soit rec fold_aux f stack accu = fonction
    Empty ->
      début filtre stack avec
        [] -> accu
      | a :: l -> fold_aux f l accu a
      fin
  | Node(l, k, r, _) ->
      fold_aux f (l :: stack) (f k accu) r

soit fold_name f tbl accu = fold_aux (fonc k -> f k.ident k.data) [] accu tbl

soit rec fold_data f d accu =
  filtre d avec
    None -> accu
  | Some k -> f k.ident k.data (fold_data f k.previous accu)

soit fold_all f tbl accu =
  fold_aux (fonc k -> fold_data f (Some k)) [] accu tbl

(* let keys tbl = fold_name (fun k _ accu -> k::accu) tbl [] *)

soit rec iter f = fonction
    Empty -> ()
  | Node(l, k, r, _) ->
      iter f l; f k.ident k.data; iter f r
