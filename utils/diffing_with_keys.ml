(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Florian Angeletti, projet Cambium, Inria Paris             *)
(*                                                                        *)
(*   Copyright 2021 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)


type 'a with_pos = int * 'a
let with_pos l = List.mapi (fun n x -> n+1,x) l
let pos (x,_) = x
let data (_,x) = x
let mk_pos pos data = pos, data

type ('l, 'r, 'tdiff) mismatch =
  | Name of {pos:int; got:string; expected:string; types_match:bool}
  | Type of {pos:int; got:'l; expected:'r; reason:'tdiff}

type ('l, 'r, 'tdiff) change =
  | Change of ('l, 'r, 'tdiff) mismatch
  | Swap of {pos: int * int; first: string; last: string}
  | Move of {name:string; got:int; expected:int}
  | Delete of {pos:int; delete:'l}
  | Insert of {pos:int; insert:'r}

let prefix ppf x =
  let kind = match x with
    | Change _ | Swap _ | Move _ -> Diffing.Modification
    | Insert _ -> Diffing.Insertion
    | Delete _ -> Diffing.Deletion
  in
  let style k ppf inner =
    let sty = Diffing.style k in
    Format.pp_open_stag ppf (Misc.Color.Style sty);
    Format.kfprintf (fun ppf -> Format.pp_close_stag ppf () ) ppf inner
  in
  match x with
  | Change (Name {pos; _ } | Type {pos; _})
  | Insert { pos; _ } | Delete { pos; _ } ->
      style kind ppf "%i. " pos
  | Swap { pos = left, right; _ } ->
      style kind ppf "%i<->%i. " left right
  | Move { got; expected; _ } ->
      style kind ppf "%i->%i. " expected got

module Swap = Map.Make(struct
    type t = string * string
    let compare: t -> t -> int = Stdlib.compare
  end)
module Move = Misc.Stdlib.String.Map

type ('l, 'r, 'state) partial_edge =
  | Left of int * 'state * 'l
  | Right of int * 'state * 'r
  | Both of 'state * 'l * 'r

type ('l, 'r) keys = ('l -> string) * ('r -> string)

let swap_edge (type l r state)
    (key : (l, r) keys)
    (state : state)
    (x : l with_pos)
    (y : r with_pos)
  : Swap.key
    * (l with_pos * r with_pos, l with_pos * r with_pos, state) partial_edge
=
  let kx, ky = fst key (data x), snd key (data y) in
  if kx <= ky then
    (kx,ky), Left (pos x, state, (x,y))
  else
    (ky,kx), Right(pos x,state, (x,y))

let add_edge (type l r state)
    (ex : (l, r, state) partial_edge)
    (ey : (l, r, state) partial_edge option)
  : (l, r, state) partial_edge option
= match ex, ey with
  | ex, None -> Some ex
  | Left (lpos, lstate, l), Some Right (rpos, rstate,r)
  | Right (rpos, rstate,r), Some Left (lpos, lstate, l) ->
      let state = if lpos < rpos then rstate else lstate in
      Some (Both (state,l,r))
  | Both _ as b, _ | _, Some (Both _ as b)  -> Some b
  | l, _ -> Some l

type ('l, 'r, 'state) swaps =
  ('l with_pos * 'r with_pos, 'l with_pos * 'r with_pos, 'state)
    partial_edge Swap.t
type ('l, 'r, 'state) moves =
  ('l with_pos, 'r with_pos, 'state)
    partial_edge Move.t

type ('l, 'r, 'eq, 'diff, 'state) update =
  ('l with_pos, 'r with_pos, 'eq, 'diff) Diffing.change -> 'state -> 'state
type ('l, 'r, 'eq, 'diff, 'state) test =
  'state -> 'l with_pos -> 'r with_pos -> ('eq, 'diff) result

let exchanges (type l r eq diff state)
    ~(update : (l, r, eq, diff, state) update)
    ~(key : (l, r) keys)
    (state : state)
    (changes : (l with_pos, r with_pos, eq, diff) Diffing.change list)
  : state * ((l, r, state) swaps * (l, r, state) moves)
=
  let add (state,
           ((swaps : (l, r, state) swaps),
            (moves : (l, r, state) moves))) d =
    update d state,
    match d with
    | Diffing.Change (x,y,_) ->
        let k, edge = swap_edge key state x y in
        Swap.update k (add_edge edge) swaps, moves
    | Diffing.Insert nx ->
        let k = snd key (data nx) in
        let edge = Right (pos nx, state,nx) in
        swaps, Move.update k (add_edge edge) moves
    | Diffing.Delete nx ->
        let k, edge = fst key (data nx), Left (pos nx, state, nx) in
        swaps, Move.update k (add_edge edge) moves
    | _ -> swaps, moves
  in
  List.fold_left add (state,(Swap.empty, Move.empty)) changes


let swap (type l r state eq diff)
    ~(key : (l, r) keys)
    ~(test : (l, r, eq, diff, state) test)
    (swaps : (l, r, state) swaps)
    (x : l with_pos) (y : r with_pos)
  : (string with_pos * string with_pos) option
=
  let kx, ky = fst key (data x), snd key (data y) in
  let k = if kx <= ky then kx, ky else ky, kx in
  match Swap.find_opt k swaps with
  | None | Some (Left _ | Right _)-> None
  | Some Both (state, (ll,lr),(rl,rr)) ->
      match test state ll rr, test state rl lr with
      | Ok _, Ok _ ->
          Some (mk_pos (pos ll) kx, mk_pos (pos rl) ky)
      | Error _, _ | _, Error _ -> None

let move (type l r eq diff tdiff state)
    ~(key : (l, r) keys)
    ~(test : (l, r, eq, diff, state) test)
    (moves : (l, r, state) moves)
    (v : (l with_pos, r with_pos) Either.t)
  : (l, r, tdiff) change option
=
  let name =
    match v with
    | Either.Left l -> fst key (data l)
    | Either.Right r -> snd key (data r)
  in
  match Move.find_opt name moves with
  | None | Some (Left _ | Right _)-> None
  | Some Both (state,got,expected) ->
      match test state got expected with
      | Ok _ ->
          Some (Move {name; got=pos got; expected=pos expected})
      | Error _ -> None

let refine (type l r eq state tdiff)
    ~(key : (l, r) keys)
    ~(update : (l, r, eq, (l, r, tdiff) mismatch, state) update)
    ~(test : (l, r, eq, (l, r, tdiff) mismatch, state) test)
    (state : state)
    (patch :
       (l with_pos, r with_pos, eq, (l, r, tdiff) mismatch)
         Diffing.change list)
  : (l, r, tdiff) change list
=
  let _, (swaps, moves) = exchanges ~key ~update state patch in
  let filter = function
    | Diffing.Keep _ -> None
    | Diffing.Insert x ->
        begin match move ~key ~test moves (Either.Right x) with
        | Some _ as move -> move
        | None -> Some (Insert {pos=pos x;insert=data x})
        end
    | Diffing.Delete x ->
        begin match move ~key ~test moves (Either.Left x) with
        | Some _ -> None
        | None -> Some (Delete {pos=pos x;delete=data x})
        end
    | Diffing.Change(x,y, reason) ->
        match swap ~key ~test swaps x y with
        | Some ((pos1,first),(pos2,last)) ->
            if pos x = pos1 then
              Some (Swap { pos = pos1, pos2; first; last})
            else None
        | None -> Some (Change reason)
  in
  List.filter_map filter patch
