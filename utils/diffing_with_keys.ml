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
let with_pos t = Array.mapi (fun i n -> (i+1, n)) t
let pos (x,_) = x
let data (_,x) = x
let mk_pos pos data = pos, data

type ('l, 'r, 'tdiff) mismatch =
  | Name of {pos:int; got:string; expected:string; types_match:bool}
  | Type of {pos:int; got:'l; expected:'r; reason:'tdiff}

type ('l, 'r, 'tdiff) keyed_change =
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

module type Diffable_with_keys = sig
  type tdiff

  type left
  type right

  type keyed_left = left with_pos
  type keyed_right = right with_pos

  include (Diffing.Diffable with
    type left := keyed_left
    and type right := keyed_right
    and type diff = (left, right, tdiff) mismatch
  )

  (* diffing-with-keys does not support variadic diffing *)
  val update : change -> state -> state

  val key_left : left -> string
  val key_right : right -> string
  type nonrec keyed_change = (left, right, tdiff) keyed_change
  type keyed_patch = keyed_change list
end

module Make (T : Diffable_with_keys) = struct
  open T

  module Swap = Map.Make(struct
      type t = string * string
      let compare: t -> t -> int = Stdlib.compare
    end)
  module Move = Misc.Stdlib.String.Map

  type ('l, 'r) partial_edge =
    | Left of int * state * 'l
    | Right of int * state * 'r
    | Both of state * 'l * 'r

  let add_edge (type l r)
      (ex : (l, r) partial_edge)
      (ey : (l, r) partial_edge option)
    : (l, r) partial_edge option
  = match ex, ey with
    | ex, None -> Some ex
    | Left (lpos, lstate, l), Some Right (rpos, rstate,r)
    | Right (rpos, rstate,r), Some Left (lpos, lstate, l) ->
        let state = if lpos < rpos then rstate else lstate in
        Some (Both (state,l,r))
    | Both _ as b, _ | _, Some (Both _ as b)  -> Some b
    | l, _ -> Some l

  type partial_move_edge =
   (keyed_left, keyed_right) partial_edge
  type partial_swap_edge =
    (keyed_left * keyed_right, keyed_left * keyed_right) partial_edge

  let swap_edge (state : state) (x : keyed_left) (y : keyed_right)
    : Swap.key * partial_swap_edge
  =
    let kx, ky = key_left (data x), key_right (data y) in
    if kx <= ky then
      (kx,ky), Left (pos x, state, (x,y))
    else
      (ky,kx), Right(pos x,state, (x,y))

  type swaps = partial_swap_edge Swap.t
  type moves = partial_move_edge Move.t

  let exchanges (state : state) (changes : change list): state * (swaps * moves) =
    let add (state, (swaps, moves)) d =
      update d state,
      match d with
      | Diffing.Change (x,y,_) ->
          let k, edge = swap_edge state x y in
          Swap.update k (add_edge edge) swaps, moves
      | Diffing.Insert nx ->
          let k = key_right (data nx) in
          let edge = Right (pos nx, state,nx) in
          swaps, Move.update k (add_edge edge) moves
      | Diffing.Delete nx ->
          let k, edge = key_left (data nx), Left (pos nx, state, nx) in
          swaps, Move.update k (add_edge edge) moves
      | _ -> swaps, moves
    in
    List.fold_left add (state,(Swap.empty, Move.empty)) changes

  let swap (swaps : swaps) (x : keyed_left) (y : keyed_right)
    : (string with_pos * string with_pos) option
  =
    let kx, ky = key_left (data x), key_right (data y) in
    let k = if kx <= ky then kx, ky else ky, kx in
    match Swap.find_opt k swaps with
    | None | Some (Left _ | Right _)-> None
    | Some Both (state, (ll,lr),(rl,rr)) ->
        match test state ll rr, test state rl lr with
        | Ok _, Ok _ ->
            Some (mk_pos (pos ll) kx, mk_pos (pos rl) ky)
        | Error _, _ | _, Error _ -> None

  let move (moves : moves) (v : (keyed_left, keyed_right) Either.t)
    : keyed_change option
  =
    let name =
      match v with
      | Either.Left l -> key_left (data l)
      | Either.Right r -> key_right (data r)
    in
    match Move.find_opt name moves with
    | None | Some (Left _ | Right _)-> None
    | Some Both (state,got,expected) ->
        match test state got expected with
        | Ok _ ->
            Some (Move {name; got=pos got; expected=pos expected})
        | Error _ -> None

  let refine (state : state) (patch : change list) : keyed_change list =
    let _, (swaps, moves) = exchanges state patch in
    let filter = function
      | Diffing.Keep _ -> None
      | Diffing.Insert x ->
          begin match move moves (Either.Right x) with
          | Some _ as move -> move
          | None -> Some (Insert {pos=pos x;insert=data x})
          end
      | Diffing.Delete x ->
          begin match move moves (Either.Left x) with
          | Some _ -> None
          | None -> Some (Delete {pos=pos x;delete=data x})
          end
      | Diffing.Change(x,y, reason) ->
          match swap swaps x y with
          | Some ((pos1,first),(pos2,last)) ->
              if pos x = pos1 then
                Some (Swap { pos = pos1, pos2; first; last})
              else None
          | None -> Some (Change reason)
    in
    List.filter_map filter patch

  let diff state line column =
    let module Diff = Diffing.Make(struct
        include T
        type left = keyed_left
        type right = keyed_right
        let update d st = update d st, None, None
      end)
    in
    Diff.diff state (with_pos line) (with_pos column)
    |> refine state
end
