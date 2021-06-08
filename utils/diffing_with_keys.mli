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

(**

   When diffing lists where each element has a distinct key, we can refine
   the diffing patch by introducing two composite edit moves: swaps and moves.

   [Swap]s exchange the position of two elements. [Swap] cost is set to
   [2 * change - epsilon].
   [Move]s change the position of one element. [Move] cost is set to
   [delete + addition - epsilon].

   When the cost [delete + addition] is greater than [change] and with those
   specific weights, the optimal patch with [Swap]s and [Move]s can be computed
   directly and cheaply from the original optimal patch.

*)

type 'a with_pos = int * 'a

type ('l, 'r, 'tdiff) mismatch =
  | Name of {pos:int; got:string; expected:string; types_match:bool}
  | Type of {pos:int; got:'l; expected:'r; reason:'tdiff}

type ('l, 'r, 'tdiff) keyed_change =
  | Change of ('l, 'r, 'tdiff) mismatch
  | Swap of {pos: int * int; first: string; last: string}
  | Move of {name:string; got:int; expected:int}
  | Delete of {pos:int; delete:'l}
  | Insert of {pos:int; insert:'r}

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

module Make (T : Diffable_with_keys) : sig
  open T
  val diff : state -> left array -> right array -> keyed_patch
end

val prefix: Format.formatter -> ('l, 'r, 'tdiff) keyed_change -> unit
