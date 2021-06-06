
(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Gabriel Radanne, projet Cambium, Inria Paris               *)
(*                                                                        *)
(*   Copyright 2020 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(** {0 Parametric diffing}

    This module implements diffing over lists of arbitrary content.
    It is parameterized by
    - The content of the two lists
    - The equality witness when an element is kept
    - The diffing witness when an element is changed

    Diffing is extended to maintain state depending on the
    computed changes while walking through the two lists.

    The underlying algorithm is a modified Wagner-Fischer algorithm
    (see <https://en.wikipedia.org/wiki/Wagner%E2%80%93Fischer_algorithm>).

    We provide the following guarantee:
    Given two lists [l] and [r], if different patches result in different
    states, we say that the state diverges.
    - We always return the optimal patch on prefixes of [l] and [r]
      on which state does not diverge.
    - Otherwise, we return a correct but non-optimal patch where subpatches
      with no divergent states are optimal for the given initial state.

    More precisely, the optimality of Wagner-Fischer depends on the property
    that the edit-distance between a k-prefix of the left input and a l-prefix
    of the right input d(k,l) satisfies

    d(k,l) = min (
     del_cost + d(k-1,l),
     insert_cost + d(k,l-1),
     change_cost + d(k-1,l-1)
    )

   Under this hypothesis, it is optimal to choose greedily the state of the
   minimal patch transforming the left k-prefix into the right l-prefix as a
   representative of the states of all possible patches transforming the left
   k-prefix into the right l-prefix.

   If this property is not satisfied, we can still choose greedily a
   representative state. However, the computed patch is no more guaranteed to
   be globally optimal.
   Nevertheless, it is still a correct patch, which is even optimal among all
   explored patches.

*)

(** The type of potential changes on a list. *)
type ('left, 'right, 'eq, 'diff) change =
  | Delete of 'left
  | Insert of 'right
  | Keep of 'left * 'right * 'eq
  | Change of 'left * 'right * 'diff

type ('left, 'right, 'eq, 'diff) patch = ('left, 'right, 'eq, 'diff) change list

(** Printing default function *)
type change_kind =
  | Deletion
  | Insertion
  | Modification
  | Preservation

val classify: _ change -> change_kind
val prefix: Format.formatter -> (int * change_kind) -> unit
val style: change_kind -> Misc.Color.style list

module type Diffable = sig
  type left
  type right

  type eq
  type diff

  (** The type of potential changes on a list. *)
  type nonrec change = (left, right, eq, diff) change

  (** A patch is an ordered list of changes. *)
  type patch = change list

  val weight : change -> int

  type state

  (** [test st xl xr] tests if the elements [xl] and [xr] are
      compatible ([Ok]) or not ([Error]). *)
  val test : state -> left -> right -> (eq, diff) result

  (** [update change state] return the new state after applying a change.

     We support variadic diffing: dynamically extending the lists to
     diff depending on the placement choices for a prefix of the
     input. This is done by returning (optional) extensions for the
     left or right input array. *)
  val update : change -> state -> state * left array option * right array option
end

module Make (T : Diffable) : sig
  val diff : T.state -> T.left array -> T.right array -> T.patch
end
