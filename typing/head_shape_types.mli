(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*   Gabriel Scherer, projet Partout, INRIA Saclay                        *)
(*   Nicolas Chataing, ENS Paris                                          *)
(*                                                                        *)
(*   Copyright 2021 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* Over-approximation of the possible values of a type,
   used to verify and compile unboxed head constructors.

   We consider the "head" of a value: the value itself if it is an
   immediate, or its tag and size if is a block. A head "shape" is a set of
   possible heads.

   The "head" of a value is an abstraction or approximation of the value,
   the "head shape" is an abstraction or approximation of a (closed) type.
*)

type imm = Imm of int [@@unboxed]
type tag = Tag of int [@@unboxed]

module ImmSet : Set.S with type elt = imm
module TagSet : Set.S with type elt = tag

module Or_any : sig
  type 'a t = Those of 'a | Any
  val mon_map2 : ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t
  val mon_bind2 : ('a -> 'b -> 'c t) -> 'a t -> 'b t -> 'c t
end
type 'a or_any = 'a Or_any.t = Those of 'a | Any

type imm_set = ImmSet.t or_any
type block_set = TagSet.t or_any

type t = {
  imms: imm_set; (* set of immediates the head can be *)
  blocks: block_set; (* set of block shapes the head can be *)
}

type unboxed_cstr_description = TODO
