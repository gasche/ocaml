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

type imm = Imm of int [@@unboxed]
type tag = Tag of int [@@unboxed]

type head =
  | Immediate of imm
  | Block of tag

module ImmSet = Set.Make(struct type t = imm let compare = Stdlib.compare end)
module TagSet = Set.Make(struct type t = tag let compare = Stdlib.compare end)

module Or_any = struct
  type 'a t = Those of 'a | Any

  let mon_bind2 f a b =
    match a, b with
    | Any, _ | _, Any -> Any
    | Those va, Those vb -> f va vb

  let mon_map2 f a b =
    mon_bind2 (fun va vb -> Those (f va vb)) a b
end
type 'a or_any = 'a Or_any.t = Those of 'a | Any

type imm_set = ImmSet.t or_any
type block_set = TagSet.t or_any

type t = {
  imms: imm_set;
  blocks: block_set;
}
type shape = t

let mem head shape =
  match head with
  | Immediate imm ->
    begin match shape.imms with
    | Any -> true
    | Those set -> ImmSet.mem imm set
    end
  | Block tag ->
    begin match shape.blocks with
    | Any -> true
    | Those set -> TagSet.mem tag set
    end

type unboxed_cstr_description = (Types.type_expr, t) Misc.Cached.t
