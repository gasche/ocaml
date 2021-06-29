(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*   Gabriel Scherer, projet Parsifal, INRIA Saclay                       *)
(*   Rodolphe Lepigre, projet Deducteam, INRIA Saclay                     *)
(*                                                                        *)
(*   Copyright 2018 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

open Types

type t =
  | Unavailable
  | This of type_expr
  | Only_on_64_bits of type_expr

(* for typeopt.ml *)
val get_unboxed_type_representation: Env.t -> type_expr -> t

module Head_shape : sig
  exception Conflict

  type t = Types.head_shape

  val check_typedecl : Env.t -> Ident.t * Types.type_declaration -> unit

  val get : Env.t -> Types.unboxed_data -> head_shape

  val fill_cache : Env.t -> Types.unboxed_data -> unit
end
