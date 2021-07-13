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
  type t = Types.head_shape

  (** Check a new type decalaration, that may be a variant type
      containing unboxed constructors, to verify that the unboxing
      requests respect the "disjointness" requirement of constructor
      unboxing -- the values of two constructors must not conflict.

     This function fails with a fatal error if the declaration is
     unsafe. *)
  val check_typedecl : Env.t -> Path.t * Types.type_declaration -> unit

  (** Returns the head shape information of an unboxed constructor,
      computing it on the fly if necessary. The typing environment must
      be an extension of the environment in which the unboxed
      constructor was declared. *)
  val get : Env.t -> Types.unboxed_data -> head_shape

  (** Returns the head shape information of variant type path,
      similarly to [get] above. *)
  val of_type : Env.t -> Path.t -> t

  val unboxed_type_data_of_shape : t -> Types.unboxed_type_data
end
