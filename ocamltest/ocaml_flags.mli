(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Sebastien Hinderer, projet Gallium, INRIA Paris            *)
(*                                                                        *)
(*   Copyright 2018 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* Flags used in OCaml commands *)

val stdlib : string list

val include_toplevel_directory : string list

val c_includes : string list

val runtime_flags :
  Environments.t -> Ocaml_backends.t -> bool -> string list

val toplevel_default_flags : string list

val ocamldebug_default_flags : string list

val ocamlobjinfo_default_flags : string list
