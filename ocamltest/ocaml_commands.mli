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

(* Helper functions to build OCaml-related commands *)

val ocamlrun_ocamlc : string list

val ocamlrun_ocamlopt : string list

val ocamlrun_ocaml : string list

val ocamlrun_expect_test : string list

val ocamlrun_ocamllex : string list

val ocamlrun_ocamldoc : string list

val ocamlrun_ocamldebug : string list

val ocamlrun_ocamlobjinfo : string list

val ocamlrun_ocamlmklib : string list
val ocamlrun_codegen : string list
