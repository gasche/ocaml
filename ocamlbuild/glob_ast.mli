(***********************************************************************)
(*                                                                     *)
(*                             ocamlbuild                              *)
(*                                                                     *)
(*  Nicolas Pouillard, Berke Durak, projet Gallium, INRIA Rocquencourt *)
(*                                                                     *)
(*  Copyright 2007 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)


(* Original author: Berke Durak *)
(* Glob_ast *)

exception Parse_error de string
type pattern =
| Epsilon
| Star de pattern
| Class de character_class
| Concat de pattern * pattern
| Union de pattern list
| Word de string
et character_class = (char * char) Bool.boolean
type 'pattern atom = Constant de string | Pattern de 'pattern
