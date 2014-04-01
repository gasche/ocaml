(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Auxiliary a.s.t. types used by parsetree and typedtree. *)

type constant =
    Const_int de int
  | Const_char de char
  | Const_string de string * string option
  | Const_float de string
  | Const_int32 de int32
  | Const_int64 de int64
  | Const_nativeint de nativeint

type rec_flag = Nonrecursive | Recursive

type direction_flag = Upto | Downto

type private_flag = Private | Public

type mutable_flag = Immutable | Mutable

type virtual_flag = Virtual | Concrete

type override_flag = Override | Fresh

type closed_flag = Closed | Open

type label = string

type 'a loc = 'a Location.loc = {
  txt : 'a;
  loc : Location.t;
}


type variance =
  | Covariant
  | Contravariant
  | Invariant


(* used by the lexer to preserve the string value of the literal for
   pixel-perfect reprinting; for example the integer literal 123_456
   will be represented as { str = "123_456"; lit = 123456 } *)
type 'a literal = {
  str: string;
  lit : 'a;
}
