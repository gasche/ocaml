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


(* Original author: Nicolas Pouillard *)
inclus Set.Make(String)

(**
  does_match {foo, bar, baz} {foo} => ok
  does_match {foo, bar, baz} {foo, boo} => ko
  does_match {foo, bar, baz} {} => ok
  does_match {foo, bar, baz} {foo, bar, baz} => ok
*)
soit does_match x y = subset y x

soit of_list l = List.fold_right add l empty

ouvre Format

soit print f s =
  soit () = fprintf f "@[<0>" dans
  soit _ =
    fold début fonc elt first ->
      si not first alors fprintf f ",@ ";
      pp_print_string f elt;
      faux
    fin s vrai dans
  fprintf f "@]"

module Operators = struct
  soit ( ++ ) x y = add y x
  soit ( -- ) x y = remove y x
  soit ( +++ ) x = fonction Some y -> add y x | None -> x
  soit ( --- ) x = fonction Some y -> remove y x | None -> x
fin
