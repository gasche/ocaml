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
(* Bool *)

type 'a boolean = And de 'a boolean list | Or de 'a boolean list | Not de 'a boolean | Atom de 'a | True | False;;

soit rec eval f = fonction
  | And l -> List.for_all (eval f) l
  | Or l -> List.exists (eval f) l
  | Not x -> not (eval f x)
  | Atom a -> f a
  | True -> vrai
  | False -> faux
;;
soit rec iter f = fonction
  | (And l|Or l) -> List.iter (iter f) l
  | Not x -> iter f x
  | Atom a -> f a
  | True|False -> ()
;;
soit rec map f = fonction
  | And l -> And(List.map (map f) l)
  | Or l -> Or(List.map (map f) l)
  | Not x -> Not(map f x)
  | Atom a -> Atom(f a)
  | (True|False) tel b -> b
;;
