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

type t =
    Pident de Ident.t
  | Pdot de t * string * int
  | Papply de t * t

soit nopos = -1

soit rec same p1 p2 =
  filtre (p1, p2) avec
    (Pident id1, Pident id2) -> Ident.same id1 id2
  | (Pdot(p1, s1, pos1), Pdot(p2, s2, pos2)) -> s1 = s2 && same p1 p2
  | (Papply(fun1, arg1), Papply(fun2, arg2)) ->
       same fun1 fun2 && same arg1 arg2
  | (_, _) -> faux

soit rec isfree id = fonction
    Pident id' -> Ident.same id id'
  | Pdot(p, s, pos) -> isfree id p
  | Papply(p1, p2) -> isfree id p1 || isfree id p2

soit rec binding_time = fonction
    Pident id -> Ident.binding_time id
  | Pdot(p, s, pos) -> binding_time p
  | Papply(p1, p2) -> max (binding_time p1) (binding_time p2)

soit kfalse x = faux

soit rec name ?(paren=kfalse) = fonction
    Pident id -> Ident.name id
  | Pdot(p, s, pos) ->
      name ~paren p ^ si paren s alors ".( " ^ s ^ " )" sinon "." ^ s
  | Papply(p1, p2) -> name ~paren p1 ^ "(" ^ name ~paren p2 ^ ")"

soit rec head = fonction
    Pident id -> id
  | Pdot(p, s, pos) -> head p
  | Papply(p1, p2) -> affirme faux

soit rec last = fonction
  | Pident id -> Ident.name id
  | Pdot(_, s, _) -> s
  | Papply(_, p) -> last p
