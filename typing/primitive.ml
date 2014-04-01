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

(* Description of primitive functions *)

ouvre Misc

type description =
  { prim_name: string;         (* Name of primitive  or C function *)
    prim_arity: int;           (* Number of arguments *)
    prim_alloc: bool;          (* Does it allocates or raise? *)
    prim_native_name: string;  (* Name of C function for the nat. code gen. *)
    prim_native_float: bool }  (* Does the above operate on unboxed floats? *)

soit parse_declaration arity decl =
  filtre decl avec
  | name :: "noalloc" :: name2 :: "float" :: _ ->
      {prim_name = name; prim_arity = arity; prim_alloc = faux;
       prim_native_name = name2; prim_native_float = vrai}
  | name :: "noalloc" :: name2 :: _ ->
      {prim_name = name; prim_arity = arity; prim_alloc = faux;
       prim_native_name = name2; prim_native_float = faux}
  | name :: name2 :: "float" :: _ ->
      {prim_name = name; prim_arity = arity; prim_alloc = vrai;
       prim_native_name = name2; prim_native_float = vrai}
  | name :: "noalloc" :: _ ->
      {prim_name = name; prim_arity = arity; prim_alloc = faux;
       prim_native_name = ""; prim_native_float = faux}
  | name :: name2 :: _ ->
      {prim_name = name; prim_arity = arity; prim_alloc = vrai;
       prim_native_name = name2; prim_native_float = faux}
  | name :: _ ->
      {prim_name = name; prim_arity = arity; prim_alloc = vrai;
       prim_native_name = ""; prim_native_float = faux}
  | [] ->
      fatal_error "Primitive.parse_declaration"

soit description_list p =
  soit list = [p.prim_name] dans
  soit list = si not p.prim_alloc alors "noalloc" :: list sinon list dans
  soit list =
    si p.prim_native_name <> "" alors p.prim_native_name :: list sinon list
  dans
  soit list = si p.prim_native_float alors "float" :: list sinon list dans
  List.rev list

soit native_name p =
  si p.prim_native_name <> ""
  alors p.prim_native_name
  sinon p.prim_name

soit byte_name p =
  p.prim_name
