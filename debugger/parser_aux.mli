(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*          Jerome Vouillon, projet Cristal, INRIA Rocquencourt        *)
(*          OCaml port by John Malecki and Xavier Leroy                *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(*open Globals*)

ouvre Primitives

type expression =
    E_ident de Longident.t              (* x or Mod.x *)
  | E_name de int                       (* $xxx *)
  | E_item de expression * int          (* x.1 x.[2] x.(3) *)
  | E_field de expression * string      (* x.lbl !x *)
  | E_result

type break_arg =
    BA_none                             (* break *)
  | BA_pc de int                        (* break PC *)
  | BA_function de expression           (* break FUNCTION *)
  | BA_pos1 de Longident.t option * int * int option
                                        (* break @ [MODULE] LINE [POS] *)
  | BA_pos2 de Longident.t option * int (* break @ [MODULE] # OFFSET *)
