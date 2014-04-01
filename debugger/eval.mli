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

ouvre Types
ouvre Parser_aux
ouvre Format

val expression :
    Instruct.debug_event option -> Env.t -> expression ->
    Debugcom.Remote_value.t * type_expr

type error =
  | Unbound_identifier de Ident.t
  | Not_initialized_yet de Path.t
  | Unbound_long_identifier de Longident.t
  | Unknown_name de int
  | Tuple_index de type_expr * int * int
  | Array_index de int * int
  | List_index de int * int
  | String_index de string * int * int
  | Wrong_item_type de type_expr * int
  | Wrong_label de type_expr * string
  | Not_a_record de type_expr
  | No_result

exception Error de error

val report_error: formatter -> error -> unit
