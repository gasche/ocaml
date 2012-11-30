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

(* A variant of the "lambda" code with direct / indirect calls explicit
   and closures explicit too *)

open Asttypes
open Lambda

type function_label = string

type ulambda =
    Uvar of Ident.t
  | Uconst of structured_constant * string option
  | Udirect_apply of function_label * ulambda list * Debuginfo.t
  | Ugeneric_apply of ulambda * ulambda list * Debuginfo.t
  | Uclosure of ufunction list * ulambda list
  | Uoffset of ulambda * int
  | Ulet of Ident.t * ulambda * ulambda
  | Uletrec of (Ident.t * ulambda) list * ulambda
  | Uprim of primitive * ulambda list * Debuginfo.t
  | Uswitch of ulambda * ulambda_switch
  | Ustaticfail of int * ulambda list
  | Ucatch of int * Ident.t list * ulambda * ulambda
  | Utrywith of ulambda * Ident.t * ulambda
  | Uifthenelse of ulambda * ulambda * ulambda
  | Usequence of ulambda * ulambda
  | Uwhile of ulambda * ulambda
  | Ufor of Ident.t * ulambda * ulambda * direction_flag * ulambda
  | Uassign of Ident.t * ulambda
  | Usend of meth_kind * ulambda * ulambda * ulambda list * Debuginfo.t

and ufunction = {
  label  : function_label;
  arity  : int;
  params : Ident.t list;
  body   : ulambda;
  dbg    : Debuginfo.t
}

and ulambda_switch =
  { us_index_consts: int option array;
    us_actions_consts : ulambda array;
    us_index_blocks: int option array;
    us_actions_blocks: ulambda array}

(* Description of known functions *)

type function_description =
  { fun_label: function_label;          (* Label of direct entry point *)
    fun_arity: int;                     (* Number of arguments *)
    mutable fun_closed: bool;           (* True if environment not used *)
    mutable fun_inline: (Ident.t list * ulambda) option }

(* Approximation of values *)

type approx_var =
  | Var_unknown
  | Var_local of Ident.t
  | Var_global of Ident.t * int

type possible_tag = bool array

type closure_approx =
    { clos_desc : function_description;
      clos_approx_res : value_approximation;
      clos_approx_env : value_approximation array; }

and value_approximation_desc =
    Value_closure of closure_approx
  | Value_tag of possible_tag
  | Value_block of int * value_approximation array
  | Value_unknown
  | Value_integer of int
  | Value_constptr of int
  | Value_bottom

and value_approximation =
  { approx_desc : value_approximation_desc;
    approx_var : approx_var }

let mkapprox ?id approx_desc =
  { approx_desc;
    approx_var =
      match id with
      | None -> Var_unknown
      | Some id -> Var_local id }

let value_unknown = mkapprox Value_unknown
let value_bottom = mkapprox Value_bottom
let value_integer i = mkapprox (Value_integer i)
let value_constptr i = mkapprox (Value_constptr i)
let value_closure fundesc approx_res env_approx =
  mkapprox (Value_closure{ clos_desc = fundesc;
                           clos_approx_res = approx_res;
                           clos_approx_env = env_approx })

let possible_tag ?tag () =
  let tags = match tag with
    | None -> Array.create 256 true
    | Some l -> Array.init 256 (fun j -> List.mem j l) in
  mkapprox (Value_tag tags)

let rec remove_approx ?(remove_global=false) approx =
  let clean_desc = function
    | Value_closure { clos_desc;
                      clos_approx_res = approx_res;
                      clos_approx_env = approx_env } ->
       Value_closure { clos_desc;
                       clos_approx_res = remove_approx ~remove_global approx_res;
                       clos_approx_env = Array.map (remove_approx ~remove_global) approx_env }
    | Value_block (tag, a) ->
       Value_block (tag, Array.map (remove_approx ~remove_global) a)
    | (Value_unknown
      | Value_integer _
      | Value_constptr _
      | Value_bottom
      | Value_tag _) as desc -> desc
  in
  match approx.approx_var with
  | Var_global _ when not remove_global ->
     approx
  | Var_global _
  | Var_unknown
  | Var_local _ ->
     { approx_desc = clean_desc approx.approx_desc;
       approx_var = Var_unknown }
