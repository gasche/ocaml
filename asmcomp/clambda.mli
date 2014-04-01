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

ouvre Asttypes
ouvre Lambda

type function_label = string

type ustructured_constant =
  | Uconst_float de string
  | Uconst_int32 de int32
  | Uconst_int64 de int64
  | Uconst_nativeint de nativeint
  | Uconst_block de int * uconstant list
  | Uconst_float_array de string list
  | Uconst_string de string

et uconstant =
  | Uconst_ref de string * ustructured_constant
  | Uconst_int de int
  | Uconst_ptr de int

type ulambda =
    Uvar de Ident.t
  | Uconst de uconstant
  | Udirect_apply de function_label * ulambda list * Debuginfo.t
  | Ugeneric_apply de ulambda * ulambda list * Debuginfo.t
  | Uclosure de ufunction list * ulambda list
  | Uoffset de ulambda * int
  | Ulet de Ident.t * ulambda * ulambda
  | Uletrec de (Ident.t * ulambda) list * ulambda
  | Uprim de primitive * ulambda list * Debuginfo.t
  | Uswitch de ulambda * ulambda_switch
  | Ustringswitch de ulambda * (string * ulambda) list * ulambda
  | Ustaticfail de int * ulambda list
  | Ucatch de int * Ident.t list * ulambda * ulambda
  | Utrywith de ulambda * Ident.t * ulambda
  | Uifthenelse de ulambda * ulambda * ulambda
  | Usequence de ulambda * ulambda
  | Uwhile de ulambda * ulambda
  | Ufor de Ident.t * ulambda * ulambda * direction_flag * ulambda
  | Uassign de Ident.t * ulambda
  | Usend de meth_kind * ulambda * ulambda * ulambda list * Debuginfo.t

et ufunction = {
  label  : function_label;
  arity  : int;
  params : Ident.t list;
  body   : ulambda;
  dbg    : Debuginfo.t;
}

et ulambda_switch =
  { us_index_consts: int array;
    us_actions_consts: ulambda array;
    us_index_blocks: int array;
    us_actions_blocks: ulambda array}

(* Description of known functions *)

type function_description =
  { fun_label: function_label;          (* Label of direct entry point *)
    fun_arity: int;                     (* Number of arguments *)
    modifiable fun_closed: bool;           (* True if environment not used *)
    modifiable fun_inline: (Ident.t list * ulambda) option }

(* Approximation of values *)

type value_approximation =
    Value_closure de function_description * value_approximation
  | Value_tuple de value_approximation array
  | Value_unknown
  | Value_const de uconstant
  | Value_global_field de string * int
