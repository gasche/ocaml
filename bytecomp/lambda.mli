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

(* The "lambda" intermediate code *)

ouvre Asttypes

type compile_time_constant =
  | Big_endian
  | Word_size
  | Ostype_unix
  | Ostype_win32
  | Ostype_cygwin

type primitive =
    Pidentity
  | Pignore
  | Prevapply de Location.t
  | Pdirapply de Location.t
    (* Globals *)
  | Pgetglobal de Ident.t
  | Psetglobal de Ident.t
  (* Operations on heap blocks *)
  | Pmakeblock de int * mutable_flag
  | Pfield de int
  | Psetfield de int * bool
  | Pfloatfield de int
  | Psetfloatfield de int
  | Pduprecord de Types.record_representation * int
  (* Force lazy values *)
  | Plazyforce
  (* External call *)
  | Pccall de Primitive.description
  (* Exceptions *)
  | Praise de raise_kind
  (* Boolean operations *)
  | Psequand | Psequor | Pnot
  (* Integer operations *)
  | Pnegint | Paddint | Psubint | Pmulint | Pdivint | Pmodint
  | Pandint | Porint | Pxorint
  | Plslint | Plsrint | Pasrint
  | Pintcomp de comparison
  | Poffsetint de int
  | Poffsetref de int
  (* Float operations *)
  | Pintoffloat | Pfloatofint
  | Pnegfloat | Pabsfloat
  | Paddfloat | Psubfloat | Pmulfloat | Pdivfloat
  | Pfloatcomp de comparison
  (* String operations *)
  | Pstringlength | Pstringrefu | Pstringsetu | Pstringrefs | Pstringsets
  (* Array operations *)
  | Pmakearray de array_kind
  | Parraylength de array_kind
  | Parrayrefu de array_kind
  | Parraysetu de array_kind
  | Parrayrefs de array_kind
  | Parraysets de array_kind
  (* Test if the argument is a block or an immediate integer *)
  | Pisint
  (* Test if the (integer) argument is outside an interval *)
  | Pisout
  (* Bitvect operations *)
  | Pbittest
  (* Operations on boxed integers (Nativeint.t, Int32.t, Int64.t) *)
  | Pbintofint de boxed_integer
  | Pintofbint de boxed_integer
  | Pcvtbint de boxed_integer (*source*) * boxed_integer (*destination*)
  | Pnegbint de boxed_integer
  | Paddbint de boxed_integer
  | Psubbint de boxed_integer
  | Pmulbint de boxed_integer
  | Pdivbint de boxed_integer
  | Pmodbint de boxed_integer
  | Pandbint de boxed_integer
  | Porbint de boxed_integer
  | Pxorbint de boxed_integer
  | Plslbint de boxed_integer
  | Plsrbint de boxed_integer
  | Pasrbint de boxed_integer
  | Pbintcomp de boxed_integer * comparison
  (* Operations on big arrays: (unsafe, #dimensions, kind, layout) *)
  | Pbigarrayref de bool * int * bigarray_kind * bigarray_layout
  | Pbigarrayset de bool * int * bigarray_kind * bigarray_layout
  (* size of the nth dimension of a big array *)
  | Pbigarraydim de int
  (* load/set 16,32,64 bits from a string: (unsafe)*)
  | Pstring_load_16 de bool
  | Pstring_load_32 de bool
  | Pstring_load_64 de bool
  | Pstring_set_16 de bool
  | Pstring_set_32 de bool
  | Pstring_set_64 de bool
  (* load/set 16,32,64 bits from a
     (char, int8_unsigned_elt, c_layout) Bigarray.Array1.t : (unsafe) *)
  | Pbigstring_load_16 de bool
  | Pbigstring_load_32 de bool
  | Pbigstring_load_64 de bool
  | Pbigstring_set_16 de bool
  | Pbigstring_set_32 de bool
  | Pbigstring_set_64 de bool
  (* Compile time constants *)
  | Pctconst de compile_time_constant
  (* byte swap *)
  | Pbswap16
  | Pbbswap de boxed_integer

et comparison =
    Ceq | Cneq | Clt | Cgt | Cle | Cge

et array_kind =
    Pgenarray | Paddrarray | Pintarray | Pfloatarray

et boxed_integer =
    Pnativeint | Pint32 | Pint64

et bigarray_kind =
    Pbigarray_unknown
  | Pbigarray_float32 | Pbigarray_float64
  | Pbigarray_sint8 | Pbigarray_uint8
  | Pbigarray_sint16 | Pbigarray_uint16
  | Pbigarray_int32 | Pbigarray_int64
  | Pbigarray_caml_int | Pbigarray_native_int
  | Pbigarray_complex32 | Pbigarray_complex64

et bigarray_layout =
    Pbigarray_unknown_layout
  | Pbigarray_c_layout
  | Pbigarray_fortran_layout

et raise_kind =
  | Raise_regular
  | Raise_reraise
  | Raise_notrace

type structured_constant =
    Const_base de constant
  | Const_pointer de int
  | Const_block de int * structured_constant list
  | Const_float_array de string list
  | Const_immstring de string

type function_kind = Curried | Tupled

type let_kind = Strict | Alias | StrictOpt | Variable
(* Meaning of kinds for let x = e in e':
    Strict: e may have side-effets; always evaluate e first
      (If e is a simple expression, e.g. a variable or constant,
       we may still substitute e'[x/e].)
    Alias: e is pure, we can substitute e'[x/e] if x has 0 or 1 occurrences
      in e'
    StrictOpt: e does not have side-effects, but depend on the store;
      we can discard e if x does not appear in e'
    Variable: the variable x is assigned later in e' *)

type meth_kind = Self | Public | Cached

type shared_code = (int * int) list     (* stack size -> code label *)

type lambda =
    Lvar de Ident.t
  | Lconst de structured_constant
  | Lapply de lambda * lambda list * Location.t
  | Lfunction de function_kind * Ident.t list * lambda
  | Llet de let_kind * Ident.t * lambda * lambda
  | Lletrec de (Ident.t * lambda) list * lambda
  | Lprim de primitive * lambda list
  | Lswitch de lambda * lambda_switch
(* switch on strings, clauses are sorted by string order,
   strings are pairwise distinct *)
  | Lstringswitch de lambda * (string * lambda) list * lambda
  | Lstaticraise de int * lambda list
  | Lstaticcatch de lambda * (int * Ident.t list) * lambda
  | Ltrywith de lambda * Ident.t * lambda
  | Lifthenelse de lambda * lambda * lambda
  | Lsequence de lambda * lambda
  | Lwhile de lambda * lambda
  | Lfor de Ident.t * lambda * lambda * direction_flag * lambda
  | Lassign de Ident.t * lambda
  | Lsend de meth_kind * lambda * lambda * lambda list * Location.t
  | Levent de lambda * lambda_event
  | Lifused de Ident.t * lambda

et lambda_switch =
  { sw_numconsts: int;                  (* Number of integer cases *)
    sw_consts: (int * lambda) list;     (* Integer cases *)
    sw_numblocks: int;                  (* Number of tag block cases *)
    sw_blocks: (int * lambda) list;     (* Tag block cases *)
    sw_failaction : lambda option}      (* Action to take if failure *)
et lambda_event =
  { lev_loc: Location.t;
    lev_kind: lambda_event_kind;
    lev_repr: int ref option;
    lev_env: Env.summary }

et lambda_event_kind =
    Lev_before
  | Lev_after de Types.type_expr
  | Lev_function

val same: lambda -> lambda -> bool
val const_unit: structured_constant
val lambda_unit: lambda
val name_lambda: let_kind -> lambda -> (Ident.t -> lambda) -> lambda
val name_lambda_list: lambda list -> (lambda list -> lambda) -> lambda

val iter: (lambda -> unit) -> lambda -> unit
module IdentSet: Set.S avec type elt = Ident.t
val free_variables: lambda -> IdentSet.t
val free_methods: lambda -> IdentSet.t

val transl_normal_path: Path.t -> lambda   (* Path.t is already normal *)
val transl_path: ?loc:Location.t -> Env.t -> Path.t -> lambda
val make_sequence: ('a -> lambda) -> 'a list -> lambda

val subst_lambda: lambda Ident.tbl -> lambda -> lambda
val bind : let_kind -> Ident.t -> lambda -> lambda -> lambda

val commute_comparison : comparison -> comparison
val negate_comparison : comparison -> comparison

(***********************)
(* For static failures *)
(***********************)

(* Get a new static failure ident *)
val next_raise_count : unit -> int


val staticfail : lambda (* Anticipated static failure *)

(* Check anticipated failure, substitute its final value *)
val is_guarded: lambda -> bool
val patch_guarded : lambda -> lambda -> lambda

val raise_kind: raise_kind -> string
