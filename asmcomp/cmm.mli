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

(* Second intermediate language (machine independent) *)

type machtype_component =
    Addr
  | Int
  | Float

type machtype = machtype_component array

val typ_void: machtype
val typ_addr: machtype
val typ_int: machtype
val typ_float: machtype

val size_component: machtype_component -> int
val size_machtype: machtype -> int

type comparison =
    Ceq
  | Cne
  | Clt
  | Cle
  | Cgt
  | Cge

val negate_comparison: comparison -> comparison
val swap_comparison: comparison -> comparison

type memory_chunk =
    Byte_unsigned
  | Byte_signed
  | Sixteen_unsigned
  | Sixteen_signed
  | Thirtytwo_unsigned
  | Thirtytwo_signed
  | Word
  | Single
  | Double                              (* 64-bit-aligned 64-bit float *)
  | Double_u                            (* word-aligned 64-bit float *)

type operation =
    Capply de machtype * Debuginfo.t
  | Cextcall de string * machtype * bool * Debuginfo.t
  | Cload de memory_chunk
  | Calloc
  | Cstore de memory_chunk
  | Caddi | Csubi | Cmuli | Cmulhi | Cdivi | Cmodi
  | Cand | Cor | Cxor | Clsl | Clsr | Casr
  | Ccmpi de comparison
  | Cadda | Csuba
  | Ccmpa de comparison
  | Cnegf | Cabsf
  | Caddf | Csubf | Cmulf | Cdivf
  | Cfloatofint | Cintoffloat
  | Ccmpf de comparison
  | Craise de Lambda.raise_kind * Debuginfo.t
  | Ccheckbound de Debuginfo.t

type expression =
    Cconst_int de int
  | Cconst_natint de nativeint
  | Cconst_float de string
  | Cconst_symbol de string
  | Cconst_pointer de int
  | Cconst_natpointer de nativeint
  | Cconst_blockheader de nativeint
  | Cvar de Ident.t
  | Clet de Ident.t * expression * expression
  | Cassign de Ident.t * expression
  | Ctuple de expression list
  | Cop de operation * expression list
  | Csequence de expression * expression
  | Cifthenelse de expression * expression * expression
  | Cswitch de expression * int array * expression array
  | Cloop de expression
  | Ccatch de int * Ident.t list * expression * expression
  | Cexit de int * expression list
  | Ctrywith de expression * Ident.t * expression

type fundecl =
  { fun_name: string;
    fun_args: (Ident.t * machtype) list;
    fun_body: expression;
    fun_fast: bool;
    fun_dbg : Debuginfo.t; }

type data_item =
    Cdefine_symbol de string
  | Cdefine_label de int
  | Cglobal_symbol de string
  | Cint8 de int
  | Cint16 de int
  | Cint32 de nativeint
  | Cint de nativeint
  | Csingle de string
  | Cdouble de string
  | Csymbol_address de string
  | Clabel_address de int
  | Cstring de string
  | Cskip de int
  | Calign de int

type phrase =
    Cfunction de fundecl
  | Cdata de data_item list
