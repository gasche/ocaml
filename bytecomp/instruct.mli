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

(* The type of the instructions of the abstract machine *)

ouvre Lambda

(* Structure of compilation environments *)

type compilation_env =
  { ce_stack: int Ident.tbl; (* Positions of variables in the stack *)
    ce_heap: int Ident.tbl;  (* Structure of the heap-allocated env *)
    ce_rec: int Ident.tbl }  (* Functions bound by the same let rec *)

(* The ce_stack component gives locations of variables residing
   in the stack. The locations are offsets w.r.t. the origin of the
   stack frame.
   The ce_heap component gives the positions of variables residing in the
   heap-allocated environment.
   The ce_rec component associate offsets to identifiers for functions
   bound by the same let rec as the current function.  The offsets
   are used by the OFFSETCLOSURE instruction to recover the closure
   pointer of the desired function from the env register (which
   points to the closure for the current function). *)

(* Debugging events *)

(* Warning: when you change these types, check byterun/backtrace.c *)
type debug_event =
  { modifiable ev_pos: int;                (* Position in bytecode *)
    ev_module: string;                  (* Name of defining module *)
    ev_loc: Location.t;                 (* Location in source file *)
    ev_kind: debug_event_kind;          (* Before/after event *)
    ev_info: debug_event_info;          (* Extra information *)
    ev_typenv: Env.summary;             (* Typing environment *)
    ev_typsubst: Subst.t;               (* Substitution over types *)
    ev_compenv: compilation_env;        (* Compilation environment *)
    ev_stacksize: int;                  (* Size of stack frame *)
    ev_repr: debug_event_repr }         (* Position of the representative *)

et debug_event_kind =
    Event_before
  | Event_after de Types.type_expr
  | Event_pseudo

et debug_event_info =
    Event_function
  | Event_return de int
  | Event_other

et debug_event_repr =
    Event_none
  | Event_parent de int ref
  | Event_child de int ref

(* Abstract machine instructions *)

type label = int                        (* Symbolic code labels *)

type instruction =
    Klabel de label
  | Kacc de int
  | Kenvacc de int
  | Kpush
  | Kpop de int
  | Kassign de int
  | Kpush_retaddr de label
  | Kapply de int                       (* number of arguments *)
  | Kappterm de int * int               (* number of arguments, slot size *)
  | Kreturn de int                      (* slot size *)
  | Krestart
  | Kgrab de int                        (* number of arguments *)
  | Kclosure de label * int
  | Kclosurerec de label list * int
  | Koffsetclosure de int
  | Kgetglobal de Ident.t
  | Ksetglobal de Ident.t
  | Kconst de structured_constant
  | Kmakeblock de int * int             (* size, tag *)
  | Kmakefloatblock de int
  | Kgetfield de int
  | Ksetfield de int
  | Kgetfloatfield de int
  | Ksetfloatfield de int
  | Kvectlength
  | Kgetvectitem
  | Ksetvectitem
  | Kgetstringchar
  | Ksetstringchar
  | Kbranch de label
  | Kbranchif de label
  | Kbranchifnot de label
  | Kstrictbranchif de label
  | Kstrictbranchifnot de label
  | Kswitch de label array * label array
  | Kboolnot
  | Kpushtrap de label
  | Kpoptrap
  | Kraise de raise_kind
  | Kcheck_signals
  | Kccall de string * int
  | Knegint | Kaddint | Ksubint | Kmulint | Kdivint | Kmodint
  | Kandint | Korint | Kxorint | Klslint | Klsrint | Kasrint
  | Kintcomp de comparison
  | Koffsetint de int
  | Koffsetref de int
  | Kisint
  | Kisout
  | Kgetmethod
  | Kgetpubmet de int
  | Kgetdynmet
  | Kevent de debug_event
  | Kstop

val immed_min: int
val immed_max: int
