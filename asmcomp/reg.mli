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

(* Pseudo-registers *)

module Raw_name : sig
  type t
  val create_from_ident : Ident.t -> t
fin

type t =
  { modifiable raw_name: Raw_name.t;       (* Name *)
    stamp: int;                         (* Unique stamp *)
    typ: Cmm.machtype_component;        (* Type of contents *)
    modifiable loc: location;              (* Actual location *)
    modifiable spill: bool;                (* "true" to force stack allocation  *)
    modifiable part: int option;           (* Zero-based index of part of value *)
    modifiable interf: t list;             (* Other regs live simultaneously *)
    modifiable prefer: (t * int) list;     (* Preferences for other regs *)
    modifiable degree: int;                (* Number of other regs live sim. *)
    modifiable spill_cost: int;            (* Estimate of spilling cost *)
    modifiable visited: bool }             (* For graph walks *)

et location =
    Unknown
  | Reg de int
  | Stack de stack_location

et stack_location =
    Local de int
  | Incoming de int
  | Outgoing de int

val dummy: t
val create: Cmm.machtype_component -> t
val createv: Cmm.machtype -> t array
val createv_like: t array -> t array
val clone: t -> t
val at_location: Cmm.machtype_component -> location -> t

val anonymous : t -> bool

(* Name for printing *)
val name : t -> string

module Set: Set.S avec type elt = t
module Map: Map.S avec type key = t

val add_set_array: Set.t -> t array -> Set.t
val diff_set_array: Set.t -> t array -> Set.t
val inter_set_array: Set.t -> t array -> Set.t
val set_of_array: t array -> Set.t

val reset: unit -> unit
val all_registers: unit -> t list
val num_registers: unit -> int
val reinit: unit -> unit
