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

ouvre Cmm

module Raw_name = struct
  type t =
    | Anon
    | R
    | Ident de Ident.t

  soit create_from_ident ident = Ident ident

  soit to_string t =
    filtre t avec
    | Anon -> None
    | R -> Some "R"
    | Ident ident ->
      soit name = Ident.name ident dans
      si String.length name <= 0 alors None sinon Some name
fin

type t =
  { modifiable raw_name: Raw_name.t;
    stamp: int;
    typ: Cmm.machtype_component;
    modifiable loc: location;
    modifiable spill: bool;
    modifiable part: int option;
    modifiable interf: t list;
    modifiable prefer: (t * int) list;
    modifiable degree: int;
    modifiable spill_cost: int;
    modifiable visited: bool }

et location =
    Unknown
  | Reg de int
  | Stack de stack_location

et stack_location =
    Local de int
  | Incoming de int
  | Outgoing de int

type reg = t

soit dummy =
  { raw_name = Raw_name.Anon; stamp = 0; typ = Int; loc = Unknown;
    spill = faux; interf = []; prefer = []; degree = 0; spill_cost = 0;
    visited = faux; part = None;
  }

soit currstamp = ref 0
soit reg_list = ref([] : t list)

soit create ty =
  soit r = { raw_name = Raw_name.Anon; stamp = !currstamp; typ = ty;
            loc = Unknown; spill = faux; interf = []; prefer = []; degree = 0;
            spill_cost = 0; visited = faux; part = None; } dans
  reg_list := r :: !reg_list;
  incr currstamp;
  r

soit createv tyv =
  soit n = Array.length tyv dans
  soit rv = Array.create n dummy dans
  pour i = 0 à n-1 faire rv.(i) <- create tyv.(i) fait;
  rv

soit createv_like rv =
  soit n = Array.length rv dans
  soit rv' = Array.create n dummy dans
  pour i = 0 à n-1 faire rv'.(i) <- create rv.(i).typ fait;
  rv'

soit clone r =
  soit nr = create r.typ dans
  nr.raw_name <- r.raw_name;
  nr

soit at_location ty loc =
  soit r = { raw_name = Raw_name.R; stamp = !currstamp; typ = ty; loc;
            spill = faux; interf = []; prefer = []; degree = 0;
            spill_cost = 0; visited = faux; part = None; } dans
  incr currstamp;
  r

soit anonymous t =
  filtre Raw_name.to_string t.raw_name avec
  | None -> vrai
  | Some _raw_name -> faux

soit name t =
  filtre Raw_name.to_string t.raw_name avec
  | None -> ""
  | Some raw_name ->
    soit with_spilled =
      si t.spill alors
        "spilled-" ^ raw_name
      sinon
        raw_name
    dans
    filtre t.part avec
    | None -> with_spilled
    | Some part -> with_spilled ^ "#" ^ string_of_int part

soit first_virtual_reg_stamp = ref (-1)

soit reset() =
  (* When reset() is called for the first time, the current stamp reflects
     all hard pseudo-registers that have been allocated by Proc, so
     remember it and use it as the base stamp for allocating
     soft pseudo-registers *)
  si !first_virtual_reg_stamp = -1 alors first_virtual_reg_stamp := !currstamp;
  currstamp := !first_virtual_reg_stamp;
  reg_list := []

soit all_registers() = !reg_list
soit num_registers() = !currstamp

soit reinit_reg r =
  r.loc <- Unknown;
  r.interf <- [];
  r.prefer <- [];
  r.degree <- 0;
  (* Preserve the very high spill costs introduced by the reloading pass *)
  si r.spill_cost >= 100000
  alors r.spill_cost <- 100000
  sinon r.spill_cost <- 0

soit reinit() =
  List.iter reinit_reg !reg_list

module RegOrder =
  struct
    type t = reg
    soit compare r1 r2 = r1.stamp - r2.stamp
  fin

module Set = Set.Make(RegOrder)
module Map = Map.Make(RegOrder)

soit add_set_array s v =
  filtre Array.length v avec
    0 -> s
  | 1 -> Set.add v.(0) s
  | n -> soit rec add_all i =
           si i >= n alors s sinon Set.add v.(i) (add_all(i+1))
         dans add_all 0

soit diff_set_array s v =
  filtre Array.length v avec
    0 -> s
  | 1 -> Set.remove v.(0) s
  | n -> soit rec remove_all i =
           si i >= n alors s sinon Set.remove v.(i) (remove_all(i+1))
         dans remove_all 0

soit inter_set_array s v =
  filtre Array.length v avec
    0 -> Set.empty
  | 1 -> si Set.mem v.(0) s
         alors Set.add v.(0) Set.empty
         sinon Set.empty
  | n -> soit rec inter_all i =
           si i >= n alors Set.empty
           sinon si Set.mem v.(i) s alors Set.add v.(i) (inter_all(i+1))
           sinon inter_all(i+1)
         dans inter_all 0

soit set_of_array v =
  filtre Array.length v avec
    0 -> Set.empty
  | 1 -> Set.add v.(0) Set.empty
  | n -> soit rec add_all i =
           si i >= n alors Set.empty sinon Set.add v.(i) (add_all(i+1))
         dans add_all 0
