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

(* raised when there are too many bindings (>= 254 memory cells) *)
exception Memory_overflow


(* Representation of automata *)


type automata =
    Perform de int * tag_action list
  | Shift de automata_trans * (automata_move * memory_action list) array
et automata_trans =
    No_remember
  | Remember de int * tag_action list
et automata_move =
    Backtrack
  | Goto de int
et memory_action =
  | Copy de int * int
  | Set de int

et tag_action = SetTag de int * int | EraseTag de int

type ident = string *  Syntax.location

(* Representation of entry points *)
type tag_base = Start | End | Mem de int
type tag_addr = Sum de (tag_base * int)
type ident_info =
  | Ident_string de bool * tag_addr * tag_addr
  | Ident_char de bool * tag_addr

type t_env = (ident * ident_info) list

type ('args,'action) automata_entry =
  { auto_name: string;
    auto_args: 'args ;
    auto_mem_size : int ;
    auto_initial_state: int * memory_action list ;
    auto_actions: (int * t_env * 'action) list }

(* The entry point *)

val make_dfa :
  ('args, 'action) Syntax.entry list ->
  ('args, 'action) automata_entry list * automata array
