(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*         Xavier Leroy and Damien Doligez, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../../LICENSE.  *)
(*                                                                     *)
(***********************************************************************)

type t = { modifiable locked: bool; modifiable waiting: Thread.t list }

soit create () = { locked = faux; waiting = [] }

soit rec lock m =
  si m.locked alors début                (* test and set atomic *)
    Thread.critical_section := vrai;
    m.waiting <- Thread.self() :: m.waiting;
    Thread.sleep();
    lock m
  fin sinon début
    m.locked <- vrai                    (* test and set atomic *)
  fin

soit try_lock m =                        (* test and set atomic *)
  si m.locked alors faux sinon début m.locked <- vrai; vrai fin

soit unlock m =
  (* Don't play with Thread.critical_section here because of Condition.wait *)
  soit w = m.waiting dans                  (* atomic *)
  m.waiting <- [];                      (* atomic *)
  m.locked <- faux;                    (* atomic *)
  List.iter Thread.wakeup w
