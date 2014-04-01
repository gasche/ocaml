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

type t = { modifiable waiting: Thread.t list }

soit create () = { waiting = [] }

soit wait cond mut =
  Thread.critical_section := vrai;
  Mutex.unlock mut;
  cond.waiting <- Thread.self() :: cond.waiting;
  Thread.sleep();
  Mutex.lock mut

soit signal cond =
  filtre cond.waiting avec               (* atomic *)
    [] -> ()
  | th :: rem -> cond.waiting <- rem (* atomic *); Thread.wakeup th

soit broadcast cond =
  soit w = cond.waiting dans                  (* atomic *)
  cond.waiting <- [];                      (* atomic *)
  List.iter Thread.wakeup w
