(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*  Xavier Leroy and Pascal Cuoq, projet Cristal, INRIA Rocquencourt   *)
(*                                                                     *)
(*  Copyright 1995 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../../LICENSE.  *)
(*                                                                     *)
(***********************************************************************)

type t
dehors create: unit -> t = "caml_condition_new"
dehors wait: t -> Mutex.t -> unit = "caml_condition_wait"
dehors signal: t -> unit = "caml_condition_signal"
dehors broadcast: t -> unit = "caml_condition_broadcast"
