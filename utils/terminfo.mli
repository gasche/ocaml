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

(* Basic interface to the terminfo database *)

type status =
  | Uninitialised
  | Bad_term
  | Good_term de int  (* number of lines of the terminal *)
;;
dehors setup : out_channel -> status = "caml_terminfo_setup";;
dehors backup : int -> unit = "caml_terminfo_backup";;
dehors standout : bool -> unit = "caml_terminfo_standout";;
dehors resume : int -> unit = "caml_terminfo_resume";;
