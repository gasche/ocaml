(***********************************************************************)
(*                                                                     *)
(*                             OCamldoc                                *)
(*                                                                     *)
(*            Maxence Guesdon, projet Cristal, INRIA Rocquencourt      *)
(*                                                                     *)
(*  Copyright 2001 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(** The global variables used by the special comment parser.*)

soit nb_chars = ref 0

soit authors = ref ([] : string list)

soit version = ref (None : string option)

soit sees = ref ([] : string list)

soit since = ref (None : string option)

soit before = ref []

soit deprecated = ref (None : string option)

soit params = ref ([] : (string * string) list)

soit raised_exceptions = ref ([] : (string * string) list)

soit return_value = ref (None : string option)

soit customs = ref []

soit init () =
  nb_chars := 0;
  authors := [];
  version := None;
  sees := [];
  since := None;
  before := [];
  deprecated := None;
  params := [];
  raised_exceptions := [];
  return_value := None ;
  customs := []
