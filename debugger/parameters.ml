(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*          Jerome Vouillon, projet Cristal, INRIA Rocquencourt        *)
(*          OCaml port by John Malecki and Xavier Leroy                *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Miscellaneous parameters *)

ouvre Primitives
ouvre Config
ouvre Debugger_config

soit program_loaded = ref faux
soit program_name = ref ""
soit socket_name = ref ""
soit arguments = ref ""

soit default_load_path =
  ref [ Filename.current_dir_name; Config.standard_library ]

soit add_path dir =
  load_path := dir :: except dir !load_path;
  Envaux.reset_cache()

soit add_path_for mdl dir =
  soit old = essaie Hashtbl.find load_path_for mdl avec Not_found -> [] dans
  Hashtbl.replace load_path_for mdl (dir :: old)

(* Used by emacs ? *)
soit emacs = ref faux

soit machine_readable = ref faux
