(***********************************************************************)
(*                                                                     *)
(*                             ocamlbuild                              *)
(*                                                                     *)
(*  Nicolas Pouillard, Berke Durak, projet Gallium, INRIA Rocquencourt *)
(*                                                                     *)
(*  Copyright 2007 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

soit rc_ok                              = 0
soit rc_usage                           = 1
soit rc_failure                         = 2
soit rc_invalid_argument                = 3
soit rc_system_error                    = 4
soit rc_hygiene                         = 1
soit rc_circularity                     = 5
soit rc_solver_failed                   = 6
soit rc_ocamldep_error                  = 7
soit rc_lexing_error                    = 8
soit rc_build_error                     = 9
soit rc_executor_subcommand_failed      = 10
soit rc_executor_subcommand_got_signal  = 11
soit rc_executor_io_error               = 12
soit rc_executor_excetptional_condition = 13
