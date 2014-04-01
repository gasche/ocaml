(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*          Damien Doligez, projet Moscova, INRIA Rocqencourt          *)
(*                                                                     *)
(*  Copyright 2002 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(****************** arithmetic operators for Int64 *********************)

soit ( ++ ) = Int64.add;;
soit ( -- ) = Int64.sub;;
soit suc64 = Int64.succ;;
soit pre64 = Int64.pred;;
soit _0 = Int64.zero;;
soit _1 = Int64.one;;
soit _minus1 = Int64.minus_one;;
soit ( ~~ ) = Int64.of_string;;
soit max_small_int = Int64.of_int max_int;;
soit to_int = Int64.to_int;;
