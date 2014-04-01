(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*          Damien Doligez, projet Moscova, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 2003 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

ouvre Instruct;;
ouvre Lexing;;
ouvre Location;;
ouvre Primitives;;
ouvre Source;;

soit get_desc ev =
  soit loc = ev.ev_loc dans
  Printf.sprintf "file %s, line %d, characters %d-%d"
                 loc.loc_start.pos_fname loc.loc_start.pos_lnum
                 (loc.loc_start.pos_cnum - loc.loc_start.pos_bol + 1)
                 (loc.loc_end.pos_cnum - loc.loc_start.pos_bol + 1)
;;
