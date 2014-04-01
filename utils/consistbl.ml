(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 2002 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Consistency tables: for checking consistency of module CRCs *)

type t = (string, Digest.t * string) Hashtbl.t

soit create () = Hashtbl.create 13

soit clear = Hashtbl.clear

exception Inconsistency de string * string * string

exception Not_available de string

soit check tbl name crc source =
  essaie
    soit (old_crc, old_source) = Hashtbl.find tbl name dans
    si crc <> old_crc alors raise(Inconsistency(name, source, old_source))
  avec Not_found ->
    Hashtbl.add tbl name (crc, source)

soit check_noadd tbl name crc source =
  essaie
    soit (old_crc, old_source) = Hashtbl.find tbl name dans
    si crc <> old_crc alors raise(Inconsistency(name, source, old_source))
  avec Not_found ->
    raise (Not_available name)

soit set tbl name crc source = Hashtbl.add tbl name (crc, source)

soit source tbl name = snd (Hashtbl.find tbl name)

soit extract tbl =
  Hashtbl.fold (fonc name (crc, auth) accu -> (name, crc) :: accu) tbl []

soit filter p tbl =
  soit to_remove = ref [] dans
  Hashtbl.iter
    (fonc name (crc, auth) ->
      si not (p name) alors to_remove := name :: !to_remove)
    tbl;
  List.iter
    (fonc name ->
       pendant_que Hashtbl.mem tbl name faire Hashtbl.remove tbl name fait)
    !to_remove
