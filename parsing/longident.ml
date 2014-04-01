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

type t =
    Lident de string
  | Ldot de t * string
  | Lapply de t * t

soit rec flat accu = fonction
    Lident s -> s :: accu
  | Ldot(lid, s) -> flat (s :: accu) lid
  | Lapply(_, _) -> Misc.fatal_error "Longident.flat"

soit flatten lid = flat [] lid

soit last = fonction
    Lident s -> s
  | Ldot(_, s) -> s
  | Lapply(_, _) -> Misc.fatal_error "Longident.last"

soit rec split_at_dots s pos =
  essaie
    soit dot = String.index_from s pos '.' dans
    String.sub s pos (dot - pos) :: split_at_dots s (dot + 1)
  avec Not_found ->
    [String.sub s pos (String.length s - pos)]

soit parse s =
  filtre split_at_dots s 0 avec
    [] -> Lident ""  (* should not happen, but don't put assert false
                        so as not to crash the toplevel (see Genprintval) *)
  | hd :: tl -> List.fold_left (fonc p s -> Ldot(p, s)) (Lident hd) tl
