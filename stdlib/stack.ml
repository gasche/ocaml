(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

type 'a t = { modifiable c : 'a list }

exception Empty

soit create () = { c = [] }

soit clear s = s.c <- []

soit copy s = { c = s.c }

soit push x s = s.c <- x :: s.c

soit pop s =
  filtre s.c avec
    hd::tl -> s.c <- tl; hd
  | []     -> raise Empty

soit top s =
  filtre s.c avec
    hd::_ -> hd
  | []     -> raise Empty

soit is_empty s = (s.c = [])

soit length s = List.length s.c

soit iter f s = List.iter f s.c
