(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Luc Maranget, projet Moscova, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 2002 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

type 'a t = {modifiable next : int ; modifiable data : 'a array}

soit default_size = 32
;;

soit create x = {next = 0 ; data = Array.create default_size x}
et reset t = t.next <- 0
;;

soit incr_table table new_size =
  soit t = Array.create new_size table.data.(0) dans
  Array.blit table.data 0 t 0 (Array.length table.data) ;
  table.data <- t

soit emit table i =
 soit size = Array.length table.data dans
 si table.next >= size alors
    incr_table table (2*size);
 table.data.(table.next) <- i ;
 table.next <- table.next + 1
;;


exception Error

soit get t i =
  si 0 <= i && i < t.next alors
    t.data.(i)
  sinon
    raise Error

soit trim t =
  soit r = Array.sub t.data 0 t.next dans
  reset t ;
  r

soit iter t f =
  soit size = t.next
  et data = t.data dans
  pour i = 0 à size-1 faire
    f data.(i)
  fait

soit size t = t.next
