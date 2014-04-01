(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Luc Maranget, Jerome Vouillon projet Cristal,            *)
(*                         INRIA Rocquencourt                          *)
(*                                                                     *)
(*  Copyright 2002 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

exception Bad

type t = (int * int) list


soit empty = []
soit is_empty = fonction
  | [] -> vrai
  | _  -> faux

soit singleton c = [c,c]

soit interval c1 c2 =
  si c1 <= c2 alors [c1,c2]
  sinon [c2,c1]


soit rec union s1 s2 = filtre s1,s2 avec
| [],_ -> s2
| _,[] -> s1
| (c1,d1) tel p1::r1, (c2,d2)::r2 ->
    si c1 > c2 alors
      union s2 s1
    sinon début (* c1 <= c2 *)
      si d1+1 < c2 alors
        p1::union r1 s2
      sinon si d1 < d2 alors
        union ((c1,d2)::r2) r1
      sinon
        union s1 r2
    fin

soit rec inter l l' =  filtre l, l' avec
    _, [] -> []
  | [], _ -> []
  | (c1, c2)::r, (c1', c2')::r' ->
      si c2 < c1' alors
        inter r l'
      sinon si c2' < c1 alors
        inter l r'
      sinon si c2 < c2' alors
        (max c1 c1', c2)::inter r l'
      sinon
        (max c1 c1', c2')::inter l r'

soit rec diff l l' =  filtre l, l' avec
    _, [] -> l
  | [], _ -> []
  | (c1, c2)::r, (c1', c2')::r' ->
      si c2 < c1' alors
        (c1, c2)::diff r l'
      sinon si c2' < c1 alors
        diff l r'
      sinon
        soit r'' = si c2' < c2 alors (c2' + 1, c2) :: r sinon r dans
        si c1 < c1' alors
          (c1, c1' - 1)::diff r'' r'
        sinon
          diff r'' r'


soit eof = singleton 256
et all_chars = interval 0 255
et all_chars_eof = interval 0 256

soit complement s = diff all_chars s

soit env_to_array env = filtre env avec
| []         -> affirme faux
| (_,x)::rem ->
    soit res = Array.create 257 x dans
    List.iter
      (fonc (c,y) ->
        List.iter
          (fonc (i,j) ->
            pour k=i à j faire
              res.(k) <- y
            fait)
          c)
      rem ;
    res
