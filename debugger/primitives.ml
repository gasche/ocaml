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

(*********************** Basic functions and types *********************)

(*** Miscellaneous ***)
exception Out_of_range

soit nothing _ = ()

(*** Operations on lists. ***)

(* Remove an element from a list *)
soit except e l =
 soit rec except_e = fonction
     [] -> []
   | elem::l -> si e = elem alors l sinon elem::except_e l
 dans except_e l

(* Position of an element in a list. Head of list has position 0. *)
soit index a l =
 soit rec index_rec i = fonction
     []  -> raise Not_found
  | b::l -> si a = b alors i sinon index_rec (i + 1) l
 dans index_rec 0 l

(* Return the `n' first elements of `l' *)
(* ### n l -> l' *)
soit rec list_truncate =
  fonc
    p0 p1 -> filtre (p0,p1) avec (0, _)      -> []
  | (_, [])     -> []
  | (n, (a::l)) -> a::(list_truncate (n - 1) l)

(* Separe the `n' first elements of `l' and the others *)
(* ### n list -> (first, last) *)
soit rec list_truncate2 =
  fonc
    p0 p1 -> filtre (p0,p1) avec (0, l) ->
      ([], l)
  | (_, []) ->
      ([], [])
  | (n, (a::l)) ->
      soit (first, last) = (list_truncate2 (n - 1) l) dans
        (a::first, last)

(* Replace x by y in list l *)
(* ### x y l -> l' *)
soit list_replace x y =
  soit rec repl =
    fonction
      [] -> []
    | a::l ->
        si a == x alors y::l
        sinon a::(repl l)
  dans repl

(*** Operations on strings. ***)

(* Remove blanks (spaces and tabs) at beginning and end of a string. *)
soit is_space = fonction
  | ' ' | '\t' -> vrai | _ -> faux

soit string_trim s =
  soit l = String.length s et i = ref 0 dans
    pendant_que
      !i < l && is_space (String.get s !i)
    faire
      incr i
    fait;
    soit j = ref (l - 1) dans
      pendant_que
        !j >= !i && is_space (String.get s !j)
      faire
        decr j
      fait;
      String.sub s !i (!j - !i + 1)

(* isprefix s1 s2 returns true if s1 is a prefix of s2. *)

soit isprefix s1 s2 =
  soit l1 = String.length s1 et l2 = String.length s2 dans
  (l1 = l2 && s1 = s2) || (l1 < l2 && s1 = String.sub s2 0 l1)

(* Split a string at the given delimiter char *)

soit split_string sep str =
  soit rec split i j =
    si j >= String.length str alors
      si i >= j alors [] sinon [String.sub str i (j-i)]
    sinon si str.[j] = sep alors
      si i >= j
      alors skip_sep (j+1)
      sinon String.sub str i (j-i) :: skip_sep (j+1)
    sinon
      split i (j+1)
  et skip_sep j =
    si j < String.length str && str.[j] = sep
    alors skip_sep (j+1)
    sinon split j j
  dans split 0 0

(*** I/O channels ***)

type io_channel = {
  io_in : in_channel;
  io_out : out_channel;
  io_fd : Unix.file_descr
  }

soit io_channel_of_descr fd = {
  io_in = Unix.in_channel_of_descr fd;
  io_out = Unix.out_channel_of_descr fd;
  io_fd = fd
  }

soit close_io io_channel =
  close_out_noerr io_channel.io_out;
  close_in_noerr io_channel.io_in;
;;

soit std_io = {
  io_in = stdin;
  io_out = stdout;
  io_fd = Unix.stdin
  }
