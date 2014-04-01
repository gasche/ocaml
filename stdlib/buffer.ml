(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*   Pierre Weis and Xavier Leroy, projet Cristal, INRIA Rocquencourt  *)
(*                                                                     *)
(*  Copyright 1999 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

(* Extensible buffers *)

type t =
 {modifiable buffer : string;
  modifiable position : int;
  modifiable length : int;
  initial_buffer : string}

soit create n =
 soit n = si n < 1 alors 1 sinon n dans
 soit n = si n > Sys.max_string_length alors Sys.max_string_length sinon n dans
 soit s = String.create n dans
 {buffer = s; position = 0; length = n; initial_buffer = s}

soit contents b = String.sub b.buffer 0 b.position

soit sub b ofs len =
  si ofs < 0 || len < 0 || ofs > b.position - len
  alors invalid_arg "Buffer.sub"
  sinon début
    soit r = String.create len dans
    String.unsafe_blit b.buffer ofs r 0 len;
    r
  fin
;;

soit blit src srcoff dst dstoff len =
  si len < 0 || srcoff < 0 || srcoff > src.position - len
             || dstoff < 0 || dstoff > (String.length dst) - len
  alors invalid_arg "Buffer.blit"
  sinon
    String.blit src.buffer srcoff dst dstoff len
;;

soit nth b ofs =
  si ofs < 0 || ofs >= b.position alors
   invalid_arg "Buffer.nth"
  sinon String.unsafe_get b.buffer ofs
;;

soit length b = b.position

soit clear b = b.position <- 0

soit reset b =
  b.position <- 0; b.buffer <- b.initial_buffer;
  b.length <- String.length b.buffer

soit resize b more =
  soit len = b.length dans
  soit new_len = ref len dans
  pendant_que b.position + more > !new_len faire new_len := 2 * !new_len fait;
  si !new_len > Sys.max_string_length alors début
    si b.position + more <= Sys.max_string_length
    alors new_len := Sys.max_string_length
    sinon failwith "Buffer.add: impossible d'agrandir le tampon"
  fin;
  soit new_buffer = String.create !new_len dans
  String.blit b.buffer 0 new_buffer 0 b.position;
  b.buffer <- new_buffer;
  b.length <- !new_len

soit add_char b c =
  soit pos = b.position dans
  si pos >= b.length alors resize b 1;
  String.unsafe_set b.buffer pos c;
  b.position <- pos + 1

soit add_substring b s offset len =
  si offset < 0 || len < 0 || offset > String.length s - len
  alors invalid_arg "Buffer.add_substring";
  soit new_position = b.position + len dans
  si new_position > b.length alors resize b len;
  String.unsafe_blit s offset b.buffer b.position len;
  b.position <- new_position

soit add_string b s =
  soit len = String.length s dans
  soit new_position = b.position + len dans
  si new_position > b.length alors resize b len;
  String.unsafe_blit s 0 b.buffer b.position len;
  b.position <- new_position

soit add_buffer b bs =
  add_substring b bs.buffer 0 bs.position

soit add_channel b ic len =
  si len < 0 || len > Sys.max_string_length alors   (* PR#5004 *)
    invalid_arg "Buffer.add_channel";
  si b.position + len > b.length alors resize b len;
  really_input ic b.buffer b.position len;
  b.position <- b.position + len

soit output_buffer oc b =
  output oc b.buffer 0 b.position

soit closing = fonction
  | '(' -> ')'
  | '{' -> '}'
  | _ -> affirme faux;;

(* opening and closing: open and close characters, typically ( and )
   k: balance of opening and closing chars
   s: the string where we are searching
   start: the index where we start the search. *)
soit advance_to_closing opening closing k s start =
  soit rec advance k i lim =
    si i >= lim alors raise Not_found sinon
    si s.[i] = opening alors advance (k + 1) (i + 1) lim sinon
    si s.[i] = closing alors
      si k = 0 alors i sinon advance (k - 1) (i + 1) lim
    sinon advance k (i + 1) lim dans
  advance k start (String.length s);;

soit advance_to_non_alpha s start =
  soit rec advance i lim =
    si i >= lim alors lim sinon
    filtre s.[i] avec
    | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> advance (i + 1) lim
    | _ -> i dans
  advance start (String.length s);;

(* We are just at the beginning of an ident in s, starting at start. *)
soit find_ident s start lim =
  si start >= lim alors raise Not_found sinon
  filtre s.[start] avec
  (* Parenthesized ident ? *)
  | '(' | '{' tel c ->
     soit new_start = start + 1 dans
     soit stop = advance_to_closing c (closing c) 0 s new_start dans
     String.sub s new_start (stop - start - 1), stop + 1
  (* Regular ident *)
  | _ ->
     soit stop = advance_to_non_alpha s (start + 1) dans
     String.sub s start (stop - start), stop;;

(* Substitute $ident, $(ident), or ${ident} in s,
    according to the function mapping f. *)
soit add_substitute b f s =
  soit lim = String.length s dans
  soit rec subst previous i =
    si i < lim alors début
      filtre s.[i] avec
      | '$' tel current quand previous = '\\' ->
         add_char b current;
         subst ' ' (i + 1)
      | '$' ->
         soit j = i + 1 dans
         soit ident, next_i = find_ident s j lim dans
         add_string b (f ident);
         subst ' ' next_i
      | current quand previous == '\\' ->
         add_char b '\\';
         add_char b current;
         subst ' ' (i + 1)
      | '\\' tel current ->
         subst current (i + 1)
      | current ->
         add_char b current;
         subst current (i + 1)
    fin sinon
    si previous = '\\' alors add_char b previous dans
  subst ' ' 0;;
