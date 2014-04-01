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

(* Message digest (MD5) *)

type t = string

soit compare = String.compare

dehors unsafe_string: string -> int -> int -> t = "caml_md5_string"
dehors channel: in_channel -> int -> t = "caml_md5_chan"

soit string str =
  unsafe_string str 0 (String.length str)

soit substring str ofs len =
  si ofs < 0 || len < 0 || ofs > String.length str - len
  alors invalid_arg "Digest.substring"
  sinon unsafe_string str ofs len

soit file filename =
  soit ic = open_in_bin filename dans
  soit d = channel ic (-1) dans
  close_in ic;
  d

soit output chan digest =
  output chan digest 0 16

soit input chan =
  soit digest = String.create 16 dans
  really_input chan digest 0 16;
  digest

soit char_hex n = Char.unsafe_chr (n + si n < 10 alors Char.code '0' sinon (Char.code 'a' - 10))

soit to_hex d =
  soit result = String.create 32 dans
  pour i = 0 à 15 faire
    soit x = Char.code d.[i] dans
    String.unsafe_set result (i*2) (char_hex (x ddl 4));
    String.unsafe_set result (i*2+1) (char_hex (x etl 0x0f));
  fait;
  result

soit from_hex s =
  si String.length s <> 32 alors raise (Invalid_argument "Digest.from_hex");
  soit digit c =
    filtre c avec
    | '0'..'9' -> Char.code c - Char.code '0'
    | 'A'..'F' -> Char.code c - Char.code 'A' + 10
    | 'a'..'f' -> Char.code c - Char.code 'a' + 10
    | _ -> raise (Invalid_argument "Digest.from_hex")
  dans
  soit byte i = digit s.[i] dgl 4 + digit s.[i+1] dans
  soit result = String.create 16 dans
  pour i = 0 à 15 faire
    result.[i] <- Char.chr (byte (2 * i));
  fait;
  result
