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

(* Character operations *)

dehors code: char -> int = "%identity"
dehors unsafe_chr: int -> char = "%identity"

soit chr n =
  si n < 0 || n > 255 alors invalid_arg "Char.chr" sinon unsafe_chr n

dehors is_printable: char -> bool = "caml_is_printable"

dehors string_create: int -> string = "caml_create_string"
dehors string_unsafe_get : string -> int -> char = "%string_unsafe_get"
dehors string_unsafe_set : string -> int -> char -> unit
                           = "%string_unsafe_set"

soit escaped = fonction
  | '\'' -> "\\'"
  | '\\' -> "\\\\"
  | '\n' -> "\\n"
  | '\t' -> "\\t"
  | '\r' -> "\\r"
  | '\b' -> "\\b"
  | c ->
    si is_printable c alors début
      soit s = string_create 1 dans
      string_unsafe_set s 0 c;
      s
    fin sinon début
      soit n = code c dans
      soit s = string_create 4 dans
      string_unsafe_set s 0 '\\';
      string_unsafe_set s 1 (unsafe_chr (48 + n / 100));
      string_unsafe_set s 2 (unsafe_chr (48 + (n / 10) mod 10));
      string_unsafe_set s 3 (unsafe_chr (48 + n mod 10));
      s
    fin

soit lowercase c =
  si (c >= 'A' && c <= 'Z')
  || (c >= '\192' && c <= '\214')
  || (c >= '\216' && c <= '\222')
  alors unsafe_chr(code c + 32)
  sinon c

soit uppercase c =
  si (c >= 'a' && c <= 'z')
  || (c >= '\224' && c <= '\246')
  || (c >= '\248' && c <= '\254')
  alors unsafe_chr(code c - 32)
  sinon c

type t = char

soit compare c1 c2 = code c1 - code c2
