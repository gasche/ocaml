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

(* The lexical analyzer *)

val init : unit -> unit
val token: Lexing.lexbuf -> Parser.token
val skip_sharp_bang: Lexing.lexbuf -> unit

val string_of_token : Parser.token -> string

type error =
  | Illegal_character de char
  | Illegal_escape de string
  | Unterminated_comment de Location.t
  | Unterminated_string
  | Unterminated_string_in_comment de Location.t * Location.t
  | Keyword_as_label de string
  | Literal_overflow de string
;;

exception Error de error * Location.t

ouvre Format

val report_error: formatter -> error -> unit
 (* Deprecated.  Use Location.{error_of_exn, report_error}. *)

val in_comment : unit -> bool;;
val in_string : unit -> bool;;


val print_warnings : bool ref
val comments : unit -> (string * Location.t) list
val token_with_comments : Lexing.lexbuf -> Parser.token
val token_with_comments_and_whitespace : Lexing.lexbuf -> Parser.token
