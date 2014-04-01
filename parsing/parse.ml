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

(* Entry points in the parser *)

(* Skip tokens to the end of the phrase *)

soit rec skip_phrase lexbuf =
  essaie
    filtre Lexer.token lexbuf avec
      Parser.SEMISEMI | Parser.EOF -> ()
    | _ -> skip_phrase lexbuf
  avec
    | Lexer.Error (Lexer.Unterminated_comment _, _)
    | Lexer.Error (Lexer.Unterminated_string, _)
    | Lexer.Error (Lexer.Unterminated_string_in_comment _, _)
    | Lexer.Error (Lexer.Illegal_character _, _) -> skip_phrase lexbuf
;;

soit maybe_skip_phrase lexbuf =
  si Parsing.is_current_lookahead Parser.SEMISEMI
  || Parsing.is_current_lookahead Parser.EOF
  alors ()
  sinon skip_phrase lexbuf

soit wrap parsing_fun lexbuf =
  essaie
    Lexer.init ();
    soit ast = parsing_fun Lexer.token lexbuf dans
    Parsing.clear_parser();
    ast
  avec
  | Lexer.Error(Lexer.Illegal_character _, _) tel err
    quand !Location.input_name = "//toplevel//"->
      skip_phrase lexbuf;
      raise err
  | Syntaxerr.Error _ tel err
    quand !Location.input_name = "//toplevel//" ->
      maybe_skip_phrase lexbuf;
      raise err
  | Parsing.Parse_error | Syntaxerr.Escape_error ->
      soit loc = Location.curr lexbuf dans
      si !Location.input_name = "//toplevel//"
      alors maybe_skip_phrase lexbuf;
      raise(Syntaxerr.Error(Syntaxerr.Other loc))

soit implementation = wrap Parser.implementation
et interface = wrap Parser.interface
et toplevel_phrase = wrap Parser.toplevel_phrase
et use_file = wrap Parser.use_file
et core_type = wrap Parser.parse_core_type
et expression = wrap Parser.parse_expression
et pattern = wrap Parser.parse_pattern
