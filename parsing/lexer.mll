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

(* The lexer definition *)

{
open Lexing
open Misc
open Parser
open Asttypes

type error =
  | Illegal_character of char
  | Illegal_escape of string
  | Unterminated_comment of Location.t
  | Unterminated_string
  | Unterminated_string_in_comment of Location.t * Location.t
  | Keyword_as_label of string
  | Literal_overflow of string
;;

exception Error of error * Location.t;;

(* The table of keywords *)

let keywords_assoc = [
    "and", AND;
    "as", AS;
    "assert", ASSERT;
    "begin", BEGIN;
    "class", CLASS;
    "constraint", CONSTRAINT;
    "do", DO;
    "done", DONE;
    "downto", DOWNTO;
    "else", ELSE;
    "end", END;
    "exception", EXCEPTION;
    "external", EXTERNAL;
    "false", FALSE;
    "for", FOR;
    "fun", FUN;
    "function", FUNCTION;
    "functor", FUNCTOR;
    "if", IF;
    "in", IN;
    "include", INCLUDE;
    "inherit", INHERIT;
    "initializer", INITIALIZER;
    "lazy", LAZY;
    "let", LET;
    "match", MATCH;
    "method", METHOD;
    "module", MODULE;
    "mutable", MUTABLE;
    "new", NEW;
    "object", OBJECT;
    "of", OF;
    "open", OPEN;
    "or", OR;
(*  "parser", PARSER; *)
    "private", PRIVATE;
    "rec", REC;
    "sig", SIG;
    "struct", STRUCT;
    "then", THEN;
    "to", TO;
    "true", TRUE;
    "try", TRY;
    "type", TYPE;
    "val", VAL;
    "virtual", VIRTUAL;
    "when", WHEN;
    "while", WHILE;
    "with", WITH;
    "mod", INFIXOP3("mod");
    "land", INFIXOP3("land");
    "lor", INFIXOP3("lor");
    "lxor", INFIXOP3("lxor");
    "lsl", INFIXOP4("lsl");
    "lsr", INFIXOP4("lsr");
    "asr", INFIXOP4("asr");
]

let keyword_table =
  create_hashtable 149 keywords_assoc

let string_of_keyword_table =
  create_hashtable 149
    (List.rev_map (fun (str,kwd) -> (kwd,str)) keywords_assoc)

let string_of_token = function
  (* first, rule out the keywords (tokens but not symbols) *)
  | AND
  | AS
  | ASSERT
  | BEGIN
  | CLASS
  | CONSTRAINT
  | DO
  | DONE
  | DOWNTO
  | ELSE
  | END
  | EXCEPTION
  | EXTERNAL
  | FALSE
  | FOR
  | FUN
  | FUNCTION
  | FUNCTOR
  | IF
  | IN
  | INCLUDE
  | INHERIT
  | INITIALIZER
  | LAZY
  | LET
  | MATCH
  | METHOD
  | MODULE
  | MUTABLE
  | NEW
  | OBJECT
  | OF
  | OPEN
  | OR
  | PRIVATE
  | REC
  | SIG
  | STRUCT
  | THEN
  | TO
  | TRUE
  | TRY
  | TYPE
  | VAL
  | VIRTUAL
  | WHEN
  | WHILE
  | WITH
  (* we match on keywords first as the following infix keywords would
     get caught by the cases for infix operator symbols below; the
     ordering of clauses matters *)
  | INFIXOP3("mod")
  | INFIXOP3("land")
  | INFIXOP3("lor")
  | INFIXOP3("lxor")
  | INFIXOP4("lsl")
  | INFIXOP4("lsr")
  | INFIXOP4("asr")
  as kwd
    ->
    assert (Hashtbl.mem string_of_keyword_table kwd);
    Hashtbl.find string_of_keyword_table kwd

  | AMPERAMPER -> "&&"
  | AMPERSAND -> "&"
  | BACKQUOTE -> "`"
  | BANG -> "!"
  | BAR -> "|"
  | BARBAR -> "||"
  | BARRBRACKET -> "|]"
  | CHAR lit -> lit.str
  | COLON -> ":"
  | COLONCOLON -> "::"
  | COLONEQUAL -> ":="
  | COLONGREATER -> ":>"
  | COMMA -> ","
  | DOT -> "."
  | DOTDOT -> ".."
  | EOF -> ""
  | EQUAL -> "="
  | FLOAT lit -> lit.str
  | GREATER -> ">"
  | GREATERRBRACE -> ">}"
  | GREATERRBRACKET -> ">]"
  | INFIXOP0 s -> s
  | INFIXOP1 s -> s
  | INFIXOP2 s -> s
  | INFIXOP3 s -> s
  | INFIXOP4 s -> s
  | INT lit -> lit.str
  | INT32 lit -> lit.str
  | INT64 lit -> lit.str
  | LABEL l -> "~" ^ l ^ ":"
  | LBRACE -> "{"
  | LBRACELESS -> "{<"
  | LBRACKET -> "["
  | LBRACKETBAR -> "[|"
  | LBRACKETLESS -> "[<"
  | LBRACKETGREATER -> "[>"
  | LBRACKETPERCENT -> "[%"
  | LBRACKETPERCENTPERCENT -> "[%%"
  | LESS -> "<"
  | LESSMINUS -> "<-"
  | LIDENT id -> id
  | LPAREN -> "("
  | LBRACKETAT -> "[@"
  | LBRACKETATAT -> "[@@"
  | MINUS -> "-"
  | MINUSDOT -> "-."
  | MINUSGREATER -> "->"
  | NATIVEINT lit -> lit.str
  | OPTLABEL s -> "?"^s^":"
  | PERCENT -> "%"
  | PLUS -> "+"
  | PLUSDOT -> "+."
  | PREFIXOP s -> s
  | QUESTION -> "?"
  | QUOTE -> "'"
  | RBRACE -> "}"
  | RBRACKET -> "]"
  | RPAREN -> ")"
  | SEMI -> ";"
  | SEMISEMI -> ";;"
  | SHARP -> "#"
  | STAR -> "*"
  | TILDE -> "~"
  | UNDERSCORE -> "_"
  | STRING lit -> lit.str
  | UIDENT id -> id
  | WHITESPACE s -> s
  | COMMENT (s, _loc) -> Printf.sprintf "(*%s*)" s

(* To buffer string literals *)

let string_buff = Buffer.create 256

let reset_string_buffer () =
  Buffer.reset string_buff

let store_string_char c =
  Buffer.add_char string_buff c

let store_string s =
  Buffer.add_string string_buff s

let store_lexeme lexbuf =
  store_string (Lexing.lexeme lexbuf)

let get_stored_string () = Buffer.contents string_buff

(* [raw_string_buff] stores the string as is present in the source
   code, as opposed to [string_buff] which applies escaping rules to
   return the string representation as intended as an OCaml value *)
let raw_string_buff = Buffer.create 256

let store_raw lexbuf =
  Buffer.add_string raw_string_buff (Lexing.lexeme lexbuf)

(* distinguishing [store_raw] and [init_raw] gives us sanity checks
   that the [init_raw] / [flush_raw] are parenthesized as expected *)
let init_raw lexbuf =
  assert (Buffer.length raw_string_buff = 0);
  store_raw lexbuf

let reset_raw () =
  Buffer.reset raw_string_buff

let flush_raw_string () =
  let raw_string = Buffer.contents raw_string_buff in
  reset_raw ();
  raw_string

(* To store the position of the beginning of a string and comment *)
let string_start_loc = ref Location.none;;
let comment_start_loc = ref [];;
let in_comment () = !comment_start_loc <> [];;
let is_in_string = ref false
let in_string () = !is_in_string
let print_warnings = ref true

(* To translate escape sequences *)

let char_lit lexbuf lit = {
  str = Lexing.lexeme lexbuf;
  lit;
}

let char lexbuf i = char_lit lexbuf (Lexing.lexeme_char lexbuf i)

let char_for_backslash lexbuf i =
  char_lit lexbuf (match Lexing.lexeme_char lexbuf i with
  | 'n' -> '\010'
  | 'r' -> '\013'
  | 'b' -> '\008'
  | 't' -> '\009'
  | c   -> c)

let char_for_decimal_code lexbuf i =
  let c = 100 * (Char.code(Lexing.lexeme_char lexbuf i) - 48) +
           10 * (Char.code(Lexing.lexeme_char lexbuf (i+1)) - 48) +
                (Char.code(Lexing.lexeme_char lexbuf (i+2)) - 48) in
  if (c < 0 || c > 255) then
    if in_comment ()
    then char_lit lexbuf 'x'
    else raise (Error(Illegal_escape (Lexing.lexeme lexbuf),
                      Location.curr lexbuf))
  else char_lit lexbuf (Char.chr c)

let char_for_hexadecimal_code lexbuf i =
  let d1 = Char.code (Lexing.lexeme_char lexbuf i) in
  let val1 = if d1 >= 97 then d1 - 87
             else if d1 >= 65 then d1 - 55
             else d1 - 48
  in
  let d2 = Char.code (Lexing.lexeme_char lexbuf (i+1)) in
  let val2 = if d2 >= 97 then d2 - 87
             else if d2 >= 65 then d2 - 55
             else d2 - 48
  in
  char_lit lexbuf (Char.chr (val1 * 16 + val2))

(* To convert integer literals, allowing max_int + 1 (PR#4210) *)

let cvt_int_literal s = {
  str = s;
  lit = - int_of_string ("-" ^ s);
}
let cvt_int32_literal s = {
  str = s;
  lit = Int32.neg (Int32.of_string
                     ("-" ^ String.sub s 0 (String.length s - 1)));
}
let cvt_int64_literal s = {
  str = s;
  lit = Int64.neg (Int64.of_string
                     ("-" ^ String.sub s 0 (String.length s - 1)));
}
let cvt_nativeint_literal s = {
  str = s;
  lit = Nativeint.neg (Nativeint.of_string
                         ("-" ^ String.sub s 0 (String.length s - 1)));
}

(* Remove underscores from float literals *)

let remove_underscores s =
  let l = String.length s in
  let rec remove src dst =
    if src >= l then
      if dst >= l then s else String.sub s 0 dst
    else
      match s.[src] with
        '_' -> remove (src + 1) dst
      |  c  -> s.[dst] <- c; remove (src + 1) (dst + 1)
  in remove 0 0

let cvt_float_literal s = {
  str = s;
  lit = remove_underscores s;
}

(* recover the name from a LABEL or OPTLABEL token *)

let get_label_name lexbuf =
  let s = Lexing.lexeme lexbuf in
  let name = String.sub s 1 (String.length s - 2) in
  if Hashtbl.mem keyword_table name then
    raise (Error(Keyword_as_label name, Location.curr lexbuf));
  name
;;

(* Update the current location with file name and line number. *)

let update_loc lexbuf file line absolute chars =
  let pos = lexbuf.lex_curr_p in
  let new_file = match file with
                 | None -> pos.pos_fname
                 | Some s -> s
  in
  lexbuf.lex_curr_p <- { pos with
    pos_fname = new_file;
    pos_lnum = if absolute then line else pos.pos_lnum + line;
    pos_bol = pos.pos_cnum - chars;
  }
;;

(* Warn about Latin-1 characters used in idents *)

let warn_latin1 lexbuf =
  Location.prerr_warning (Location.curr lexbuf)
    (Warnings.Deprecated "ISO-Latin1 characters in identifiers")
;;

(* Error report *)

open Format

let report_error ppf = function
  | Illegal_character c ->
      fprintf ppf "Illegal character (%s)" (Char.escaped c)
  | Illegal_escape s ->
      fprintf ppf "Illegal backslash escape in string or character (%s)" s
  | Unterminated_comment _ ->
      fprintf ppf "Comment not terminated"
  | Unterminated_string ->
      fprintf ppf "String literal not terminated"
  | Unterminated_string_in_comment (_, loc) ->
      fprintf ppf "This comment contains an unterminated string literal@.%aString literal begins here"
        Location.print_error loc
  | Keyword_as_label kwd ->
      fprintf ppf "`%s' is a keyword, it cannot be used as label name" kwd
  | Literal_overflow ty ->
      fprintf ppf "Integer literal exceeds the range of representable \
                   integers of type %s" ty

let () =
  Location.register_error_of_exn
    (function
      | Error (err, loc) ->
          Some (Location.error_of_printer loc report_error err)
      | _ ->
          None
    )

}

let newline = ('\013'* '\010' )
let blank = [' ' '\009' '\012']
let lowercase = ['a'-'z' '_']
let uppercase = ['A'-'Z']
let identchar = ['A'-'Z' 'a'-'z' '_' '\'' '0'-'9']
let lowercase_latin1 = ['a'-'z' '\223'-'\246' '\248'-'\255' '_']
let uppercase_latin1 = ['A'-'Z' '\192'-'\214' '\216'-'\222']
let identchar_latin1 =
  ['A'-'Z' 'a'-'z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255' '\'' '0'-'9']
let symbolchar =
  ['!' '$' '%' '&' '*' '+' '-' '.' '/' ':' '<' '=' '>' '?' '@' '^' '|' '~']
let decimal_literal =
  ['0'-'9'] ['0'-'9' '_']*
let hex_literal =
  '0' ['x' 'X'] ['0'-'9' 'A'-'F' 'a'-'f']['0'-'9' 'A'-'F' 'a'-'f' '_']*
let oct_literal =
  '0' ['o' 'O'] ['0'-'7'] ['0'-'7' '_']*
let bin_literal =
  '0' ['b' 'B'] ['0'-'1'] ['0'-'1' '_']*
let int_literal =
  decimal_literal | hex_literal | oct_literal | bin_literal
let float_literal =
  ['0'-'9'] ['0'-'9' '_']*
  ('.' ['0'-'9' '_']* )?
  (['e' 'E'] ['+' '-']? ['0'-'9'] ['0'-'9' '_']*)?

rule token = parse
  | newline
      { update_loc lexbuf None 1 false 0;
        WHITESPACE (Lexing.lexeme lexbuf) }
  | blank +
      { WHITESPACE (Lexing.lexeme lexbuf) }
  | "_"
      { UNDERSCORE }
  | "~"
      { TILDE }
  | "~" lowercase identchar * ':'
      { LABEL (get_label_name lexbuf) }
  | "~" lowercase_latin1 identchar_latin1 * ':'
      { warn_latin1 lexbuf; LABEL (get_label_name lexbuf) }
  | "?"
      { QUESTION }
  | "?" lowercase identchar * ':'
      { OPTLABEL (get_label_name lexbuf) }
  | "?" lowercase_latin1 identchar_latin1 * ':'
      { warn_latin1 lexbuf; OPTLABEL (get_label_name lexbuf) }
  | lowercase identchar *
      { let s = Lexing.lexeme lexbuf in
        try Hashtbl.find keyword_table s
        with Not_found -> LIDENT s }
  | lowercase_latin1 identchar_latin1 *
      { warn_latin1 lexbuf; LIDENT (Lexing.lexeme lexbuf) }
  | uppercase identchar *
      { UIDENT(Lexing.lexeme lexbuf) }       (* No capitalized keywords *)
  | uppercase_latin1 identchar_latin1 *
      { warn_latin1 lexbuf; UIDENT(Lexing.lexeme lexbuf) }
  | int_literal
      { try
          INT (cvt_int_literal (Lexing.lexeme lexbuf))
        with Failure _ ->
          raise (Error(Literal_overflow "int", Location.curr lexbuf))
      }
  | float_literal
      { FLOAT (cvt_float_literal(Lexing.lexeme lexbuf)) }
  | int_literal "l"
      { try
          INT32 (cvt_int32_literal (Lexing.lexeme lexbuf))
        with Failure _ ->
          raise (Error(Literal_overflow "int32", Location.curr lexbuf)) }
  | int_literal "L"
      { try
          INT64 (cvt_int64_literal (Lexing.lexeme lexbuf))
        with Failure _ ->
          raise (Error(Literal_overflow "int64", Location.curr lexbuf)) }
  | int_literal "n"
      { try
          NATIVEINT (cvt_nativeint_literal (Lexing.lexeme lexbuf))
        with Failure _ ->
          raise (Error(Literal_overflow "nativeint", Location.curr lexbuf)) }
  | "\""
      { reset_string_buffer();
        is_in_string := true;
        init_raw lexbuf;
        let string_start = lexbuf.lex_start_p in
        string_start_loc := Location.curr lexbuf;
        string lexbuf;
        let raw_string = flush_raw_string () in
        is_in_string := false;
        lexbuf.lex_start_p <- string_start;
        STRING {
          str = raw_string;
          lit = (get_stored_string(), None);
        } }
  | "{" lowercase* "|"
      { reset_string_buffer();
        let delim = Lexing.lexeme lexbuf in
        let delim = String.sub delim 1 (String.length delim - 2) in
        is_in_string := true;
        init_raw lexbuf;
        let string_start = lexbuf.lex_start_p in
        string_start_loc := Location.curr lexbuf;
        quoted_string delim lexbuf;
        let raw_string = flush_raw_string () in
        is_in_string := false;
        lexbuf.lex_start_p <- string_start;
        STRING {
          str = raw_string;
          lit = (get_stored_string(), Some delim);
        } }
  | "'" newline "'"
      { update_loc lexbuf None 1 false 1;
        CHAR (char lexbuf 1) }
  | "'" [^ '\\' '\'' '\010' '\013'] "'"
      { CHAR (char lexbuf 1) }
  | "'\\" ['\\' '\'' '"' 'n' 't' 'b' 'r' ' '] "'"
      { CHAR (char_for_backslash lexbuf 2) }
  | "'\\" ['0'-'9'] ['0'-'9'] ['0'-'9'] "'"
      { CHAR (char_for_decimal_code lexbuf 2) }
  | "'\\" 'x' ['0'-'9' 'a'-'f' 'A'-'F'] ['0'-'9' 'a'-'f' 'A'-'F'] "'"
      { CHAR (char_for_hexadecimal_code lexbuf 3) }
  | "'\\" _
      { let l = Lexing.lexeme lexbuf in
        let esc = String.sub l 1 (String.length l - 1) in
        raise (Error(Illegal_escape esc, Location.curr lexbuf))
      }
  | "(*"
      { let start_loc = Location.curr lexbuf  in
        comment_start_loc := [start_loc];
        reset_string_buffer ();
        let end_loc = comment lexbuf in
        let s = get_stored_string () in
        reset_string_buffer ();
        COMMENT (s, { start_loc with
                      Location.loc_end = end_loc.Location.loc_end })
      }
  | "(*)"
      { let loc = Location.curr lexbuf  in
        if !print_warnings then
          Location.prerr_warning loc Warnings.Comment_start;
        comment_start_loc := [loc];
        reset_string_buffer ();
        let end_loc = comment lexbuf in
        let s = get_stored_string () in
        reset_string_buffer ();
        COMMENT (s, { loc with Location.loc_end = end_loc.Location.loc_end })
      }
  | "*)"
      { let loc = Location.curr lexbuf in
        Location.prerr_warning loc Warnings.Comment_not_end;
        lexbuf.Lexing.lex_curr_pos <- lexbuf.Lexing.lex_curr_pos - 1;
        let curpos = lexbuf.lex_curr_p in
        lexbuf.lex_curr_p <- { curpos with pos_cnum = curpos.pos_cnum - 1 };
        STAR
      }
  | "#" [' ' '\t']* (['0'-'9']+ as num) [' ' '\t']*
        ("\"" ([^ '\010' '\013' '"' ] * as name) "\"")?
        [^ '\010' '\013'] * newline
      { update_loc lexbuf name (int_of_string num) true 0;
        WHITESPACE (Lexing.lexeme lexbuf)
      }
  | "#"  { SHARP }
  | "&"  { AMPERSAND }
  | "&&" { AMPERAMPER }
  | "`"  { BACKQUOTE }
  | "'"  { QUOTE }
  | "("  { LPAREN }
  | ")"  { RPAREN }
  | "*"  { STAR }
  | ","  { COMMA }
  | "->" { MINUSGREATER }
  | "."  { DOT }
  | ".." { DOTDOT }
  | ":"  { COLON }
  | "::" { COLONCOLON }
  | ":=" { COLONEQUAL }
  | ":>" { COLONGREATER }
  | ";"  { SEMI }
  | ";;" { SEMISEMI }
  | "<"  { LESS }
  | "<-" { LESSMINUS }
  | "="  { EQUAL }
  | "["  { LBRACKET }
  | "[|" { LBRACKETBAR }
  | "[<" { LBRACKETLESS }
  | "[>" { LBRACKETGREATER }
  | "]"  { RBRACKET }
  | "{"  { LBRACE }
  | "{<" { LBRACELESS }
  | "|"  { BAR }
  | "||" { BARBAR }
  | "|]" { BARRBRACKET }
  | ">"  { GREATER }
  | ">]" { GREATERRBRACKET }
  | "}"  { RBRACE }
  | ">}" { GREATERRBRACE }
  | "[@" { LBRACKETAT }
  | "[%" { LBRACKETPERCENT }
  | "[%%" { LBRACKETPERCENTPERCENT }
  | "[@@" { LBRACKETATAT }
  | "!"  { BANG }
  | "!=" { INFIXOP0 "!=" }
  | "+"  { PLUS }
  | "+." { PLUSDOT }
  | "-"  { MINUS }
  | "-." { MINUSDOT }

  | "!" symbolchar +
            { PREFIXOP(Lexing.lexeme lexbuf) }
  | ['~' '?'] symbolchar +
            { PREFIXOP(Lexing.lexeme lexbuf) }
  | ['=' '<' '>' '|' '&' '$'] symbolchar *
            { INFIXOP0(Lexing.lexeme lexbuf) }
  | ['@' '^'] symbolchar *
            { INFIXOP1(Lexing.lexeme lexbuf) }
  | ['+' '-'] symbolchar *
            { INFIXOP2(Lexing.lexeme lexbuf) }
  | "**" symbolchar *
            { INFIXOP4(Lexing.lexeme lexbuf) }
  | '%'     { PERCENT }
  | ['*' '/' '%'] symbolchar *
            { INFIXOP3(Lexing.lexeme lexbuf) }
  | eof { EOF }
  | _
      { raise (Error(Illegal_character (Lexing.lexeme_char lexbuf 0),
                     Location.curr lexbuf))
      }

and comment = parse
    "(*"
      { comment_start_loc := (Location.curr lexbuf) :: !comment_start_loc;
        store_lexeme lexbuf;
        comment lexbuf;
      }
  | "*)"
      { match !comment_start_loc with
        | [] -> assert false
        | [_] -> comment_start_loc := []; Location.curr lexbuf
        | _ :: l -> comment_start_loc := l;
                  store_lexeme lexbuf;
                  comment lexbuf;
       }
  | "\""
      {
        string_start_loc := Location.curr lexbuf;
        store_string_char '"';
        is_in_string := true;
        begin try string lexbuf
        with Error (Unterminated_string, str_start) ->
          match !comment_start_loc with
          | [] -> assert false
          | loc :: _ ->
            let start = List.hd (List.rev !comment_start_loc) in
            comment_start_loc := [];
            raise (Error (Unterminated_string_in_comment (start, str_start),
                          loc))
        end;
        is_in_string := false;
        reset_raw ();
        store_string_char '"';
        comment lexbuf }
  | "{" lowercase* "|"
      {
        let delim = Lexing.lexeme lexbuf in
        let delim = String.sub delim 1 (String.length delim - 2) in
        string_start_loc := Location.curr lexbuf;
        store_lexeme lexbuf;
        is_in_string := true;
        begin try quoted_string delim lexbuf
        with Error (Unterminated_string, str_start) ->
          match !comment_start_loc with
          | [] -> assert false
          | loc :: _ ->
            let start = List.hd (List.rev !comment_start_loc) in
            comment_start_loc := [];
            raise (Error (Unterminated_string_in_comment (start, str_start), loc))
        end;
        is_in_string := false;
        reset_raw ();
        store_string_char '|';
        store_string delim;
        store_string_char '}';
        comment lexbuf }

  | "''"
      { store_lexeme lexbuf; comment lexbuf }
  | "'" newline "'"
      { update_loc lexbuf None 1 false 1;
        store_lexeme lexbuf;
        comment lexbuf
      }
  | "'" [^ '\\' '\'' '\010' '\013' ] "'"
      { store_lexeme lexbuf; comment lexbuf }
  | "'\\" ['\\' '"' '\'' 'n' 't' 'b' 'r' ' '] "'"
      { store_lexeme lexbuf; comment lexbuf }
  | "'\\" ['0'-'9'] ['0'-'9'] ['0'-'9'] "'"
      { store_lexeme lexbuf; comment lexbuf }
  | "'\\" 'x' ['0'-'9' 'a'-'f' 'A'-'F'] ['0'-'9' 'a'-'f' 'A'-'F'] "'"
      { store_lexeme lexbuf; comment lexbuf }
  | eof
      { match !comment_start_loc with
        | [] -> assert false
        | loc :: _ ->
          let start = List.hd (List.rev !comment_start_loc) in
          comment_start_loc := [];
          raise (Error (Unterminated_comment start, loc))
      }
  | newline
      { update_loc lexbuf None 1 false 0;
        store_lexeme lexbuf;
        comment lexbuf
      }
  | _
      { store_lexeme lexbuf; comment lexbuf }

and string = parse
    '"'
      { store_raw lexbuf }
  | '\\' newline ([' ' '\t'] * as space)
      { update_loc lexbuf None 1 false (String.length space);
        store_raw lexbuf;
        string lexbuf
      }
  | '\\' ['\\' '\'' '"' 'n' 't' 'b' 'r' ' ']
      { store_string_char (char_for_backslash lexbuf 1).lit;
        store_raw lexbuf;
        string lexbuf }
  | '\\' ['0'-'9'] ['0'-'9'] ['0'-'9']
      { store_string_char (char_for_decimal_code lexbuf 1).lit;
        store_raw lexbuf;
        string lexbuf }
  | '\\' 'x' ['0'-'9' 'a'-'f' 'A'-'F'] ['0'-'9' 'a'-'f' 'A'-'F']
      { store_string_char (char_for_hexadecimal_code lexbuf 2).lit;
        store_raw lexbuf;
        string lexbuf }
  | '\\' _
      { if in_comment ()
        then string lexbuf
        else begin
(*  Should be an error, but we are very lax.
          raise (Error (Illegal_escape (Lexing.lexeme lexbuf),
                        Location.curr lexbuf))
*)
          let loc = Location.curr lexbuf in
          Location.prerr_warning loc Warnings.Illegal_backslash;
          store_string_char (Lexing.lexeme_char lexbuf 0);
          store_string_char (Lexing.lexeme_char lexbuf 1);
          store_raw lexbuf;
          string lexbuf
        end
      }
  | newline
      { if not (in_comment ()) then
          Location.prerr_warning (Location.curr lexbuf) Warnings.Eol_in_string;
        update_loc lexbuf None 1 false 0;
        store_lexeme lexbuf;
        store_raw lexbuf;
        string lexbuf
      }
  | eof
      { is_in_string := false;
        raise (Error (Unterminated_string, !string_start_loc)) }
  | _
      { store_string_char(Lexing.lexeme_char lexbuf 0);
        store_raw lexbuf;
        string lexbuf }

and quoted_string delim = parse
  | newline
      { update_loc lexbuf None 1 false 0;
        store_lexeme lexbuf;
        store_raw lexbuf;
        quoted_string delim lexbuf
      }
  | eof
      { is_in_string := false;
        raise (Error (Unterminated_string, !string_start_loc)) }
  | "|" lowercase* "}"
      {
        let edelim = Lexing.lexeme lexbuf in
        let edelim = String.sub edelim 1 (String.length edelim - 2) in
        store_raw lexbuf;
        if delim = edelim then ()
        else (store_lexeme lexbuf; quoted_string delim lexbuf)
      }
  | _
      { store_string_char(Lexing.lexeme_char lexbuf 0);
        store_raw lexbuf;
        quoted_string delim lexbuf }

and skip_sharp_bang = parse
  | "#!" [^ '\n']* '\n' [^ '\n']* "\n!#\n"
       { update_loc lexbuf None 3 false 0 }
  | "#!" [^ '\n']* '\n'
       { update_loc lexbuf None 1 false 0 }
  | "" { () }

{
  let token_with_comments_and_whitespace = token

  let last_comments = ref []

  let rec token_with_comments lexbuf =
    match token_with_comments_and_whitespace lexbuf with
    | WHITESPACE _ -> token_with_comments lexbuf
    | tok -> tok

  let rec token lexbuf =
    match token_with_comments lexbuf with
        COMMENT (s, comment_loc) ->
          last_comments := (s, comment_loc) :: !last_comments;
          token lexbuf
      | tok -> tok

  let comments () = List.rev !last_comments
  let init () =
    is_in_string := false;
    last_comments := [];
    comment_start_loc := []

}
