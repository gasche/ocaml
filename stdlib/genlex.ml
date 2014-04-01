(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*              Xavier Leroy, projet Cristal, INRIA Rocquencourt       *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

type token =
    Kwd de string
  | Ident de string
  | Int de int
  | Float de float
  | String de string
  | Char de char

(* The string buffering machinery *)

soit initial_buffer = String.create 32

soit buffer = ref initial_buffer
soit bufpos = ref 0

soit reset_buffer () = buffer := initial_buffer; bufpos := 0

soit store c =
  si !bufpos >= String.length !buffer alors
    début
      soit newbuffer = String.create (2 * !bufpos) dans
      String.blit !buffer 0 newbuffer 0 !bufpos; buffer := newbuffer
    fin;
  String.set !buffer !bufpos c;
  incr bufpos

soit get_string () =
  soit s = String.sub !buffer 0 !bufpos dans buffer := initial_buffer; s

(* The lexer *)

soit make_lexer keywords =
  soit kwd_table = Hashtbl.create 17 dans
  List.iter (fonc s -> Hashtbl.add kwd_table s (Kwd s)) keywords;
  soit ident_or_keyword id =
    essaie Hashtbl.find kwd_table id avec
      Not_found -> Ident id
  et keyword_or_error c =
    soit s = String.make 1 c dans
    essaie Hashtbl.find kwd_table s avec
      Not_found -> raise (Stream.Error ("Illegal character " ^ s))
  dans
  soit rec next_token (strm__ : _ Stream.t) =
    filtre Stream.peek strm__ avec
      Some (' ' | '\010' | '\013' | '\009' | '\026' | '\012') ->
        Stream.junk strm__; next_token strm__
    | Some ('A'..'Z' | 'a'..'z' | '_' | '\192'..'\255' tel c) ->
        Stream.junk strm__;
        soit s = strm__ dans reset_buffer (); store c; ident s
    | Some
        ('!' | '%' | '&' | '$' | '#' | '+' | '/' | ':' | '<' | '=' | '>' |
         '?' | '@' | '\\' | '~' | '^' | '|' | '*' tel c) ->
        Stream.junk strm__;
        soit s = strm__ dans reset_buffer (); store c; ident2 s
    | Some ('0'..'9' tel c) ->
        Stream.junk strm__;
        soit s = strm__ dans reset_buffer (); store c; number s
    | Some '\'' ->
        Stream.junk strm__;
        soit c =
          essaie char strm__ avec
            Stream.Failure -> raise (Stream.Error "")
        dans
        début filtre Stream.peek strm__ avec
          Some '\'' -> Stream.junk strm__; Some (Char c)
        | _ -> raise (Stream.Error "")
        fin
    | Some '\"' ->
        Stream.junk strm__;
        soit s = strm__ dans reset_buffer (); Some (String (string s))
    | Some '-' -> Stream.junk strm__; neg_number strm__
    | Some '(' -> Stream.junk strm__; maybe_comment strm__
    | Some c -> Stream.junk strm__; Some (keyword_or_error c)
    | _ -> None
  et ident (strm__ : _ Stream.t) =
    filtre Stream.peek strm__ avec
      Some
        ('A'..'Z' | 'a'..'z' | '\192'..'\255' | '0'..'9' | '_' | '\'' tel c) ->
        Stream.junk strm__; soit s = strm__ dans store c; ident s
    | _ -> Some (ident_or_keyword (get_string ()))
  et ident2 (strm__ : _ Stream.t) =
    filtre Stream.peek strm__ avec
      Some
        ('!' | '%' | '&' | '$' | '#' | '+' | '-' | '/' | ':' | '<' | '=' |
         '>' | '?' | '@' | '\\' | '~' | '^' | '|' | '*' tel c) ->
        Stream.junk strm__; soit s = strm__ dans store c; ident2 s
    | _ -> Some (ident_or_keyword (get_string ()))
  et neg_number (strm__ : _ Stream.t) =
    filtre Stream.peek strm__ avec
      Some ('0'..'9' tel c) ->
        Stream.junk strm__;
        soit s = strm__ dans reset_buffer (); store '-'; store c; number s
    | _ -> soit s = strm__ dans reset_buffer (); store '-'; ident2 s
  et number (strm__ : _ Stream.t) =
    filtre Stream.peek strm__ avec
      Some ('0'..'9' tel c) ->
        Stream.junk strm__; soit s = strm__ dans store c; number s
    | Some '.' ->
        Stream.junk strm__; soit s = strm__ dans store '.'; decimal_part s
    | Some ('e' | 'E') ->
        Stream.junk strm__; soit s = strm__ dans store 'E'; exponent_part s
    | _ -> Some (Int (int_of_string (get_string ())))
  et decimal_part (strm__ : _ Stream.t) =
    filtre Stream.peek strm__ avec
      Some ('0'..'9' tel c) ->
        Stream.junk strm__; soit s = strm__ dans store c; decimal_part s
    | Some ('e' | 'E') ->
        Stream.junk strm__; soit s = strm__ dans store 'E'; exponent_part s
    | _ -> Some (Float (float_of_string (get_string ())))
  et exponent_part (strm__ : _ Stream.t) =
    filtre Stream.peek strm__ avec
      Some ('+' | '-' tel c) ->
        Stream.junk strm__; soit s = strm__ dans store c; end_exponent_part s
    | _ -> end_exponent_part strm__
  et end_exponent_part (strm__ : _ Stream.t) =
    filtre Stream.peek strm__ avec
      Some ('0'..'9' tel c) ->
        Stream.junk strm__; soit s = strm__ dans store c; end_exponent_part s
    | _ -> Some (Float (float_of_string (get_string ())))
  et string (strm__ : _ Stream.t) =
    filtre Stream.peek strm__ avec
      Some '\"' -> Stream.junk strm__; get_string ()
    | Some '\\' ->
        Stream.junk strm__;
        soit c =
          essaie escape strm__ avec
            Stream.Failure -> raise (Stream.Error "")
        dans
        soit s = strm__ dans store c; string s
    | Some c -> Stream.junk strm__; soit s = strm__ dans store c; string s
    | _ -> raise Stream.Failure
  et char (strm__ : _ Stream.t) =
    filtre Stream.peek strm__ avec
      Some '\\' ->
        Stream.junk strm__;
        début essaie escape strm__ avec
          Stream.Failure -> raise (Stream.Error "")
        fin
    | Some c -> Stream.junk strm__; c
    | _ -> raise Stream.Failure
  et escape (strm__ : _ Stream.t) =
    filtre Stream.peek strm__ avec
      Some 'n' -> Stream.junk strm__; '\n'
    | Some 'r' -> Stream.junk strm__; '\r'
    | Some 't' -> Stream.junk strm__; '\t'
    | Some ('0'..'9' tel c1) ->
        Stream.junk strm__;
        début filtre Stream.peek strm__ avec
          Some ('0'..'9' tel c2) ->
            Stream.junk strm__;
            début filtre Stream.peek strm__ avec
              Some ('0'..'9' tel c3) ->
                Stream.junk strm__;
                Char.chr
                  ((Char.code c1 - 48) * 100 + (Char.code c2 - 48) * 10 +
                     (Char.code c3 - 48))
            | _ -> raise (Stream.Error "")
            fin
        | _ -> raise (Stream.Error "")
        fin
    | Some c -> Stream.junk strm__; c
    | _ -> raise Stream.Failure
  et maybe_comment (strm__ : _ Stream.t) =
    filtre Stream.peek strm__ avec
      Some '*' ->
        Stream.junk strm__; soit s = strm__ dans comment s; next_token s
    | _ -> Some (keyword_or_error '(')
  et comment (strm__ : _ Stream.t) =
    filtre Stream.peek strm__ avec
      Some '(' -> Stream.junk strm__; maybe_nested_comment strm__
    | Some '*' -> Stream.junk strm__; maybe_end_comment strm__
    | Some c -> Stream.junk strm__; comment strm__
    | _ -> raise Stream.Failure
  et maybe_nested_comment (strm__ : _ Stream.t) =
    filtre Stream.peek strm__ avec
      Some '*' -> Stream.junk strm__; soit s = strm__ dans comment s; comment s
    | Some c -> Stream.junk strm__; comment strm__
    | _ -> raise Stream.Failure
  et maybe_end_comment (strm__ : _ Stream.t) =
    filtre Stream.peek strm__ avec
      Some ')' -> Stream.junk strm__; ()
    | Some '*' -> Stream.junk strm__; maybe_end_comment strm__
    | Some c -> Stream.junk strm__; comment strm__
    | _ -> raise Stream.Failure
  dans
  fonc input -> Stream.from (fonc count -> next_token input)
