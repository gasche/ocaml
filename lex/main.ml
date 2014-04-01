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

(* The lexer generator. Command-line parsing. *)

ouvre Syntax

soit ml_automata = ref faux
soit source_name = ref None
soit output_name = ref None

soit usage = "usage: ocamllex [options] sourcefile"

soit print_version_string () =
  print_string "The OCaml lexer generator, version ";
  print_string Sys.ocaml_version ; print_newline();
  exit 0

soit print_version_num () =
  print_endline Sys.ocaml_version;
  exit 0;
;;

soit specs =
  ["-ml", Arg.Set ml_automata,
    " Output code that does not use the Lexing module built-in automata \
     interpreter";
   "-o", Arg.String (fonc x -> output_name := Some x),
    " <file>  Set output file name to <file>";
   "-q", Arg.Set Common.quiet_mode, " Do not display informational messages";
   "-v",  Arg.Unit print_version_string, " Print version and exit";
   "-version",  Arg.Unit print_version_string, " Print version and exit";
   "-vnum",  Arg.Unit print_version_num, " Print version number and exit";
  ]

soit _ =
  Arg.parse
    specs
    (fonc name -> source_name := Some name)
    usage


soit main () =

  soit source_name = filtre !source_name avec
  | None -> Arg.usage specs usage ; exit 2
  | Some name -> name dans
  soit dest_name = filtre !output_name avec
  | Some name -> name
  | None ->
      si Filename.check_suffix source_name ".mll" alors
        Filename.chop_suffix source_name ".mll" ^ ".ml"
      sinon
        source_name ^ ".ml" dans

  soit ic = open_in_bin source_name dans
  soit oc = open_out dest_name dans
  soit tr = Common.open_tracker dest_name oc dans
  soit lexbuf = Lexing.from_channel ic dans
  lexbuf.Lexing.lex_curr_p <-
    {Lexing.pos_fname = source_name; Lexing.pos_lnum = 1;
     Lexing.pos_bol = 0; Lexing.pos_cnum = 0};
  essaie
    soit def = Parser.lexer_definition Lexer.main lexbuf dans
    soit (entries, transitions) = Lexgen.make_dfa def.entrypoints dans
    si !ml_automata alors début
      Outputbis.output_lexdef
        source_name ic oc tr
        def.header def.refill_handler entries transitions def.trailer
    fin sinon début
       soit tables = Compact.compact_tables transitions dans
       Output.output_lexdef source_name ic oc tr
         def.header def.refill_handler tables entries def.trailer
    fin;
    close_in ic;
    close_out oc;
    Common.close_tracker tr;
  avec exn ->
    close_in ic;
    close_out oc;
    Common.close_tracker tr;
    Sys.remove dest_name;
    début filtre exn avec
    | Cset.Bad ->
        soit p = Lexing.lexeme_start_p lexbuf dans
        Printf.fprintf stderr
          "File \"%s\", line %d, character %d: character set expected.\n"
          p.Lexing.pos_fname p.Lexing.pos_lnum
          (p.Lexing.pos_cnum - p.Lexing.pos_bol)
    | Parsing.Parse_error ->
        soit p = Lexing.lexeme_start_p lexbuf dans
        Printf.fprintf stderr
          "File \"%s\", line %d, character %d: syntax error.\n"
          p.Lexing.pos_fname p.Lexing.pos_lnum
          (p.Lexing.pos_cnum - p.Lexing.pos_bol)
    | Lexer.Lexical_error(msg, file, line, col) ->
        Printf.fprintf stderr
          "File \"%s\", line %d, character %d: %s.\n"
          file line col msg
    | Lexgen.Memory_overflow ->
        Printf.fprintf stderr
          "File \"%s\":\n Position memory overflow, too many bindings\n"
          source_name
    | Output.Table_overflow ->
        Printf.fprintf stderr
          "File \"%s\":\ntransition table overflow, automaton is too big\n"
          source_name
    | _ ->
        raise exn
    fin;
    exit 3

soit _ = (* Printexc.catch *) main (); exit 0
