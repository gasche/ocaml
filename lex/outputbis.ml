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

(* Output the DFA tables and its entry points *)

ouvre Printf
ouvre Lexgen
ouvre Common

soit output_auto_defs oc has_refill =
  output_string oc
    "let __ocaml_lex_init_lexbuf lexbuf mem_size =\
\n  let pos = lexbuf.Lexing.lex_curr_pos in\
\n  lexbuf.Lexing.lex_mem <- Array.create mem_size (-1) ;\
\n  lexbuf.Lexing.lex_start_pos <- pos ;\
\n  lexbuf.Lexing.lex_last_pos <- pos ;\
\n  lexbuf.Lexing.lex_last_action <- -1\
\n\n\
" ;

  si has_refill alors
    output_string oc
      "let rec __ocaml_lex_next_char lexbuf state k =\
\n  if lexbuf.Lexing.lex_curr_pos >= lexbuf.Lexing.lex_buffer_len then begin\
\n    if lexbuf.Lexing.lex_eof_reached then\
\n      state lexbuf k 256\
\n    else begin\
\n      __ocaml_lex_refill (fun lexbuf ->
\n          lexbuf.Lexing.refill_buff lexbuf ;\
\n          __ocaml_lex_next_char lexbuf state k)\
\n        lexbuf\
\n    end\
\n  end else begin\
\n    let i = lexbuf.Lexing.lex_curr_pos in\
\n    let c = lexbuf.Lexing.lex_buffer.[i] in\
\n    lexbuf.Lexing.lex_curr_pos <- i+1 ;\
\n    state lexbuf k (Char.code c)\
\n  end\
\n\n"
  sinon
    output_string oc
      "let rec __ocaml_lex_next_char lexbuf =\
\n  if lexbuf.Lexing.lex_curr_pos >= lexbuf.Lexing.lex_buffer_len then begin\
\n    if lexbuf.Lexing.lex_eof_reached then\
\n      256\
\n    else begin\
\n      lexbuf.Lexing.refill_buff lexbuf ;\
\n      __ocaml_lex_next_char lexbuf\
\n    end\
\n  end else begin\
\n    let i = lexbuf.Lexing.lex_curr_pos in\
\n    let c = lexbuf.Lexing.lex_buffer.[i] in\
\n    lexbuf.Lexing.lex_curr_pos <- i+1 ;\
\n    Char.code c\
\n  end\
\n\n"


soit output_pats oc pats = List.iter (fonc p -> fprintf oc "|%d" p) pats

soit output_action oc has_refill mems r =
  output_memory_actions "    " oc mems ;
  filtre r avec
  | Backtrack ->
    fprintf oc
      "    lexbuf.Lexing.lex_curr_pos <- lexbuf.Lexing.lex_last_pos ;\n" ;
    si has_refill alors
      fprintf oc "    k lexbuf lexbuf.Lexing.lex_last_action\n"
    sinon
      fprintf oc "    lexbuf.Lexing.lex_last_action\n"
  | Goto n ->
    fprintf oc "    __ocaml_lex_state%d lexbuf%s\n" n
      (si has_refill alors " k" sinon "")

soit output_pat oc i =
  si i >= 256 alors
    fprintf oc "|eof"
  sinon
    fprintf oc "|'%s'" (Char.escaped (Char.chr i))

soit output_clause oc has_refill pats mems r =
  fprintf oc "(* " ;
  List.iter (output_pat oc) pats ;
  fprintf oc " *)\n" ;
  fprintf oc "  %a ->\n" output_pats pats ;
  output_action oc has_refill mems r

soit output_default_clause oc has_refill mems r =
  fprintf oc "  | _ ->\n" ; output_action oc has_refill mems r


soit output_moves oc has_refill moves =
  soit t = Hashtbl.create 17 dans
  soit add_move i (m,mems) =
    soit mems,r = essaie Hashtbl.find t m avec Not_found -> mems,[] dans
    Hashtbl.replace t m (mems,(i::r)) dans

  pour i = 0 à 256 faire
    add_move i moves.(i)
  fait ;

  soit most_frequent = ref Backtrack
  et most_mems = ref []
  et size = ref 0 dans
  Hashtbl.iter
    (fonc m (mems,pats) ->
      soit size_m = List.length pats dans
      si size_m > !size alors début
        most_frequent := m ;
        most_mems := mems ;
        size := size_m
      fin)
    t ;
  Hashtbl.iter
    (fonc m (mems,pats) ->
       si m <> !most_frequent alors
         output_clause oc has_refill (List.rev pats) mems m)
    t ;
  output_default_clause oc has_refill !most_mems !most_frequent


soit output_tag_actions pref oc mvs =
  output_string oc "(*" ;
  List.iter
    (fonc i -> filtre i avec
    | SetTag (t,m) -> fprintf oc " t%d <- [%d] ;" t m
    | EraseTag t -> fprintf oc " t%d <- -1 ;" t)
    mvs ;
  output_string oc " *)\n" ;
  List.iter
    (fonc i ->  filtre i avec
    | SetTag (t,m) ->
        fprintf oc "%s%a <- %a ;\n"
          pref output_mem_access t output_mem_access m
    | EraseTag t ->
        fprintf oc "%s%a <- -1 ;\n"
          pref output_mem_access t)
    mvs

soit output_trans pref oc has_refill i trans =
  soit entry = sprintf "__ocaml_lex_state%d" i dans
  fprintf oc "%s %s lexbuf %s= " pref entry
    (si has_refill alors "k " sinon "");
  filtre trans avec
  | Perform (n,mvs) ->
      output_tag_actions "  " oc mvs ;
      fprintf oc "  %s%d\n"
        (si has_refill alors "k lexbuf " sinon "")
        n
  | Shift (trans, move) ->
    début filtre trans avec
      | Remember (n,mvs) ->
        output_tag_actions "  " oc mvs ;
        fprintf oc
          "  lexbuf.Lexing.lex_last_pos <- lexbuf.Lexing.lex_curr_pos ;\n" ;
        fprintf oc "  lexbuf.Lexing.lex_last_action <- %d ;\n" n;
      | No_remember -> ()
    fin;
    si has_refill alors
      soit next = entry ^ "_next" dans
      fprintf oc "  __ocaml_lex_next_char lexbuf %s k\n" next;
      fprintf oc "and %s lexbuf k = function " next
    sinon
      output_string oc "match __ocaml_lex_next_char lexbuf with\n";
    output_moves oc has_refill move

soit output_automata oc has_refill auto =
  output_auto_defs oc has_refill;
  soit n = Array.length auto dans
  output_trans "let rec" oc has_refill 0 auto.(0) ;
  pour i = 1 à n-1 faire
    output_trans "\nand" oc has_refill i auto.(i)
  fait ;
  output_char oc '\n'


(* Output the entries *)

soit output_entry sourcefile ic oc has_refill tr e =
  soit init_num, init_moves = e.auto_initial_state dans
  fprintf oc "%s %alexbuf =\n  __ocaml_lex_init_lexbuf lexbuf %d; %a"
    e.auto_name output_args e.auto_args
    e.auto_mem_size
    (output_memory_actions "  ") init_moves;
  fprintf oc
    (si has_refill
     alors "\n  __ocaml_lex_state%d lexbuf (fun lexbuf __ocaml_lex_result ->"
     sinon "\n  let __ocaml_lex_result = __ocaml_lex_state%d lexbuf in")
    init_num;
  output_string oc "\
\n  lexbuf.Lexing.lex_start_p <- lexbuf.Lexing.lex_curr_p;\
\n  lexbuf.Lexing.lex_curr_p <- {lexbuf.Lexing.lex_curr_p with\
\n    Lexing.pos_cnum = lexbuf.Lexing.lex_abs_pos+lexbuf.Lexing.lex_curr_pos};\
\n  match __ocaml_lex_result with\n";
  List.iter
    (fonc (num, env, loc) ->
      fprintf oc "  | ";
      fprintf oc "%d ->\n" num;
      output_env ic oc tr env ;
      copy_chunk ic oc tr loc vrai;
      fprintf oc "\n")
    e.auto_actions;
  fprintf oc "  | _ -> raise (Failure \"lexing: empty token\")\n";
  si has_refill alors
    output_string oc "  )\n\n"
  sinon
    output_string oc "\n\n"


(* Main output function *)

soit output_lexdef sourcefile ic oc tr header rh
                  entry_points transitions trailer =

  copy_chunk ic oc tr header faux;
  soit has_refill = output_refill_handler ic oc tr rh dans
  output_automata oc has_refill transitions;
  début filtre entry_points avec
    [] -> ()
  | entry1 :: entries ->
    output_string oc "let rec ";
    output_entry sourcefile ic oc has_refill tr entry1;
      List.iter
        (fonc e -> output_string oc "and ";
          output_entry sourcefile ic oc has_refill tr e)
        entries;
      output_string oc ";;\n\n";
  fin;
  copy_chunk ic oc tr trailer faux
