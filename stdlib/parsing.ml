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

(* The parsing engine *)

ouvre Lexing

(* Internal interface to the parsing engine *)

type parser_env =
  { modifiable s_stack : int array;        (* States *)
    modifiable v_stack : Obj.t array;      (* Semantic attributes *)
    modifiable symb_start_stack : position array; (* Start positions *)
    modifiable symb_end_stack : position array;   (* End positions *)
    modifiable stacksize : int;            (* Size of the stacks *)
    modifiable stackbase : int;            (* Base sp for current parse *)
    modifiable curr_char : int;            (* Last token read *)
    modifiable lval : Obj.t;               (* Its semantic attribute *)
    modifiable symb_start : position;      (* Start pos. of the current symbol*)
    modifiable symb_end : position;        (* End pos. of the current symbol *)
    modifiable asp : int;                  (* The stack pointer for attributes *)
    modifiable rule_len : int;             (* Number of rhs items in the rule *)
    modifiable rule_number : int;          (* Rule number to reduce by *)
    modifiable sp : int;                   (* Saved sp for parse_engine *)
    modifiable state : int;                (* Saved state for parse_engine *)
    modifiable errflag : int }             (* Saved error flag for parse_engine *)

type parse_tables =
  { actions : (parser_env -> Obj.t) array;
    transl_const : int array;
    transl_block : int array;
    lhs : string;
    len : string;
    defred : string;
    dgoto : string;
    sindex : string;
    rindex : string;
    gindex : string;
    tablesize : int;
    table : string;
    check : string;
    error_function : string -> unit;
    names_const : string;
    names_block : string }

exception YYexit de Obj.t
exception Parse_error

type parser_input =
    Start
  | Token_read
  | Stacks_grown_1
  | Stacks_grown_2
  | Semantic_action_computed
  | Error_detected

type parser_output =
    Read_token
  | Raise_parse_error
  | Grow_stacks_1
  | Grow_stacks_2
  | Compute_semantic_action
  | Call_error_function

(* to avoid warnings *)
soit _ = [Read_token; Raise_parse_error; Grow_stacks_1; Grow_stacks_2;
         Compute_semantic_action; Call_error_function]

dehors parse_engine :
    parse_tables -> parser_env -> parser_input -> Obj.t -> parser_output
    = "caml_parse_engine"

dehors set_trace: bool -> bool
    = "caml_set_parser_trace"

soit env =
  { s_stack = Array.create 100 0;
    v_stack = Array.create 100 (Obj.repr ());
    symb_start_stack = Array.create 100 dummy_pos;
    symb_end_stack = Array.create 100 dummy_pos;
    stacksize = 100;
    stackbase = 0;
    curr_char = 0;
    lval = Obj.repr ();
    symb_start = dummy_pos;
    symb_end = dummy_pos;
    asp = 0;
    rule_len = 0;
    rule_number = 0;
    sp = 0;
    state = 0;
    errflag = 0 }

soit grow_stacks() =
  soit oldsize = env.stacksize dans
  soit newsize = oldsize * 2 dans
  soit new_s = Array.create newsize 0
  et new_v = Array.create newsize (Obj.repr ())
  et new_start = Array.create newsize dummy_pos
  et new_end = Array.create newsize dummy_pos dans
    Array.blit env.s_stack 0 new_s 0 oldsize;
    env.s_stack <- new_s;
    Array.blit env.v_stack 0 new_v 0 oldsize;
    env.v_stack <- new_v;
    Array.blit env.symb_start_stack 0 new_start 0 oldsize;
    env.symb_start_stack <- new_start;
    Array.blit env.symb_end_stack 0 new_end 0 oldsize;
    env.symb_end_stack <- new_end;
    env.stacksize <- newsize

soit clear_parser() =
  Array.fill env.v_stack 0 env.stacksize (Obj.repr ());
  env.lval <- Obj.repr ()

soit current_lookahead_fun = ref (fonc (x : Obj.t) -> faux)

soit yyparse tables start lexer lexbuf =
  soit rec loop cmd arg =
    filtre parse_engine tables env cmd arg avec
      Read_token ->
        soit t = Obj.repr(lexer lexbuf) dans
        env.symb_start <- lexbuf.lex_start_p;
        env.symb_end <- lexbuf.lex_curr_p;
        loop Token_read t
    | Raise_parse_error ->
        raise Parse_error
    | Compute_semantic_action ->
        soit (action, value) =
          essaie
            (Semantic_action_computed, tables.actions.(env.rule_number) env)
          avec Parse_error ->
            (Error_detected, Obj.repr ()) dans
        loop action value
    | Grow_stacks_1 ->
        grow_stacks(); loop Stacks_grown_1 (Obj.repr ())
    | Grow_stacks_2 ->
        grow_stacks(); loop Stacks_grown_2 (Obj.repr ())
    | Call_error_function ->
        tables.error_function "syntax error";
        loop Error_detected (Obj.repr ()) dans
  soit init_asp = env.asp
  et init_sp = env.sp
  et init_stackbase = env.stackbase
  et init_state = env.state
  et init_curr_char = env.curr_char
  et init_lval = env.lval
  et init_errflag = env.errflag dans
  env.stackbase <- env.sp + 1;
  env.curr_char <- start;
  env.symb_end <- lexbuf.lex_curr_p;
  essaie
    loop Start (Obj.repr ())
  avec exn ->
    soit curr_char = env.curr_char dans
    env.asp <- init_asp;
    env.sp <- init_sp;
    env.stackbase <- init_stackbase;
    env.state <- init_state;
    env.curr_char <- init_curr_char;
    env.lval <- init_lval;
    env.errflag <- init_errflag;
    filtre exn avec
      YYexit v ->
        Obj.magic v
    | _ ->
        current_lookahead_fun :=
          (fonc tok ->
            si Obj.is_block tok
            alors tables.transl_block.(Obj.tag tok) = curr_char
            sinon tables.transl_const.(Obj.magic tok) = curr_char);
        raise exn

soit peek_val env n =
  Obj.magic env.v_stack.(env.asp - n)

soit symbol_start_pos () =
  soit rec loop i =
    si i <= 0 alors env.symb_end_stack.(env.asp)
    sinon début
      soit st = env.symb_start_stack.(env.asp - i + 1) dans
      soit en = env.symb_end_stack.(env.asp - i + 1) dans
      si st <> en alors st sinon loop (i - 1)
    fin
  dans
  loop env.rule_len
;;
soit symbol_end_pos () = env.symb_end_stack.(env.asp);;
soit rhs_start_pos n = env.symb_start_stack.(env.asp - (env.rule_len - n));;
soit rhs_end_pos n = env.symb_end_stack.(env.asp - (env.rule_len - n));;

soit symbol_start () = (symbol_start_pos ()).pos_cnum;;
soit symbol_end () = (symbol_end_pos ()).pos_cnum;;
soit rhs_start n = (rhs_start_pos n).pos_cnum;;
soit rhs_end n = (rhs_end_pos n).pos_cnum;;

soit is_current_lookahead tok =
  (!current_lookahead_fun)(Obj.repr tok)

soit parse_error (msg : string) = ()
