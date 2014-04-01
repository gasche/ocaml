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

(* Compaction of an automata *)

ouvre Lexgen

(* Code for memory actions  *)
soit code = Table.create 0

(* instructions are 2 8-bits integers, a 0xff byte means return *)

soit emit_int i = Table.emit code i

soit ins_mem i c =  filtre i avec
  | Copy (dst, src) -> dst::src::c
  | Set dst         -> dst::0xff::c


soit ins_tag i c = filtre i avec
  | SetTag (dst, src) -> dst::src::c
  | EraseTag dst      -> dst::0xff::c


soit do_emit_code c =
  soit r = Table.size code dans
  List.iter emit_int c ;
  emit_int 0xff ;
  r

soit memory = Hashtbl.create 101

soit mem_emit_code c =
  essaie Hashtbl.find memory c avec
  | Not_found ->
      soit r = do_emit_code c dans
      Hashtbl.add memory c r ;
      r

(* Code address 0 is the empty code (ie do nothing) *)
soit _ = mem_emit_code []

soit emit_tag_code c = mem_emit_code (List.fold_right ins_tag c [])
et emit_mem_code c  =mem_emit_code (List.fold_right ins_mem c [])

(*******************************************)
(* Compact the transition and check arrays *)
(*******************************************)


(* Determine the integer occurring most frequently in an array *)

soit most_frequent_elt v =
  soit frequencies = Hashtbl.create 17 dans
  soit max_freq = ref 0 dans
  soit most_freq = ref (v.(0)) dans
  pour i = 0 à Array.length v - 1 faire
    soit e = v.(i) dans
    soit r =
      essaie
        Hashtbl.find frequencies e
      avec Not_found ->
        soit r = ref 1 dans Hashtbl.add frequencies e r; r dans
    incr r;
    si !r > !max_freq alors début max_freq := !r; most_freq := e fin
  fait;
  !most_freq

(* Transform an array into a list of (position, non-default element) *)

soit non_default_elements def v =
  soit rec nondef i =
    si i >= Array.length v alors [] sinon début
      soit e = v.(i) dans
      si e = def alors nondef(i+1) sinon (i, e) :: nondef(i+1)
    fin dans
  nondef 0


type t_compact =
 {modifiable c_trans : int array ;
  modifiable c_check : int array ;
  modifiable c_last_used : int ; }

soit create_compact () =
  { c_trans = Array.create 1024 0 ;
    c_check = Array.create 1024 (-1) ;
    c_last_used = 0 ; }

soit reset_compact c =
  c.c_trans <- Array.create 1024 0 ;
  c.c_check <- Array.create 1024 (-1) ;
  c.c_last_used <- 0

(* One compacted table for transitions, one other for memory actions *)
soit trans = create_compact ()
et moves = create_compact ()


soit grow_compact c =
  soit old_trans = c.c_trans
  et old_check = c.c_check dans
  soit n = Array.length old_trans dans
  c.c_trans <- Array.create (2*n) 0;
  Array.blit old_trans 0 c.c_trans 0 c.c_last_used;
  c.c_check <- Array.create (2*n) (-1);
  Array.blit old_check 0 c.c_check 0 c.c_last_used

soit do_pack state_num orig compact =
  soit default = most_frequent_elt orig dans
  soit nondef = non_default_elements default orig dans
  soit rec pack_from b =
    pendant_que
      b + 257 > Array.length compact.c_trans
    faire
      grow_compact compact
    fait;
    soit rec try_pack = fonction
      [] -> b
    | (pos, v) :: rem ->
        si compact.c_check.(b + pos) = -1 alors
          try_pack rem
        sinon pack_from (b+1) dans
    try_pack nondef dans
  soit base = pack_from 0 dans
  List.iter
    (fonc (pos, v) ->
      compact.c_trans.(base + pos) <- v;
      compact.c_check.(base + pos) <- state_num)
    nondef;
  si base + 257 > compact.c_last_used alors
    compact.c_last_used <- base + 257;
  (base, default)

soit pack_moves state_num move_t =
  soit move_v = Array.create 257 0
  et move_m = Array.create 257 0 dans
  pour i = 0 à 256 faire
    soit act,c = move_t.(i) dans
    move_v.(i) <- (filtre act avec Backtrack -> -1 | Goto n -> n) ;
    move_m.(i) <- emit_mem_code c
  fait ;
  soit pk_trans = do_pack state_num move_v trans
  et pk_moves = do_pack state_num move_m moves dans
  pk_trans, pk_moves


(* Build the tables *)

type lex_tables =
  { tbl_base: int array;                 (* Perform / Shift *)
    tbl_backtrk: int array;              (* No_remember / Remember *)
    tbl_default: int array;              (* Default transition *)
    tbl_trans: int array;                (* Transitions (compacted) *)
    tbl_check: int array;                (* Check (compacted) *)
(* code addresses are managed in a similar fashion as transitions *)
    tbl_base_code : int array;           (* code ptr / base for Shift *)
    tbl_backtrk_code : int array;        (* nothing / code when Remember *)
(* moves to execute before transitions (compacted) *)
    tbl_default_code : int array;
    tbl_trans_code : int array;
    tbl_check_code : int array;
(* byte code itself *)
    tbl_code: int array;}


soit compact_tables state_v =
  soit n = Array.length state_v dans
  soit base = Array.create n 0
  et backtrk = Array.create n (-1)
  et default = Array.create n 0
  et base_code = Array.create n 0
  et backtrk_code = Array.create n 0
  et default_code = Array.create n 0 dans
  pour i = 0 à n - 1 faire
    filtre state_v.(i) avec
    | Perform (n,c) ->
        base.(i) <- -(n+1) ;
        base_code.(i) <- emit_tag_code c
    | Shift(trans, move) ->
        début filtre trans avec
        | No_remember -> ()
        | Remember (n,c) ->
            backtrk.(i) <- n ;
            backtrk_code.(i) <- emit_tag_code c
        fin;
        soit (b_trans, d_trans),(b_moves,d_moves) = pack_moves i move dans
        base.(i) <- b_trans; default.(i) <- d_trans ;
        base_code.(i) <- b_moves; default_code.(i) <- d_moves ;
  fait;
  soit code = Table.trim code dans
  soit tables =
    si Array.length code > 1 alors
      { tbl_base = base;
        tbl_backtrk = backtrk;
        tbl_default = default;
        tbl_trans = Array.sub trans.c_trans 0 trans.c_last_used;
        tbl_check = Array.sub trans.c_check 0 trans.c_last_used;
        tbl_base_code = base_code ;
        tbl_backtrk_code = backtrk_code;
        tbl_default_code = default_code;
        tbl_trans_code = Array.sub moves.c_trans 0 moves.c_last_used;
        tbl_check_code = Array.sub moves.c_check 0 moves.c_last_used;
        tbl_code = code}
    sinon (* when no memory moves, do not emit related tables *)
       { tbl_base = base;
        tbl_backtrk = backtrk;
        tbl_default = default;
        tbl_trans = Array.sub trans.c_trans 0 trans.c_last_used;
        tbl_check = Array.sub trans.c_check 0 trans.c_last_used;
        tbl_base_code = [||] ;
        tbl_backtrk_code = [||];
        tbl_default_code = [||];
        tbl_trans_code = [||];
        tbl_check_code = [||];
        tbl_code = [||]}
  dans
  reset_compact trans ;
  reset_compact moves ;
  tables
