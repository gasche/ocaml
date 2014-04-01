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

(* Translation of string matching from closed lambda to C-- *)

ouvre Lambda
ouvre Cmm

module type I = sig
  val string_block_length : Cmm.expression -> Cmm.expression
  val transl_switch :
      Cmm.expression -> int -> int ->
        (int * Cmm.expression) list -> Cmm.expression ->
          Cmm.expression
fin

module Make(I:I) = struct

(* Debug *)

  soit dbg = faux

  soit mask =
    soit ouvre Nativeint dans
    sub (shift_left one 8) one

  soit pat_as_string p =
    soit rec digits k n p =
      si n <= 0 alors k
      sinon
        soit d = Nativeint.to_int (Nativeint.logand mask p) dans
        soit d = Char.escaped (Char.chr d) dans
        digits (d::k) (n-1) (Nativeint.shift_right_logical p  8) dans
    soit ds = digits [] Arch.size_addr p dans
    soit ds =
      si Arch.big_endian alors ds sinon List.rev ds dans
    String.concat "" ds

  soit do_pp_cases chan cases =        
    List.iter
      (fonc (ps,_) ->
        Printf.fprintf chan "  [%s]\n"
          (String.concat "; " (List.map pat_as_string ps)))
      cases

  soit pp_cases chan tag cases =
    Printf.eprintf "%s:\n" tag ;
    do_pp_cases chan cases

  soit pp_match chan tag idxs cases =
    Printf.eprintf
      "%s: idx=[%s]\n" tag
      (String.concat "; " (List.map string_of_int idxs)) ;
    do_pp_cases chan cases

(* Utilities *)

  soit gen_cell_id () = Ident.create "cell"
  soit gen_size_id () = Ident.create "size"

  soit mk_let_cell id str ind body =
    soit cell =
      Cop(Cload Word,[Cop(Cadda,[str;Cconst_int(Arch.size_int*ind)])]) dans
    Clet(id, cell, body)

  soit mk_let_size id str body =
    soit size = I.string_block_length str dans
    Clet(id, size, body)

  soit mk_cmp_gen cmp_op id nat ifso ifnot =
    soit test = Cop (Ccmpi cmp_op, [ Cvar id; Cconst_natpointer nat ]) dans
    Cifthenelse (test, ifso, ifnot)

  soit mk_lt = mk_cmp_gen Clt
  soit mk_eq = mk_cmp_gen Ceq

  module IntArg =
    struct
      type t = int
      soit compare (x:int) (y:int) =
        si x < y alors -1
        sinon si x > y alors 1
        sinon 0
    fin

  soit interval m0 n =
    soit rec do_rec m =
      si m >= n alors []
      sinon m::do_rec (m+1) dans
    do_rec m0


(*****************************************************)
(* Compile strings to a lists of words [native ints] *)
(*****************************************************)

  soit pat_of_string str =
    soit len = String.length str dans
    soit n = len / Arch.size_addr + 1 dans
    soit get_byte i =
      si i < len alors int_of_char str.[i]
      sinon si i < n * Arch.size_addr - 1 alors 0
      sinon n * Arch.size_addr - 1 - len dans
    soit mk_word ind =
      soit w = ref 0n dans
      soit imin = ind * Arch.size_addr
      et imax = (ind + 1) * Arch.size_addr - 1 dans
      si Arch.big_endian alors
        pour i = imin à imax faire
          w := Nativeint.logor (Nativeint.shift_left !w 8)
              (Nativeint.of_int (get_byte i));
        fait
      sinon
        pour i = imax descendant_jusqu'a imin faire
          w := Nativeint.logor (Nativeint.shift_left !w 8)
              (Nativeint.of_int (get_byte i));
        fait;
      !w dans
    soit rec mk_words ind  =
      si ind >= n alors []
      sinon mk_word ind::mk_words (ind+1) dans
    mk_words 0

(*****************************)
(* Discriminating heuristics *)
(*****************************)

  module IntSet = Set.Make(IntArg)
  module NativeSet = Set.Make(Nativeint)

  soit rec add_one sets ps = filtre sets,ps avec
  | [],[] -> []
  | set::sets,p::ps ->
      soit sets = add_one sets ps dans
      NativeSet.add p set::sets
  | _,_ -> affirme faux

  soit count_arities cases = filtre cases avec
  | [] -> affirme faux
  | (ps,_)::_ ->
      soit sets =
        List.fold_left
          (fonc sets (ps,_) -> add_one sets ps)
          (List.map (fonc _ -> NativeSet.empty) ps) cases dans
      List.map NativeSet.cardinal sets

  soit count_arities_first cases =
    soit set =
      List.fold_left
        (fonc set case -> filtre case avec
        | (p::_,_) -> NativeSet.add p set
        | _ -> affirme faux)
        NativeSet.empty cases dans
    NativeSet.cardinal set

  soit count_arities_length cases =
    soit set =
      List.fold_left
        (fonc set (ps,_) -> IntSet.add (List.length ps) set)
        IntSet.empty cases dans
    IntSet.cardinal set
      
  soit best_col =
    soit rec do_rec kbest best k = fonction
      | [] -> kbest
      | x::xs ->
          si x < best alors
            do_rec k x (k+1) xs
          sinon
            do_rec kbest best (k+1) xs dans
    soit smallest = do_rec (-1) max_int 0 dans
    fonc cases ->
      soit ars = count_arities cases dans
      smallest ars

  soit swap_list =
    soit rec do_rec k xs = filtre xs avec
    | [] -> affirme faux
    | x::xs ->
        si k <= 0 alors [],x,xs
        sinon
          soit xs,mid,ys = do_rec (k-1) xs dans
          x::xs,mid,ys dans
    fonc k xs ->
      soit xs,x,ys = do_rec  k xs dans
      x::xs @ ys

  soit swap k idxs cases =
    si k = 0 alors idxs,cases
    sinon
      soit idxs = swap_list k idxs
      et cases =
        List.map
          (fonc (ps,act) -> swap_list k ps,act)
          cases dans
      si dbg alors début
        pp_match stderr "SWAP" idxs cases
      fin ;
      idxs,cases

  soit best_first idxs cases = filtre idxs avec
  | []|[_] -> idxs,cases (* optimisation: one column only *)
  | _ ->
      soit k = best_col cases dans
      swap k idxs cases

(************************************)
(* Divide according to first column *)
(************************************)

  module Divide(O:Set.OrderedType) = struct

    module OMap = Map.Make(O)

    soit do_find key env =
      essaie OMap.find key env
      avec Not_found -> affirme faux

          
    soit divide cases =
      soit env =
        List.fold_left
          (fonc env (p,psact) ->
            soit old =
              essaie OMap.find p env
              avec Not_found -> [] dans
            OMap.add p ((psact)::old) env)
          OMap.empty cases dans
      soit r =  OMap.fold (fonc key v k -> (key,v)::k) env [] dans
      List.rev r (* Now sorted *)
  fin

(***************)
(* Compilation *)
(***************)

(* Group by cell *)

    module DivideNative = Divide(Nativeint)

    soit by_cell cases =
      DivideNative.divide
        (List.map
           (fonc case -> filtre case avec
           | (p::ps),act -> p,(ps,act)
           | [],_ -> affirme faux)
           cases)

(* Split into two halves *)

    soit rec do_split idx env = filtre env avec
    | [] -> affirme faux
    | (midkey,_ tel x)::rem ->
        si idx <= 0 alors [],midkey,env
        sinon
          soit lt,midkey,ge = do_split (idx-1) rem dans
          x::lt,midkey,ge

    soit split_env len env = do_split (len/2) env

(* Switch according to one cell *)

(*
  Emit the switch, here as a comparison tree.
  Argument compile_rec is to be called to compile the rest of patterns,
  as match_on_cell can be called in two different contexts :
  from do_compile_pats and top_compile below.
 *)
    soit match_oncell compile_rec str default idx env =
      soit id = gen_cell_id () dans
      soit rec comp_rec env =
        soit len = List.length env dans
        si len <= 3 alors
          List.fold_right
            (fonc (key,cases) ifnot ->
              mk_eq id key
                (compile_rec str default cases)
              ifnot)
            env default
        sinon
          soit lt,midkey,ge = split_env len env dans
          mk_lt id midkey (comp_rec lt) (comp_rec ge) dans
      mk_let_cell id str idx (comp_rec env)
        

(*
  Recursive 'list of cells' compile function:
  - choose the matched cell and switch on it
  - notice: patterns (and idx) all have the same length
 *)

    soit rec do_compile_pats idxs str default cases =
      si dbg alors début
        pp_match stderr "COMPILE" idxs cases
      fin ;
      filtre idxs avec
      | [] ->
          début filtre cases avec
          | [] -> default
          | (_,e)::_ -> e
          fin
      | _::_ ->
          soit idxs,cases = best_first idxs cases dans
          début filtre idxs avec
          | [] -> affirme faux
          | idx::idxs ->
              match_oncell
                (do_compile_pats idxs) str default idx (by_cell cases)
          fin


(* Group by size *)
            
    module DivideInt = Divide(IntArg)


    soit by_size cases =
      DivideInt.divide
        (List.map
           (fonc (ps,_ tel case) -> List.length ps,case)
           cases)
(*
  Switch according to pattern size
  Argument from_ind is the starting index, it can be zero
  or one (when the swicth on the cell 0 has already been performed.
  In that latter case pattern len is string length-1 and is corrected.
 *)

    soit compile_by_size from_ind str default cases =
      soit size_cases =
        List.map
          (fonc (len,cases) ->
            soit len = len+from_ind dans
            soit act =
              do_compile_pats
                (interval from_ind len)
                str default  cases dans
            (len,act))
          (by_size cases) dans
      soit id = gen_size_id () dans
      soit switch = I.transl_switch (Cvar id) 1 max_int size_cases default dans
      mk_let_size id str switch

(*
  Compilation entry point: we choose to switch
  either on size or on first cell, using the
  'least discriminant' heuristics.  
 *)      
    soit top_compile str default cases =
      soit a_len = count_arities_length cases
      et a_fst = count_arities_first cases dans
      si a_len <= a_fst alors début
        si dbg alors pp_cases stderr "SIZE" cases ;
        compile_by_size 0 str default cases
      fin sinon début
        si dbg alors pp_cases stderr "FIRST COL" cases ;
        soit compile_size_rest str default cases =
          compile_by_size 1 str default cases dans
        match_oncell compile_size_rest str default 0 (by_cell cases)
      fin

(* Module entry point *)

    soit catch arg k = filtre arg avec
    | Cexit (e,[]) ->  k arg
    | _ ->
        soit e =  next_raise_count () dans
        Ccatch (e,[],k (Cexit (e,[])),arg)

    soit compile str default cases =
      soit cases =
        List.rev_map
          (fonc (s,act) -> pat_of_string s,act)
          cases dans
      catch default (fonc default -> top_compile str default cases)

  fin
