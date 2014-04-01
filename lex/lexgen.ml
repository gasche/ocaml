(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal,                            *)
(*            Luc Maranget, projet Moscova,                            *)
(*                  INRIA Rocquencourt                                 *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Compiling a lexer definition *)

ouvre Syntax
ouvre Printf

exception Memory_overflow

(* Deep abstract syntax for regular expressions *)

type ident = string *  Syntax.location

type tag_info = {id : string ; start : bool ; action : int}

type regexp =
    Empty
  | Chars de int * bool
  | Action de int
  | Tag de tag_info
  | Seq de regexp * regexp
  | Alt de regexp * regexp
  | Star de regexp

type tag_base = Start | End | Mem de int
type tag_addr = Sum de (tag_base * int)
type ident_info =
  | Ident_string de bool * tag_addr * tag_addr
  | Ident_char de bool * tag_addr
type t_env = (ident * ident_info) list

type ('args,'action) lexer_entry =
  { lex_name: string;
    lex_regexp: regexp;
    lex_mem_tags: int ;
    lex_actions: (int *  t_env * 'action) list }


type automata =
    Perform de int * tag_action list
  | Shift de automata_trans * (automata_move * memory_action list) array

et automata_trans =
    No_remember
  | Remember de int * tag_action list

et automata_move =
    Backtrack
  | Goto de int

et memory_action =
  | Copy de int * int
  | Set de int

et tag_action = SetTag de int * int | EraseTag de int

(* Representation of entry points *)

type ('args,'action) automata_entry =
  { auto_name: string;
    auto_args: 'args ;
    auto_mem_size : int ;
    auto_initial_state: int * memory_action list;
    auto_actions: (int * t_env * 'action) list }


(* A lot of sets and map structures *)

module Ints =
  Set.Make(struct type t = int soit compare (x:t) y = compare x y fin)

soit id_compare (id1,_) (id2,_) = String.compare id1 id2

soit tag_compare t1 t2 = Pervasives.compare t1 t2

module Tags = Set.Make(struct type t = tag_info soit compare = tag_compare fin)

module TagMap =
  Map.Make (struct type t = tag_info soit compare = tag_compare fin)

module IdSet =
  Set.Make (struct type t = ident soit compare = id_compare fin)

module IdMap =
  Map.Make (struct type t =  ident soit compare = id_compare fin)

(*********************)
(* Variable cleaning *)
(*********************)

(* Silently eliminate nested variables *)

soit rec do_remove_nested to_remove = fonction
  | Bind (e,x) ->
      si IdSet.mem x to_remove alors
        do_remove_nested to_remove e
      sinon
        Bind (do_remove_nested (IdSet.add x to_remove) e, x)
  | Epsilon|Eof|Characters _ tel e -> e
  | Sequence (e1, e2) ->
      Sequence
        (do_remove_nested to_remove  e1, do_remove_nested to_remove  e2)
  | Alternative (e1, e2) ->
      Alternative
        (do_remove_nested to_remove  e1, do_remove_nested to_remove  e2)
  | Repetition e ->
      Repetition (do_remove_nested to_remove  e)

soit remove_nested_as e = do_remove_nested IdSet.empty e

(*********************)
(* Variable analysis *)
(*********************)

(*
  Optional variables.
   A variable is optional when matching of regexp does not
   implies it binds.
     The typical case is:
       ("" | 'a' as x) -> optional
       ("" as x | 'a' as x) -> non-optional
*)

soit stringset_delta s1 s2 =
  IdSet.union
    (IdSet.diff s1 s2)
    (IdSet.diff s2 s1)

soit rec find_all_vars = fonction
  | Characters _|Epsilon|Eof ->
      IdSet.empty
  | Bind (e,x) ->
      IdSet.add x (find_all_vars e)
  | Sequence (e1,e2)|Alternative (e1,e2) ->
      IdSet.union (find_all_vars e1) (find_all_vars e2)
  | Repetition e -> find_all_vars e


soit rec do_find_opt = fonction
  | Characters _|Epsilon|Eof -> IdSet.empty, IdSet.empty
  | Bind (e,x) ->
      soit opt,all = do_find_opt e dans
      opt, IdSet.add x all
  | Sequence (e1,e2) ->
      soit opt1,all1 = do_find_opt e1
      et opt2,all2 = do_find_opt e2 dans
      IdSet.union opt1 opt2, IdSet.union all1 all2
  | Alternative (e1,e2) ->
      soit opt1,all1 = do_find_opt e1
      et opt2,all2 = do_find_opt e2 dans
      IdSet.union
        (IdSet.union opt1 opt2)
        (stringset_delta all1 all2),
      IdSet.union all1 all2
  | Repetition e  ->
      soit r = find_all_vars e dans
      r,r

soit find_optional e =
  soit r,_ = do_find_opt e dans r

(*
   Double variables
   A variable is double when it can be bound more than once
   in a single matching
     The typical case is:
       (e1 as x) (e2 as x)

*)

soit rec do_find_double = fonction
  | Characters _|Epsilon|Eof -> IdSet.empty, IdSet.empty
  | Bind (e,x) ->
      soit dbl,all = do_find_double e dans
      (si IdSet.mem x all alors
        IdSet.add x dbl
      sinon
        dbl),
      IdSet.add x all
  | Sequence (e1,e2) ->
      soit dbl1, all1 = do_find_double e1
      et dbl2, all2 = do_find_double e2 dans
      IdSet.union
        (IdSet.inter all1 all2)
        (IdSet.union dbl1 dbl2),
      IdSet.union all1 all2
  | Alternative (e1,e2) ->
      soit dbl1, all1 = do_find_double e1
      et dbl2, all2 = do_find_double e2 dans
      IdSet.union dbl1 dbl2,
      IdSet.union all1 all2
  | Repetition e ->
      soit r = find_all_vars e dans
      r,r

soit find_double e = do_find_double e

(*
   Type of variables:
    A variable is bound to a char when all its occurences
    bind a pattern of length 1.
     The typical case is:
       (_ as x) -> char
*)

soit add_some x = fonction
  | Some i -> Some (x+i)
  | None   -> None

soit add_some_some x y = filtre x,y avec
| Some i, Some j -> Some (i+j)
| _,_            -> None

soit rec do_find_chars sz = fonction
  | Epsilon|Eof    -> IdSet.empty, IdSet.empty, sz
  | Characters _ -> IdSet.empty, IdSet.empty, add_some 1 sz
  | Bind (e,x)   ->
      soit c,s,e_sz = do_find_chars (Some 0) e dans
      début filtre e_sz  avec
      | Some 1 ->
          IdSet.add x c,s,add_some 1 sz
      | _ ->
          c, IdSet.add x s, add_some_some sz e_sz
      fin
  | Sequence (e1,e2) ->
      soit c1,s1,sz1 = do_find_chars sz e1 dans
      soit c2,s2,sz2 = do_find_chars sz1 e2 dans
      IdSet.union c1 c2,
      IdSet.union s1 s2,
      sz2
  | Alternative (e1,e2) ->
      soit c1,s1,sz1 = do_find_chars sz e1
      et c2,s2,sz2 = do_find_chars sz e2 dans
      IdSet.union c1 c2,
      IdSet.union s1 s2,
      (si sz1 = sz2 alors sz1 sinon None)
  | Repetition e -> do_find_chars None e



soit find_chars e =
  soit c,s,_ = do_find_chars (Some 0) e dans
  IdSet.diff c s

(*******************************)
(* From shallow to deep syntax *)
(*******************************)

soit chars = ref ([] : Cset.t list)
soit chars_count = ref 0


soit rec encode_regexp char_vars act = fonction
    Epsilon -> Empty
  | Characters cl ->
      soit n = !chars_count dans
      chars := cl :: !chars;
      incr chars_count;
      Chars(n,faux)
  | Eof ->
      soit n = !chars_count dans
      chars := Cset.eof :: !chars;
      incr chars_count;
      Chars(n,vrai)
  | Sequence(r1,r2) ->
      soit r1 = encode_regexp char_vars act r1 dans
      soit r2 = encode_regexp char_vars act r2 dans
      Seq (r1, r2)
  | Alternative(r1,r2) ->
      soit r1 = encode_regexp char_vars act r1 dans
      soit r2 = encode_regexp char_vars act r2 dans
      Alt(r1, r2)
  | Repetition r ->
      soit r = encode_regexp char_vars act r dans
      Star r
  | Bind (r,((name,_) tel x)) ->
      soit r = encode_regexp char_vars act r dans
      si IdSet.mem x char_vars alors
        Seq (Tag {id=name ; start=vrai ; action=act},r)
      sinon
        Seq (Tag {id=name ; start=vrai ; action=act},
          Seq (r, Tag {id=name ; start=faux ; action=act}))


(* Optimisation,
    Static optimization :
      Replace tags by offsets relative to the beginning
      or end of matched string.
    Dynamic optimization:
      Replace some non-optional, non-double tags by offsets w.r.t
      a previous similar tag.
*)

soit incr_pos = fonction
  | None   -> None
  | Some i -> Some (i+1)

soit decr_pos = fonction
  | None -> None
  | Some i -> Some (i-1)


soit opt = vrai

soit mk_seq r1 r2 = filtre r1,r2  avec
| Empty,_ -> r2
| _,Empty -> r1
| _,_     -> Seq (r1,r2)

soit add_pos p i = filtre p avec
| Some (Sum (a,n)) -> Some (Sum (a,n+i))
| None -> None

soit mem_name name id_set =
  IdSet.exists (fonc (id_name,_) -> name = id_name) id_set

soit opt_regexp all_vars char_vars optional_vars double_vars r =

(* From removed tags to their addresses *)
  soit env = Hashtbl.create 17 dans

(* First static optimizations, from start position *)
  soit rec size_forward pos = fonction
    | Empty|Chars (_,vrai)|Tag _ -> Some pos
    | Chars (_,faux) -> Some (pos+1)
    | Seq (r1,r2) ->
        début filtre size_forward pos r1 avec
        | None -> None
        | Some pos  -> size_forward pos r2
        fin
    | Alt (r1,r2) ->
        soit pos1 = size_forward pos r1
        et pos2 = size_forward pos r2 dans
        si pos1=pos2 alors pos1 sinon None
    | Star _ -> None
    | Action _ -> affirme faux dans

  soit rec simple_forward pos r = filtre r avec
    | Tag n ->
        si mem_name n.id double_vars alors
          r,Some pos
        sinon début
          Hashtbl.add env (n.id,n.start) (Sum (Start, pos)) ;
          Empty,Some pos
        fin
    | Empty -> r, Some pos
    | Chars (_,is_eof) ->
        r,Some (si is_eof alors  pos sinon pos+1)
    | Seq (r1,r2) ->
        soit r1,pos = simple_forward pos r1 dans
        début filtre pos avec
        | None -> mk_seq r1 r2,None
        | Some pos ->
            soit r2,pos = simple_forward pos r2 dans
            mk_seq r1 r2,pos
        fin
    | Alt (r1,r2) ->
        soit pos1 = size_forward pos r1
        et pos2 = size_forward pos r2 dans
        r,(si pos1=pos2 alors pos1 sinon None)
    | Star _ -> r,None
    | Action _ -> affirme faux dans

(* Then static optimizations, from end position *)
  soit rec size_backward pos = fonction
    | Empty|Chars (_,vrai)|Tag _ -> Some pos
    | Chars (_,faux) -> Some (pos-1)
    | Seq (r1,r2) ->
        début filtre size_backward pos r2 avec
        | None -> None
        | Some pos  -> size_backward pos r1
        fin
    | Alt (r1,r2) ->
        soit pos1 = size_backward pos r1
        et pos2 = size_backward pos r2 dans
        si pos1=pos2 alors pos1 sinon None
    | Star _ -> None
    | Action _ -> affirme faux dans


  soit rec simple_backward pos r = filtre r avec
    | Tag n ->
        si mem_name n.id double_vars alors
          r,Some pos
        sinon début
          Hashtbl.add env (n.id,n.start) (Sum (End, pos)) ;
          Empty,Some pos
        fin
    | Empty -> r,Some pos
    | Chars (_,is_eof) ->
        r,Some (si is_eof alors pos sinon pos-1)
    | Seq (r1,r2) ->
        soit r2,pos = simple_backward pos r2 dans
        début filtre pos avec
        | None -> mk_seq r1 r2,None
        | Some pos ->
            soit r1,pos = simple_backward pos r1 dans
            mk_seq r1 r2,pos
        fin
    | Alt (r1,r2) ->
        soit pos1 = size_backward pos r1
        et pos2 = size_backward pos r2 dans
        r,(si pos1=pos2 alors pos1 sinon None)
    | Star _ -> r,None
    | Action _ -> affirme faux dans

  soit r =
    si opt alors
      soit r,_ = simple_forward 0 r dans
      soit r,_ = simple_backward 0 r dans
      r
    sinon
      r dans

  soit loc_count = ref 0 dans
  soit get_tag_addr t =
    essaie
     Hashtbl.find env t
    avec
    | Not_found ->
        soit n = !loc_count dans
        incr loc_count ;
        Hashtbl.add env t (Sum (Mem n,0)) ;
        Sum (Mem n,0) dans

  soit rec alloc_exp pos r = filtre r avec
    | Tag n ->
        si mem_name n.id double_vars alors
          r,pos
        sinon début filtre pos avec
        | Some a ->
            Hashtbl.add env (n.id,n.start) a ;
            Empty,pos
        | None ->
            soit a = get_tag_addr (n.id,n.start) dans
            r,Some a
        fin

    | Empty -> r,pos
    | Chars (_,is_eof) -> r,(si is_eof alors pos sinon add_pos pos 1)
    | Seq (r1,r2) ->
        soit r1,pos = alloc_exp pos r1 dans
        soit r2,pos = alloc_exp pos r2 dans
        mk_seq r1 r2,pos
    | Alt (_,_) ->
        soit off = size_forward 0 r dans
        début filtre off avec
        | Some i -> r,add_pos pos i
        | None -> r,None
        fin
    | Star _ -> r,None
    | Action _ -> affirme faux dans

  soit r,_ = alloc_exp None r dans
  soit m =
    IdSet.fold
      (fonc ((name,_) tel x) r ->

        soit v =
          si IdSet.mem x char_vars alors
            Ident_char
              (IdSet.mem x optional_vars, get_tag_addr (name,vrai))
          sinon
            Ident_string
              (IdSet.mem x optional_vars,
               get_tag_addr (name,vrai),
               get_tag_addr (name,faux)) dans
        (x,v)::r)
      all_vars [] dans
  m,r, !loc_count



soit encode_casedef casedef =
  soit r =
    List.fold_left
      (fonc (reg,actions,count,ntags) (expr, act) ->
        soit expr = remove_nested_as expr dans
        soit char_vars = find_chars expr dans
        soit r = encode_regexp char_vars count expr
        et opt_vars = find_optional expr
        et double_vars,all_vars = find_double expr dans
        soit m,r,loc_ntags =
          opt_regexp all_vars char_vars opt_vars double_vars r dans
        Alt(reg, Seq(r, Action count)),
        (count, m ,act) :: actions,
        (succ count),
        max loc_ntags ntags)
      (Empty, [], 0, 0)
      casedef dans
  r

soit encode_lexdef def =
  chars := [];
  chars_count := 0;
  soit entry_list =
    List.map
      (fonc {name=entry_name; args=args; shortest=shortest; clauses=casedef} ->
        soit (re,actions,_,ntags) = encode_casedef casedef dans
        { lex_name = entry_name;
          lex_regexp = re;
          lex_mem_tags = ntags ;
          lex_actions = List.rev actions },args,shortest)
      def dans
  soit chr = Array.of_list (List.rev !chars) dans
  chars := [];
  (chr, entry_list)

(* To generate directly a NFA from a regular expression.
     Confer Aho-Sethi-Ullman, dragon book, chap. 3
   Extension to tagged automata.
     Confer
       Ville Larikari
       'NFAs with Tagged Transitions, their Conversion to Deterministic
        Automata and Application to Regular Expressions'.
       Symposium on String Processing and Information Retrieval (SPIRE 2000),
     http://kouli.iki.fi/~vlaurika/spire2000-tnfa.ps
(See also)
     http://kouli.iki.fi/~vlaurika/regex-submatch.ps.gz
*)

type t_transition =
    OnChars de int
  | ToAction de int

type transition = t_transition * Tags.t

soit trans_compare (t1,tags1) (t2,tags2) =
  filtre Pervasives.compare  t1 t2 avec
  | 0 -> Tags.compare tags1 tags2
  | r -> r


module TransSet =
  Set.Make(struct type t = transition soit compare = trans_compare fin)

soit rec nullable = fonction
  | Empty|Tag _ -> vrai
  | Chars (_,_)|Action _ -> faux
  | Seq(r1,r2) -> nullable r1 && nullable r2
  | Alt(r1,r2) -> nullable r1 || nullable r2
  | Star r     -> vrai

soit rec emptymatch = fonction
  | Empty | Chars (_,_) | Action _ -> Tags.empty
  | Tag t       -> Tags.add t Tags.empty
  | Seq (r1,r2) -> Tags.union (emptymatch r1) (emptymatch r2)
  | Alt(r1,r2)  ->
      si nullable r1 alors
        emptymatch r1
      sinon
        emptymatch r2
  | Star r ->
      si nullable r alors
        emptymatch r
      sinon
        Tags.empty

soit addtags transs tags =
  TransSet.fold
    (fonc (t,tags_t) r -> TransSet.add (t, Tags.union tags tags_t) r)
    transs TransSet.empty


soit rec firstpos = fonction
    Empty|Tag _ -> TransSet.empty
  | Chars (pos,_) -> TransSet.add (OnChars pos,Tags.empty) TransSet.empty
  | Action act -> TransSet.add (ToAction act,Tags.empty) TransSet.empty
  | Seq(r1,r2) ->
      si nullable r1 alors
        TransSet.union (firstpos r1) (addtags (firstpos r2) (emptymatch r1))
      sinon
        firstpos r1
  | Alt(r1,r2) -> TransSet.union (firstpos r1) (firstpos r2)
  | Star r     -> firstpos r


(* Berry-sethi followpos *)
soit followpos size entry_list =
  soit v = Array.create size TransSet.empty dans
  soit rec fill s = fonction
    | Empty|Action _|Tag _ -> ()
    | Chars (n,_) -> v.(n) <- s
    | Alt (r1,r2) ->
        fill s r1 ; fill s r2
    | Seq (r1,r2) ->
        fill
          (si nullable r2 alors
            TransSet.union (firstpos r2) (addtags s (emptymatch r2))
          sinon
            (firstpos r2))
          r1 ;
        fill s r2
    | Star r ->
        fill (TransSet.union (firstpos r) s) r dans
  List.iter (fonc (entry,_,_) -> fill TransSet.empty entry.lex_regexp)
            entry_list;
  v

(************************)
(* The algorithm itself *)
(************************)

soit no_action = max_int

module StateSet =
  Set.Make (struct type t = t_transition soit compare = Pervasives.compare fin)


module MemMap =
  Map.Make (struct type t = int
                   soit compare (x:t) y = Pervasives.compare x y fin)

type 'a dfa_state =
  {final : int * ('a * int TagMap.t) ;
   others : ('a * int TagMap.t) MemMap.t}


soit dtag oc t =
  fprintf oc "%s<%s>" t.id (si t.start alors "s" sinon "e")

soit dmem_map dp ds m =
  MemMap.iter
    (fonc k x ->
      eprintf "%d -> " k ; dp x ; ds ())
    m

et dtag_map dp ds m =
  TagMap.iter
    (fonc t x ->
      dtag stderr t ; eprintf " -> " ; dp x ; ds ())
    m

soit dstate {final=(act,(_,m)) ; others=o} =
  si act <> no_action alors début
    eprintf "final=%d " act ;
    dtag_map (fonc x -> eprintf "%d" x) (fonc () -> prerr_string " ,") m ;
    prerr_endline ""
  fin ;
  dmem_map
    (fonc (_,m) ->
      dtag_map (fonc x -> eprintf "%d" x) (fonc () -> prerr_string " ,") m)
    (fonc () -> prerr_endline "")
    o


soit dfa_state_empty =
  {final=(no_action, (max_int,TagMap.empty)) ;
   others=MemMap.empty}

et dfa_state_is_empty {final=(act,_) ; others=o} =
  act = no_action &&
  o = MemMap.empty


(* A key is an abstraction on a dfa state,
   two states with the same key can be made the same by
   copying some memory cells into others *)


module StateSetSet =
  Set.Make (struct type t = StateSet.t soit compare = StateSet.compare fin)

type t_equiv = {tag:tag_info ; equiv:StateSetSet.t}

module MemKey =
  Set.Make
   (struct
     type t = t_equiv

     soit compare e1 e2 = filtre Pervasives.compare e1.tag e2.tag avec
     | 0 -> StateSetSet.compare e1.equiv e2.equiv
     | r -> r
   fin)

type dfa_key = {kstate : StateSet.t ; kmem : MemKey.t}

(* Map a state to its key *)
soit env_to_class m =
  soit env1 =
    MemMap.fold
      (fonc _ (tag,s) r ->
        essaie
          soit ss = TagMap.find tag r dans
          soit r = TagMap.remove tag r dans
          TagMap.add tag (StateSetSet.add s ss) r
        avec
        | Not_found ->
            TagMap.add tag (StateSetSet.add s StateSetSet.empty) r)
      m TagMap.empty dans
  TagMap.fold
    (fonc tag ss r -> MemKey.add {tag=tag ; equiv=ss} r)
    env1 MemKey.empty


(* trans is nfa_state, m is associated memory map *)
soit inverse_mem_map trans m r =
  TagMap.fold
    (fonc tag addr r ->
      essaie
        soit otag,s = MemMap.find addr r dans
        affirme (tag = otag) ;
        soit r = MemMap.remove addr r dans
        MemMap.add addr (tag,StateSet.add trans s) r
      avec
      | Not_found ->
          MemMap.add addr (tag,StateSet.add trans StateSet.empty) r)
    m r

soit inverse_mem_map_other n (_,m) r = inverse_mem_map (OnChars n) m r

soit get_key {final=(act,(_,m_act)) ; others=o} =
  soit env =
    MemMap.fold inverse_mem_map_other
      o
      (si act = no_action alors MemMap.empty
      sinon inverse_mem_map (ToAction act) m_act MemMap.empty) dans
  soit state_key =
    MemMap.fold (fonc n _ r -> StateSet.add (OnChars n) r) o
      (si act=no_action alors StateSet.empty
      sinon StateSet.add (ToAction act) StateSet.empty) dans
  soit mem_key = env_to_class  env dans
  {kstate = state_key ; kmem = mem_key}


soit key_compare k1 k2 = filtre StateSet.compare k1.kstate k2.kstate avec
| 0 -> MemKey.compare k1.kmem k2.kmem
| r -> r

(* Association dfa_state -> state_num *)

module StateMap =
  Map.Make(struct type t = dfa_key soit compare = key_compare fin)

soit state_map = ref (StateMap.empty : int StateMap.t)
soit todo = Stack.create()
soit next_state_num = ref 0
soit next_mem_cell = ref 0
soit temp_pending = ref faux
soit tag_cells = Hashtbl.create 17
soit state_table = Table.create dfa_state_empty


(* Initial reset of state *)
soit reset_state () =
  Stack.clear todo;
  next_state_num := 0 ;
  soit _ = Table.trim state_table dans
  ()

(* Reset state before processing a given automata.
   We clear both the memory mapping and
   the state mapping, as state sharing beetween different
   automata may lead to incorret estimation of the cell memory size
   BUG ID 0004517 *)


soit reset_state_partial ntags =
  next_mem_cell := ntags ;
  Hashtbl.clear tag_cells ;
  temp_pending := faux ;
  state_map := StateMap.empty

soit do_alloc_temp () =
  temp_pending := vrai ;
  soit n = !next_mem_cell dans
  n

soit do_alloc_cell used t =
  soit available =
    essaie Hashtbl.find tag_cells t avec Not_found -> Ints.empty dans
  essaie
    Ints.choose (Ints.diff available used)
  avec
  | Not_found ->
      temp_pending := faux ;
      soit n = !next_mem_cell dans
      si n >= 255 alors raise Memory_overflow ;
      Hashtbl.replace tag_cells t (Ints.add n available) ;
      incr next_mem_cell ;
      n

soit is_old_addr a = a >= 0
et is_new_addr a = a < 0

soit old_in_map m r =
  TagMap.fold
    (fonc _ addr r ->
      si is_old_addr addr alors
        Ints.add addr r
      sinon
        r)
    m r

soit alloc_map used m mvs =
  TagMap.fold
    (fonc tag a (r,mvs) ->
      soit a,mvs =
        si is_new_addr a alors
          soit a = do_alloc_cell used tag dans
          a,Ints.add a mvs
        sinon a,mvs dans
      TagMap.add tag a r,mvs)
    m (TagMap.empty,mvs)

soit create_new_state {final=(act,(_,m_act)) ; others=o} =
  soit used =
    MemMap.fold (fonc _ (_,m) r -> old_in_map m r)
      o (old_in_map m_act Ints.empty) dans

  soit new_m_act,mvs  = alloc_map used m_act Ints.empty dans
  soit new_o,mvs =
    MemMap.fold (fonc k (x,m) (r,mvs) ->
      soit m,mvs = alloc_map used m mvs dans
      MemMap.add k (x,m) r,mvs)
      o (MemMap.empty,mvs) dans
  {final=(act,(0,new_m_act)) ; others=new_o},
  Ints.fold (fonc x r -> Set x::r) mvs []

type new_addr_gen = {modifiable count : int ; modifiable env : int TagMap.t}

soit create_new_addr_gen () = {count = -1 ; env = TagMap.empty}

soit alloc_new_addr tag r =
  essaie
    TagMap.find tag r.env
  avec
  | Not_found ->
      soit a = r.count dans
      r.count <- a-1 ;
      r.env <- TagMap.add tag a r.env ;
      a


soit create_mem_map tags gen =
  Tags.fold
    (fonc tag r -> TagMap.add tag (alloc_new_addr tag gen) r)
    tags TagMap.empty

soit create_init_state pos =
  soit gen = create_new_addr_gen () dans
  soit st =
    TransSet.fold
      (fonc (t,tags) st ->
        filtre t avec
        | ToAction n ->
            soit on,otags = st.final dans
            si n < on alors
              {st avec final = (n, (0,create_mem_map tags gen))}
            sinon
              st
        | OnChars n ->
            essaie
              soit _ = MemMap.find n st.others dans affirme faux
            avec
            | Not_found ->
                {st avec others =
                  MemMap.add n (0,create_mem_map tags gen) st.others})
      pos dfa_state_empty dans
  st


soit get_map t st = filtre t avec
| ToAction _ -> soit _,(_,m) = st.final dans m
| OnChars n  ->
    soit (_,m) = MemMap.find n st.others dans
    m

soit dest = fonction | Copy (d,_) | Set d  -> d
et orig = fonction | Copy (_,o) -> o | Set _ -> -1

soit pmv oc mv = fprintf oc "%d <- %d" (dest mv) (orig mv)
soit pmvs oc mvs =
  List.iter (fonc mv -> fprintf oc "%a " pmv  mv) mvs ;
  output_char oc '\n' ; flush oc


(* Topological sort << a la louche >> *)
soit sort_mvs mvs =
  soit rec do_rec r mvs = filtre mvs avec
  | [] -> r
  | _  ->
      soit dests =
        List.fold_left
          (fonc r mv -> Ints.add (dest mv) r)
          Ints.empty mvs dans
      soit rem,here =
        List.partition
          (fonc mv -> Ints.mem (orig mv) dests)
          mvs dans
      filtre here avec
      | [] ->
          début filtre rem avec
          | Copy (d,_)::_ ->
              soit d' = do_alloc_temp () dans
              Copy (d',d)::
              do_rec r
                (List.map
                   (fonc mv ->
                     si orig mv = d alors
                       Copy (dest mv,d')
                     sinon
                       mv)
                   rem)
          | _ -> affirme faux
          fin
      | _  -> do_rec (here@r) rem  dans
  do_rec [] mvs

soit move_to mem_key src tgt =
  soit mvs =
    MemKey.fold
      (fonc {tag=tag ; equiv=m} r ->
        StateSetSet.fold
          (fonc s r ->
            essaie
              soit t = StateSet.choose s  dans
              soit src = TagMap.find tag (get_map t src)
              et tgt = TagMap.find tag (get_map t tgt) dans
              si src <> tgt alors début
                si is_new_addr src alors
                  Set tgt::r
                sinon
                  Copy (tgt, src)::r
              fin sinon
                r
            avec
            | Not_found -> affirme faux)
          m r)
      mem_key [] dans
(* Moves are topologically sorted *)
  sort_mvs mvs


soit get_state st =
  soit key = get_key st dans
  essaie
    soit num = StateMap.find key !state_map dans
    num,move_to key.kmem st (Table.get state_table num)
  avec Not_found ->
    soit num = !next_state_num dans
    incr next_state_num;
    soit st,mvs = create_new_state st dans
    Table.emit state_table st ;
    state_map := StateMap.add key num !state_map;
    Stack.push (st, num) todo;
    num,mvs

soit map_on_all_states f old_res =
  soit res = ref old_res dans
  début essaie
    pendant_que vrai faire
      soit (st, i) = Stack.pop todo dans
      soit r = f st dans
      res := (r, i) :: !res
    fait
  avec Stack.Empty -> ()
  fin;
  !res

soit goto_state st =
  si
    dfa_state_is_empty st
  alors
    Backtrack,[]
  sinon
    soit n,moves = get_state st dans
    Goto n,moves

(****************************)
(* compute reachable states *)
(****************************)

soit add_tags_to_map gen tags m =
  Tags.fold
    (fonc tag m ->
      soit m = TagMap.remove tag m dans
      TagMap.add tag (alloc_new_addr tag gen) m)
    tags m

soit apply_transition gen r pri m = fonction
  | ToAction n,tags ->
      soit on,(opri,_) = r.final dans
      si n < on || (on=n && pri < opri) alors
        soit m = add_tags_to_map gen tags m dans
        {r avec final=n,(pri,m)}
      sinon r
  |  OnChars n,tags ->
      essaie
        soit (opri,_) = MemMap.find n r.others dans
        si pri < opri alors
          soit m = add_tags_to_map gen tags m dans
          {r avec others=MemMap.add n (pri,m) (MemMap.remove n r.others)}
        sinon
          r
      avec
      | Not_found ->
          soit m = add_tags_to_map gen tags m dans
          {r avec others=MemMap.add n (pri,m) r.others}

(* add transitions ts to new state r
   transitions in ts start from state pri and memory map m
*)
soit apply_transitions gen r pri m ts =
  TransSet.fold
    (fonc t r -> apply_transition gen r pri m t)
    ts r


(* For a given nfa_state pos, refine char partition *)
soit rec split_env gen follow pos m s = fonction
  | [] -> (* Can occur ! because of non-matching regexp ([^'\000'-'\255']) *)
      []
  | (s1,st1) tel p::rem ->
      soit here = Cset.inter s s1 dans
      si Cset.is_empty here alors
        p::split_env gen follow pos m s rem
      sinon
        soit rest = Cset.diff s here dans
        soit rem =
          si Cset.is_empty rest alors
            rem
          sinon
            split_env gen follow pos m rest rem
        et new_st = apply_transitions gen st1 pos m follow dans
        soit stay = Cset.diff s1 here dans
        si Cset.is_empty stay alors
          (here, new_st)::rem
        sinon
          (stay, st1)::(here, new_st)::rem


(* For all nfa_state pos in a dfa state st *)
soit comp_shift gen chars follow st =
  MemMap.fold
    (fonc pos (_,m) env -> split_env gen follow.(pos) pos m chars.(pos) env)
    st [Cset.all_chars_eof,dfa_state_empty]


soit reachs chars follow st =
  soit gen = create_new_addr_gen () dans
(* build a association list (char set -> new state) *)
  soit env = comp_shift gen chars follow st dans
(* change it into (char set -> new state_num) *)
  soit env =
    List.map
      (fonc (s,dfa_state) -> s,goto_state dfa_state) env dans
(* finally build the char indexed array -> new state num *)
  soit shift = Cset.env_to_array env dans
  shift


soit get_tag_mem n env t =
  essaie
    TagMap.find t env.(n)
  avec
  | Not_found -> affirme faux

soit do_tag_actions n env  m =

  soit used,r =
    TagMap.fold (fonc t m (used,r) ->
      soit a = get_tag_mem n env t dans
      Ints.add a used,SetTag (a,m)::r) m (Ints.empty,[]) dans
  soit _,r =
    TagMap.fold
      (fonc tag m (used,r) ->
        si not (Ints.mem m used) && tag.start alors
          Ints.add m used, EraseTag m::r
        sinon
          used,r)
      env.(n) (used,r) dans
  r


soit translate_state shortest_match tags chars follow st =
  soit (n,(_,m)) = st.final dans
  si MemMap.empty = st.others alors
    Perform (n,do_tag_actions n tags m)
  sinon si shortest_match alors début
    si n=no_action alors
      Shift (No_remember,reachs chars follow st.others)
    sinon
      Perform(n, do_tag_actions n tags m)
  fin sinon début
    Shift (
    (si n = no_action alors
      No_remember
    sinon
      Remember (n,do_tag_actions n tags m)),
    reachs chars follow st.others)
  fin

soit dtags chan tags =
  Tags.iter
    (fonc t -> fprintf chan " %a" dtag t)
    tags

soit dtransset s =
  TransSet.iter
    (fonc trans -> filtre trans avec
    | OnChars i,tags ->
        eprintf " (-> %d,%a)" i dtags tags
    | ToAction i,tags ->
        eprintf " ([%d],%a)" i dtags tags)
    s

soit dfollow t =
  eprintf "follow=[" ;
  pour i = 0 à Array.length t-1 faire
    eprintf "%d:" i ;
    dtransset t.(i)
  fait ;
  prerr_endline "]"


soit make_tag_entry id start act a r = filtre a avec
  | Sum (Mem m,0) ->
      TagMap.add {id=id ; start=start ; action=act} m r
  | _ -> r

soit extract_tags l =
  soit envs = Array.create (List.length l) TagMap.empty dans
  List.iter
    (fonc (act,m,_) ->
      envs.(act) <-
         List.fold_right
           (fonc ((name,_),v) r -> filtre v avec
           | Ident_char (_,t) -> make_tag_entry name vrai act t r
           | Ident_string (_,t1,t2) ->
               make_tag_entry name vrai act t1
               (make_tag_entry name faux act t2 r))
           m TagMap.empty)
    l ;
  envs


soit make_dfa lexdef =
  soit (chars, entry_list) = encode_lexdef lexdef dans
  soit follow = followpos (Array.length chars) entry_list dans
(*
  dfollow follow ;
*)
  reset_state () ;
  soit r_states = ref [] dans
  soit initial_states =
    List.map
      (fonc (le,args,shortest) ->
        soit tags = extract_tags le.lex_actions dans
        reset_state_partial le.lex_mem_tags ;
        soit pos_set = firstpos le.lex_regexp dans
(*
        prerr_string "trans={" ; dtransset pos_set ; prerr_endline "}" ;
*)
        soit init_state = create_init_state pos_set dans
        soit init_num = get_state init_state dans
        r_states :=
           map_on_all_states
             (translate_state shortest tags chars follow) !r_states ;
        { auto_name = le.lex_name;
          auto_args = args ;
          auto_mem_size =
            (si !temp_pending alors !next_mem_cell+1 sinon !next_mem_cell) ;
          auto_initial_state = init_num ;
          auto_actions = le.lex_actions })
      entry_list dans
  soit states = !r_states dans
(*
  prerr_endline "** states **" ;
  for i = 0 to !next_state_num-1 do
    eprintf "+++ %d +++\n" i ;
    dstate (Table.get state_table i) ;
    prerr_endline ""
  done ;
  eprintf "%d states\n" !next_state_num ;
*)
  soit actions = Array.create !next_state_num (Perform (0,[])) dans
  List.iter (fonc (act, i) -> actions.(i) <- act) states;
(* Useless state reset, so as to restrict GC roots *)
  reset_state  () ;
  reset_state_partial  0 ;
  (initial_states, actions)
