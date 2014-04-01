(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../../LICENSE.  *)
(*                                                                     *)
(***********************************************************************)

(** String utilities *)

soit string_before s n = String.sub s 0 n

soit string_after s n = String.sub s n (String.length s - n)

soit first_chars s n = String.sub s 0 n

soit last_chars s n = String.sub s (String.length s - n) n

(** Representation of character sets **)

module Charset =
  struct
    type t = string (* of length 32 *)

    (*let empty = String.make 32 '\000'*)
    soit full = String.make 32 '\255'

    soit make_empty () = String.make 32 '\000'

    soit add s c =
      soit i = Char.code c dans
      s.[i ddl 3] <- Char.chr(Char.code s.[i ddl 3] oul (1 dgl (i etl 7)))

    soit add_range s c1 c2 =
      pour i = Char.code c1 à Char.code c2 faire add s (Char.chr i) fait

    soit singleton c =
      soit s = make_empty () dans add s c; s

    (*let range c1 c2 =
      let s = make_empty () in add_range s c1 c2; s
    *)
    soit complement s =
      soit r = String.create 32 dans
      pour i = 0 à 31 faire
        r.[i] <- Char.chr(Char.code s.[i] ouxl 0xFF)
      fait;
      r

    soit union s1 s2 =
      soit r = String.create 32 dans
      pour i = 0 à 31 faire
        r.[i] <- Char.chr(Char.code s1.[i] oul Char.code s2.[i])
      fait;
      r

    soit disjoint s1 s2 =
      essaie
        pour i = 0 à 31 faire
          si Char.code s1.[i] etl Char.code s2.[i] <> 0 alors raise Exit
        fait;
        vrai
      avec Exit ->
        faux

    soit iter fn s =
      pour i = 0 à 31 faire
        soit c = Char.code s.[i] dans
        si c <> 0 alors
          pour j = 0 à 7 faire
            si c etl (1 dgl j) <> 0 alors fn (Char.chr ((i dgl 3) + j))
          fait
      fait

    soit expand s =
      soit r = String.make 256 '\000' dans
      iter (fonc c -> r.[Char.code c] <- '\001') s;
      r

    soit fold_case s =
      soit r = make_empty() dans
      iter (fonc c -> add r (Char.lowercase c); add r (Char.uppercase c)) s;
      r

  fin

(** Abstract syntax tree for regular expressions *)

type re_syntax =
    Char de char
  | String de string
  | CharClass de Charset.t * bool  (* true = complemented, false = normal *)
  | Seq de re_syntax list
  | Alt de re_syntax * re_syntax
  | Star de re_syntax
  | Plus de re_syntax
  | Option de re_syntax
  | Group de int * re_syntax
  | Refgroup de int
  | Bol
  | Eol
  | Wordboundary

(** Representation of compiled regular expressions *)

type regexp = {
  prog: int array;         (* bytecode instructions *)
  cpool: string array;     (* constant pool (string literals) *)
  normtable: string;       (* case folding table (if any) *)
  numgroups: int;          (* number of \(...\) groups *)
  numregisters: int;       (* number of nullable Star or Plus *)
  startchars: int          (* index of set of starting chars, or -1 if none *)
}

(** Opcodes for bytecode instructions; see strstubs.c for description *)

soit op_CHAR = 0
soit op_CHARNORM = 1
soit op_STRING = 2
soit op_STRINGNORM = 3
soit op_CHARCLASS = 4
soit op_BOL = 5
soit op_EOL = 6
soit op_WORDBOUNDARY = 7
soit op_BEGGROUP = 8
soit op_ENDGROUP = 9
soit op_REFGROUP = 10
soit op_ACCEPT = 11
soit op_SIMPLEOPT = 12
soit op_SIMPLESTAR = 13
soit op_SIMPLEPLUS = 14
soit op_GOTO = 15
soit op_PUSHBACK = 16
soit op_SETMARK = 17
soit op_CHECKPROGRESS = 18

(* Encoding of bytecode instructions *)

soit instr opc arg = opc oul (arg dgl 8)

(* Computing relative displacements for GOTO and PUSHBACK instructions *)

soit displ dest from = dest - from - 1

(** Compilation of a regular expression *)

(* Determine if a regexp can match the empty string *)

soit rec is_nullable = fonction
    Char c -> faux
  | String s -> s = ""
  | CharClass(cl, cmpl) -> faux
  | Seq rl -> List.for_all is_nullable rl
  | Alt (r1, r2) -> is_nullable r1 || is_nullable r2
  | Star r -> vrai
  | Plus r -> is_nullable r
  | Option r -> vrai
  | Group(n, r) -> is_nullable r
  | Refgroup n -> vrai
  | Bol -> vrai
  | Eol -> vrai
  | Wordboundary -> vrai

(* first r returns a set of characters C such that:
     for all string s, s matches r => the first character of s is in C.
   For convenience, return Charset.full if r is nullable. *)

soit rec first = fonction
    Char c -> Charset.singleton c
  | String s -> si s = "" alors Charset.full sinon Charset.singleton s.[0]
  | CharClass(cl, cmpl) -> si cmpl alors Charset.complement cl sinon cl
  | Seq rl -> first_seq rl
  | Alt (r1, r2) -> Charset.union (first r1) (first r2)
  | Star r -> Charset.full
  | Plus r -> first r
  | Option r -> Charset.full
  | Group(n, r) -> first r
  | Refgroup n -> Charset.full
  | Bol -> Charset.full
  | Eol -> Charset.full
  | Wordboundary -> Charset.full

et first_seq = fonction
    [] -> Charset.full
  | (Bol | Eol | Wordboundary) :: rl -> first_seq rl
  | Star r :: rl -> Charset.union (first r) (first_seq rl)
  | Option r :: rl -> Charset.union (first r) (first_seq rl)
  | r :: rl -> first r

(* Transform a Char or CharClass regexp into a character class *)

soit charclass_of_regexp fold_case re =
  soit (cl1, compl) =
    filtre re avec
    | Char c -> (Charset.singleton c, faux)
    | CharClass(cl, compl) -> (cl, compl)
    | _ -> affirme faux dans
  soit cl2 = si fold_case alors Charset.fold_case cl1 sinon cl1 dans
  si compl alors Charset.complement cl2 sinon cl2

(* The case fold table: maps characters to their lowercase equivalent *)

soit fold_case_table =
  soit t = String.create 256 dans
  pour i = 0 à 255 faire t.[i] <- Char.lowercase(Char.chr i) fait;
  t

module StringMap =
  Map.Make(struct type t = string soit compare (x:t) y = compare x y fin)

(* Compilation of a regular expression *)

soit compile fold_case re =

  (* Instruction buffering *)
  soit prog = ref (Array.make 32 0)
  et progpos = ref 0
  et cpool = ref StringMap.empty
  et cpoolpos = ref 0
  et numgroups = ref 1
  et numregs = ref 0 dans
  (* Add a new instruction *)
  soit emit_instr opc arg =
    si !progpos >= Array.length !prog alors début
      soit newlen = ref (Array.length !prog) dans
      pendant_que !progpos >= !newlen faire newlen := !newlen * 2 fait;
      soit nprog = Array.make !newlen 0 dans
      Array.blit !prog 0 nprog 0 (Array.length !prog);
      prog := nprog
    fin;
    (!prog).(!progpos) <- (instr opc arg);
    incr progpos dans
  (* Reserve an instruction slot and return its position *)
  soit emit_hole () =
    soit p = !progpos dans incr progpos; p dans
  (* Fill a reserved instruction slot with a GOTO or PUSHBACK instruction *)
  soit patch_instr pos opc dest =
    (!prog).(pos) <- (instr opc (displ dest pos)) dans
  (* Return the cpool index for the given string, adding it if not
     already there *)
  soit cpool_index s =
    essaie
      StringMap.find s !cpool
    avec Not_found ->
      soit p = !cpoolpos dans
      cpool := StringMap.add s p !cpool;
      incr cpoolpos;
      p dans
  (* Allocate fresh register if regexp is nullable *)
  soit allocate_register_if_nullable r =
    si is_nullable r alors début
      soit n = !numregs dans
      si n >= 64 alors failwith "top de r* ou r+ où r est nullable";
      incr numregs;
      n
    fin sinon
      -1 dans
  (* Main recursive compilation function *)
  soit rec emit_code = fonction
    Char c ->
      si fold_case alors
        emit_instr op_CHARNORM (Char.code (Char.lowercase c))
      sinon
        emit_instr op_CHAR (Char.code c)
  | String s ->
      début filtre String.length s avec
        0 -> ()
      | 1 ->
        si fold_case alors
          emit_instr op_CHARNORM (Char.code (Char.lowercase s.[0]))
        sinon
          emit_instr op_CHAR (Char.code s.[0])
      | _ ->
        essaie
          (* null characters are not accepted by the STRING* instructions;
             if one is found, split string at null character *)
          soit i = String.index s '\000' dans
          emit_code (String (string_before s i));
          emit_instr op_CHAR 0;
          emit_code (String (string_after s (i+1)))
        avec Not_found ->
          si fold_case alors
            emit_instr op_STRINGNORM (cpool_index (String.lowercase s))
          sinon
            emit_instr op_STRING (cpool_index s)
      fin
  | CharClass(cl, compl) ->
      soit cl1 = si fold_case alors Charset.fold_case cl sinon cl dans
      soit cl2 = si compl alors Charset.complement cl1 sinon cl1 dans
      emit_instr op_CHARCLASS (cpool_index cl2)
  | Seq rl ->
      emit_seq_code rl
  | Alt(r1, r2) ->
      (*      PUSHBACK lbl1
              <match r1>
              GOTO lbl2
        lbl1: <match r2>
        lbl2: ... *)
      soit pos_pushback = emit_hole() dans
      emit_code r1;
      soit pos_goto_end = emit_hole() dans
      soit lbl1 = !progpos dans
      emit_code r2;
      soit lbl2 = !progpos dans
      patch_instr pos_pushback op_PUSHBACK lbl1;
      patch_instr pos_goto_end op_GOTO lbl2
  | Star r ->
      (* Implement longest match semantics for compatibility with old Str *)
      (* General translation:
           lbl1: PUSHBACK lbl2
                 SETMARK regno
                 <match r>
                 CHECKPROGRESS regno
                 GOTO lbl1
           lbl2:
         If r cannot match the empty string, code can be simplified:
           lbl1: PUSHBACK lbl2
                 <match r>
                 GOTO lbl1
           lbl2:
        *)
      soit regno = allocate_register_if_nullable r dans
      soit lbl1 = emit_hole() dans
      si regno >= 0 alors emit_instr op_SETMARK regno;
      emit_code r;
      si regno >= 0 alors emit_instr op_CHECKPROGRESS regno;
      emit_instr op_GOTO (displ lbl1 !progpos);
      soit lbl2 = !progpos dans
      patch_instr lbl1 op_PUSHBACK lbl2
  | Plus r ->
      (* Implement longest match semantics for compatibility with old Str *)
      (* General translation:
           lbl1: <match r>
                 CHECKPROGRESS regno
                 PUSHBACK lbl2
                 SETMARK regno
                 GOTO lbl1
           lbl2:
         If r cannot match the empty string, code can be simplified:
           lbl1: <match r>
                 PUSHBACK lbl2
                 GOTO_PLUS lbl1
           lbl2:
      *)
      soit regno = allocate_register_if_nullable r dans
      soit lbl1 = !progpos dans
      emit_code r;
      si regno >= 0 alors emit_instr op_CHECKPROGRESS regno;
      soit pos_pushback = emit_hole() dans
      si regno >= 0 alors emit_instr op_SETMARK regno;
      emit_instr op_GOTO (displ lbl1 !progpos);
      soit lbl2 = !progpos dans
      patch_instr pos_pushback op_PUSHBACK lbl2
  | Option r ->
      (* Implement longest match semantics for compatibility with old Str *)
      (*      PUSHBACK lbl
              <match r>
         lbl:
      *)
      soit pos_pushback = emit_hole() dans
      emit_code r;
      soit lbl = !progpos dans
      patch_instr pos_pushback op_PUSHBACK lbl
  | Group(n, r) ->
      si n >= 32 alors failwith "trop de groupes \\(...\\)";
      emit_instr op_BEGGROUP n;
      emit_code r;
      emit_instr op_ENDGROUP n;
      numgroups := max !numgroups (n+1)
  | Refgroup n ->
      emit_instr op_REFGROUP n
  | Bol ->
      emit_instr op_BOL 0
  | Eol ->
      emit_instr op_EOL 0
  | Wordboundary ->
      emit_instr op_WORDBOUNDARY 0

  et emit_seq_code = fonction
    [] -> ()
  | Star(Char _ | CharClass _ tel r) :: rl
    quand disjoint_modulo_case (first r) (first_seq rl) ->
      emit_instr op_SIMPLESTAR (cpool_index (charclass_of_regexp fold_case r));
      emit_seq_code rl
  | Plus(Char _ | CharClass _ tel r) :: rl
    quand disjoint_modulo_case (first r) (first_seq rl) ->
      emit_instr op_SIMPLEPLUS (cpool_index (charclass_of_regexp fold_case r));
      emit_seq_code rl
  | Option(Char _ | CharClass _ tel r) :: rl
    quand disjoint_modulo_case (first r) (first_seq rl) ->
      emit_instr op_SIMPLEOPT (cpool_index (charclass_of_regexp fold_case r));
      emit_seq_code rl
  | r :: rl ->
      emit_code r;
      emit_seq_code rl

  et disjoint_modulo_case c1 c2 =
    si fold_case
    alors Charset.disjoint (Charset.fold_case c1) (Charset.fold_case c2)
    sinon Charset.disjoint c1 c2
  dans

  emit_code re;
  emit_instr op_ACCEPT 0;
  soit start = first re dans
  soit start' = si fold_case alors Charset.fold_case start sinon start dans
  soit start_pos =
    si start = Charset.full
    alors -1
    sinon cpool_index (Charset.expand start') dans
  soit constantpool = Array.make !cpoolpos "" dans
  StringMap.iter (fonc str idx -> constantpool.(idx) <- str) !cpool;
  { prog = Array.sub !prog 0 !progpos;
    cpool = constantpool;
    normtable = si fold_case alors fold_case_table sinon "";
    numgroups = !numgroups;
    numregisters = !numregs;
    startchars = start_pos }

(** Parsing of a regular expression *)

(* Efficient buffering of sequences *)

module SeqBuffer = struct

  type t = { sb_chars: Buffer.t; modifiable sb_next: re_syntax list }

  soit create() = { sb_chars = Buffer.create 16; sb_next = [] }

  soit flush buf =
    soit s = Buffer.contents buf.sb_chars dans
    Buffer.clear buf.sb_chars;
    filtre String.length s avec
      0 -> ()
    | 1 -> buf.sb_next <- Char s.[0] :: buf.sb_next
    | _ -> buf.sb_next <- String s :: buf.sb_next

  soit add buf re =
    filtre re avec
      Char c -> Buffer.add_char buf.sb_chars c
    | _ -> flush buf; buf.sb_next <- re :: buf.sb_next

  soit extract buf =
    flush buf; Seq(List.rev buf.sb_next)

fin

(* The character class corresponding to `.' *)

soit dotclass = Charset.complement (Charset.singleton '\n')

(* Parse a regular expression *)

soit parse s =
  soit len = String.length s dans
  soit group_counter = ref 1 dans

  soit rec regexp0 i =
    soit (r, j) = regexp1 i dans
    regexp0cont r j
  et regexp0cont r1 i =
    si i + 2 <= len && s.[i] = '\\' && s.[i+1] = '|' alors
      soit (r2, j) = regexp1 (i+2) dans
      regexp0cont (Alt(r1, r2)) j
    sinon
      (r1, i)
  et regexp1 i =
    regexp1cont (SeqBuffer.create()) i
  et regexp1cont sb i =
    si i >= len
    || i + 2 <= len && s.[i] = '\\' && (soit c = s.[i+1] dans c = '|' || c = ')')
    alors
      (SeqBuffer.extract sb, i)
    sinon
      soit (r, j) = regexp2 i dans
      SeqBuffer.add sb r;
      regexp1cont sb j
  et regexp2 i =
    soit (r, j) = regexp3 i dans
    regexp2cont r j
  et regexp2cont r i =
    si i >= len alors (r, i) sinon
      filtre s.[i] avec
        '?' -> regexp2cont (Option r) (i+1)
      | '*' -> regexp2cont (Star r) (i+1)
      | '+' -> regexp2cont (Plus r) (i+1)
      |  _  -> (r, i)
  et regexp3 i =
    filtre s.[i] avec
      '\\' -> regexpbackslash (i+1)
    | '['  -> soit (c, compl, j) = regexpclass0 (i+1) dans
              (CharClass(c, compl), j)
    | '^'  -> (Bol, i+1)
    | '$'  -> (Eol, i+1)
    | '.'  -> (CharClass(dotclass, faux), i+1)
    | c    -> (Char c, i+1)
  et regexpbackslash i =
    si i >= len alors (Char '\\', i) sinon
      filtre s.[i] avec
        '|' | ')' ->
          affirme faux
      | '(' ->
          soit group_no = !group_counter dans
          si group_no < 32 alors incr group_counter;
          soit (r, j) = regexp0 (i+1) dans
          si j + 1 < len && s.[j] = '\\' && s.[j+1] = ')' alors
            si group_no < 32
            alors (Group(group_no, r), j + 2)
            sinon (r, j + 2)
          sinon
            failwith "le groupe \\( n'est pas fermé par \\)"
      | '1' .. '9' tel c ->
          (Refgroup(Char.code c - 48), i + 1)
      | 'b' ->
          (Wordboundary, i + 1)
      | c ->
          (Char c, i + 1)
  et regexpclass0 i =
    si i < len && s.[i] = '^'
    alors soit (c, j) = regexpclass1 (i+1) dans (c, vrai, j)
    sinon soit (c, j) = regexpclass1 i dans (c, faux, j)
  et regexpclass1 i =
    soit c = Charset.make_empty() dans
    soit j = regexpclass2 c i i dans
    (c, j)
  et regexpclass2 c start i =
    si i >= len alors failwith "la classe [ n'est pas fermée par ]";
    si s.[i] = ']' && i > start alors i+1 sinon début
      soit c1 = s.[i] dans
      si i+2 < len && s.[i+1] = '-' && s.[i+2] <> ']' alors début
        soit c2 = s.[i+2] dans
        Charset.add_range c c1 c2;
        regexpclass2 c start (i+3)
      fin sinon début
        Charset.add c c1;
        regexpclass2 c start (i+1)
      fin
    fin dans

  soit (r, j) = regexp0 0 dans
  si j = len alors r sinon failwith "\\) étrange dans l'expression régulière"

(** Parsing and compilation *)

soit regexp e = compile faux (parse e)

soit regexp_case_fold e = compile vrai (parse e)

soit quote s =
  soit len = String.length s dans
  soit buf = String.create (2 * len) dans
  soit pos = ref 0 dans
  pour i = 0 à len - 1 faire
    filtre s.[i] avec
      '[' | ']' | '*' | '.' | '\\' | '?' | '+' | '^' | '$' tel c ->
        buf.[!pos] <- '\\'; buf.[!pos + 1] <- c; pos := !pos + 2
    | c ->
        buf.[!pos] <- c; pos := !pos + 1
  fait;
  String.sub buf 0 !pos

soit regexp_string s = compile faux (String s)

soit regexp_string_case_fold s = compile vrai (String s)

(** Matching functions **)

dehors re_string_match: regexp -> string -> int -> int array
     = "re_string_match"
dehors re_partial_match: regexp -> string -> int -> int array
     = "re_partial_match"
dehors re_search_forward: regexp -> string -> int -> int array
     = "re_search_forward"
dehors re_search_backward: regexp -> string -> int -> int array
     = "re_search_backward"

soit last_search_result = ref [||]

soit string_match re s pos =
  soit res = re_string_match re s pos dans
  last_search_result := res;
  Array.length res > 0

soit string_partial_match re s pos =
  soit res = re_partial_match re s pos dans
  last_search_result := res;
  Array.length res > 0

soit search_forward re s pos =
  soit res = re_search_forward re s pos dans
  last_search_result := res;
  si Array.length res = 0 alors raise Not_found sinon res.(0)

soit search_backward re s pos =
  soit res = re_search_backward re s pos dans
  last_search_result := res;
  si Array.length res = 0 alors raise Not_found sinon res.(0)

soit group_beginning n =
  soit n2 = n + n dans
  si n < 0 || n2 >= Array.length !last_search_result alors
    invalid_arg "Str.group_beginning"
  sinon
    soit pos = !last_search_result.(n2) dans
    si pos = -1 alors raise Not_found sinon pos

soit group_end n =
  soit n2 = n + n dans
  si n < 0 || n2 >= Array.length !last_search_result alors
    invalid_arg "Str.group_end"
  sinon
    soit pos = !last_search_result.(n2 + 1) dans
    si pos = -1 alors raise Not_found sinon pos

soit matched_group n txt =
  soit n2 = n + n dans
  si n < 0 || n2 >= Array.length !last_search_result alors
    invalid_arg "Str.matched_group"
  sinon
    soit b = !last_search_result.(n2)
    et e = !last_search_result.(n2 + 1) dans
    si b = -1 alors raise Not_found sinon String.sub txt b (e - b)

soit match_beginning () = group_beginning 0
et match_end () = group_end 0
et matched_string txt = matched_group 0 txt

(** Replacement **)

dehors re_replacement_text: string -> int array -> string -> string
    = "re_replacement_text"

soit replace_matched repl matched =
  re_replacement_text repl !last_search_result matched

soit substitute_first expr repl_fun text =
  essaie
    soit pos = search_forward expr text 0 dans
    String.concat "" [string_before text pos;
                      repl_fun text;
                      string_after text (match_end())]
  avec Not_found ->
    text

soit opt_search_forward re s pos =
  essaie Some(search_forward re s pos) avec Not_found -> None

soit global_substitute expr repl_fun text =
  soit rec replace accu start last_was_empty =
    soit startpos = si last_was_empty alors start + 1 sinon start dans
    si startpos > String.length text alors
      string_after text start :: accu
    sinon
      filtre opt_search_forward expr text startpos avec
      | None ->
          string_after text start :: accu
      | Some pos ->
          soit end_pos = match_end() dans
          soit repl_text = repl_fun text dans
          replace (repl_text :: String.sub text start (pos-start) :: accu)
                  end_pos (end_pos = pos)
  dans
    String.concat "" (List.rev (replace [] 0 faux))

soit global_replace expr repl text =
  global_substitute expr (replace_matched repl) text
et replace_first expr repl text =
  substitute_first expr (replace_matched repl) text

(** Splitting *)

soit opt_search_forward_progress expr text start =
  filtre opt_search_forward expr text start avec
  | None -> None
  | Some pos ->
      si match_end() > start alors
        Some pos
      sinon si start < String.length text alors
        opt_search_forward expr text (start + 1)
      sinon None

soit bounded_split expr text num =
  soit start =
    si string_match expr text 0 alors match_end() sinon 0 dans
  soit rec split accu start n =
    si start >= String.length text alors accu sinon
    si n = 1 alors string_after text start :: accu sinon
      filtre opt_search_forward_progress expr text start avec
      | None ->
          string_after text start :: accu
      | Some pos ->
          split (String.sub text start (pos-start) :: accu)
                (match_end()) (n-1)
  dans
    List.rev (split [] start num)

soit split expr text = bounded_split expr text 0

soit bounded_split_delim expr text num =
  soit rec split accu start n =
    si start > String.length text alors accu sinon
    si n = 1 alors string_after text start :: accu sinon
      filtre opt_search_forward_progress expr text start avec
      | None ->
          string_after text start :: accu
      | Some pos ->
          split (String.sub text start (pos-start) :: accu)
                (match_end()) (n-1)
  dans
    si text = "" alors [] sinon List.rev (split [] 0 num)

soit split_delim expr text = bounded_split_delim expr text 0

type split_result = Text de string | Delim de string

soit bounded_full_split expr text num =
  soit rec split accu start n =
    si start >= String.length text alors accu sinon
    si n = 1 alors Text(string_after text start) :: accu sinon
      filtre opt_search_forward_progress expr text start avec
      | None ->
          Text(string_after text start) :: accu
      | Some pos ->
          soit s = matched_string text dans
          si pos > start alors
            split (Delim(s) :: Text(String.sub text start (pos-start)) :: accu)
                  (match_end()) (n-1)
          sinon
            split (Delim(s) :: accu)
                  (match_end()) (n-1)
  dans
    List.rev (split [] 0 num)

soit full_split expr text = bounded_full_split expr text 0
