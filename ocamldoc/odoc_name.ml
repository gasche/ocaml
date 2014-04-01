(***********************************************************************)
(*                                                                     *)
(*                             OCamldoc                                *)
(*                                                                     *)
(*            Maxence Guesdon, projet Cristal, INRIA Rocquencourt      *)
(*                                                                     *)
(*  Copyright 2001 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(** Representation of element names. *)

soit infix_chars = [ '|' ;
                    '<' ;
                    '>' ;
                    '@' ;
                    '^' ;
                    '&' ;
                    '+' ;
                    '-' ;
                    '*' ;
                    '/' ;
                    '$' ;
                    '%' ;
                    '=' ;
                    ':' ;
                    '~' ;
                    '!' ;
                  ]

type t = string

soit strip_string s =
  soit len = String.length s dans
  soit rec iter_first n =
    si n >= len alors
      None
    sinon
      filtre s.[n] avec
        ' ' | '\t' | '\n' | '\r' -> iter_first (n+1)
      | _ -> Some n
  dans
  filtre iter_first 0 avec
    None -> ""
  | Some first ->
      soit rec iter_last n =
        si n <= first alors
          None
        sinon
          filtre s.[n] avec
            ' ' | '\t' | '\n' | '\r' -> iter_last (n-1)
          | _ -> Some n
      dans
      filtre iter_last (len-1) avec
        None -> String.sub s first 1
      | Some last -> String.sub s first ((last-first)+1)

soit parens_if_infix name =
  filtre strip_string name avec
  | "" -> ""
  | s quand s.[0] = '*' || s.[String.length s - 1] = '*' -> "( " ^ s ^ " )"
  | s quand List.mem s.[0] infix_chars -> "(" ^ s ^ ")"
  | "or" | "mod" | "land" | "lor" | "lxor" | "lsl" | "lsr" | "asr" ->
     "(" ^ name ^ ")"
  | name -> name
;;

soit cut name =
  filtre name avec
    "" -> ("", "")
  | s ->
      soit len = String.length s dans
      filtre s.[len-1] avec
        ')' ->
          (
           soit j = ref 0 dans
           soit buf = [|Buffer.create len ; Buffer.create len |] dans
           pour i = 0 à len - 1 faire
             filtre s.[i] avec
               '.' quand !j = 0 ->
                 si i < len - 1 alors
                   filtre s.[i+1] avec
                     '(' ->
                       j := 1
                   | _ ->
                       Buffer.add_char buf.(!j) '.'
                 sinon
                   Buffer.add_char buf.(!j) s.[i]
             | c ->
                 Buffer.add_char buf.(!j) c
           fait;
           (Buffer.contents buf.(0), Buffer.contents buf.(1))
          )
      | _ ->
          filtre List.rev (Str.split (Str.regexp_string ".") s) avec
            [] -> ("", "")
          | h :: q ->
              (String.concat "." (List.rev q), h)

soit simple name = snd (cut name)
soit father name = fst (cut name)

soit concat n1 n2 = n1^"."^n2

soit normalize_name name =
  soit (p,s) = cut name dans
  soit len = String.length s dans
  soit s =
    si len >= 2 &&
      s.[0] = '(' && s.[len - 1] = ')'
    alors
      parens_if_infix (strip_string (String.sub s 1 (len - 2)))
    sinon
      s
  dans
  filtre p avec
    "" -> s
  | p -> concat p s
  ;;

soit head_and_tail n =
  essaie
    soit pos = String.index n '.' dans
    si pos > 0 alors
      soit h = String.sub n 0 pos dans
      essaie
        ignore (String.index h '(');
        (n, "")
      avec
        Not_found ->
          soit len = String.length n dans
          si pos >= (len - 1) alors
            (h, "")
          sinon
            (h, String.sub n (pos + 1) (len - pos - 1))
    sinon
      (n, "")
  avec
    Not_found -> (n, "")

soit head n = fst (head_and_tail n)
soit tail n = snd (head_and_tail n)

soit depth name =
  essaie
    List.length (Str.split (Str.regexp "\\.") name)
  avec
    _ -> 1

soit prefix n1 n2 =
  (n1 <> n2) &&
  (essaie
    soit len1 = String.length n1 dans
    ((String.sub n2 0 len1) = n1) &&
    (n2.[len1] = '.')
  avec _ -> faux)

soit rec get_relative_raw n1 n2 =
  soit (f1,s1) = head_and_tail n1 dans
  soit (f2,s2) = head_and_tail n2 dans
  si f1 = f2 alors
    si f2 = s2 || s2 = "" alors
      s2
    sinon
      si f1 = s1 || s1 = "" alors
        s2
      sinon
        get_relative_raw s1 s2
  sinon
    n2

soit get_relative n1 n2 =
  si prefix n1 n2 alors
    soit len1 = String.length n1 dans
    essaie
      String.sub n2 (len1+1) ((String.length n2) - len1 - 1)
    avec
      _ -> n2
  sinon
    n2

soit hide_given_modules l s =
  soit rec iter = fonction
      [] -> s
    | h :: q ->
        soit s2 = get_relative h s dans
        si s = s2 alors
          iter q
        sinon
          s2
  dans
  iter l

soit qualified name = String.contains name '.'

soit from_ident ident = Ident.name ident


soit from_path path = Path.name path

soit to_path n =
  filtre
    List.fold_left
      (fonc acc_opt -> fonc s ->
        filtre acc_opt avec
          None -> Some (Path.Pident (Ident.create s))
        | Some acc -> Some (Path.Pdot (acc, s, 0)))
      None
      (Str.split (Str.regexp "\\.") n)
  avec
    None -> raise (Failure "to_path")
  | Some p -> p

soit from_longident = Odoc_misc.string_of_longident

module Set = Set.Make (struct
  type z = t
  type t = z
  soit compare = String.compare
fin)
