(***********************************************************************)
(*                                                                     *)
(*                             ocamlbuild                              *)
(*                                                                     *)
(*  Nicolas Pouillard, Berke Durak, projet Gallium, INRIA Rocquencourt *)
(*                                                                     *)
(*  Copyright 2007 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)


(* Original author: Berke Durak *)
(* Glob *)
ouvre My_std;;
ouvre Bool;;
inclus Glob_ast;;
ouvre Glob_lexer;;

soit sf = Printf.sprintf;;

soit brute_limit = 10;;

(*** string_of_token *)
soit string_of_token = fonction
| ATOM _ -> "ATOM"
| AND -> "AND"
| OR -> "OR"
| NOT -> "NOT"
| LPAR -> "LPAR"
| RPAR -> "RPAR"
| TRUE -> "TRUE"
| FALSE -> "FALSE"
| EOF -> "EOF"
;;
(* ***)
(*** match_character_class *)
soit match_character_class cl c =
  Bool.eval
    début fonction (c1,c2) ->
      c1 <= c && c <= c2
    fin
    cl
;;
(* ***)
(*** NFA *)
module NFA =
  struct
    type transition =
    | QCLASS de character_class
    | QEPSILON
    ;;

    module IS = Set.Make(struct type t = int soit compare (x:t) y = compare x y soit print = Format.pp_print_int fin);;
    module ISM = Map.Make(struct type t = IS.t soit compare = IS.compare soit print = IS.print fin);;

    type machine = {
      mc_qi : IS.t;
      mc_table : (character_class * IS.t) list array;
      mc_qf : int;
      mc_power_table : (char, IS.t ISM.t) Hashtbl.t
    }

    (*** build' *)
    soit build' p =
      soit count = ref 0 dans
      soit transitions = ref [] dans
      soit epsilons : (int * int) list ref = ref [] dans
      soit state () = soit id = !count dans incr count; id dans
      soit ( --> ) q1 t q2 =
        filtre t avec
        | QEPSILON -> epsilons := (q1,q2) :: !epsilons; q1
        | QCLASS cl -> transitions := (q1,cl,q2) :: !transitions; q1
      dans
      (* Construit les transitions correspondant au motif donne et arrivant
       * sur l'etat qf.  Retourne l'etat d'origine. *)
      soit rec loop qf = fonction
        | Epsilon  -> qf
        | Word u   ->
            soit m = String.length u dans
            soit q0 = state () dans
            soit rec loop q i =
              si i = m alors
                q0
              sinon
                début
                  soit q' =
                    si i = m - 1 alors
                      qf
                    sinon
                      state ()
                  dans
                  soit _ = (q --> QCLASS(Atom(u.[i], u.[i]))) q' dans
                  loop q' (i + 1)
                fin
            dans
            loop q0 0
        | Class cl ->
            soit q1 = state () dans
            (q1 --> QCLASS cl) qf
        | Star p ->
            (* The fucking Kleene star *)
            soit q2 = state () dans
            soit q1 = loop q2 p dans (* q1 -{p}-> q2 *)
            soit _ = (q1 --> QEPSILON) qf dans
            soit _ = (q2 --> QEPSILON) q1 dans
            soit _ = (q2 --> QEPSILON) q1 dans
            q1
        | Concat(p1,p2) ->
            soit q12 = state () dans
            soit q1  = loop q12 p1 dans (* q1  -{p1}-> q12 *)
            soit q2  = loop qf  p2 dans (* q2  -{p2}-> qf *)
            soit _   = (q12 --> QEPSILON) q2 dans
            q1
        | Union pl ->
            soit qi = state () dans
            List.iter
              début fonc p ->
                soit q = loop qf p dans           (* q -{p2}-> qf *)
                soit _ = (qi --> QEPSILON) q dans (* qi -{}---> q  *)
                ()
              fin
              pl;
            qi
      dans
      soit qf = state () dans
      soit qi = loop qf p dans
      soit m = !count dans

      (* Compute epsilon closure *)
      soit graph = Array.make m IS.empty dans
      List.iter
        début fonc (q,q') ->
          graph.(q) <- IS.add q' graph.(q)
        fin
        !epsilons;

      soit closure = Array.make m IS.empty dans
      soit rec transitive past = fonction
      | [] -> past
      | q :: future ->
          soit past' = IS.add q past dans
          soit future' =
            IS.fold
              début fonc q' future' ->
                (* q -{}--> q' *)
                si IS.mem q' past' alors
                  future'
                sinon
                  q' :: future'
              fin
              graph.(q)
              future
          dans
          transitive past' future'
      dans
      pour i = 0 à m - 1 faire
        closure.(i) <- transitive IS.empty [i] (* O(n^2), I know *)
      fait;

      (* Finally, build the table *)
      soit table = Array.make m [] dans
      List.iter
        début fonc (q,t,q') ->
          table.(q) <- (t, closure.(q')) :: table.(q)
        fin
        !transitions;

      (graph, closure,
      { mc_qi = closure.(qi);
        mc_table = table;
        mc_qf = qf;
        mc_power_table = Hashtbl.create 37 })
    ;;
    soit build x = soit (_,_, machine) = build' x dans machine;;
    (* ***)
    (*** run *)
    soit run ?(trace=faux) machine u =
      soit m = String.length u dans
      soit apply qs c =
        essaie
          soit t = Hashtbl.find machine.mc_power_table c dans
          ISM.find qs t
        avec
        | Not_found ->
            soit qs' =
              IS.fold
                début fonc q qs' ->
                  List.fold_left
                    début fonc qs' (cl,qs'') ->
                      si match_character_class cl c alors
                        IS.union qs' qs''
                      sinon
                        qs'
                    fin
                    qs'
                    machine.mc_table.(q)
                fin
                qs
                IS.empty
            dans
            soit t =
              essaie
                Hashtbl.find machine.mc_power_table c
              avec
              | Not_found -> ISM.empty
            dans
            Hashtbl.replace machine.mc_power_table c (ISM.add qs qs' t);
            qs'
      dans
      soit rec loop qs i =
        si IS.is_empty qs alors
          faux
        sinon
          début
            si i = m alors
              IS.mem machine.mc_qf qs
            sinon
              début
                soit c = u.[i] dans
                si trace alors
                  début
                    Printf.printf "%d %C {" i c;
                    IS.iter (fonc q -> Printf.printf " %d" q) qs;
                    Printf.printf " }\n%!"
                  fin;
                soit qs' = apply qs c dans
                loop qs' (i + 1)
              fin
          fin
      dans
      loop machine.mc_qi 0
    ;;
    (* ***)
  fin
;;
(* ***)
(*** Brute *)
module Brute =
  struct
    exception Succeed;;
    exception Fail;;
    exception Too_hard;;

    (*** match_pattern *)
    soit match_pattern counter p u =
      soit m = String.length u dans
      (** [loop i n p] returns [true] iff the word [u.(i .. i + n - 1)] is in the
       ** language generated by the pattern [p].
       ** We must have 0 <= i and i + n <= m *)
      soit rec loop (i,n,p) =
        affirme (0 <= i && 0 <= n && i + n <= m);
        incr counter;
        si !counter >= brute_limit alors raise Too_hard;
        filtre p avec
        | Word v   ->
            String.length v = n &&
            début
              soit rec check j = j = n || (v.[j] = u.[i + j] && check (j + 1))
              dans
              check 0
            fin
        | Epsilon  -> n = 0
        | Star(Class True) -> vrai
        | Star(Class cl) ->
            soit rec check k =
              si k = n alors
                vrai
              sinon
                (match_character_class cl u.[i + k]) && check (k + 1)
            dans
            check 0
        | Star _ -> raise Too_hard
        | Class cl -> n = 1 && match_character_class cl u.[i]
        | Concat(p1,p2) ->
            soit rec scan j =
              j <= n && ((loop (i,j,p1) && loop (i+j, n - j,p2)) || scan (j + 1))
            dans
            scan 0
        | Union pl -> List.exists (fonc p' -> loop (i,n,p')) pl
      dans
      loop (0,m,p)
    ;;
    (* ***)
fin
;;
(* ***)
(*** fast_pattern_contents, fast_pattern, globber *)
type fast_pattern_contents =
| Brute de int ref * pattern
| Machine de NFA.machine
;;
type fast_pattern = fast_pattern_contents ref;;
type globber = fast_pattern atom Bool.boolean;;
(* ***)
(*** fast_pattern_of_pattern *)
soit fast_pattern_of_pattern p = ref (Brute(ref 0, p));;
(* ***)
(*** add_dir *)
soit add_dir dir x =
  filtre dir avec
  | None -> x
  | Some(dir) ->
      filtre x avec
      | Constant(s) ->
          Constant(My_std.filename_concat dir s)
      | Pattern(p) ->
          Pattern(Concat(Word(My_std.filename_concat dir ""), p))
;;
(* ***)
(*** add_ast_dir *)
soit add_ast_dir dir x =
  filtre dir avec
  | None -> x
  | Some dir ->
      soit slash = Class(Atom('/','/')) dans
      soit any = Class True dans
      soit q = Union[Epsilon; Concat(slash, Star any)] dans (* ( /** )? *)
      And[Atom(Pattern(ref (Brute(ref 0, Concat(Word dir, q))))); x]
;;
(* ***)
(*** parse *)
soit parse ?dir u =
  soit l = Lexing.from_string u dans
  soit tok = ref None dans
  soit f =
    fonc () ->
      filtre !tok avec
      | None -> token l
      | Some x ->
          tok := None;
          x
  dans
  soit g t =
    filtre !tok avec
    | None -> tok := Some t
    | Some t' ->
        raise (Parse_error(sf "Trying to unput token %s while %s is active" (string_of_token t) (string_of_token t')))
  dans
  soit read x =
    soit y = f () dans
    si x = y alors
      ()
    sinon
      raise (Parse_error(sf "Unexpected token, expecting %s, got %s" (string_of_token x) (string_of_token y)))
  dans
  soit rec atomizer continuation = filtre f () avec
  | NOT    -> atomizer (fonc x -> continuation (Not x))
  | ATOM x ->
      début
        soit a =
          filtre add_dir dir x avec
          | Constant u -> Constant u
          | Pattern p -> Pattern(fast_pattern_of_pattern p)
        dans
        continuation (Atom a)
      fin
  | TRUE   -> continuation True
  | FALSE  -> continuation False
  | LPAR   ->
      soit y = parse_s () dans
      read RPAR;
      continuation y
  | t      -> raise (Parse_error(sf "Unexpected token %s in atomizer" (string_of_token t)))
  et parse_s1 x = filtre f () avec
  | OR     -> soit y = parse_s () dans Or[x; y]
  | AND    -> parse_t x
  | t      -> g t; x
  et parse_t1 x y = filtre f () avec
  | OR     -> soit z = parse_s () dans Or[And[x;y]; z]
  | AND    -> parse_t (And[x;y])
  | t      -> g t; And[x;y]
  et parse_s () = atomizer parse_s1
  et parse_t x = atomizer (parse_t1 x)
  dans
  soit x = parse_s () dans
  read EOF;
  add_ast_dir dir x
;;
(* ***)
(*** eval *)
soit eval g u =
  Bool.eval
    début fonction
      | Constant v -> u = v
      | Pattern kind ->
          filtre !kind avec
          | Brute(count, p) ->
            début
              soit do_nfa () =
                soit m = NFA.build p dans
                kind := Machine m;
                NFA.run m u
              dans
              si !count >= brute_limit alors
                do_nfa ()
              sinon
                essaie
                  Brute.match_pattern count p u
                avec
                | Brute.Too_hard -> do_nfa ()
            fin
          | Machine m -> NFA.run m u
    fin
    g
(* ***)
(*** Debug *)
(*let (Atom(Pattern x)) = parse "<{a,b}>";;
#install_printer IS.print;;
#install_printer ISM.print;;
let (graph, closure, machine) = build' x;;*)
(* ***)
