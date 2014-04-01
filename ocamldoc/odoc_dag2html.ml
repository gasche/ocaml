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

(** The types and functions to create a html table representing a dag. Thanks to Daniel De Rauglaudre. *)

type 'a dag = { modifiable dag : 'a node array }
et 'a node =
  { modifiable pare : idag list; valu : 'a; modifiable chil : idag list }
et idag = int
;;

dehors int_of_idag : idag -> int = "%identity";;
dehors idag_of_int : int -> idag = "%identity";;

type 'a table = { modifiable table : 'a data array array }
et 'a data = { modifiable elem : 'a elem; modifiable span : span_id }
et 'a elem = Elem de 'a | Ghost de ghost_id | Nothing
et span_id
et ghost_id
;;

dehors span_id_of_int : int -> span_id = "%identity";;
dehors int_of_span_id : span_id -> int = "%identity";;
dehors ghost_id_of_int : int -> ghost_id = "%identity";;
dehors int_of_ghost_id : ghost_id -> int = "%identity";;

soit new_span_id = soit i = ref 0 dans fonc () -> incr i; span_id_of_int !i;;

soit new_ghost_id = soit i = ref 0 dans fonc () -> incr i; ghost_id_of_int !i;;

(** creating the html table structure *)

type align = LeftA | CenterA | RightA;;
type table_data = TDstring de string | TDhr de align;;
type html_table = (int * align * table_data) array array;;

soit html_table_struct indi_txt phony d t =
  soit phony =
    fonction
      Elem e -> phony d.dag.(int_of_idag e)
    | Ghost _ -> faux
    | Nothing -> vrai
  dans
  soit elem_txt =
    fonction
      Elem e -> indi_txt d.dag.(int_of_idag e)
    | Ghost _ -> "|"
    | Nothing -> "&nbsp;"
  dans
  soit bar_txt =
    fonction
      Elem _ | Ghost _ -> "|"
    | Nothing -> "&nbsp;"
  dans
  soit all_empty i =
    soit rec loop j =
      si j = Array.length t.table.(i) alors vrai
      sinon
        filtre t.table.(i).(j).elem avec
          Nothing -> loop (j + 1)
        | e -> si phony e alors loop (j + 1) sinon faux
    dans
    loop 0
  dans
  soit line_elem_txt i =
    soit les =
      soit rec loop les j =
        si j = Array.length t.table.(i) alors les
        sinon
          soit x = t.table.(i).(j) dans
          soit next_j =
            soit rec loop j =
              si j = Array.length t.table.(i) alors j
              sinon si t.table.(i).(j) = x alors loop (j + 1)
              sinon j
            dans
            loop (j + 1)
          dans
          soit colspan = 3 * (next_j - j) dans
          soit les = (1, LeftA, TDstring "&nbsp;") :: les dans
          soit les =
            soit s =
              si t.table.(i).(j).elem = Nothing alors "&nbsp;"
              sinon elem_txt t.table.(i).(j).elem
            dans
            (colspan - 2, CenterA, TDstring s) :: les
          dans
          soit les = (1, LeftA, TDstring "&nbsp;") :: les dans loop les next_j
      dans
      loop [] 0
    dans
    Array.of_list (List.rev les)
  dans
  soit vbars_txt k i =
    soit les =
      soit rec loop les j =
        si j = Array.length t.table.(i) alors les
        sinon
          soit x = t.table.(i).(j) dans
          soit next_j =
            soit rec loop j =
              si j = Array.length t.table.(i) alors j
              sinon si t.table.(i).(j) = x alors loop (j + 1)
              sinon j
            dans
            loop (j + 1)
          dans
          soit colspan = 3 * (next_j - j) dans
          soit les = (1, LeftA, TDstring "&nbsp;") :: les dans
          soit les =
            soit s =
              si k > 0 && t.table.(k - 1).(j).elem = Nothing ||
                 t.table.(k).(j).elem = Nothing alors
                "&nbsp;"
              sinon si phony t.table.(i).(j).elem alors "&nbsp;"
              sinon bar_txt t.table.(i).(j).elem
            dans
            (colspan - 2, CenterA, TDstring s) :: les
          dans
          soit les = (1, LeftA, TDstring "&nbsp;") :: les dans loop les next_j
      dans
      loop [] 0
    dans
    Array.of_list (List.rev les)
  dans
  soit alone_bar_txt i =
    soit les =
      soit rec loop les j =
        si j = Array.length t.table.(i) alors les
        sinon
          soit next_j =
            soit x = t.table.(i).(j).span dans
            soit rec loop j =
              si j = Array.length t.table.(i) alors j
              sinon si t.table.(i).(j).span = x alors loop (j + 1)
              sinon j
            dans
            loop (j + 1)
          dans
          soit colspan = 3 * (next_j - j) - 2 dans
          soit les = (1, LeftA, TDstring "&nbsp;") :: les dans
          soit les =
            si t.table.(i).(j).elem = Nothing ||
               t.table.(i + 1).(j).elem = Nothing alors
              (colspan, LeftA, TDstring "&nbsp;") :: les
            sinon
              soit s =
                soit all_ph =
                  soit rec loop j =
                    si j = next_j alors vrai
                    sinon si phony t.table.(i + 1).(j).elem alors loop (j + 1)
                    sinon faux
                  dans
                  loop j
                dans
                si all_ph alors "&nbsp;" sinon "|"
              dans
              (colspan, CenterA, TDstring s) :: les
          dans
          soit les = (1, LeftA, TDstring "&nbsp;") :: les dans loop les next_j
      dans
      loop [] 0
    dans
    Array.of_list (List.rev les)
  dans
  soit exist_several_branches i k =
    soit rec loop j =
      si j = Array.length t.table.(i) alors faux
      sinon
        soit x = t.table.(i).(j).span dans
        soit e = t.table.(k).(j).elem dans
        soit rec loop1 j =
          si j = Array.length t.table.(i) alors faux
          sinon si t.table.(i).(j).elem = Nothing alors loop j
          sinon si t.table.(i).(j).span <> x alors loop j
          sinon si t.table.(k).(j).elem <> e alors vrai
          sinon loop1 (j + 1)
        dans
        loop1 (j + 1)
    dans
    loop 0
  dans
  soit hbars_txt i k =
    soit les =
      soit rec loop les j =
        si j = Array.length t.table.(i) alors les
        sinon
          soit next_j =
            soit e = t.table.(i).(j).elem dans
            soit x = t.table.(i).(j).span dans
            soit rec loop j =
              si j = Array.length t.table.(i) alors j
              sinon si e = Nothing && t.table.(i).(j).elem = Nothing alors
                loop (j + 1)
              sinon si t.table.(i).(j).span = x alors loop (j + 1)
              sinon j
            dans
            loop (j + 1)
          dans
          soit rec loop1 les l =
            si l = next_j alors loop les next_j
            sinon
              soit next_l =
                soit y = t.table.(k).(l) dans
                filtre y.elem avec
                  Elem _ | Ghost _ ->
                    soit rec loop l =
                      si l = Array.length t.table.(i) alors l
                      sinon si t.table.(k).(l) = y alors loop (l + 1)
                      sinon l
                    dans
                    loop (l + 1)
                | _ -> l + 1
              dans
              si next_l > next_j alors
                début
                  Printf.eprintf
                    "assert false i %d k %d l %d next_l %d next_j %d\n" i k l
                    next_l next_j;
                  flush stderr
                fin;
              soit next_l = min next_l next_j dans
              soit colspan = 3 * (next_l - l) - 2 dans
              soit les =
                filtre t.table.(i).(l).elem, t.table.(i + 1).(l).elem avec
                  Nothing, _ | _, Nothing ->
                    (colspan + 2, LeftA, TDstring "&nbsp;") :: les
                | _ ->
                    soit ph s =
                      si phony t.table.(k).(l).elem alors TDstring "&nbsp;"
                      sinon s
                    dans
                    si l = j && next_l = next_j alors
                      soit les = (1, LeftA, TDstring "&nbsp;") :: les dans
                      soit s = ph (TDstring "|") dans
                      soit les = (colspan, CenterA, s) :: les dans
                      soit les = (1, LeftA, TDstring "&nbsp;") :: les dans les
                    sinon si l = j alors
                      soit les = (1, LeftA, TDstring "&nbsp;") :: les dans
                      soit s = ph (TDhr RightA) dans
                      soit les = (colspan, RightA, s) :: les dans
                      soit s = ph (TDhr CenterA) dans
                      soit les = (1, LeftA, s) :: les dans les
                    sinon si next_l = next_j alors
                      soit s = ph (TDhr CenterA) dans
                      soit les = (1, LeftA, s) :: les dans
                      soit s = ph (TDhr LeftA) dans
                      soit les = (colspan, LeftA, s) :: les dans
                      soit les = (1, LeftA, TDstring "&nbsp;") :: les dans les
                    sinon
                      soit s = ph (TDhr CenterA) dans
                      (colspan + 2, LeftA, s) :: les
              dans
              loop1 les next_l
          dans
          loop1 les j
      dans
      loop [] 0
    dans
    Array.of_list (List.rev les)
  dans
  soit hts =
    soit rec loop hts i =
      si i = Array.length t.table alors hts
      sinon si i = Array.length t.table - 1 && all_empty i alors hts
      sinon
        soit hts = line_elem_txt i :: hts dans
        soit hts =
          si i < Array.length t.table - 1 alors
            soit hts = vbars_txt (i + 1) i :: hts dans
            soit hts =
              si exist_several_branches i i alors
                alone_bar_txt i :: hbars_txt i i :: hts
              sinon hts
            dans
            soit hts =
              si exist_several_branches i (i + 1) &&
                 (i < Array.length t.table - 2 ||
                  not (all_empty (i + 1))) alors
                vbars_txt (i + 1) (i + 1) :: hbars_txt i (i + 1) :: hts
              sinon hts
            dans
            hts
          sinon hts
        dans
        loop hts (i + 1)
    dans
    loop [] 0
  dans
  Array.of_list (List.rev hts)
;;

(** transforming dag into table *)

soit ancestors d =
  soit rec loop i =
    si i = Array.length d.dag alors []
    sinon
      soit n = d.dag.(i) dans
      si n.pare = [] alors idag_of_int i :: loop (i + 1) sinon loop (i + 1)
  dans
  loop 0
;;

soit get_children d parents =
  soit rec merge_children children el =
    List.fold_right
      (fonc (x, _) children ->
         filtre x avec
           Elem e ->
             soit e = d.dag.(int_of_idag e) dans
             List.fold_right
               (fonc c children ->
                  si List.mem c children alors children sinon c :: children)
               e.chil children
         | _ -> [])
      el children
  dans
  merge_children [] parents
;;

soit rec get_block t i j =
  si j = Array.length t.table.(i) alors None
  sinon si j = Array.length t.table.(i) - 1 alors
    soit x = t.table.(i).(j) dans Some ([x.elem, 1], 1, x.span)
  sinon
    soit x = t.table.(i).(j) dans
    soit y = t.table.(i).(j + 1) dans
    si y.span = x.span alors
      filtre get_block t i (j + 1) avec
        Some ((x1, c1) :: list, mpc, span) ->
          soit (list, mpc) =
            si x1 = x.elem alors (x1, c1 + 1) :: list, max mpc (c1 + 1)
            sinon (x.elem, 1) :: (x1, c1) :: list, max mpc c1
          dans
          Some (list, mpc, span)
      | _ -> affirme faux
    sinon Some ([x.elem, 1], 1, x.span)
;;

soit group_by_common_children d list =
  soit module O = struct type t = idag;; soit compare (x:t) y = compare x y;; fin
  dans
  soit module S = Set.Make (O)
  dans
  soit nlcsl =
    List.map
      (fonc id ->
         soit n = d.dag.(int_of_idag id) dans
         soit cs = List.fold_right S.add n.chil S.empty dans [id], cs)
      list
  dans
  soit nlcsl =
    soit rec loop =
      fonction
        [] -> []
      | (nl, cs) :: rest ->
          soit rec loop1 beg =
            fonction
              (nl1, cs1) :: rest1 ->
                si S.is_empty (S.inter cs cs1) alors
                  loop1 ((nl1, cs1) :: beg) rest1
                sinon
                  loop ((nl @ nl1, S.union cs cs1) :: (List.rev beg @ rest1))
            | [] -> (nl, cs) :: loop rest
          dans
          loop1 [] rest
    dans
    loop nlcsl
  dans
  List.fold_right
    (fonc (nl, _) a ->
       soit span = new_span_id () dans
       List.fold_right (fonc n a -> {elem = Elem n; span = span} :: a) nl a)
    nlcsl []
;;

soit copy_data d = {elem = d.elem; span = d.span};;

soit insert_columns t nb j =
  soit t1 = Array.create (Array.length t.table) [| |] dans
  pour i = 0 à Array.length t.table - 1 faire
    soit line = t.table.(i) dans
    soit line1 = Array.create (Array.length line + nb) line.(0) dans
    t1.(i) <- line1;
    soit rec loop k =
      si k = Array.length line alors ()
      sinon
        début
          si k < j alors line1.(k) <- copy_data line.(k)
          sinon si k = j alors
            pour r = 0 à nb faire line1.(k + r) <- copy_data line.(k) fait
          sinon line1.(k + nb) <- copy_data line.(k);
          loop (k + 1)
        fin
    dans
    loop 0
  fait;
  {table = t1}
;;

soit rec gcd a b =
  si a < b alors gcd b a sinon si b = 0 alors a sinon gcd b (a mod b)
;;

soit treat_new_row d t =
  soit i = Array.length t.table - 1 dans
  soit rec loop t i j =
    filtre get_block t i j avec
      Some (parents, max_parent_colspan, span) ->
        soit children = get_children d parents dans
        soit children =
          si children = [] alors [{elem = Nothing; span = new_span_id ()}]
          sinon
            List.map (fonc n -> {elem = Elem n; span = new_span_id ()})
              children
        dans
        soit simple_parents_colspan =
          List.fold_left (fonc x (_, c) -> x + c) 0 parents
        dans
        si simple_parents_colspan mod List.length children = 0 alors
          soit j = j + simple_parents_colspan dans
          soit children =
            soit cnt = simple_parents_colspan / List.length children dans
            List.fold_right
              (fonc d list ->
                 soit rec loop cnt list =
                   si cnt = 1 alors d :: list
                   sinon copy_data d :: loop (cnt - 1) list
                 dans
                 loop cnt list)
              children []
          dans
          soit (t, children_rest) = loop t i j dans t, children @ children_rest
        sinon
          soit parent_colspan =
            List.fold_left
              (fonc scm (_, c) -> soit g = gcd scm c dans scm / g * c)
              max_parent_colspan parents
          dans
          soit (t, parents, _) =
            List.fold_left
              (fonc (t, parents, j) (x, c) ->
                 soit to_add = parent_colspan / c - 1 dans
                 soit t =
                   soit rec loop cc t j =
                     si cc = 0 alors t
                     sinon
                       soit t = insert_columns t to_add j dans
                       loop (cc - 1) t (j + to_add + 1)
                   dans
                   loop c t j
                 dans
                 t, (x, parent_colspan) :: parents, j + parent_colspan)
              (t, [], j) parents
          dans
          soit parents = List.rev parents dans
          soit parents_colspan = parent_colspan * List.length parents dans
          soit children_colspan = List.length children dans
          soit g = gcd parents_colspan children_colspan dans
          soit (t, j) =
            soit cnt = children_colspan / g dans
            List.fold_left
              (fonc (t, j) (_, c) ->
                 soit rec loop cc t j =
                   si cc = 0 alors t, j
                   sinon
                     soit t = insert_columns t (cnt - 1) j dans
                     soit j = j + cnt dans loop (cc - 1) t j
                 dans
                 loop c t j)
              (t, j) parents
          dans
          soit children =
            soit cnt = parents_colspan / g dans
            List.fold_right
              (fonc d list ->
                 soit rec loop cnt list =
                   si cnt = 0 alors list sinon d :: loop (cnt - 1) list
                 dans
                 loop cnt list)
              children []
          dans
          soit (t, children_rest) = loop t i j dans t, children @ children_rest
    | None -> t, []
  dans
  loop t i 0
;;

soit down_it t i k y =
  t.table.(Array.length t.table - 1).(k) <- t.table.(i).(k);
  pour r = i à Array.length t.table - 2 faire
    t.table.(r).(k) <- {elem = Ghost (new_ghost_id ()); span = new_span_id ()}
  fait
;;

(* equilibrate:
   in the last line, for all elem A, make fall all As, which are located at
   its right side above, to its line,
                             A             |
   i.e. transform all        . into        |
                      A.......      A......A
*)

soit equilibrate t =
  soit ilast = Array.length t.table - 1 dans
  soit last = t.table.(ilast) dans
  soit len = Array.length last dans
  soit rec loop j =
    si j = len alors ()
    sinon
      filtre last.(j).elem avec
        Elem x ->
          soit rec loop1 i =
            si i = ilast alors loop (j + 1)
            sinon
              soit rec loop2 k =
                si k = len alors loop1 (i + 1)
                sinon
                  filtre t.table.(i).(k).elem avec
                    Elem y quand x = y -> down_it t i k y; loop 0
                  | _ -> loop2 (k + 1)
              dans
              loop2 0
          dans
          loop1 0
      | _ -> loop (j + 1)
  dans
  loop 0
;;

(* group_elem:
   transform all x y into x x
                 A A      A A *)

soit group_elem t =
  pour i = 0 à Array.length t.table - 2 faire
    pour j = 1 à Array.length t.table.(0) - 1 faire
      filtre t.table.(i + 1).(j - 1).elem, t.table.(i + 1).(j).elem avec
        Elem x, Elem y quand x = y ->
          t.table.(i).(j).span <- t.table.(i).(j - 1).span
      | _ -> ()
    fait
  fait
;;

(* group_ghost:
                 x  x       x  x           |a |a      |a |a
   transform all |a |b into |a |a and all  x  y  into x  x
                 y  z       y  y           A  A       A  A  *)

soit group_ghost t =
  pour i = 0 à Array.length t.table - 2 faire
    pour j = 1 à Array.length t.table.(0) - 1 faire
      début filtre t.table.(i + 1).(j - 1).elem, t.table.(i + 1).(j).elem avec
        Ghost x, Ghost _ ->
          si t.table.(i).(j - 1).span = t.table.(i).(j).span alors
            t.table.(i + 1).(j) <-
              {elem = Ghost x; span = t.table.(i + 1).(j - 1).span}
      | _ -> ()
      fin;
      filtre t.table.(i).(j - 1).elem, t.table.(i).(j).elem avec
        Ghost x, Ghost _ ->
          si t.table.(i + 1).(j - 1).elem = t.table.(i + 1).(j).elem alors
            début
              t.table.(i).(j) <-
                {elem = Ghost x; span = t.table.(i).(j - 1).span};
              si i > 0 alors
                t.table.(i - 1).(j).span <- t.table.(i - 1).(j - 1).span
            fin
      | _ -> ()
    fait
  fait
;;

(* group_children:
   transform all A A into A A
                 x y      x x *)

soit group_children t =
  pour i = 0 à Array.length t.table - 1 faire
    soit line = t.table.(i) dans
    soit len = Array.length line dans
    pour j = 1 à len - 1 faire
      si line.(j).elem = line.(j - 1).elem && line.(j).elem <> Nothing alors
        line.(j).span <- line.(j - 1).span
    fait
  fait
;;

(* group_span_by_common_children:
   in the last line, transform all
     A B into A B
     x y      x x
   if A and B have common children *)

soit group_span_by_common_children d t =
  soit module O = struct type t = idag;; soit compare (x:t) y = compare x y;; fin
  dans
  soit module S = Set.Make (O)
  dans
  soit i = Array.length t.table - 1 dans
  soit line = t.table.(i) dans
  soit rec loop j cs =
    si j = Array.length line alors ()
    sinon
      filtre line.(j).elem avec
        Elem id ->
          soit n = d.dag.(int_of_idag id) dans
          soit curr_cs = List.fold_right S.add n.chil S.empty dans
          si S.is_empty (S.inter cs curr_cs) alors loop (j + 1) curr_cs
          sinon
            début
              line.(j).span <- line.(j - 1).span;
              loop (j + 1) (S.union cs curr_cs)
            fin
      | _ -> loop (j + 1) S.empty
  dans
  loop 0 S.empty
;;

soit find_same_parents t i j1 j2 j3 j4 =
  soit rec loop i j1 j2 j3 j4 =
    si i = 0 alors i, j1, j2, j3, j4
    sinon
      soit x1 = t.(i - 1).(j1) dans
      soit x2 = t.(i - 1).(j2) dans
      soit x3 = t.(i - 1).(j3) dans
      soit x4 = t.(i - 1).(j4) dans
      si x1.span = x4.span alors i, j1, j2, j3, j4
      sinon
        soit j1 =
          soit rec loop j =
            si j < 0 alors 0
            sinon si t.(i - 1).(j).span = x1.span alors loop (j - 1)
            sinon j + 1
          dans
          loop (j1 - 1)
        dans
        soit j2 =
          soit rec loop j =
            si j >= Array.length t.(i) alors j - 1
            sinon si t.(i - 1).(j).span = x2.span alors loop (j + 1)
            sinon j - 1
          dans
          loop (j2 + 1)
        dans
        soit j3 =
          soit rec loop j =
            si j < 0 alors 0
            sinon si t.(i - 1).(j).span = x3.span alors loop (j - 1)
            sinon j + 1
          dans
          loop (j3 - 1)
        dans
        soit j4 =
          soit rec loop j =
            si j >= Array.length t.(i) alors j - 1
            sinon si t.(i - 1).(j).span = x4.span alors loop (j + 1)
            sinon j - 1
          dans
          loop (j4 + 1)
        dans
        loop (i - 1) j1 j2 j3 j4
  dans
  loop i j1 j2 j3 j4
;;

soit find_linked_children t i j1 j2 j3 j4 =
  soit rec loop i j1 j2 j3 j4 =
    si i = Array.length t - 1 alors j1, j2, j3, j4
    sinon
      soit x1 = t.(i).(j1) dans
      soit x2 = t.(i).(j2) dans
      soit x3 = t.(i).(j3) dans
      soit x4 = t.(i).(j4) dans
      soit j1 =
        soit rec loop j =
          si j < 0 alors 0
          sinon si t.(i).(j).span = x1.span alors loop (j - 1)
          sinon j + 1
        dans
        loop (j1 - 1)
      dans
      soit j2 =
        soit rec loop j =
          si j >= Array.length t.(i) alors j - 1
          sinon si t.(i).(j).span = x2.span alors loop (j + 1)
          sinon j - 1
        dans
        loop (j2 + 1)
      dans
      soit j3 =
        soit rec loop j =
          si j < 0 alors 0
          sinon si t.(i).(j).span = x3.span alors loop (j - 1)
          sinon j + 1
        dans
        loop (j3 - 1)
      dans
      soit j4 =
        soit rec loop j =
          si j >= Array.length t.(i) alors j - 1
          sinon si t.(i).(j).span = x4.span alors loop (j + 1)
          sinon j - 1
        dans
        loop (j4 + 1)
      dans
      loop (i + 1) j1 j2 j3 j4
  dans
  loop i j1 j2 j3 j4
;;

soit mirror_block t i1 i2 j1 j2 =
  pour i = i1 à i2 faire
    soit line = t.(i) dans
    soit rec loop j1 j2 =
      si j1 >= j2 alors ()
      sinon
        soit v = line.(j1) dans
        line.(j1) <- line.(j2); line.(j2) <- v; loop (j1 + 1) (j2 - 1)
    dans
    loop j1 j2
  fait
;;

soit exch_blocks t i1 i2 j1 j2 j3 j4 =
  pour i = i1 à i2 faire
    soit line = t.(i) dans
    soit saved = Array.copy line dans
    pour j = j1 à j2 faire line.(j4 - j2 + j) <- saved.(j) fait;
    pour j = j3 à j4 faire line.(j1 - j3 + j) <- saved.(j) fait
  fait
;;

soit find_block_with_parents t i jj1 jj2 jj3 jj4 =
  soit rec loop ii jj1 jj2 jj3 jj4 =
    soit (nii, njj1, njj2, njj3, njj4) =
      find_same_parents t i jj1 jj2 jj3 jj4
    dans
    si nii <> ii || njj1 <> jj1 || njj2 <> jj2 || njj3 <> jj3 ||
       njj4 <> jj4 alors
      soit nii = min ii nii dans
      soit (jj1, jj2, jj3, jj4) =
        find_linked_children t nii njj1 njj2 njj3 njj4
      dans
      si njj1 <> jj1 || njj2 <> jj2 || njj3 <> jj3 || njj4 <> jj4 alors
        loop nii jj1 jj2 jj3 jj4
      sinon nii, jj1, jj2, jj3, jj4
    sinon ii, jj1, jj2, jj3, jj4
  dans
  loop i jj1 jj2 jj3 jj4
;;

soit push_to_right d t i j1 j2 =
  soit line = t.(i) dans
  soit rec loop j =
    si j = j2 alors j - 1
    sinon
      soit ini_jj1 =
        filtre line.(j - 1).elem avec
          Nothing -> j - 1
        | x ->
            soit rec same_value j =
              si j < 0 alors 0
              sinon si line.(j).elem = x alors same_value (j - 1)
              sinon j + 1
            dans
            same_value (j - 2)
      dans
      soit jj1 = ini_jj1 dans
      soit jj2 = j - 1 dans
      soit jj3 = j dans
      soit jj4 =
        filtre line.(j).elem avec
          Nothing -> j
        | x ->
            soit rec same_value j =
              si j >= Array.length line alors j - 1
              sinon si line.(j).elem = x alors same_value (j + 1)
              sinon j - 1
            dans
            same_value (j + 1)
      dans
      soit (ii, jj1, jj2, jj3, jj4) =
        find_block_with_parents t i jj1 jj2 jj3 jj4
      dans
      si jj4 < j2 && jj2 < jj3 alors
        début exch_blocks t ii i jj1 jj2 jj3 jj4; loop (jj4 + 1) fin
      sinon si jj4 < j2 && jj1 = ini_jj1 && jj2 <= jj4 alors
        début mirror_block t ii i jj1 jj4; loop (jj4 + 1) fin
      sinon j - 1
  dans
  loop (j1 + 1)
;;

soit push_to_left d t i j1 j2 =
  soit line = t.(i) dans
  soit rec loop j =
    si j = j1 alors j + 1
    sinon
      soit jj1 =
        filtre line.(j).elem avec
          Nothing -> j
        | x ->
            soit rec same_value j =
              si j < 0 alors 0
              sinon si line.(j).elem = x alors same_value (j - 1)
              sinon j + 1
            dans
            same_value (j - 1)
      dans
      soit jj2 = j dans
      soit jj3 = j + 1 dans
      soit ini_jj4 =
        filtre line.(j + 1).elem avec
          Nothing -> j + 1
        | x ->
            soit rec same_value j =
              si j >= Array.length line alors j - 1
              sinon si line.(j).elem = x alors same_value (j + 1)
              sinon j - 1
            dans
            same_value (j + 2)
      dans
      soit jj4 = ini_jj4 dans
      soit (ii, jj1, jj2, jj3, jj4) =
        find_block_with_parents t i jj1 jj2 jj3 jj4
      dans
      si jj1 > j1 && jj2 < jj3 alors
        début exch_blocks t ii i jj1 jj2 jj3 jj4; loop (jj1 - 1) fin
      sinon si jj1 > j1 && jj4 = ini_jj4 && jj3 >= jj1 alors
        début mirror_block t ii i jj1 jj4; loop (jj1 - 1) fin
      sinon j + 1
  dans
  loop (j2 - 1)
;;

soit fill_gap d t i j1 j2 =
  soit t1 =
    soit t1 = Array.copy t.table dans
    pour i = 0 à Array.length t.table - 1 faire
      t1.(i) <- Array.copy t.table.(i);
      pour j = 0 à Array.length t1.(i) - 1 faire
        t1.(i).(j) <- copy_data t.table.(i).(j)
      fait
    fait;
    t1
  dans
  soit j2 = push_to_left d t1 i j1 j2 dans
  soit j1 = push_to_right d t1 i j1 j2 dans
  si j1 = j2 - 1 alors
    soit line = t1.(i - 1) dans
    soit x = line.(j1).span dans
    soit y = line.(j2).span dans
    soit rec loop y j =
      si j >= Array.length line alors ()
      sinon si line.(j).span = y || t1.(i).(j).elem = t1.(i).(j - 1).elem alors
        soit y = line.(j).span dans
        line.(j).span <- x;
        si i > 0 alors t1.(i - 1).(j).span <- t1.(i - 1).(j - 1).span;
        loop y (j + 1)
    dans
    loop y j2; Some ({table = t1}, vrai)
  sinon None
;;

soit treat_gaps d t =
  soit i = Array.length t.table - 1 dans
  soit rec loop t j =
    soit line = t.table.(i) dans
    si j = Array.length line alors t
    sinon
      filtre line.(j).elem avec
        Elem _ tel y ->
          si y = line.(j - 1).elem alors loop t (j + 1)
          sinon
            soit rec loop1 t j1 =
              si j1 < 0 alors loop t (j + 1)
              sinon si y = line.(j1).elem alors
                filtre fill_gap d t i j1 j avec
                  Some (t, ok) -> si ok alors loop t 2 sinon loop t (j + 1)
                | None -> loop t (j + 1)
              sinon loop1 t (j1 - 1)
            dans
            loop1 t (j - 2)
      | _ -> loop t (j + 1)
  dans
  si Array.length t.table.(i) = 1 alors t sinon loop t 2
;;

soit group_span_last_row t =
  soit row = t.table.(Array.length t.table - 1) dans
  soit rec loop i =
    si i >= Array.length row alors ()
    sinon
      début
        début filtre row.(i).elem avec
          Elem _ | Ghost _ tel x ->
            si x = row.(i - 1).elem alors row.(i).span <- row.(i - 1).span
        | _ -> ()
        fin;
        loop (i + 1)
      fin
  dans
  loop 1
;;

soit has_phony_children phony d t =
  soit line = t.table.(Array.length t.table - 1) dans
  soit rec loop j =
    si j = Array.length line alors faux
    sinon
      filtre line.(j).elem avec
        Elem x -> si phony d.dag.(int_of_idag x) alors vrai sinon loop (j + 1)
      | _ -> loop (j + 1)
  dans
  loop 0
;;

soit tablify phony no_optim no_group d =
  soit a = ancestors d dans
  soit r = group_by_common_children d a dans
  soit t = {table = [| Array.of_list r |]} dans
  soit rec loop t =
    soit (t, new_row) = treat_new_row d t dans
    si List.for_all (fonc x -> x.elem = Nothing) new_row alors t
    sinon
      soit t = {table = Array.append t.table [| Array.of_list new_row |]} dans
      soit t =
        si no_group && not (has_phony_children phony d t) alors t
        sinon
          soit _ = si no_optim alors () sinon equilibrate t dans
          soit _ = group_elem t dans
          soit _ = group_ghost t dans
          soit _ = group_children t dans
          soit _ = group_span_by_common_children d t dans
          soit t = si no_optim alors t sinon treat_gaps d t dans
          soit _ = group_span_last_row t dans t
      dans
      loop t
  dans
  loop t
;;

soit fall d t =
  pour i = 1 à Array.length t.table - 1 faire
    soit line = t.table.(i) dans
    soit rec loop j =
      si j = Array.length line alors ()
      sinon
        filtre line.(j).elem avec
          Ghost x ->
            soit j2 =
              soit rec loop j =
                si j = Array.length line alors j - 1
                sinon
                  filtre line.(j).elem avec
                    Ghost y quand y = x -> loop (j + 1)
                  | _ -> j - 1
              dans
              loop (j + 1)
            dans
            soit i1 =
              soit rec loop i =
                si i < 0 alors i + 1
                sinon
                  soit line = t.table.(i) dans
                  si (j = 0 || line.(j - 1).span <> line.(j).span) &&
                     (j2 = Array.length line - 1 ||
                      line.(j2 + 1).span <> line.(j2).span) alors
                    loop (i - 1)
                  sinon i + 1
              dans
              loop (i - 1)
            dans
            soit i1 =
              si i1 = i alors i1
              sinon si i1 = 0 alors i1
              sinon si t.table.(i1).(j).elem = Nothing alors i1
              sinon i
            dans
            si i1 < i alors
              début
                pour k = i descendant_jusqu'a i1 + 1 faire
                  pour j = j à j2 faire
                    t.table.(k).(j).elem <- t.table.(k - 1).(j).elem;
                    si k < i alors
                      t.table.(k).(j).span <- t.table.(k - 1).(j).span
                  fait
                fait;
                pour l = j à j2 faire
                  si i1 = 0 || t.table.(i1 - 1).(l).elem = Nothing alors
                    t.table.(i1).(l).elem <- Nothing
                  sinon
                    t.table.(i1).(l) <-
                      si l = j ||
                         t.table.(i1 - 1).(l - 1).span <>
                           t.table.(i1 - 1).(l).span alors
                        {elem = Ghost (new_ghost_id ());
                         span = new_span_id ()}
                      sinon copy_data t.table.(i1).(l - 1)
                fait
              fin;
            loop (j2 + 1)
        | _ -> loop (j + 1)
    dans
    loop 0
  fait
;;

soit fall2_cool_right t i1 i2 i3 j1 j2 =
  soit span = t.table.(i2 - 1).(j1).span dans
  pour i = i2 - 1 descendant_jusqu'a 0 faire
    pour j = j1 à j2 - 1 faire
      t.table.(i).(j) <-
        si i - i2 + i1 >= 0 alors t.table.(i - i2 + i1).(j)
        sinon {elem = Nothing; span = new_span_id ()}
    fait
  fait;
  pour i = Array.length t.table - 1 descendant_jusqu'a 0 faire
    pour j = j2 à Array.length t.table.(i) - 1 faire
      t.table.(i).(j) <-
        si i - i2 + i1 >= 0 alors t.table.(i - i2 + i1).(j)
        sinon {elem = Nothing; span = new_span_id ()}
    fait
  fait;
  soit old_span = t.table.(i2 - 1).(j1).span dans
  soit rec loop j =
    si j = Array.length t.table.(i2 - 1) alors ()
    sinon si t.table.(i2 - 1).(j).span = old_span alors
      début t.table.(i2 - 1).(j).span <- span; loop (j + 1) fin
  dans
  loop j1
;;

soit fall2_cool_left t i1 i2 i3 j1 j2 =
  soit span = t.table.(i2 - 1).(j2).span dans
  pour i = i2 - 1 descendant_jusqu'a 0 faire
    pour j = j1 + 1 à j2 faire
      t.table.(i).(j) <-
        si i - i2 + i1 >= 0 alors t.table.(i - i2 + i1).(j)
        sinon {elem = Nothing; span = new_span_id ()}
    fait
  fait;
  pour i = Array.length t.table - 1 descendant_jusqu'a 0 faire
    pour j = j1 descendant_jusqu'a 0 faire
      t.table.(i).(j) <-
        si i - i2 + i1 >= 0 alors t.table.(i - i2 + i1).(j)
        sinon {elem = Nothing; span = new_span_id ()}
    fait
  fait;
  soit old_span = t.table.(i2 - 1).(j2).span dans
  soit rec loop j =
    si j < 0 alors ()
    sinon si t.table.(i2 - 1).(j).span = old_span alors
      début t.table.(i2 - 1).(j).span <- span; loop (j - 1) fin
  dans
  loop j2
;;

soit do_fall2_right t i1 i2 j1 j2 =
  soit i3 =
    soit rec loop_i i =
      si i < 0 alors 0
      sinon
        soit rec loop_j j =
          si j = Array.length t.table.(i) alors loop_i (i - 1)
          sinon
            filtre t.table.(i).(j).elem avec
              Nothing -> loop_j (j + 1)
            | _ -> i + 1
        dans
        loop_j j2
    dans
    loop_i (Array.length t.table - 1)
  dans
  soit new_height = i3 + i2 - i1 dans
  soit t =
    si new_height > Array.length t.table alors
      soit rec loop cnt t =
        si cnt = 0 alors t
        sinon
          soit new_line =
            Array.init (Array.length t.table.(0))
              (fonc i -> {elem = Nothing; span = new_span_id ()})
          dans
          soit t = {table = Array.append t.table [| new_line |]} dans
          loop (cnt - 1) t
      dans
      loop (new_height - Array.length t.table) t
    sinon t
  dans
  fall2_cool_right t i1 i2 i3 j1 j2; t
;;

soit do_fall2_left t i1 i2 j1 j2 =
  soit i3 =
    soit rec loop_i i =
      si i < 0 alors 0
      sinon
        soit rec loop_j j =
          si j < 0 alors loop_i (i - 1)
          sinon
            filtre t.table.(i).(j).elem avec
              Nothing -> loop_j (j - 1)
            | _ -> i + 1
        dans
        loop_j j1
    dans
    loop_i (Array.length t.table - 1)
  dans
  soit new_height = i3 + i2 - i1 dans
  soit t =
    si new_height > Array.length t.table alors
      soit rec loop cnt t =
        si cnt = 0 alors t
        sinon
          soit new_line =
            Array.init (Array.length t.table.(0))
              (fonc i -> {elem = Nothing; span = new_span_id ()})
          dans
          soit t = {table = Array.append t.table [| new_line |]} dans
          loop (cnt - 1) t
      dans
      loop (new_height - Array.length t.table) t
    sinon t
  dans
  fall2_cool_left t i1 i2 i3 j1 j2; t
;;

soit do_shorten_too_long t i1 j1 j2 =
  pour i = i1 à Array.length t.table - 2 faire
    pour j = j1 à j2 - 1 faire t.table.(i).(j) <- t.table.(i + 1).(j) fait
  fait;
  soit i = Array.length t.table - 1 dans
  pour j = j1 à j2 - 1 faire
    t.table.(i).(j) <- {elem = Nothing; span = new_span_id ()}
  fait;
  t
;;

soit try_fall2_right t i j =
  filtre t.table.(i).(j).elem avec
    Ghost _ ->
      soit i1 =
        soit rec loop i =
          si i < 0 alors 0
          sinon
            filtre t.table.(i).(j).elem avec
              Ghost _ -> loop (i - 1)
            | _ -> i + 1
        dans
        loop (i - 1)
      dans
      soit separated1 =
        soit rec loop i =
          si i < 0 alors vrai
          sinon si
            j > 0 && t.table.(i).(j - 1).span = t.table.(i).(j).span alors
            faux
          sinon loop (i - 1)
        dans
        loop (i1 - 1)
      dans
      soit j2 =
        soit x = t.table.(i).(j).span dans
        soit rec loop j2 =
          si j2 = Array.length t.table.(i) alors j2
          sinon
            filtre t.table.(i).(j2) avec
              {elem = Ghost _; span = y} quand y = x -> loop (j2 + 1)
            | _ -> j2
        dans
        loop (j + 1)
      dans
      soit separated2 =
        soit rec loop i =
          si i = Array.length t.table alors vrai
          sinon si j2 = Array.length t.table.(i) alors faux
          sinon si t.table.(i).(j2 - 1).span = t.table.(i).(j2).span alors faux
          sinon loop (i + 1)
        dans
        loop (i + 1)
      dans
      si not separated1 || not separated2 alors None
      sinon Some (do_fall2_right t i1 (i + 1) j j2)
  | _ -> None
;;

soit try_fall2_left t i j =
  filtre t.table.(i).(j).elem avec
    Ghost _ ->
      soit i1 =
        soit rec loop i =
          si i < 0 alors 0
          sinon
            filtre t.table.(i).(j).elem avec
              Ghost _ -> loop (i - 1)
            | _ -> i + 1
        dans
        loop (i - 1)
      dans
      soit separated1 =
        soit rec loop i =
          si i < 0 alors vrai
          sinon si
            j < Array.length t.table.(i) - 1 &&
            t.table.(i).(j).span = t.table.(i).(j + 1).span alors
            faux
          sinon loop (i - 1)
        dans
        loop (i1 - 1)
      dans
      soit j1 =
        soit x = t.table.(i).(j).span dans
        soit rec loop j1 =
          si j1 < 0 alors j1
          sinon
            filtre t.table.(i).(j1) avec
              {elem = Ghost _; span = y} quand y = x -> loop (j1 - 1)
            | _ -> j1
        dans
        loop (j - 1)
      dans
      soit separated2 =
        soit rec loop i =
          si i = Array.length t.table alors vrai
          sinon si j1 < 0 alors faux
          sinon si t.table.(i).(j1).span = t.table.(i).(j1 + 1).span alors faux
          sinon loop (i + 1)
        dans
        loop (i + 1)
      dans
      si not separated1 || not separated2 alors None
      sinon Some (do_fall2_left t i1 (i + 1) j1 j)
  | _ -> None
;;

soit try_shorten_too_long t i j =
  filtre t.table.(i).(j).elem avec
    Ghost _ ->
      soit j2 =
        soit x = t.table.(i).(j).span dans
        soit rec loop j2 =
          si j2 = Array.length t.table.(i) alors j2
          sinon
            filtre t.table.(i).(j2) avec
              {elem = Ghost _; span = y} quand y = x -> loop (j2 + 1)
            | _ -> j2
        dans
        loop (j + 1)
      dans
      soit i1 =
        soit rec loop i =
          si i = Array.length t.table alors i
          sinon
            filtre t.table.(i).(j).elem avec
              Elem _ -> loop (i + 1)
            | _ -> i
        dans
        loop (i + 1)
      dans
      soit i2 =
        soit rec loop i =
          si i = Array.length t.table alors i
          sinon
            filtre t.table.(i).(j).elem avec
              Nothing -> loop (i + 1)
            | _ -> i
        dans
        loop i1
      dans
      soit separated_left =
        soit rec loop i =
          si i = i2 alors vrai
          sinon si
            j > 0 && t.table.(i).(j).span = t.table.(i).(j - 1).span alors
            faux
          sinon loop (i + 1)
        dans
        loop i
      dans
      soit separated_right =
        soit rec loop i =
          si i = i2 alors vrai
          sinon si
            j2 < Array.length t.table.(i) &&
            t.table.(i).(j2 - 1).span = t.table.(i).(j2).span alors
            faux
          sinon loop (i + 1)
        dans
        loop i
      dans
      si not separated_left || not separated_right alors None
      sinon si i2 < Array.length t.table alors None
      sinon Some (do_shorten_too_long t i j j2)
  | _ -> None
;;

soit fall2_right t =
  soit rec loop_i i t =
    si i <= 0 alors t
    sinon
      soit rec loop_j j t =
        si j < 0 alors loop_i (i - 1) t
        sinon
          filtre try_fall2_right t i j avec
            Some t -> loop_i (Array.length t.table - 1) t
          | None -> loop_j (j - 1) t
      dans
      loop_j (Array.length t.table.(i) - 2) t
  dans
  loop_i (Array.length t.table - 1) t
;;

soit fall2_left t =
  soit rec loop_i i t =
    si i <= 0 alors t
    sinon
      soit rec loop_j j t =
        si j >= Array.length t.table.(i) alors loop_i (i - 1) t
        sinon
          filtre try_fall2_left t i j avec
            Some t -> loop_i (Array.length t.table - 1) t
          | None -> loop_j (j + 1) t
      dans
      loop_j 1 t
  dans
  loop_i (Array.length t.table - 1) t
;;

soit shorten_too_long t =
  soit rec loop_i i t =
    si i <= 0 alors t
    sinon
      soit rec loop_j j t =
        si j >= Array.length t.table.(i) alors loop_i (i - 1) t
        sinon
          filtre try_shorten_too_long t i j avec
            Some t -> loop_i (Array.length t.table - 1) t
          | None -> loop_j (j + 1) t
      dans
      loop_j 1 t
  dans
  loop_i (Array.length t.table - 1) t
;;

(* top_adjust:
   deletes all empty rows that might have appeared on top of the table
   after the falls *)

soit top_adjust t =
  soit di =
    soit rec loop i =
      si i = Array.length t.table alors i
      sinon
        soit rec loop_j j =
          si j = Array.length t.table.(i) alors loop (i + 1)
          sinon si t.table.(i).(j).elem <> Nothing alors i
          sinon loop_j (j + 1)
        dans
        loop_j 0
    dans
    loop 0
  dans
  si di > 0 alors
    début
      pour i = 0 à Array.length t.table - 1 - di faire
        t.table.(i) <- t.table.(i + di)
      fait;
      {table = Array.sub t.table 0 (Array.length t.table - di)}
    fin
  sinon t
;;

(* bottom_adjust:
   deletes all empty rows that might have appeared on bottom of the table
   after the falls *)

soit bottom_adjust t =
  soit last_i =
    soit rec loop i =
      si i < 0 alors i
      sinon
        soit rec loop_j j =
          si j = Array.length t.table.(i) alors loop (i - 1)
          sinon si t.table.(i).(j).elem <> Nothing alors i
          sinon loop_j (j + 1)
        dans
        loop_j 0
    dans
    loop (Array.length t.table - 1)
  dans
  si last_i < Array.length t.table - 1 alors
    {table = Array.sub t.table 0 (last_i + 1)}
  sinon t
;;

(* invert *)

soit invert_dag d =
  soit d = {dag = Array.copy d.dag} dans
  pour i = 0 à Array.length d.dag - 1 faire
    soit n = d.dag.(i) dans
    d.dag.(i) <-
      {pare = List.map (fonc x -> x) n.chil; valu = n.valu;
       chil = List.map (fonc x -> x) n.pare}
  fait;
  d
;;

soit invert_table t =
  soit t' = {table = Array.copy t.table} dans
  soit len = Array.length t.table dans
  pour i = 0 à len - 1 faire
    t'.table.(i) <-
      Array.init (Array.length t.table.(0))
        (fonc j ->
           soit d = t.table.(len - 1 - i).(j) dans
           {elem = d.elem; span = d.span});
    si i < len - 1 alors
      pour j = 0 à Array.length t'.table.(i) - 1 faire
        t'.table.(i).(j).span <- t.table.(len - 2 - i).(j).span
      fait
  fait;
  t'
;;

(* main *)

soit table_of_dag phony no_optim invert no_group d =
  soit d = si invert alors invert_dag d sinon d dans
  soit t = tablify phony no_optim no_group d dans
  soit t = si invert alors invert_table t sinon t dans
  soit _ = fall () t dans
  soit t = fall2_right t dans
  soit t = fall2_left t dans
  soit t = shorten_too_long t dans
  soit t = top_adjust t dans soit t = bottom_adjust t dans t
;;


soit version = "1.01";;

(* input dag *)

soit strip_spaces str =
  soit start =
    soit rec loop i =
      si i == String.length str alors i
      sinon
        filtre str.[i] avec
          ' ' | '\013' | '\n' | '\t' -> loop (i + 1)
        | _ -> i
    dans
    loop 0
  dans
  soit stop =
    soit rec loop i =
      si i == -1 alors i + 1
      sinon
        filtre str.[i] avec
          ' ' | '\013' | '\n' | '\t' -> loop (i - 1)
        | _ -> i + 1
    dans
    loop (String.length str - 1)
  dans
  si start == 0 && stop == String.length str alors str
  sinon si start > stop alors ""
  sinon String.sub str start (stop - start)
;;

soit rec get_line ic =
  essaie
    soit line = input_line ic dans
    si String.length line > 0 && line.[0] = '#' alors get_line ic
    sinon Some (strip_spaces line)
  avec
    End_of_file -> None
;;

soit input_dag ic =
  soit rec find cnt s =
    fonction
      n :: nl ->
        si n.valu = s alors n, idag_of_int cnt sinon find (cnt - 1) s nl
    | [] -> raise Not_found
  dans
  soit add_node pl cl nl cnt =
    soit cl = List.rev cl dans
    soit pl = List.rev pl dans
    soit (pl, pnl, nl, cnt) =
      List.fold_left
        (fonc (pl, pnl, nl, cnt) p ->
           essaie
             soit (n, p) = find (cnt - 1) p nl dans p :: pl, n :: pnl, nl, cnt
           avec
             Not_found ->
               soit n = {pare = []; valu = p; chil = []} dans
               soit p = idag_of_int cnt dans p :: pl, n :: pnl, n :: nl, cnt + 1)
        ([], [], nl, cnt) pl
    dans
    soit pl = List.rev pl dans
    soit (cl, nl, cnt) =
      List.fold_left
        (fonc (cl, nl, cnt) c ->
           essaie
             soit (n, c) = find (cnt - 1) c nl dans
             n.pare <- n.pare @ pl; c :: cl, nl, cnt
           avec
             Not_found ->
               soit n = {pare = pl; valu = c; chil = []} dans
               soit c = idag_of_int cnt dans c :: cl, n :: nl, cnt + 1)
        ([], nl, cnt) cl
    dans
    soit cl = List.rev cl dans
    List.iter (fonc p -> p.chil <- p.chil @ cl) pnl; nl, cnt
  dans
  soit rec input_parents nl pl cnt =
    fonction
      Some "" -> input_parents nl pl cnt (get_line ic)
    | Some line ->
        début filtre line.[0] avec
          'o' ->
            soit p =
              strip_spaces (String.sub line 1 (String.length line - 1))
            dans
            si p = "" alors failwith line
            sinon input_parents nl (p :: pl) cnt (get_line ic)
        | '-' ->
            si pl = [] alors failwith line
            sinon input_children nl pl [] cnt (Some line)
        | _ -> failwith line
        fin
    | None -> si pl = [] alors nl, cnt sinon failwith "fin de fichier 1"
  et input_children nl pl cl cnt =
    fonction
      Some "" -> input_children nl pl cl cnt (get_line ic)
    | Some line ->
        début filtre line.[0] avec
          'o' ->
            si cl = [] alors failwith line
            sinon
              soit (nl, cnt) = add_node pl cl nl cnt dans
              input_parents nl [] cnt (Some line)
        | '-' ->
            soit c =
              strip_spaces (String.sub line 1 (String.length line - 1))
            dans
            si c = "" alors failwith line
            sinon input_children nl pl (c :: cl) cnt (get_line ic)
        | _ -> failwith line
        fin
    | None ->
        si cl = [] alors failwith "fin de fichier 2" sinon add_node pl cl nl cnt
  dans
  soit (nl, _) = input_parents [] [] 0 (get_line ic) dans
  {dag = Array.of_list (List.rev nl)}
;;

(* testing *)

soit map_dag f d =
  soit a =
    Array.map (fonc d -> {pare = d.pare; valu = f d.valu; chil = d.chil}) d.dag
  dans
  {dag = a}
;;

soit tag_dag d =
  soit c = ref 'A' dans
  map_dag
    (fonc v ->
       soit v = !c dans
       c :=
         si !c = 'Z' alors 'a'
         sinon si !c = 'z' alors '1'
         sinon Char.chr (Char.code !c + 1);
       String.make 1 v)
    d
;;

(* *)

soit phony _ = faux;;
soit indi_txt n = n.valu;;

soit string_table border hts =
  soit buf = Buffer.create 30 dans
  Printf.bprintf buf "<center><table border=%d" border;
  Printf.bprintf buf " cellspacing=0 cellpadding=0>\n";
  pour i = 0 à Array.length hts - 1 faire
    Printf.bprintf buf  "<tr>\n";
    pour j = 0 à Array.length hts.(i) - 1 faire
      soit (colspan, align, td) = hts.(i).(j) dans
      Printf.bprintf buf "<td";
      si colspan = 1 && (td = TDstring "&nbsp;" || td = TDhr CenterA) alors ()
      sinon Printf.bprintf buf " colspan=%d" colspan;
      début filtre align, td avec
        LeftA, TDhr LeftA -> Printf.bprintf buf " align=left"
      | LeftA, _ -> ()
      | CenterA, _ -> Printf.bprintf buf " align=center"
      | RightA, _ -> Printf.bprintf buf " align=right"
      fin;
      Printf.bprintf buf ">";
      début filtre td avec
        TDstring s -> Printf.bprintf buf "%s" s
      | TDhr align ->
          Printf.bprintf buf "<hr noshade size=1";
          début filtre align avec
            LeftA -> Printf.bprintf buf " width=\"50%%\" align=left"
          | RightA -> Printf.bprintf buf " width=\"50%%\" align=right"
          | _ -> ()
          fin;
          Printf.bprintf buf ">";
          ()
      fin;
      Printf.bprintf buf "</td>\n";
      ()
    fait
  fait;
  Printf.bprintf buf "</table></center>\n";
  Buffer.contents buf
;;

soit fname = ref "";;
soit invert = ref faux;;
soit char = ref faux;;
soit border = ref 0;;
soit no_optim = ref faux;;
soit no_group = ref faux;;

soit html_of_dag d =
  soit t = table_of_dag phony !no_optim !invert !no_group d dans
  soit hts = html_table_struct indi_txt phony d t dans
  string_table !border hts
;;


(********************************* Max's code **********************************)
(** This function takes a list of classes and a list of class types
   and create the associate dag. *)
soit create_class_dag cl_list clt_list =
  soit module M = Odoc_info.Class dans
  (* the list of all the classes concerned *)
  soit cl_list2 = List.map (fonc c -> (c.M.cl_name, Some (M.Cl c))) cl_list dans
  soit clt_list2 = List.map (fonc ct -> (ct.M.clt_name, Some (M.Cltype (ct, [])))) clt_list dans
  soit list = cl_list2 @ clt_list2 dans
  soit all_classes =
    soit rec iter list2 =
      List.fold_left
        (fonc acc -> fonc (name, cct_opt) ->
          soit l =
            filtre cct_opt avec
              None -> []
            | Some (M.Cl c) ->
                iter
                  (List.map
                     (fonc inh ->(inh.M.ic_name, inh.M.ic_class))
                     (filtre c.M.cl_kind avec
                       M.Class_structure (inher_l, _) ->
                         inher_l
                     | _ ->
                         []
                     )
                  )
            | Some (M.Cltype (ct, _)) ->
                iter
                  (List.map
                     (fonc inh ->(inh.M.ic_name, inh.M.ic_class))
                     (filtre ct.M.clt_kind avec
                       M.Class_signature (inher_l, _) ->
                         inher_l
                     | _ ->
                         []
                     )
                  )
          dans
          (name, cct_opt) :: (acc @ l)
        )
        []
        list2
    dans
    iter list
  dans
  soit rec distinct acc = fonction
    [] ->
      acc
    |   (name, cct_opt) :: q ->
        si List.exists (fonc (name2, _) -> name = name2) acc alors
          distinct acc q
        sinon
          distinct ((name, cct_opt) :: acc) q
  dans
  soit distinct_classes = distinct [] all_classes dans
  soit liste_index =
    soit rec f n = fonction
        [] -> []
      | (name, _) :: q -> (name, n) :: (f (n+1) q)
    dans
    f 0 distinct_classes
  dans
  soit array1 = Array.of_list distinct_classes dans
  (* create the dag array, filling parents and values *)
  soit fmap (name, cct_opt) =
    { pare = List.map
        (fonc inh -> List.assoc inh.M.ic_name liste_index )
        (filtre cct_opt avec
          None -> []
        | Some (M.Cl c) ->
            (filtre c.M.cl_kind avec
              M.Class_structure (inher_l, _) ->
                inher_l
            | _ ->
                []
            )
        | Some (M.Cltype (ct, _)) ->
            (filtre ct.M.clt_kind avec
              M.Class_signature (inher_l, _) ->
                inher_l
            | _ ->
                []
            )
        );
      valu = (name, cct_opt) ;
      chil = []
    }
  dans
  soit dag = { dag = Array.map fmap array1 } dans
  (* fill the children *)
  soit fiter i node =
    soit l = Array.to_list dag.dag dans
    soit l2 = List.map (fonc n -> n.valu)
        (List.filter (fonc n -> List.mem i n.pare) l)
    dans
    node.chil <- List.map (fonc (name,_) -> List.assoc name liste_index) l2
  dans
  Array.iteri fiter dag.dag;
  dag
