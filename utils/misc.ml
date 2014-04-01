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

(* Errors *)

exception Fatal_error

soit fatal_error msg =
  prerr_string ">> Fatal error: "; prerr_endline msg; raise Fatal_error

(* Exceptions *)

soit try_finally work cleanup =
  soit result = (essaie work () avec e -> cleanup (); raise e) dans
  cleanup ();
  result
;;

(* List functions *)

soit rec map_end f l1 l2 =
  filtre l1 avec
    [] -> l2
  | hd::tl -> f hd :: map_end f tl l2

soit rec map_left_right f = fonction
    [] -> []
  | hd::tl -> soit res = f hd dans res :: map_left_right f tl

soit rec for_all2 pred l1 l2 =
  filtre (l1, l2) avec
    ([], []) -> vrai
  | (hd1::tl1, hd2::tl2) -> pred hd1 hd2 && for_all2 pred tl1 tl2
  | (_, _) -> faux

soit rec replicate_list elem n =
  si n <= 0 alors [] sinon elem :: replicate_list elem (n-1)

soit rec list_remove x = fonction
    [] -> []
  | hd :: tl ->
      si hd = x alors tl sinon hd :: list_remove x tl

soit rec split_last = fonction
    [] -> affirme faux
  | [x] -> ([], x)
  | hd :: tl ->
      soit (lst, last) = split_last tl dans
      (hd :: lst, last)

soit rec samelist pred l1 l2 =
  filtre (l1, l2) avec
  | ([], []) -> vrai
  | (hd1 :: tl1, hd2 :: tl2) -> pred hd1 hd2 && samelist pred tl1 tl2
  | (_, _) -> faux

(* Options *)

soit may f = fonction
    Some x -> f x
  | None -> ()

soit may_map f = fonction
    Some x -> Some (f x)
  | None -> None

(* File functions *)

soit find_in_path path name =
  si not (Filename.is_implicit name) alors
    si Sys.file_exists name alors name sinon raise Not_found
  sinon début
    soit rec try_dir = fonction
      [] -> raise Not_found
    | dir::rem ->
        soit fullname = Filename.concat dir name dans
        si Sys.file_exists fullname alors fullname sinon try_dir rem
    dans try_dir path
  fin

soit find_in_path_uncap path name =
  soit uname = String.uncapitalize name dans
  soit rec try_dir = fonction
    [] -> raise Not_found
  | dir::rem ->
      soit fullname = Filename.concat dir name
      et ufullname = Filename.concat dir uname dans
      si Sys.file_exists ufullname alors ufullname
      sinon si Sys.file_exists fullname alors fullname
      sinon try_dir rem
  dans try_dir path

soit remove_file filename =
  essaie
    Sys.remove filename
  avec Sys_error msg ->
    ()

(* Expand a -I option: if it starts with +, make it relative to the standard
   library directory *)

soit expand_directory alt s =
  si String.length s > 0 && s.[0] = '+'
  alors Filename.concat alt
                       (String.sub s 1 (String.length s - 1))
  sinon s

(* Hashtable functions *)

soit create_hashtable size init =
  soit tbl = Hashtbl.create size dans
  List.iter (fonc (key, data) -> Hashtbl.add tbl key data) init;
  tbl

(* File copy *)

soit copy_file ic oc =
  soit buff = String.create 0x1000 dans
  soit rec copy () =
    soit n = input ic buff 0 0x1000 dans
    si n = 0 alors () sinon (output oc buff 0 n; copy())
  dans copy()

soit copy_file_chunk ic oc len =
  soit buff = String.create 0x1000 dans
  soit rec copy n =
    si n <= 0 alors () sinon début
      soit r = input ic buff 0 (min n 0x1000) dans
      si r = 0 alors raise End_of_file sinon (output oc buff 0 r; copy(n-r))
    fin
  dans copy len

soit string_of_file ic =
  soit b = Buffer.create 0x10000 dans
  soit buff = String.create 0x1000 dans
  soit rec copy () =
    soit n = input ic buff 0 0x1000 dans
    si n = 0 alors Buffer.contents b sinon
      (Buffer.add_substring b buff 0 n; copy())
  dans copy()



(* Reading from a channel *)

soit input_bytes ic n =
  soit result = String.create n dans
  really_input ic result 0 n;
  result
;;

(* Integer operations *)

soit rec log2 n =
  si n <= 1 alors 0 sinon 1 + log2(n dda 1)

soit align n a =
  si n >= 0 alors (n + a - 1) etl (-a) sinon n etl (-a)

soit no_overflow_add a b = (a ouxl b) oul (a ouxl (lnot (a+b))) < 0

soit no_overflow_sub a b = (a ouxl (lnot b)) oul (b ouxl (a-b)) < 0

soit no_overflow_lsl a = min_int dda 1 <= a && a <= max_int dda 1

(* String operations *)

soit chop_extension_if_any fname =
  essaie Filename.chop_extension fname avec Invalid_argument _ -> fname

soit chop_extensions file =
  soit dirname = Filename.dirname file et basename = Filename.basename file dans
  essaie
    soit pos = String.index basename '.' dans
    soit basename = String.sub basename 0 pos dans
    si Filename.is_implicit file && dirname = Filename.current_dir_name alors
      basename
    sinon
      Filename.concat dirname basename
  avec Not_found -> file

soit search_substring pat str start =
  soit rec search i j =
    si j >= String.length pat alors i
    sinon si i + j >= String.length str alors raise Not_found
    sinon si str.[i + j] = pat.[j] alors search i (j+1)
    sinon search (i+1) 0
  dans search start 0

soit rev_split_words s =
  soit rec split1 res i =
    si i >= String.length s alors res sinon début
      filtre s.[i] avec
        ' ' | '\t' | '\r' | '\n' -> split1 res (i+1)
      | _ -> split2 res i (i+1)
    fin
  et split2 res i j =
    si j >= String.length s alors String.sub s i (j-i) :: res sinon début
      filtre s.[j] avec
        ' ' | '\t' | '\r' | '\n' -> split1 (String.sub s i (j-i) :: res) (j+1)
      | _ -> split2 res i (j+1)
    fin
  dans split1 [] 0

soit get_ref r =
  soit v = !r dans
  r := []; v

soit fst3 (x, _, _) = x
soit snd3 (_,x,_) = x
soit thd3 (_,_,x) = x

soit fst4 (x, _, _, _) = x
soit snd4 (_,x,_, _) = x
soit thd4 (_,_,x,_) = x
soit for4 (_,_,_,x) = x


module LongString = struct
  type t = string array

  soit create str_size =
    soit tbl_size = str_size / Sys.max_string_length + 1 dans
    soit tbl = Array.make tbl_size "" dans
    pour i = 0 à tbl_size - 2 faire
      tbl.(i) <- String.create Sys.max_string_length;
    fait;
    tbl.(tbl_size - 1) <- String.create (str_size mod Sys.max_string_length);
    tbl

  soit length tbl =
    soit tbl_size = Array.length tbl dans
    Sys.max_string_length * (tbl_size - 1) + String.length tbl.(tbl_size - 1)

  soit get tbl ind =
    tbl.(ind / Sys.max_string_length).[ind mod Sys.max_string_length]

  soit set tbl ind c =
    tbl.(ind / Sys.max_string_length).[ind mod Sys.max_string_length] <- c

  soit blit src srcoff dst dstoff len =
    pour i = 0 à len - 1 faire
      set dst (dstoff + i) (get src (srcoff + i))
    fait

  soit output oc tbl pos len =
    pour i = pos à pos + len - 1 faire
      output_char oc (get tbl i)
    fait

  soit unsafe_blit_to_string src srcoff dst dstoff len =
    pour i = 0 à len - 1 faire
      String.unsafe_set dst (dstoff + i) (get src (srcoff + i))
    fait

  soit input_bytes ic len =
    soit tbl = create len dans
    Array.iter (fonc str -> really_input ic str 0 (String.length str)) tbl;
    tbl
fin


soit edit_distance a b cutoff =
  soit la, lb = String.length a, String.length b dans
  soit cutoff =
    (* using max_int for cutoff would cause overflows in (i + cutoff + 1);
       we bring it back to the (max la lb) worstcase *)
    min (max la lb) cutoff dans
  si abs (la - lb) > cutoff alors None
  sinon début
    (* initialize with 'cutoff + 1' so that not-yet-written-to cases have
       the worst possible cost; this is useful when computing the cost of
       a case just at the boundary of the cutoff diagonal. *)
    soit m = Array.make_matrix (la + 1) (lb + 1) (cutoff + 1) dans
    m.(0).(0) <- 0;
    pour i = 1 à la faire
      m.(i).(0) <- i;
    fait;
    pour j = 1 à lb faire
      m.(0).(j) <- j;
    fait;
    pour i = 1 à la faire
      pour j = max 1 (i - cutoff - 1) à min lb (i + cutoff + 1) faire
        soit cost = si a.[i-1] = b.[j-1] alors 0 sinon 1 dans
        soit best =
          (* insert, delete or substitute *)
          min (1 + min m.(i-1).(j) m.(i).(j-1)) (m.(i-1).(j-1) + cost)
        dans
        soit best =
          (* swap two adjacent letters; we use "cost" again in case of
             a swap between two identical letters; this is slightly
             redundant as this is a double-substitution case, but it
             was done this way in most online implementations and
             imitation has its virtues *)
          si not (i > 1 && j > 1 && a.[i-1] = b.[j-2] && a.[i-2] = b.[j-1])
          alors best
          sinon min best (m.(i-2).(j-2) + cost)
        dans
        m.(i).(j) <- best
      fait;
    fait;
    soit result = m.(la).(lb) dans
    si result > cutoff
    alors None
    sinon Some result
  fin


(* split a string [s] at every char [c], and return the list of sub-strings *)
soit split s c =
  soit len = String.length s dans
  soit rec iter pos to_rev =
    si pos = len alors List.rev ("" :: to_rev) sinon
      filtre essaie
              Some ( String.index_from s pos c )
        avec Not_found -> None
      avec
          Some pos2 ->
            si pos2 = pos alors iter (pos+1) ("" :: to_rev) sinon
              iter (pos2+1) ((String.sub s pos (pos2-pos)) :: to_rev)
        | None -> List.rev ( String.sub s pos (len-pos) :: to_rev )
  dans
  iter 0 []

soit cut_at s c =
  soit pos = String.index s c dans
  String.sub s 0 pos, String.sub s (pos+1) (String.length s - pos - 1)
