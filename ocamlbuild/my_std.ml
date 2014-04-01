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


(* Original author: Nicolas Pouillard *)
ouvre Format

exception Exit_OK
exception Exit_usage de string
exception Exit_system_error de string
exception Exit_with_code de int
exception Exit_silently_with_code de int

module Outcome = struct
  type ('a,'b) t =
    | Good de 'a
    | Bad de 'b

  soit ignore_good =
    fonction
    | Good _ -> ()
    | Bad e -> raise e

  soit good =
    fonction
    | Good x -> x
    | Bad exn -> raise exn

  soit wrap f x =
    essaie Good (f x) avec e -> Bad e

fin

soit opt_print elt ppf =
  fonction
  | Some x -> fprintf ppf "@[<2>Some@ %a@]" elt x
  | None -> pp_print_string ppf "None"

ouvre Format
soit ksbprintf g fmt =
  soit buff = Buffer.create 42 dans
  soit f = formatter_of_buffer buff dans
  kfprintf (fonc f -> (pp_print_flush f (); g (Buffer.contents buff))) f fmt
soit sbprintf fmt = ksbprintf (fonc x -> x) fmt

(** Some extensions of the standard library *)
module Set = struct

  module type OrderedTypePrintable = sig
    inclus Set.OrderedType
    val print : formatter -> t -> unit
  fin

  module type S = sig
    inclus Set.S
    val find_elt : (elt -> bool) -> t -> elt
    val map : (elt -> elt) -> t -> t
    val of_list : elt list -> t
    val print : formatter -> t -> unit
  fin

  module Make (M : OrderedTypePrintable) : S avec type elt = M.t = struct
    inclus Set.Make(M)
    exception Found de elt
    soit find_elt p set =
      essaie
        iter début fonc elt ->
          si p elt alors raise (Found elt)
        fin set; raise Not_found
      avec Found elt -> elt
    soit map f set = fold (fonc x -> add (f x)) set empty
    soit of_list l = List.fold_right add l empty
    soit print f s =
      soit () = fprintf f "@[<hv0>@[<hv2>{.@ " dans
      soit _ =
        fold début fonc elt first ->
          si not first alors fprintf f ",@ ";
          M.print f elt;
          faux
        fin s vrai dans
      fprintf f "@]@ .}@]"
  fin
fin

module List = struct
  inclus List
  soit print pp_elt f ls =
    fprintf f "@[<2>[@ ";
    soit _ =
      fold_left début fonc first elt ->
        si not first alors fprintf f ";@ ";
        pp_elt f elt;
        faux
      fin vrai ls dans
    fprintf f "@ ]@]"

  soit filter_opt f xs =
    List.fold_right début fonc x acc ->
      filtre f x avec
      | Some x -> x :: acc
      | None -> acc
    fin xs []

  soit rec rev_append_uniq acc =
    fonction
    | [] -> acc
    | x :: xs ->
        si mem x acc alors rev_append_uniq acc xs
        sinon rev_append_uniq (x :: acc) xs

  soit union a b =
    rev (rev_append_uniq (rev_append_uniq [] a) b)

  soit ordered_unique (type el) (lst : el list)  =
    soit module Set = Set.Make(struct
      type t = el
      soit compare = Pervasives.compare
      soit print _ _ = ()
    fin)
    dans
    soit _, lst =
      List.fold_left (fonc (set,acc) el ->
        si Set.mem el set
        alors set, acc
        sinon Set.add el set, el :: acc) (Set.empty,[]) lst
    dans
    List.rev lst

fin

module String = struct
  inclus String

  soit print f s = fprintf f "%S" s

  soit chomp s =
    soit is_nl_char = fonction '\n' | '\r' -> vrai | _ -> faux dans
    soit rec cut n =
      si n = 0 alors 0 sinon si is_nl_char s.[n-1] alors cut (n-1) sinon n
    dans
    soit ls = length s dans
    soit n = cut ls dans
    si n = ls alors s sinon sub s 0 n

  soit before s pos = sub s 0 pos
  soit after s pos = sub s pos (length s - pos)
  soit first_chars s n = sub s 0 n
  soit last_chars s n = sub s (length s - n) n

  soit rec eq_sub_strings s1 p1 s2 p2 len =
    si len > 0 alors s1.[p1] = s2.[p2] && eq_sub_strings s1 (p1+1) s2 (p2+1) (len-1)
    sinon vrai

  soit rec contains_string s1 p1 s2 =
    soit ls1 = length s1 dans
    soit ls2 = length s2 dans
    essaie soit pos = index_from s1 p1 s2.[0] dans
        si ls1 - pos < ls2 alors None
        sinon si eq_sub_strings s1 pos s2 0 ls2 alors
        Some pos sinon contains_string s1 (pos + 1) s2
    avec Not_found -> None

  soit subst patt repl s =
    soit lpatt = length patt dans
    soit lrepl = length repl dans
    soit rec loop s from =
      filtre contains_string s from patt avec
      | Some pos ->
          loop (before s pos ^ repl ^ after s (pos + lpatt)) (pos + lrepl)
      | None -> s
    dans loop s 0

  soit tr patt subst text =
    soit len = length text dans
    soit text = copy text dans
    soit rec loop pos =
      si pos < len alors début
        (si text.[pos] = patt alors text.[pos] <- subst);
        loop (pos + 1)
      fin
    dans loop 0; text

  (*** is_prefix : is u a prefix of v ? *)
  soit is_prefix u v =
    soit m = String.length u
    et n = String.length v
    dans
    m <= n &&
      soit rec loop i = i = m || u.[i] = v.[i] && loop (i + 1) dans
      loop 0
  (* ***)

  (*** is_suffix : is v a suffix of u ? *)
  soit is_suffix u v =
    soit m = String.length u
    et n = String.length v
    dans
    n <= m &&
      soit rec loop i = i = n || u.[m - 1 - i] = v.[n - 1 - i] && loop (i + 1) dans
      loop 0
  (* ***)

  soit rev s =
    soit sl = String.length s dans
    soit s' = String.create sl dans
    pour i = 0 à sl - 1 faire
      s'.[i] <- s.[sl - i - 1]
    fait;
    s';;

  soit implode l =
    filtre l avec
    | [] -> ""
    | cs ->
        soit r = create (List.length cs) dans
        soit pos = ref 0 dans
        List.iter début fonc c ->
          unsafe_set r !pos c;
          incr pos
        fin cs;
        r

  soit explode s =
    soit sl = String.length s dans
    soit rec go pos =
      si pos >= sl alors [] sinon unsafe_get s pos :: go (pos + 1)
    dans go 0
fin

module StringSet = Set.Make(String)

soit sys_readdir, reset_readdir_cache, reset_readdir_cache_for =
  soit cache = Hashtbl.create 103 dans
  soit sys_readdir dir =
    essaie Hashtbl.find cache dir avec Not_found ->
      soit res = Outcome.wrap Sys.readdir dir dans
      (Hashtbl.add cache dir res; res)
  et reset_readdir_cache () =
    Hashtbl.clear cache
  et reset_readdir_cache_for dir =
    Hashtbl.remove cache dir dans
  (sys_readdir, reset_readdir_cache, reset_readdir_cache_for)

soit sys_file_exists x =
  soit dirname = Filename.dirname x dans
  soit basename = Filename.basename x dans
  filtre sys_readdir dirname avec
  | Outcome.Bad _ -> faux
  | Outcome.Good a ->
      si basename = Filename.current_dir_name alors vrai sinon
      essaie Array.iter (fonc x -> si x = basename alors raise Exit) a; faux
      avec Exit -> vrai

soit sys_command =
  filtre Sys.os_type avec
  | "Win32" -> fonc cmd ->
      si cmd = "" alors 0 sinon
      soit cmd = "bash --norc -c "^Filename.quote cmd dans
      Sys.command cmd
  | _ -> fonc cmd -> si cmd = "" alors 0 sinon Sys.command cmd

(* FIXME warning fix and use Filename.concat *)
soit filename_concat x y =
  si x = Filename.current_dir_name || x = "" alors y sinon
  si Sys.os_type = "Win32" && (x.[String.length x - 1] = '\\') || x.[String.length x - 1] = '/' alors
    si y = "" alors x
    sinon x ^ y
  sinon
    x ^ "/" ^ y

(* let reslash =
  match Sys.os_type with
  | "Win32" -> tr '\\' '/'
  | _ -> (fun x -> x) *)

ouvre Format

soit invalid_arg' fmt = ksbprintf invalid_arg fmt

soit the = fonction Some x -> x | None -> invalid_arg "the: Some est attendu, pas None"

soit getenv ?default var =
  essaie Sys.getenv var
  avec Not_found ->
    filtre default avec
    | Some x -> x
    | None -> failwith (sprintf "Cette commande doit avoir %S dans son environnement" var);;

soit with_input_file ?(bin=faux) x f =
  soit ic = (si bin alors open_in_bin sinon open_in) x dans
  essaie soit res = f ic dans close_in ic; res avec e -> (close_in ic; raise e)

soit with_output_file ?(bin=faux) x f =
  reset_readdir_cache_for (Filename.dirname x);
  soit oc = (si bin alors open_out_bin sinon open_out) x dans
  essaie soit res = f oc dans close_out oc; res avec e -> (close_out oc; raise e)

soit read_file x =
  with_input_file ~bin:vrai x début fonc ic ->
    soit len = in_channel_length ic dans
    soit buf = String.create len dans
    soit () = really_input ic buf 0 len dans
    buf
  fin

soit copy_chan ic oc =
  soit m = in_channel_length ic dans
  soit m = (m ddl 12) dgl 12 dans
  soit m = max 16384 (min Sys.max_string_length m) dans
  soit buf = String.create m dans
  soit rec loop () =
    soit len = input ic buf 0 m dans
    si len > 0 alors début
      output oc buf 0 len;
      loop ()
    fin
  dans loop ()

soit copy_file src dest =
  reset_readdir_cache_for (Filename.dirname dest);
  with_input_file ~bin:vrai src début fonc ic ->
    with_output_file ~bin:vrai dest début fonc oc ->
      copy_chan ic oc
    fin
  fin

soit ( !* ) = Lazy.force

soit ( @:= ) ref list = ref := !ref @ list

soit ( & ) f x = f x

soit ( |> ) x f = f x

soit print_string_list = List.print String.print

module Digest = struct
  inclus Digest
(* USEFUL FOR DIGEST DEBUGING
  let digest_log_hash = Hashtbl.create 103;;
  let digest_log = "digest.log";;
  let digest_log_oc = open_out_gen [Open_append;Open_wronly;Open_text;Open_creat] 0o666 digest_log;;
  let my_to_hex x = to_hex x ^ ";";;
  if sys_file_exists digest_log then
    with_input_file digest_log begin fun ic ->
      try while true do
        let l = input_line ic in
        Scanf.sscanf l "%S: %S" (Hashtbl.replace digest_log_hash)
      done with End_of_file -> ()
    end;;
  let string s =
    let res = my_to_hex (string s) in
    if try let x = Hashtbl.find digest_log_hash res in s <> x with Not_found -> true then begin
      Hashtbl.replace digest_log_hash res s;
      Printf.fprintf digest_log_oc "%S: %S\n%!" res s
    end;
    res
  let file f = my_to_hex (file f)
  let to_hex x = x
*)

  soit digest_cache = Hashtbl.create 103
  soit reset_digest_cache () = Hashtbl.clear digest_cache
  soit reset_digest_cache_for file = Hashtbl.remove digest_cache file
  soit file f =
    essaie Hashtbl.find digest_cache f
    avec Not_found ->
      soit res = file f dans
      (Hashtbl.add digest_cache f res; res)
fin

soit reset_filesys_cache () =
  Digest.reset_digest_cache ();
  reset_readdir_cache ()

soit reset_filesys_cache_for_file file =
  Digest.reset_digest_cache_for file;
  reset_readdir_cache_for (Filename.dirname file)

soit sys_remove x =
  reset_filesys_cache_for_file x;
  Sys.remove x

soit with_temp_file pre suf fct =
  soit tmp = Filename.temp_file pre suf dans
  (* Sys.remove is used instead of sys_remove since we know that the tempfile is not that important *)
  essaie soit res = fct tmp dans Sys.remove tmp; res
  avec e -> (Sys.remove tmp; raise e)

soit memo f =
  soit cache = Hashtbl.create 103 dans
  fonc x ->
    essaie Hashtbl.find cache x
    avec Not_found ->
      soit res = f x dans
      (Hashtbl.add cache x res; res)

soit memo2 f =
  soit cache = Hashtbl.create 103 dans
  fonc x y ->
    essaie Hashtbl.find cache (x,y)
    avec Not_found ->
      soit res = f x y dans
      (Hashtbl.add cache (x,y) res; res)

soit memo3 f =
  soit cache = Hashtbl.create 103 dans
  fonc x y z ->
    essaie Hashtbl.find cache (x,y,z)
    avec Not_found ->
      soit res = f x y z dans
      (Hashtbl.add cache (x,y,z) res; res)
