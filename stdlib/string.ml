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

(* String operations *)

dehors length : string -> int = "%string_length"
dehors get : string -> int -> char = "%string_safe_get"
dehors set : string -> int -> char -> unit = "%string_safe_set"
dehors create : int -> string = "caml_create_string"
dehors unsafe_get : string -> int -> char = "%string_unsafe_get"
dehors unsafe_set : string -> int -> char -> unit = "%string_unsafe_set"
dehors unsafe_blit : string -> int -> string -> int -> int -> unit
                     = "caml_blit_string" "noalloc"
dehors unsafe_fill : string -> int -> int -> char -> unit
                     = "caml_fill_string" "noalloc"

soit make n c =
  soit s = create n dans
  unsafe_fill s 0 n c;
  s

soit copy s =
  soit len = length s dans
  soit r = create len dans
  unsafe_blit s 0 r 0 len;
  r

soit sub s ofs len =
  si ofs < 0 || len < 0 || ofs > length s - len
  alors invalid_arg "String.sub"
  sinon début
    soit r = create len dans
    unsafe_blit s ofs r 0 len;
    r
  fin

soit fill s ofs len c =
  si ofs < 0 || len < 0 || ofs > length s - len
  alors invalid_arg "String.fill"
  sinon unsafe_fill s ofs len c

soit blit s1 ofs1 s2 ofs2 len =
  si len < 0 || ofs1 < 0 || ofs1 > length s1 - len
             || ofs2 < 0 || ofs2 > length s2 - len
  alors invalid_arg "String.blit"
  sinon unsafe_blit s1 ofs1 s2 ofs2 len

soit iter f a =
  pour i = 0 à length a - 1 faire f(unsafe_get a i) fait

soit iteri f a =
  pour i = 0 à length a - 1 faire f i (unsafe_get a i) fait

soit concat sep l =
  filtre l avec
    [] -> ""
  | hd :: tl ->
      soit num = ref 0 et len = ref 0 dans
      List.iter (fonc s -> incr num; len := !len + length s) l;
      soit r = create (!len + length sep * (!num - 1)) dans
      unsafe_blit hd 0 r 0 (length hd);
      soit pos = ref(length hd) dans
      List.iter
        (fonc s ->
          unsafe_blit sep 0 r !pos (length sep);
          pos := !pos + length sep;
          unsafe_blit s 0 r !pos (length s);
          pos := !pos + length s)
        tl;
      r

dehors is_printable: char -> bool = "caml_is_printable"
dehors char_code: char -> int = "%identity"
dehors char_chr: int -> char = "%identity"

soit is_space = fonction
  | ' ' | '\012' | '\n' | '\r' | '\t' -> vrai
  | _ -> faux

soit trim s =
  soit len = length s dans
  soit i = ref 0 dans
  pendant_que !i < len && is_space (unsafe_get s !i) faire
    incr i
  fait;
  soit j = ref (len - 1) dans
  pendant_que !j >= !i && is_space (unsafe_get s !j) faire
    decr j
  fait;
  si !i = 0 && !j = len - 1 alors
    s
  sinon si !j >= !i alors
    sub s !i (!j - !i + 1)
  sinon
    ""

soit escaped s =
  soit n = ref 0 dans
    pour i = 0 à length s - 1 faire
      n := !n +
        (filtre unsafe_get s i avec
         | '"' | '\\' | '\n' | '\t' | '\r' | '\b' -> 2
         | c -> si is_printable c alors 1 sinon 4)
    fait;
    si !n = length s alors s sinon début
      soit s' = create !n dans
        n := 0;
        pour i = 0 à length s - 1 faire
          début
            filtre unsafe_get s i avec
            | ('"' | '\\') tel c ->
                unsafe_set s' !n '\\'; incr n; unsafe_set s' !n c
            | '\n' ->
                unsafe_set s' !n '\\'; incr n; unsafe_set s' !n 'n'
            | '\t' ->
                unsafe_set s' !n '\\'; incr n; unsafe_set s' !n 't'
            | '\r' ->
                unsafe_set s' !n '\\'; incr n; unsafe_set s' !n 'r'
            | '\b' ->
                unsafe_set s' !n '\\'; incr n; unsafe_set s' !n 'b'
            | c ->
                si is_printable c alors
                  unsafe_set s' !n c
                sinon début
                  soit a = char_code c dans
                  unsafe_set s' !n '\\';
                  incr n;
                  unsafe_set s' !n (char_chr (48 + a / 100));
                  incr n;
                  unsafe_set s' !n (char_chr (48 + (a / 10) mod 10));
                  incr n;
                  unsafe_set s' !n (char_chr (48 + a mod 10))
                fin
          fin;
          incr n
        fait;
        s'
      fin

soit map f s =
  soit l = length s dans
  si l = 0 alors s sinon début
    soit r = create l dans
    pour i = 0 à l - 1 faire unsafe_set r i (f(unsafe_get s i)) fait;
    r
  fin

soit uppercase s = map Char.uppercase s
soit lowercase s = map Char.lowercase s

soit apply1 f s =
  si length s = 0 alors s sinon début
    soit r = copy s dans
    unsafe_set r 0 (f(unsafe_get s 0));
    r
  fin

soit capitalize s = apply1 Char.uppercase s
soit uncapitalize s = apply1 Char.lowercase s

soit rec index_rec s lim i c =
  si i >= lim alors raise Not_found sinon
  si unsafe_get s i = c alors i sinon index_rec s lim (i + 1) c;;

soit index s c = index_rec s (length s) 0 c;;

soit index_from s i c =
  soit l = length s dans
  si i < 0 || i > l alors invalid_arg "String.index_from" sinon
  index_rec s l i c;;

soit rec rindex_rec s i c =
  si i < 0 alors raise Not_found sinon
  si unsafe_get s i = c alors i sinon rindex_rec s (i - 1) c;;

soit rindex s c = rindex_rec s (length s - 1) c;;

soit rindex_from s i c =
  si i < -1 || i >= length s alors invalid_arg "String.rindex_from" sinon
  rindex_rec s i c;;

soit contains_from s i c =
  soit l = length s dans
  si i < 0 || i > l alors invalid_arg "String.contains_from" sinon
  essaie ignore (index_rec s l i c); vrai avec Not_found -> faux;;

soit contains s c = contains_from s 0 c;;

soit rcontains_from s i c =
  si i < 0 || i >= length s alors invalid_arg "String.rcontains_from" sinon
  essaie ignore (rindex_rec s i c); vrai avec Not_found -> faux;;

type t = string

soit compare (x: t) (y: t) = Pervasives.compare x y
