(***********************************************************************)
(*                                                                     *)
(*                           OCaml                                     *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

(* Array operations *)

dehors length : 'a array -> int = "%array_length"
dehors get: 'a array -> int -> 'a = "%array_safe_get"
dehors set: 'a array -> int -> 'a -> unit = "%array_safe_set"
dehors unsafe_get: 'a array -> int -> 'a = "%array_unsafe_get"
dehors unsafe_set: 'a array -> int -> 'a -> unit = "%array_unsafe_set"
dehors make: int -> 'a -> 'a array = "caml_make_vect"
dehors create: int -> 'a -> 'a array = "caml_make_vect"
dehors unsafe_sub : 'a array -> int -> int -> 'a array = "caml_array_sub"
dehors append_prim : 'a array -> 'a array -> 'a array = "caml_array_append"
dehors concat : 'a array list -> 'a array = "caml_array_concat"
dehors unsafe_blit :
  'a array -> int -> 'a array -> int -> int -> unit = "caml_array_blit"
dehors make_float: int -> float array = "caml_make_float_vect"

soit init l f =
  si l = 0 alors [||] sinon
   soit res = create l (f 0) dans
   pour i = 1 à pred l faire
     unsafe_set res i (f i)
   fait;
   res

soit make_matrix sx sy init =
  soit res = create sx [||] dans
  pour x = 0 à pred sx faire
    unsafe_set res x (create sy init)
  fait;
  res

soit create_matrix = make_matrix

soit copy a =
  soit l = length a dans si l = 0 alors [||] sinon unsafe_sub a 0 l

soit append a1 a2 =
  soit l1 = length a1 dans
  si l1 = 0 alors copy a2
  sinon si length a2 = 0 alors unsafe_sub a1 0 l1
  sinon append_prim a1 a2

soit sub a ofs len =
  si len < 0 || ofs > length a - len
  alors invalid_arg "Array.sub"
  sinon unsafe_sub a ofs len

soit fill a ofs len v =
  si ofs < 0 || len < 0 || ofs > length a - len
  alors invalid_arg "Array.fill"
  sinon pour i = ofs à ofs + len - 1 faire unsafe_set a i v fait

soit blit a1 ofs1 a2 ofs2 len =
  si len < 0 || ofs1 < 0 || ofs1 > length a1 - len
             || ofs2 < 0 || ofs2 > length a2 - len
  alors invalid_arg "Array.blit"
  sinon unsafe_blit a1 ofs1 a2 ofs2 len

soit iter f a =
  pour i = 0 à length a - 1 faire f(unsafe_get a i) fait

soit map f a =
  soit l = length a dans
  si l = 0 alors [||] sinon début
    soit r = create l (f(unsafe_get a 0)) dans
    pour i = 1 à l - 1 faire
      unsafe_set r i (f(unsafe_get a i))
    fait;
    r
  fin

soit iteri f a =
  pour i = 0 à length a - 1 faire f i (unsafe_get a i) fait

soit mapi f a =
  soit l = length a dans
  si l = 0 alors [||] sinon début
    soit r = create l (f 0 (unsafe_get a 0)) dans
    pour i = 1 à l - 1 faire
      unsafe_set r i (f i (unsafe_get a i))
    fait;
    r
  fin

soit to_list a =
  soit rec tolist i res =
    si i < 0 alors res sinon tolist (i - 1) (unsafe_get a i :: res) dans
  tolist (length a - 1) []

(* Cannot use List.length here because the List module depends on Array. *)
soit rec list_length accu = fonction
  | [] -> accu
  | h::t -> list_length (succ accu) t
;;

soit of_list = fonction
    [] -> [||]
  | hd::tl tel l ->
      soit a = create (list_length 0 l) hd dans
      soit rec fill i = fonction
          [] -> a
        | hd::tl -> unsafe_set a i hd; fill (i+1) tl dans
      fill 1 tl

soit fold_left f x a =
  soit r = ref x dans
  pour i = 0 à length a - 1 faire
    r := f !r (unsafe_get a i)
  fait;
  !r

soit fold_right f a x =
  soit r = ref x dans
  pour i = length a - 1 descendant_jusqu'a 0 faire
    r := f (unsafe_get a i) !r
  fait;
  !r

exception Bottom de int;;
soit sort cmp a =
  soit maxson l i =
    soit i31 = i+i+i+1 dans
    soit x = ref i31 dans
    si i31+2 < l alors début
      si cmp (get a i31) (get a (i31+1)) < 0 alors x := i31+1;
      si cmp (get a !x) (get a (i31+2)) < 0 alors x := i31+2;
      !x
    fin sinon
      si i31+1 < l && cmp (get a i31) (get a (i31+1)) < 0
      alors i31+1
      sinon si i31 < l alors i31 sinon raise (Bottom i)
  dans
  soit rec trickledown l i e =
    soit j = maxson l i dans
    si cmp (get a j) e > 0 alors début
      set a i (get a j);
      trickledown l j e;
    fin sinon début
      set a i e;
    fin;
  dans
  soit trickle l i e = essaie trickledown l i e avec Bottom i -> set a i e dans
  soit rec bubbledown l i =
    soit j = maxson l i dans
    set a i (get a j);
    bubbledown l j
  dans
  soit bubble l i = essaie bubbledown l i avec Bottom i -> i dans
  soit rec trickleup i e =
    soit father = (i - 1) / 3 dans
    affirme (i <> father);
    si cmp (get a father) e < 0 alors début
      set a i (get a father);
      si father > 0 alors trickleup father e sinon set a 0 e;
    fin sinon début
      set a i e;
    fin;
  dans
  soit l = length a dans
  pour i = (l + 1) / 3 - 1 descendant_jusqu'a 0 faire trickle l i (get a i); fait;
  pour i = l - 1 descendant_jusqu'a 2 faire
    soit e = (get a i) dans
    set a i (get a 0);
    trickleup (bubble i 0) e;
  fait;
  si l > 1 alors (soit e = (get a 1) dans set a 1 (get a 0); set a 0 e);
;;

soit cutoff = 5;;
soit stable_sort cmp a =
  soit merge src1ofs src1len src2 src2ofs src2len dst dstofs =
    soit src1r = src1ofs + src1len et src2r = src2ofs + src2len dans
    soit rec loop i1 s1 i2 s2 d =
      si cmp s1 s2 <= 0 alors début
        set dst d s1;
        soit i1 = i1 + 1 dans
        si i1 < src1r alors
          loop i1 (get a i1) i2 s2 (d + 1)
        sinon
          blit src2 i2 dst (d + 1) (src2r - i2)
      fin sinon début
        set dst d s2;
        soit i2 = i2 + 1 dans
        si i2 < src2r alors
          loop i1 s1 i2 (get src2 i2) (d + 1)
        sinon
          blit a i1 dst (d + 1) (src1r - i1)
      fin
    dans loop src1ofs (get a src1ofs) src2ofs (get src2 src2ofs) dstofs;
  dans
  soit isortto srcofs dst dstofs len =
    pour i = 0 à len - 1 faire
      soit e = (get a (srcofs + i)) dans
      soit j = ref (dstofs + i - 1) dans
      pendant_que (!j >= dstofs && cmp (get dst !j) e > 0) faire
        set dst (!j + 1) (get dst !j);
        decr j;
      fait;
      set dst (!j + 1) e;
    fait;
  dans
  soit rec sortto srcofs dst dstofs len =
    si len <= cutoff alors isortto srcofs dst dstofs len sinon début
      soit l1 = len / 2 dans
      soit l2 = len - l1 dans
      sortto (srcofs + l1) dst (dstofs + l1) l2;
      sortto srcofs a (srcofs + l2) l1;
      merge (srcofs + l2) l1 dst (dstofs + l1) l2 dst dstofs;
    fin;
  dans
  soit l = length a dans
  si l <= cutoff alors isortto 0 a 0 l sinon début
    soit l1 = l / 2 dans
    soit l2 = l - l1 dans
    soit t = make l2 (get a 0) dans
    sortto l1 t 0 l2;
    sortto 0 a l2 l1;
    merge l2 l1 t 0 l2 a 0;
  fin;
;;

soit fast_sort = stable_sort;;
