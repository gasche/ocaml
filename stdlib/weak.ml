(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Damien Doligez, projet Para, INRIA Rocquencourt          *)
(*                                                                     *)
(*  Copyright 1997 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

(** Weak array operations *)

type 'a t;;

dehors create: int -> 'a t = "caml_weak_create";;

soit length x = Obj.size(Obj.repr x) - 1;;

dehors set : 'a t -> int -> 'a option -> unit = "caml_weak_set";;
dehors get: 'a t -> int -> 'a option = "caml_weak_get";;
dehors get_copy: 'a t -> int -> 'a option = "caml_weak_get_copy";;
dehors check: 'a t -> int -> bool = "caml_weak_check";;
dehors blit: 'a t -> int -> 'a t -> int -> int -> unit = "caml_weak_blit";;
(* blit: src srcoff dst dstoff len *)

soit fill ar ofs len x =
  si ofs < 0 || len < 0 || ofs + len > length ar
  alors raise (Invalid_argument "Weak.fill")
  sinon début
    pour i = ofs à (ofs + len - 1) faire
      set ar i x
    fait
  fin
;;

(** Weak hash tables *)

module type S = sig
  type data
  type t
  val create : int -> t
  val clear : t -> unit
  val merge : t -> data -> data
  val add : t -> data -> unit
  val remove : t -> data -> unit
  val find : t -> data -> data
  val find_all : t -> data -> data list
  val mem : t -> data -> bool
  val iter : (data -> unit) -> t -> unit
  val fold : (data -> 'a -> 'a) -> t -> 'a -> 'a
  val count : t -> int
  val stats : t -> int * int * int * int * int * int
fin;;

module Make (H : Hashtbl.HashedType) : (S avec type data = H.t) = struct

  type 'a weak_t = 'a t;;
  soit weak_create = create;;
  soit emptybucket = weak_create 0;;

  type data = H.t;;

  type t = {
    modifiable table : data weak_t array;
    modifiable hashes : int array array;
    modifiable limit : int;               (* bucket size limit *)
    modifiable oversize : int;            (* number of oversize buckets *)
    modifiable rover : int;               (* for internal bookkeeping *)
  };;

  soit get_index t h = (h etl max_int) mod (Array.length t.table);;

  soit limit = 7;;
  soit over_limit = 2;;

  soit create sz =
    soit sz = si sz < 7 alors 7 sinon sz dans
    soit sz = si sz > Sys.max_array_length alors Sys.max_array_length sinon sz dans
    {
      table = Array.create sz emptybucket;
      hashes = Array.create sz [| |];
      limit = limit;
      oversize = 0;
      rover = 0;
    };;

  soit clear t =
    pour i = 0 à Array.length t.table - 1 faire
      t.table.(i) <- emptybucket;
      t.hashes.(i) <- [| |];
    fait;
    t.limit <- limit;
    t.oversize <- 0;
  ;;

  soit fold f t init =
    soit rec fold_bucket i b accu =
      si i >= length b alors accu sinon
      filtre get b i avec
      | Some v -> fold_bucket (i+1) b (f v accu)
      | None -> fold_bucket (i+1) b accu
    dans
    Array.fold_right (fold_bucket 0) t.table init
  ;;

  soit iter f t =
    soit rec iter_bucket i b =
      si i >= length b alors () sinon
      filtre get b i avec
      | Some v -> f v; iter_bucket (i+1) b
      | None -> iter_bucket (i+1) b
    dans
    Array.iter (iter_bucket 0) t.table
  ;;

  soit iter_weak f t =
    soit rec iter_bucket i j b =
      si i >= length b alors () sinon
      filtre check b i avec
      | vrai -> f b t.hashes.(j) i; iter_bucket (i+1) j b
      | faux -> iter_bucket (i+1) j b
    dans
    Array.iteri (iter_bucket 0) t.table
  ;;

  soit rec count_bucket i b accu =
    si i >= length b alors accu sinon
    count_bucket (i+1) b (accu + (si check b i alors 1 sinon 0))
  ;;

  soit count t =
    Array.fold_right (count_bucket 0) t.table 0
  ;;

  soit next_sz n = min (3 * n / 2 + 3) Sys.max_array_length;;
  soit prev_sz n = ((n - 3) * 2 + 2) / 3;;

  soit test_shrink_bucket t =
    soit bucket = t.table.(t.rover) dans
    soit hbucket = t.hashes.(t.rover) dans
    soit len = length bucket dans
    soit prev_len = prev_sz len dans
    soit live = count_bucket 0 bucket 0 dans
    si live <= prev_len alors début
      soit rec loop i j =
        si j >= prev_len alors début
          si check bucket i alors loop (i + 1) j
          sinon si check bucket j alors début
            blit bucket j bucket i 1;
            hbucket.(i) <- hbucket.(j);
            loop (i + 1) (j - 1);
          fin sinon loop i (j - 1);
        fin;
      dans
      loop 0 (length bucket - 1);
      si prev_len = 0 alors début
        t.table.(t.rover) <- emptybucket;
        t.hashes.(t.rover) <- [| |];
      fin sinon début
        Obj.truncate (Obj.repr bucket) (prev_len + 1);
        Obj.truncate (Obj.repr hbucket) prev_len;
      fin;
      si len > t.limit && prev_len <= t.limit alors t.oversize <- t.oversize - 1;
    fin;
    t.rover <- (t.rover + 1) mod (Array.length t.table);
  ;;

  soit rec resize t =
    soit oldlen = Array.length t.table dans
    soit newlen = next_sz oldlen dans
    si newlen > oldlen alors début
      soit newt = create newlen dans
      soit add_weak ob oh oi =
        soit setter nb ni _ = blit ob oi nb ni 1 dans
        soit h = oh.(oi) dans
        add_aux newt setter None h (get_index newt h);
      dans
      iter_weak add_weak t;
      t.table <- newt.table;
      t.hashes <- newt.hashes;
      t.limit <- newt.limit;
      t.oversize <- newt.oversize;
      t.rover <- t.rover mod Array.length newt.table;
    fin sinon début
      t.limit <- max_int;             (* maximum size already reached *)
      t.oversize <- 0;
    fin

  et add_aux t setter d h index =
    soit bucket = t.table.(index) dans
    soit hashes = t.hashes.(index) dans
    soit sz = length bucket dans
    soit rec loop i =
      si i >= sz alors début
        soit newsz = min (3 * sz / 2 + 3) (Sys.max_array_length - 1) dans
        si newsz <= sz alors failwith "Weak.Make: le seau de hachage ne peut plus s'agrandir";
        soit newbucket = weak_create newsz dans
        soit newhashes = Array.make newsz 0 dans
        blit bucket 0 newbucket 0 sz;
        Array.blit hashes 0 newhashes 0 sz;
        setter newbucket sz d;
        newhashes.(sz) <- h;
        t.table.(index) <- newbucket;
        t.hashes.(index) <- newhashes;
        si sz <= t.limit && newsz > t.limit alors début
          t.oversize <- t.oversize + 1;
          pour _i = 0 à over_limit faire test_shrink_bucket t fait;
        fin;
        si t.oversize > Array.length t.table / over_limit alors resize t;
      fin sinon si check bucket i alors début
        loop (i + 1)
      fin sinon début
        setter bucket i d;
        hashes.(i) <- h;
      fin;
    dans
    loop 0;
  ;;

  soit add t d =
    soit h = H.hash d dans
    add_aux t set (Some d) h (get_index t h);
  ;;

  soit find_or t d ifnotfound =
    soit h = H.hash d dans
    soit index = get_index t h dans
    soit bucket = t.table.(index) dans
    soit hashes = t.hashes.(index) dans
    soit sz = length bucket dans
    soit rec loop i =
      si i >= sz alors ifnotfound h index
      sinon si h = hashes.(i) alors début
        filtre get_copy bucket i avec
        | Some v quand H.equal v d
           -> début filtre get bucket i avec
              | Some v -> v
              | None -> loop (i + 1)
              fin
        | _ -> loop (i + 1)
      fin sinon loop (i + 1)
    dans
    loop 0
  ;;

  soit merge t d =
    find_or t d (fonc h index -> add_aux t set (Some d) h index; d)
  ;;

  soit find t d = find_or t d (fonc h index -> raise Not_found);;

  soit find_shadow t d iffound ifnotfound =
    soit h = H.hash d dans
    soit index = get_index t h dans
    soit bucket = t.table.(index) dans
    soit hashes = t.hashes.(index) dans
    soit sz = length bucket dans
    soit rec loop i =
      si i >= sz alors ifnotfound
      sinon si h = hashes.(i) alors début
        filtre get_copy bucket i avec
        | Some v quand H.equal v d -> iffound bucket i
        | _ -> loop (i + 1)
      fin sinon loop (i + 1)
    dans
    loop 0
  ;;

  soit remove t d = find_shadow t d (fonc w i -> set w i None) ();;

  soit mem t d = find_shadow t d (fonc w i -> vrai) faux;;

  soit find_all t d =
    soit h = H.hash d dans
    soit index = get_index t h dans
    soit bucket = t.table.(index) dans
    soit hashes = t.hashes.(index) dans
    soit sz = length bucket dans
    soit rec loop i accu =
      si i >= sz alors accu
      sinon si h = hashes.(i) alors début
        filtre get_copy bucket i avec
        | Some v quand H.equal v d
           -> début filtre get bucket i avec
              | Some v -> loop (i + 1) (v :: accu)
              | None -> loop (i + 1) accu
              fin
        | _ -> loop (i + 1) accu
      fin sinon loop (i + 1) accu
    dans
    loop 0 []
  ;;

  soit stats t =
    soit len = Array.length t.table dans
    soit lens = Array.map length t.table dans
    Array.sort compare lens;
    soit totlen = Array.fold_left ( + ) 0 lens dans
    (len, count t, totlen, lens.(0), lens.(len/2), lens.(len-1))
  ;;

fin;;
