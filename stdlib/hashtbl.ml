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

(* Hash tables *)

dehors seeded_hash_param :
  int -> int -> int -> 'a -> int = "caml_hash" "noalloc"
dehors old_hash_param :
  int -> int -> 'a -> int = "caml_hash_univ_param" "noalloc"

soit hash x = seeded_hash_param 10 100 0 x
soit hash_param n1 n2 x = seeded_hash_param n1 n2 0 x
soit seeded_hash seed x = seeded_hash_param 10 100 seed x

(* We do dynamic hashing, and resize the table and rehash the elements
   when buckets become too long. *)

type ('a, 'b) t =
  { modifiable size: int;                        (* number of entries *)
    modifiable data: ('a, 'b) bucketlist array;  (* the buckets *)
    modifiable seed: int;                        (* for randomization *)
    initial_size: int;                        (* initial array size *)
  }

et ('a, 'b) bucketlist =
    Empty
  | Cons de 'a * 'b * ('a, 'b) bucketlist

(* To pick random seeds if requested *)

soit randomized_default =
  soit params =
    essaie Sys.getenv "OCAMLRUNPARAM" avec Not_found ->
    essaie Sys.getenv "CAMLRUNPARAM" avec Not_found -> "" dans
  String.contains params 'R'

soit randomized = ref randomized_default

soit randomize () = randomized := vrai

soit prng = paresseux (Random.State.make_self_init())

(* Creating a fresh, empty table *)

soit rec power_2_above x n =
  si x >= n alors x
  sinon si x * 2 > Sys.max_array_length alors x
  sinon power_2_above (x * 2) n

soit create ?(random = !randomized) initial_size =
  soit s = power_2_above 16 initial_size dans
  soit seed = si random alors Random.State.bits (Lazy.force prng) sinon 0 dans
  { initial_size = s; size = 0; seed = seed; data = Array.make s Empty }

soit clear h =
  h.size <- 0;
  soit len = Array.length h.data dans
  pour i = 0 à len - 1 faire
    h.data.(i) <- Empty
  fait

soit reset h =
  soit len = Array.length h.data dans
  si Obj.size (Obj.repr h) < 4 (* compatibility with old hash tables *)
    || len = h.initial_size alors
    clear h
  sinon début
    h.size <- 0;
    h.data <- Array.make h.initial_size Empty
  fin

soit copy h = { h avec data = Array.copy h.data }

soit length h = h.size

soit resize indexfun h =
  soit odata = h.data dans
  soit osize = Array.length odata dans
  soit nsize = osize * 2 dans
  si nsize < Sys.max_array_length alors début
    soit ndata = Array.make nsize Empty dans
    h.data <- ndata;          (* so that indexfun sees the new bucket count *)
    soit rec insert_bucket = fonction
        Empty -> ()
      | Cons(key, data, rest) ->
          insert_bucket rest; (* preserve original order of elements *)
          soit nidx = indexfun h key dans
          ndata.(nidx) <- Cons(key, data, ndata.(nidx)) dans
    pour i = 0 à osize - 1 faire
      insert_bucket odata.(i)
    fait
  fin

soit key_index h key =
  (* compatibility with old hash tables *)
  si Obj.size (Obj.repr h) >= 3
  alors (seeded_hash_param 10 100 h.seed key) etl (Array.length h.data - 1)
  sinon (old_hash_param 10 100 key) mod (Array.length h.data)

soit add h key info =
  soit i = key_index h key dans
  soit bucket = Cons(key, info, h.data.(i)) dans
  h.data.(i) <- bucket;
  h.size <- h.size + 1;
  si h.size > Array.length h.data dgl 1 alors resize key_index h

soit remove h key =
  soit rec remove_bucket = fonction
    | Empty ->
        Empty
    | Cons(k, i, next) ->
        si compare k key = 0
        alors début h.size <- h.size - 1; next fin
        sinon Cons(k, i, remove_bucket next) dans
  soit i = key_index h key dans
  h.data.(i) <- remove_bucket h.data.(i)

soit rec find_rec key = fonction
  | Empty ->
      raise Not_found
  | Cons(k, d, rest) ->
      si compare key k = 0 alors d sinon find_rec key rest

soit find h key =
  filtre h.data.(key_index h key) avec
  | Empty -> raise Not_found
  | Cons(k1, d1, rest1) ->
      si compare key k1 = 0 alors d1 sinon
      filtre rest1 avec
      | Empty -> raise Not_found
      | Cons(k2, d2, rest2) ->
          si compare key k2 = 0 alors d2 sinon
          filtre rest2 avec
          | Empty -> raise Not_found
          | Cons(k3, d3, rest3) ->
              si compare key k3 = 0 alors d3 sinon find_rec key rest3

soit find_all h key =
  soit rec find_in_bucket = fonction
  | Empty ->
      []
  | Cons(k, d, rest) ->
      si compare k key = 0
      alors d :: find_in_bucket rest
      sinon find_in_bucket rest dans
  find_in_bucket h.data.(key_index h key)

soit replace h key info =
  soit rec replace_bucket = fonction
    | Empty ->
        raise Not_found
    | Cons(k, i, next) ->
        si compare k key = 0
        alors Cons(key, info, next)
        sinon Cons(k, i, replace_bucket next) dans
  soit i = key_index h key dans
  soit l = h.data.(i) dans
  essaie
    h.data.(i) <- replace_bucket l
  avec Not_found ->
    h.data.(i) <- Cons(key, info, l);
    h.size <- h.size + 1;
    si h.size > Array.length h.data dgl 1 alors resize key_index h

soit mem h key =
  soit rec mem_in_bucket = fonction
  | Empty ->
      faux
  | Cons(k, d, rest) ->
      compare k key = 0 || mem_in_bucket rest dans
  mem_in_bucket h.data.(key_index h key)

soit iter f h =
  soit rec do_bucket = fonction
    | Empty ->
        ()
    | Cons(k, d, rest) ->
        f k d; do_bucket rest dans
  soit d = h.data dans
  pour i = 0 à Array.length d - 1 faire
    do_bucket d.(i)
  fait

soit fold f h init =
  soit rec do_bucket b accu =
    filtre b avec
      Empty ->
        accu
    | Cons(k, d, rest) ->
        do_bucket rest (f k d accu) dans
  soit d = h.data dans
  soit accu = ref init dans
  pour i = 0 à Array.length d - 1 faire
    accu := do_bucket d.(i) !accu
  fait;
  !accu

type statistics = {
  num_bindings: int;
  num_buckets: int;
  max_bucket_length: int;
  bucket_histogram: int array
}

soit rec bucket_length accu = fonction
  | Empty -> accu
  | Cons(_, _, rest) -> bucket_length (accu + 1) rest

soit stats h =
  soit mbl =
    Array.fold_left (fonc m b -> max m (bucket_length 0 b)) 0 h.data dans
  soit histo = Array.make (mbl + 1) 0 dans
  Array.iter
    (fonc b ->
      soit l = bucket_length 0 b dans
      histo.(l) <- histo.(l) + 1)
    h.data;
  { num_bindings = h.size;
    num_buckets = Array.length h.data;
    max_bucket_length = mbl;
    bucket_histogram = histo }

(* Functorial interface *)

module type HashedType =
  sig
    type t
    val equal: t -> t -> bool
    val hash: t -> int
  fin

module type SeededHashedType =
  sig
    type t
    val equal: t -> t -> bool
    val hash: int -> t -> int
  fin

module type S =
  sig
    type key
    type 'a t
    val create: int -> 'a t
    val clear : 'a t -> unit
    val reset : 'a t -> unit
    val copy: 'a t -> 'a t
    val add: 'a t -> key -> 'a -> unit
    val remove: 'a t -> key -> unit
    val find: 'a t -> key -> 'a
    val find_all: 'a t -> key -> 'a list
    val replace : 'a t -> key -> 'a -> unit
    val mem : 'a t -> key -> bool
    val iter: (key -> 'a -> unit) -> 'a t -> unit
    val fold: (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val length: 'a t -> int
    val stats: 'a t -> statistics
  fin

module type SeededS =
  sig
    type key
    type 'a t
    val create : ?random:bool -> int -> 'a t
    val clear : 'a t -> unit
    val reset : 'a t -> unit
    val copy : 'a t -> 'a t
    val add : 'a t -> key -> 'a -> unit
    val remove : 'a t -> key -> unit
    val find : 'a t -> key -> 'a
    val find_all : 'a t -> key -> 'a list
    val replace : 'a t -> key -> 'a -> unit
    val mem : 'a t -> key -> bool
    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val length : 'a t -> int
    val stats: 'a t -> statistics
  fin

module MakeSeeded(H: SeededHashedType): (SeededS avec type key = H.t) =
  struct
    type key = H.t
    type 'a hashtbl = (key, 'a) t
    type 'a t = 'a hashtbl
    soit create = create
    soit clear = clear
    soit reset = reset
    soit copy = copy

    soit key_index h key =
      (H.hash h.seed key) etl (Array.length h.data - 1)

    soit add h key info =
      soit i = key_index h key dans
      soit bucket = Cons(key, info, h.data.(i)) dans
      h.data.(i) <- bucket;
      h.size <- h.size + 1;
      si h.size > Array.length h.data dgl 1 alors resize key_index h

    soit remove h key =
      soit rec remove_bucket = fonction
        | Empty ->
            Empty
        | Cons(k, i, next) ->
            si H.equal k key
            alors début h.size <- h.size - 1; next fin
            sinon Cons(k, i, remove_bucket next) dans
      soit i = key_index h key dans
      h.data.(i) <- remove_bucket h.data.(i)

    soit rec find_rec key = fonction
      | Empty ->
          raise Not_found
      | Cons(k, d, rest) ->
          si H.equal key k alors d sinon find_rec key rest

    soit find h key =
      filtre h.data.(key_index h key) avec
      | Empty -> raise Not_found
      | Cons(k1, d1, rest1) ->
          si H.equal key k1 alors d1 sinon
          filtre rest1 avec
          | Empty -> raise Not_found
          | Cons(k2, d2, rest2) ->
              si H.equal key k2 alors d2 sinon
              filtre rest2 avec
              | Empty -> raise Not_found
              | Cons(k3, d3, rest3) ->
                  si H.equal key k3 alors d3 sinon find_rec key rest3

    soit find_all h key =
      soit rec find_in_bucket = fonction
      | Empty ->
          []
      | Cons(k, d, rest) ->
          si H.equal k key
          alors d :: find_in_bucket rest
          sinon find_in_bucket rest dans
      find_in_bucket h.data.(key_index h key)

    soit replace h key info =
      soit rec replace_bucket = fonction
        | Empty ->
            raise Not_found
        | Cons(k, i, next) ->
            si H.equal k key
            alors Cons(key, info, next)
            sinon Cons(k, i, replace_bucket next) dans
      soit i = key_index h key dans
      soit l = h.data.(i) dans
      essaie
        h.data.(i) <- replace_bucket l
      avec Not_found ->
        h.data.(i) <- Cons(key, info, l);
        h.size <- h.size + 1;
        si h.size > Array.length h.data dgl 1 alors resize key_index h

    soit mem h key =
      soit rec mem_in_bucket = fonction
      | Empty ->
          faux
      | Cons(k, d, rest) ->
          H.equal k key || mem_in_bucket rest dans
      mem_in_bucket h.data.(key_index h key)

    soit iter = iter
    soit fold = fold
    soit length = length
    soit stats = stats
  fin

module Make(H: HashedType): (S avec type key = H.t) =
  struct
    inclus MakeSeeded(struct
        type t = H.t
        soit equal = H.equal
        soit hash (seed: int) x = H.hash x
      fin)
    soit create sz = create ~random:faux sz
  fin
