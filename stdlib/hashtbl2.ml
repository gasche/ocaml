(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* Hash tables *)

(* We do dynamic hashing, and resize the table and rehash the elements
   when the load factor becomes too high. *)

type ('a, 'b) t =
  { mutable size: int;                        (* number of entries *)
    mutable data: ('a, 'b) bucketlist array;  (* the buckets *)
    seed: int;                                (* for randomization *)
    initial_size: int;                        (* initial array size *)
    mutable first: ('a, 'b) bucketlist;
    mutable last: ('a, 'b) bucketlist;
  }

and ('a, 'b) bucketlist =
    Empty
  | Cons of {
      mutable key: 'a;
      mutable data: 'b;
      mutable next: ('a, 'b) bucketlist; (* next element in the current bucket list *)
      mutable before: ('a, 'b) bucketlist; (* previous element in insertion order *)
      mutable after: ('a, 'b) bucketlist; (* next element in insertion order *)
    }

(* To pick random seeds if requested *)

(* The runtime stores the initial value of "R" in
   caml_runtime_hashtbl_randomized. We choose to copy this initial value here
   and then keep then in sync in order to avoid adding a C call to every call to
   Hashtbl.create. *)
external randomized : unit -> bool =
  "caml_runtime_hashtbl_is_randomized" [@@noalloc]
let randomized = Atomic.make (randomized ())

external randomize : unit -> unit = "caml_runtime_hashtbl_randomize" [@@noalloc]
let randomize () =
  Atomic.set randomized true;
  (* Update the runtime's value so that the result from Sys.runtime_parameters
     includes "R". There is technically a race here where Hashtbl.create ()
     creates randomized hash tables, but Sys.runtime_parameters doesn't yet
     return R=1. We choose not to care - Hashtbl.is_randomized will always
     return the correct value, and making Sys.runtime_parameters always be in
     sync would either add a C call to every Hashtbl.create call or would
     introduce a complicated dependency cycle between Sys and Hashtbl *)
  randomize ()

let is_randomized () = Atomic.get randomized

let prng_key = Domain.DLS.new_key Random.State.make_self_init

(* Functions which appear before the functorial interface must either be
   independent of the hash function or take it as a parameter (see #2202 and
   code below the functor definitions. *)

(* Creating a fresh, empty table *)

let rec power_2_above x n =
  if x >= n then x
  else if x * 2 > Sys.max_array_length then x
  else power_2_above (x * 2) n

let create ?(random = Atomic.get randomized) initial_size =
  let s = power_2_above 16 initial_size in
  let seed =
    if random then Random.State.bits (Domain.DLS.get prng_key) else 0
  in
  {
    initial_size = s;
    size = 0;
    seed;
    data = Array.make s Empty;
    first = Empty;
    last = Empty;
  }

let clear h =
  if h.size > 0 then begin
    h.size <- 0;
    Array.fill h.data 0 (Array.length h.data) Empty;
    h.first <- Empty;
    h.last <- Empty;
  end

let reset h =
  let len = Array.length h.data in
  if Obj.size (Obj.repr h) < 4 (* compatibility with old hash tables *)
    || len = abs h.initial_size then
    clear h
  else begin
    h.size <- 0;
    h.data <- Array.make (abs h.initial_size) Empty;
    h.first <- Empty;
    h.last <- Empty;
  end

let copy ~key_index oh =
  let ndata = Array.make (Array.length oh.data) Empty in
  let nh = { oh with data = ndata } in
  let rec copy_inorder prev = function
    | Cons {key; data; next = _; before = _; after} ->
      let idx = key_index nh key in
      let nbucket = Cons {key; data; next = ndata.(idx); before = prev; after = Empty} in
      begin match prev with
      | Empty -> nh.first <- nbucket
      | Cons cell -> cell.after <- nbucket
      end;
      copy_inorder nbucket after
    | Empty -> nh.last <- prev
  in
  copy_inorder Empty oh.first;
  nh

let length h = h.size

let insert_all_buckets ~key_index h ~ndata =
  let rec loop = function
    | Empty -> ()
    | Cons cell as bucket ->
      let nidx = key_index h cell.key in
      cell.next <- ndata.(nidx);
      ndata.(nidx) <- bucket;
      loop cell.after
  in
  loop h.first

let resize ~key_index h =
  let odata = h.data in
  let osize = Array.length odata in
  let nsize = osize * 2 in
  if nsize < Sys.max_array_length then begin
    let ndata = Array.make nsize Empty in
    h.data <- ndata;          (* so that indexfun sees the new bucket count *)
    insert_all_buckets ~key_index h ~ndata;
  end

let iter f h =
  let rec loop f = function
    | Empty ->
      ()
    | Cons{key; data; after; _} ->
      f key data; loop f after
  in
  loop f h.first

let filter_map_inplace f h =
  (* First we loop on the elements in-order, calling the user-provided
     function [f]. We update the data, mark some elements for
     deletion and update the threaded doubly-linked list, but we do
     not update the [next] pointers. *)
  let rec trav_inorder nbefore = function
    | Empty ->
      begin match nbefore with
      | Empty -> h.first <- Empty
      | Cons cell -> cell.after <- Empty
      end;
      h.last <- nbefore
    | Cons ({key; data; after; _} as cell) as bucket ->
      match f key data with
      | None ->
        h.size <- h.size - 1;
        (* to mark that a bucket was deleted, we put [h.first]
           in its [after] field, which cannot happen for an input bucket. *)
        cell.after <- h.first;
        trav_inorder nbefore after
      | Some ndata ->
        cell.data <- ndata;
        if nbefore != cell.before then begin
          cell.before <- nbefore;
          begin match nbefore with
          | Empty -> h.first <- bucket
          | Cons cell -> cell.after <- bucket
          end
        end;
        trav_inorder bucket after
  in
  (* Second we loop over the bucket lists, updating [next] pointers
     by skipping deleted elements. *)
  let fix_bucketlist i buckets =
    let rec loop prev = function
      | Empty -> ()
      | Cons cell as bucket ->
        if cell.after == h.first then loop prev cell.next
        else begin
          begin match prev with
          | Empty -> h.data.(i) <- bucket
          | Cons pcell -> pcell.next <- bucket
          end;
          loop bucket cell.next
        end
    in loop Empty buckets
  in
  trav_inorder Empty h.first;
  Array.iteri fix_bucketlist h.data;
  ()

let fold f h init =
  let rec loop f bucket accu =
    match bucket with
    | Empty -> accu
    | Cons {key; data; after; _} -> loop f after (f key data accu)
  in loop f h.first init

type statistics = {
  num_bindings: int;
  num_buckets: int;
  max_bucket_length: int;
  bucket_histogram: int array
}

let rec bucket_length accu = function
  | Empty -> accu
  | Cons{next} -> bucket_length (accu + 1) next

let stats h =
  let mbl =
    Array.fold_left (fun m b -> Int.max m (bucket_length 0 b)) 0 h.data in
  let histo = Array.make (mbl + 1) 0 in
  Array.iter
    (fun b ->
      let l = bucket_length 0 b in
      histo.(l) <- histo.(l) + 1)
    h.data;
  { num_bindings = h.size;
    num_buckets = Array.length h.data;
    max_bucket_length = mbl;
    bucket_histogram = histo }

(** {1 Iterators} *)

let to_seq h =
  let rec loop bucket () = match bucket with
    | Empty ->
      Seq.Nil
    | Cons {key; data; after} ->
      Seq.Cons ((key, data), loop after)
  in loop h.first

let to_seq_keys m = Seq.map fst (to_seq m)

let to_seq_values m = Seq.map snd (to_seq m)

(* Functorial interface *)

module type HashedType =
  sig
    type t
    val equal: t -> t -> bool
    val hash: t -> int
  end

module type SeededHashedType =
  sig
    type t
    val equal: t -> t -> bool
    val seeded_hash: int -> t -> int
  end

module type S =
  sig
    type key
    type !'a t
    val create: int -> 'a t
    val clear : 'a t -> unit
    val reset : 'a t -> unit
    val copy: 'a t -> 'a t
    val add: 'a t -> key -> 'a -> unit
    val remove: 'a t -> key -> unit
    val find_and_remove: 'a t -> key -> 'a option
    val find: 'a t -> key -> 'a
    val find_opt: 'a t -> key -> 'a option
    val find_all: 'a t -> key -> 'a list
    val replace : 'a t -> key -> 'a -> unit
    val find_and_replace : 'a t -> key -> 'a -> 'a option
    val mem : 'a t -> key -> bool
    val iter: (key -> 'a -> unit) -> 'a t -> unit
    val filter_map_inplace: (key -> 'a -> 'a option) -> 'a t -> unit
    val fold: (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val length: 'a t -> int
    val stats: 'a t -> statistics
    val to_seq : 'a t -> (key * 'a) Seq.t
    val to_seq_keys : _ t -> key Seq.t
    val to_seq_values : 'a t -> 'a Seq.t
    val add_seq : 'a t -> (key * 'a) Seq.t -> unit
    val replace_seq : 'a t -> (key * 'a) Seq.t -> unit
    val of_seq : (key * 'a) Seq.t -> 'a t
  end

module type SeededS =
  sig
    type key
    type !'a t
    val create : ?random:bool -> int -> 'a t
    val clear : 'a t -> unit
    val reset : 'a t -> unit
    val copy : 'a t -> 'a t
    val add : 'a t -> key -> 'a -> unit
    val remove : 'a t -> key -> unit
    val find_and_remove : 'a t -> key -> 'a option
    val find : 'a t -> key -> 'a
    val find_opt: 'a t -> key -> 'a option
    val find_all : 'a t -> key -> 'a list
    val replace : 'a t -> key -> 'a -> unit
    val find_and_replace :'a t -> key -> 'a -> 'a option
    val mem : 'a t -> key -> bool
    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val filter_map_inplace: (key -> 'a -> 'a option) -> 'a t -> unit
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val length : 'a t -> int
    val stats: 'a t -> statistics
    val to_seq : 'a t -> (key * 'a) Seq.t
    val to_seq_keys : _ t -> key Seq.t
    val to_seq_values : 'a t -> 'a Seq.t
    val add_seq : 'a t -> (key * 'a) Seq.t -> unit
    val replace_seq : 'a t -> (key * 'a) Seq.t -> unit
    val of_seq : (key * 'a) Seq.t -> 'a t
  end

module MakeSeeded(H: SeededHashedType): (SeededS with type key = H.t) =
  struct
    type key = H.t
    type 'a hashtbl = (key, 'a) t
    type 'a t = 'a hashtbl
    let create = create
    let clear = clear
    let reset = reset

    let key_index h key =
      (H.seeded_hash h.seed key) land (Array.length h.data - 1)

    let copy h = copy ~key_index h

    let add h key data =
      let i = key_index h key in
      let bucket =
        Cons { key; data;
               next=h.data.(i);
               before = h.last;
               after = Empty;
             } in
      begin match h.last with
      | Empty -> h.first <- bucket;
      | Cons cell -> cell.after <- bucket
      end;
      h.last <- bucket;
      h.data.(i) <- bucket;
      h.size <- h.size + 1;
      if h.size > Array.length h.data lsl 1 then resize ~key_index h

    let rec remove_bucket h i key prec bucket =
      match bucket with
      | Empty ->
          bucket
      | Cons ({key=k; _} as cell) ->
          if H.equal k key
          then begin
            h.size <- h.size - 1;
            begin match prec with
            | Empty -> h.data.(i) <- cell.next
            | Cons c -> c.next <- cell.next
            end;
            begin match cell.before with
            | Empty -> h.first <- cell.after
            | Cons bcell -> bcell.after <- cell.after
            end;
            begin match cell.after with
            | Empty -> h.last <- cell.before
            | Cons acell -> acell.before <- cell.before
            end;
            bucket
          end
          else remove_bucket h i key bucket cell.next

    let find_and_remove h key =
      let i = key_index h key in
      let bucket = remove_bucket h i key Empty h.data.(i) in
      match bucket with
      | Empty -> None
      | Cons {data; _} -> Some data

    let remove h key =
      let i = key_index h key in
      ignore (remove_bucket h i key Empty h.data.(i))

    let rec find_rec key = function
      | Empty ->
          raise Not_found
      | Cons{key=k; data; next} ->
          if H.equal key k then data else find_rec key next

    let find h key =
      match h.data.(key_index h key) with
      | Empty -> raise Not_found
      | Cons{key=k1; data=d1; next=next1} ->
          if H.equal key k1 then d1 else
          match next1 with
          | Empty -> raise Not_found
          | Cons{key=k2; data=d2; next=next2} ->
              if H.equal key k2 then d2 else
              match next2 with
              | Empty -> raise Not_found
              | Cons{key=k3; data=d3; next=next3} ->
                  if H.equal key k3 then d3 else find_rec key next3

    let rec find_rec_opt key = function
      | Empty ->
          None
      | Cons{key=k; data; next} ->
          if H.equal key k then Some data else find_rec_opt key next

    let find_opt h key =
      match h.data.(key_index h key) with
      | Empty -> None
      | Cons{key=k1; data=d1; next=next1} ->
          if H.equal key k1 then Some d1 else
          match next1 with
          | Empty -> None
          | Cons{key=k2; data=d2; next=next2} ->
              if H.equal key k2 then Some d2 else
              match next2 with
              | Empty -> None
              | Cons{key=k3; data=d3; next=next3} ->
                  if H.equal key k3 then Some d3 else find_rec_opt key next3

    let find_all h key =
      let[@tail_mod_cons] rec find_in_bucket = function
      | Empty ->
          []
      | Cons{key=k; data=d; next} ->
          if H.equal k key
          then d :: find_in_bucket next
          else find_in_bucket next in
      find_in_bucket h.data.(key_index h key)

    let rec retrieve_bucket key bucket =
      match bucket with
      | Empty ->
          bucket
      | Cons {key=k; next} ->
          if H.equal k key
          then bucket
          else retrieve_bucket key next

    let replace_bucket h key i l data = function
      | Empty ->
        let last = Cons {key; data; next=l; before = h.last; after = Empty} in
        begin match h.last with
        | Empty -> h.first <- last
        | Cons cell -> cell.after <- last
        end;
        h.last <- last;
        h.data.(i) <- last;
        h.size <- h.size + 1;
        if h.size > Array.length h.data lsl 1 then resize ~key_index h
      | Cons slot -> slot.key <- key; slot.data <- data

    let find_and_replace h key data =
      let i = key_index h key in
      let l = h.data.(i) in
      let bucket = retrieve_bucket key l in
      let old_data = match bucket with
        | Cons {data; _} -> Some data
        | Empty -> None
      in
      replace_bucket h key i l data bucket;
      old_data

    let replace h key data =
      let i = key_index h key in
      let l = h.data.(i) in
      let bucket = retrieve_bucket key l in
      replace_bucket h key i l data bucket

    (* Iterators *)

    let rec mem_in_bucket key = function
      | Empty ->
          false
      | Cons{key=k; next} ->
          H.equal k key || mem_in_bucket key next

    let mem h key =
      mem_in_bucket key h.data.(key_index h key)

    let add_seq tbl i =
      Seq.iter (fun (k,v) -> add tbl k v) i

    let replace_seq tbl i =
      Seq.iter (fun (k,v) -> replace tbl k v) i

    let of_seq i =
      let tbl = create 16 in
      replace_seq tbl i;
      tbl

    let iter = iter
    let filter_map_inplace = filter_map_inplace
    let fold = fold
    let length = length
    let stats = stats
    let to_seq = to_seq
    let to_seq_keys = to_seq_keys
    let to_seq_values = to_seq_values
  end

module Make(H: HashedType): (S with type key = H.t) =
  struct
    include MakeSeeded(struct
        type t = H.t
        let equal = H.equal
        let seeded_hash (_seed: int) x = H.hash x
      end)
    let create sz = create ~random:false sz
    let of_seq i =
      let tbl = create 16 in
      replace_seq tbl i;
      tbl
  end

(* Polymorphic hash function-based tables *)
(* Code included below the functorial interface to guard against accidental
   use - see #2202 *)

external seeded_hash_param :
  int -> int -> int -> 'a -> int = "caml_hash" [@@noalloc]

let hash x = seeded_hash_param 10 100 0 x
let hash_param n1 n2 x = seeded_hash_param n1 n2 0 x
let seeded_hash seed x = seeded_hash_param 10 100 seed x

let key_index h key =
  if Obj.size (Obj.repr h) >= 4
  then (seeded_hash_param 10 100 h.seed key) land (Array.length h.data - 1)
  else invalid_arg "Hashtbl: unsupported hash table format"

let copy h = copy ~key_index h

let add h key data =
  let i = key_index h key in
  let bucket =
    Cons {
      key; data;
      next=h.data.(i);
      before = h.last;
      after = Empty;
    } in
  begin match h.last with
  | Empty -> h.first <- bucket;
  | Cons cell -> cell.after <- bucket
  end;
  h.last <- bucket;
  h.data.(i) <- bucket;
  h.size <- h.size + 1;
  if h.size > Array.length h.data lsl 1 then resize ~key_index h

let rec remove_bucket h i key prec bucket =
  match bucket with
  | Empty ->
      bucket
  | Cons ({key=k; next; _} as cell) ->
      if compare k key = 0
      then begin
        h.size <- h.size - 1;
        begin match prec with
        | Empty -> h.data.(i) <- next
        | Cons c -> c.next <- next
        end;
        begin match cell.before with
        | Empty -> h.first <- cell.after
        | Cons bcell -> bcell.after <- cell.after
        end;
        begin match cell.after with
        | Empty -> h.last <- cell.before
        | Cons acell -> acell.before <- cell.before
        end;
        bucket
      end
      else remove_bucket h i key bucket next

let find_and_remove h key =
  let i = key_index h key in
  let bucket = remove_bucket h i key Empty h.data.(i) in
  match bucket with
  | Empty -> None
  | Cons {data; _} -> Some data

let remove h key =
  let i = key_index h key in
  ignore (remove_bucket h i key Empty h.data.(i))

let rec find_rec key = function
  | Empty ->
      raise Not_found
  | Cons{key=k; data; next} ->
      if compare key k = 0 then data else find_rec key next

let find h key =
  match h.data.(key_index h key) with
  | Empty -> raise Not_found
  | Cons{key=k1; data=d1; next=next1} ->
      if compare key k1 = 0 then d1 else
      match next1 with
      | Empty -> raise Not_found
      | Cons{key=k2; data=d2; next=next2} ->
          if compare key k2 = 0 then d2 else
          match next2 with
          | Empty -> raise Not_found
          | Cons{key=k3; data=d3; next=next3} ->
              if compare key k3 = 0 then d3 else find_rec key next3

let rec find_rec_opt key = function
  | Empty ->
      None
  | Cons{key=k; data; next} ->
      if compare key k = 0 then Some data else find_rec_opt key next

let find_opt h key =
  match h.data.(key_index h key) with
  | Empty -> None
  | Cons{key=k1; data=d1; next=next1} ->
      if compare key k1 = 0 then Some d1 else
      match next1 with
      | Empty -> None
      | Cons{key=k2; data=d2; next=next2} ->
          if compare key k2 = 0 then Some d2 else
          match next2 with
          | Empty -> None
          | Cons{key=k3; data=d3; next=next3} ->
              if compare key k3 = 0 then Some d3 else find_rec_opt key next3

let find_all h key =
  let[@tail_mod_cons] rec find_in_bucket = function
  | Empty ->
      []
  | Cons{key=k; data; next} ->
      if compare k key = 0
      then data :: find_in_bucket next
      else find_in_bucket next in
  find_in_bucket h.data.(key_index h key)

let rec retrieve_bucket key bucket =
  match bucket with
  | Empty ->
      bucket
  | Cons {key=k; next} ->
      if compare k key = 0
      then bucket
      else retrieve_bucket key next

let replace_bucket h key i l data bucket =
  match bucket with
  | Empty ->
    let bucket = Cons {key; data; next=l; before = h.last; after = Empty} in
    begin match h.last with
    | Empty -> h.first <- bucket
    | Cons cell -> cell.after <- bucket
    end;
    h.last <- bucket;
    h.data.(i) <- bucket;
    h.size <- h.size + 1;
    if h.size > Array.length h.data lsl 1 then resize ~key_index h
  | Cons (_ as slot) -> slot.key <- key; slot.data <- data

let find_and_replace h key data =
  let i = key_index h key in
  let l = h.data.(i) in
  let bucket = retrieve_bucket key l in
  let old_data = match bucket with
    | Cons {data; _} -> Some data
    | Empty -> None
  in
  replace_bucket h key i l data bucket;
  old_data

let replace h key data =
  let i = key_index h key in
  let l = h.data.(i) in
  let bucket = retrieve_bucket key l in
  replace_bucket h key i l data bucket

let rec mem_in_bucket key = function
  | Empty ->
      false
  | Cons{key=k; next} ->
      compare k key = 0 || mem_in_bucket key next

let mem h key =
  mem_in_bucket key h.data.(key_index h key)

let add_seq tbl i =
  Seq.iter (fun (k,v) -> add tbl k v) i

let replace_seq tbl i =
  Seq.iter (fun (k,v) -> replace tbl k v) i

let of_seq i =
  let tbl = create 16 in
  replace_seq tbl i;
  tbl

let rebuild ?(random = Atomic.get randomized) h =
  let s = power_2_above 16 (Array.length h.data) in
  let seed =
    if random then Random.State.bits (Domain.DLS.get prng_key)
    else if Obj.size (Obj.repr h) >= 4 then h.seed
    else 0 in
  let h' = {
    size = h.size;
    data = Array.make s Empty;
    seed = seed;
    initial_size = if Obj.size (Obj.repr h) >= 4 then h.initial_size else s;
    first = Empty;
    last = Empty;
  } in
  ignore h';
  failwith "Hashtbl.rebuild: TODO";
  (* insert_all_buckets_copy ~key_index h' h.data h'.data; *)
  (* h' *)
