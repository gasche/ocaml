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

type ('a, 'b) binding =
| Absent
| Binding of { mutable k: 'a; mutable v: 'b }

type ('a, 'b) t =
  { mutable size: int;                  (* number of entries *)
    mutable buckets: 'a bucketlist array;  (* the buckets *)
    mutable bindings: ('a, 'b) binding array; (* dynamic array of bindings *)
    (* Invariant: length bindings = (length buckets) * 2 *)
    seed: int;                          (* for randomization *)
    initial_size: int;          (* initial array size *)
  }

and 'a bucketlist =
    Empty
  | Cons of { mutable id: int;          (* unique identifier *)
              mutable key: 'a;
              mutable next: 'a bucketlist }

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
    seed = seed;
    buckets = Array.make s Empty;
    bindings = Array.make (2*s) Absent;
  }

let clear h =
  if h.size > 0 then begin
    h.size <- 0;
    Array.fill h.buckets 0 (Array.length h.buckets) Empty;
    Array.fill h.bindings 0 (Array.length h.bindings) Absent;
  end

let reset h =
  if Obj.size (Obj.repr h) < 4 (* compatibility with old hash tables *) then
    clear h
  else begin
    h.size <- 0;
    h.buckets <- Array.make h.initial_size Empty;
    h.bindings <- Array.make (h.initial_size * 2) Absent;
  end

let copy_bucketlist = function
  | Empty -> Empty
  | Cons {id; key; next} ->
      let rec loop prec = function
        | Empty -> ()
        | Cons {id; key; next} ->
            let r = Cons {id; key; next} in
            begin match prec with
            | Empty -> assert false
            | Cons prec -> prec.next <- r
            end;
            loop r next
      in
      let r = Cons {id; key; next} in
      loop r next;
      r

let copy_binding = function
| Absent -> Absent
| Binding {k; v} -> Binding {k; v}

let copy h = {
  initial_size = h.initial_size;
  size = h.size;
  seed = h.seed;
  buckets = Array.map copy_bucketlist h.buckets;
  bindings = Array.map copy_binding h.bindings;
}

let length h = h.size

let insert_all_buckets ~key_index h odata ndata =
  let nsize = Array.length ndata in
  let ndata_tail = Array.make nsize Empty in
  let rec insert_bucket = function
    | Empty -> ()
    | Cons {key; next; _} as cell ->
        let nidx = key_index h key in
        begin match ndata_tail.(nidx) with
        | Empty -> ndata.(nidx) <- cell;
        | Cons tail -> tail.next <- cell;
        end;
        ndata_tail.(nidx) <- cell;
        insert_bucket next
  in
  for i = 0 to Array.length odata - 1 do
    insert_bucket odata.(i)
  done;
  for i = 0 to nsize - 1 do
      match ndata_tail.(i) with
      | Empty -> ()
      | Cons tail -> tail.next <- Empty
    done

let resize ~key_index h =
  let odata = h.buckets in
  let osize = Array.length odata in
  let nsize = osize * 2 in
  if nsize < Sys.max_array_length then begin
    let ndata = Array.make nsize Empty in
    h.buckets <- ndata;          (* so that indexfun sees the new bucket count *)
    insert_all_buckets ~key_index h odata ndata
  end

let[@inline never] invalid_array_state _h =
  invalid_arg "Hashtbl: invalid array state due to concurrent access"

let[@inline] get_data h id =
  match Array.get h.bindings id with
  | Absent ->
      invalid_array_state h
  | Binding {k = _; v} -> v

let[@inline] set_binding h id k v =
  match Array.get h.bindings id with
  | Absent -> invalid_array_state h
  | Binding b ->
    b.k <- k;
    b.v <- v

let[@inline] size_and_bindings h =
  let bindings = h.bindings in
  let size = h.size in
  if size > Array.length bindings then invalid_array_state h;
  size, bindings

let add_binding_slow_path ~key_index h ~bindings ~size ~capacity binding =
  if size > capacity then invalid_array_state h;
  assert (size = capacity);
  (* We maintain the invariant that [capacity = 2 * length h.buckets],
     and we resize [bindings] and [buckets] at the same time. *)
  assert (capacity = min Sys.max_array_length (2 * Array.length h.buckets));
  h.bindings <- [| |]; (* concurrent operations should fail *)
  let new_capacity = min (capacity * 2) Sys.max_array_length in
  if not (size < new_capacity) then failwith "Hashtbl.add_binding: cannot grow backing array";
  let new_bindings = Array.make new_capacity Absent in
  Array.blit bindings 0 new_bindings 0 size;
  h.bindings <- new_bindings;
  Array.unsafe_set new_bindings size binding;
  h.size <- size + 1;
  resize ~key_index h;
  assert (new_capacity = min Sys.max_array_length (2 * Array.length h.buckets))

let[@inline] add_binding ~key_index h binding =
  let bindings = h.bindings in
  let size = h.size in
  let capacity = Array.length bindings in
  if size >= capacity then
    add_binding_slow_path ~key_index h ~bindings ~size ~capacity binding
  else begin 
    Array.unsafe_set bindings size binding;
    h.size <- size + 1;
  end

let iter f h =
  let size, bindings = size_and_bindings h in
  for i = 0 to size - 1 do
    match Array.unsafe_get bindings i with
    | Absent -> ()
    | Binding {k; v} -> f k v
  done

let replace_bucket_id ~key_index h ~key ~prev_id ~new_id =
  let rec find_bucket = function
  | Empty -> ()
  | Cons c ->
    if c.id = prev_id then c.id <- new_id
    else find_bucket c.next
  in find_bucket h.buckets.(key_index h key)

(* removes the bucket containing id *)
let remove_bucket ~key_index h ~key ~id =
  let i = key_index h key in
  let rec find_bucket prec = function
  | Empty -> ()
  | (Cons {id = prev; next; _}) as slot ->
    if prev = id then
      match prec with
      | Empty -> h.buckets.(i) <- Empty
      | Cons c -> c.next <- next
    else find_bucket slot next
  in find_bucket Empty h.buckets.(i)

(* function that iterates on ids *)

let filter_map_inplace ~key_index f h =
  let size, bindings = size_and_bindings h in
  (* write: the position in which to place filtered elements,
     which is before their current position if elements have been deleted. *)
  let write = ref 0 in
  for read = 0 to size - 1 do
    match Array.unsafe_get bindings read with
    | Absent -> invalid_array_state h
    | Binding ({k = key; v = old_data} as pair) as binding ->
      match f key old_data with
      | None ->
        remove_bucket ~key_index h ~key ~id:!write;
      | Some new_data ->
        if old_data != new_data then 
          pair.v <- new_data;
        if !write <> read then begin
          Array.unsafe_set bindings !write binding;
          replace_bucket_id ~key_index h ~key
            ~prev_id:read ~new_id:!write
        end;
        incr write;
    done;
  h.size <- !write;
  Array.fill bindings !write (size - !write) Absent;
  ()

let fold f h init =
  let size, bindings = size_and_bindings h in
  let accu = ref init in
  for i = 0 to size - 1 do
    match Array.unsafe_get bindings i with
    | Absent -> invalid_array_state h
    | Binding {k; v} -> accu := f k v !accu
  done;
  !accu

type statistics = {
  num_bindings: int;
  num_buckets: int;
  max_bucket_length: int;
  bucket_histogram: int array
}

let rec bucket_length accu = function
  | Empty -> accu
  | Cons {next} -> bucket_length (accu + 1) next

let stats h =
  let mbl =
    Array.fold_left (fun m b -> Int.max m (bucket_length 0 b)) 0 h.buckets in
  let histo = Array.make (mbl + 1) 0 in
  Array.iter
    (fun b ->
      let l = bucket_length 0 b in
      histo.(l) <- histo.(l) + 1)
    h.buckets;
  { num_bindings = h.size;
    num_buckets = Array.length h.buckets;
    max_bucket_length = mbl;
    bucket_histogram = histo }

(** {1 Iterators} *)

let to_seq tbl =
  let size, bindings = size_and_bindings tbl in
  let rec aux bindings ~i ~size () =
    if i = size then Seq.Nil
    else
      match Array.unsafe_get bindings i with
      | Absent -> aux bindings ~i:(i + 1) ~size ()
      | Binding {k; v} ->
          Seq.Cons ((k, v), aux bindings ~i:(i+1) ~size)
  in aux bindings ~i:0 ~size

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
    let copy = copy

    let key_index h key =
      (H.seeded_hash h.seed key) land (Array.length h.buckets - 1)

    let add h key data =
      let i = key_index h key in
      let bucket = Cons {id = h.size; key; next = h.buckets.(i)} in
      h.buckets.(i) <- bucket;
      add_binding ~key_index h (Binding {k = key; v = data})

    let rec remove_bucket h i key prec bucket =
      match bucket with
      | Empty ->
          Absent
      | Cons {id; key = k; next} ->
          if not (H.equal k key)
          then remove_bucket h i key bucket next
          else begin
            let size, bindings = size_and_bindings h in
            let binding = Array.unsafe_get bindings id in
            let last = size - 1 in
            if id <> last then begin
              (* move the last binding to position [id] *)
              let last_binding = Array.unsafe_get bindings last in
              begin match last_binding with
                | Absent -> invalid_array_state h
                | Binding {k = last_key; _} ->
                  replace_bucket_id ~key_index h ~key:last_key
                    ~prev_id:last ~new_id:id;
              end;
              Array.unsafe_set h.bindings id last_binding;
            end;
            Array.unsafe_set h.bindings last Absent;
            h.size <- last;
            begin match prec with
            | Empty -> h.buckets.(i) <- next
            | Cons c -> c.next <- next
            end;
            binding
          end

    let find_and_remove h key =
      let i = key_index h key in
      match remove_bucket h i key Empty h.buckets.(i) with
      | Absent -> None
      | Binding {k = _; v} -> Some v

    let remove h key =
      let i = key_index h key in
      ignore (remove_bucket h i key Empty h.buckets.(i))

    let rec find_rec h key = function
      | Empty ->
          raise Not_found
      | Cons {id; key = k; next} ->
          if H.equal key k then get_data h id
          else find_rec h key next

    let find h key =
      match h.buckets.(key_index h key) with
      | Empty -> raise Not_found
      | Cons {id = id1; key = key1; next = next1} ->
        if H.equal key key1 then get_data h id1
        else match next1 with
        | Empty -> raise Not_found
        | Cons {id = id2; key = key2; next = next2} ->
          if H.equal key key2 then get_data h id2
          else match next2 with
          | Empty -> raise Not_found
          | Cons {id = id3; key = key3; next = next3} ->
            if H.equal key key3 then get_data h id3
            else find_rec h key next3

    let rec find_rec_opt h key = function
    | Empty -> None
    | Cons {id; key = k; next} ->
      if H.equal key k then Some (get_data h id)
      else find_rec_opt h key next

    let find_opt h key =
      match h.buckets.(key_index h key) with
      | Empty -> None
      | Cons {id = id1; key = key1; next = next1} ->
          if H.equal key key1 then Some (get_data h id1)
          else match next1 with
          | Empty -> None
          | Cons {id = id2; key = key2; next = next2} ->
              if H.equal key key2 then Some (get_data h id2)
              else match next2 with
              | Empty -> None
              | Cons {id = id3; key = key3; next = next3} ->
                  if H.equal key key3 then Some (get_data h id3)
                  else find_rec_opt h key next3

    let find_all h key =
      let[@tail_mod_cons] rec find_in_bucket = function
      | Empty ->
          []
      | Cons {id; key = k; next} ->
          if H.equal k key then get_data h id :: find_in_bucket next
          else find_in_bucket next in
      find_in_bucket h.buckets.(key_index h key)

    let rec retrieve_bucket h key bucket =
      match bucket with
      | Empty ->
          bucket
      | Cons {key = k; next; _} ->
          if H.equal k key then bucket
          else retrieve_bucket h key next

    let replace_bucket h key i l data = function
      | Empty ->
        h.buckets.(i) <- Cons {id = h.size; key; next = l};
        add_binding ~key_index h (Binding {k = key; v = data});
      | Cons ({id; _} as slot) ->
        slot.key <- key;
        set_binding h id key data

    let find_and_replace h key data =
      let i = key_index h key in
      let l = h.buckets.(i) in
      let bucket = retrieve_bucket h key l in
      let old_data = match bucket with
        | Cons {id; _} -> Some (get_data h id)
        | Empty -> None
      in
      replace_bucket h key i l data bucket;
      old_data

    let replace h key data =
      let i = key_index h key in
      let l = h.buckets.(i) in
      let bucket = retrieve_bucket h key l in
      replace_bucket h key i l data bucket

    (* Iterators *)

    let rec mem_in_bucket h key = function
      | Empty ->
          false
      | Cons {key = k; next; _} ->
          H.equal k key || mem_in_bucket h key next

    let mem h key =
      mem_in_bucket h key h.buckets.(key_index h key)

    let add_seq tbl i =
      Seq.iter (fun (k,v) -> add tbl k v) i

    let replace_seq tbl i =
      Seq.iter (fun (k,v) -> replace tbl k v) i

    let of_seq i =
      let tbl = create 16 in
      replace_seq tbl i;
      tbl

    let iter = iter
    let filter_map_inplace f h = filter_map_inplace ~key_index f h
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
  then (seeded_hash_param 10 100 h.seed key) land (Array.length h.buckets - 1)
  else invalid_arg "Hashtbl: unsupported hash table format"

let add h key data =
  let buckets = h.buckets in
  if Obj.size (Obj.repr h) < 4 then
    invalid_arg "Hahstbl: unsupported hash table format";
  let i = seeded_hash_param 10 100 h.seed key land (Array.length buckets - 1) in
  let bucketlist = Array.unsafe_get buckets i in
  let bucket = Cons {id = h.size; key; next=bucketlist} in
  let binding = Binding {k = key; v = data} in
  Array.unsafe_set buckets i bucket;
  add_binding ~key_index h binding

let rec remove_bucket h i key prec bucket =
  match bucket with
  | Empty ->
      Absent
  | Cons {id; key = k; next} ->
      if compare k key <> 0
      then remove_bucket h i key bucket next
      else begin
        let size, bindings = size_and_bindings h in
        let binding = Array.unsafe_get bindings id in
        let last = size - 1 in
        if id <> last then begin
          (* move the last binding to position [id] *)
          let last_binding = Array.unsafe_get bindings last in
          begin match last_binding with
            | Absent -> invalid_array_state h
            | Binding {k = last_key; _} ->
              replace_bucket_id ~key_index h ~key:last_key
                ~prev_id:last ~new_id:id;
          end;
          Array.unsafe_set h.bindings id last_binding;
        end;
        Array.unsafe_set h.bindings last Absent;
        h.size <- last;
        begin match prec with
        | Empty -> h.buckets.(i) <- next
        | Cons c -> c.next <- next
        end;
        binding
      end

let find_and_remove h key =
  let i = key_index h key in
  match remove_bucket h i key Empty h.buckets.(i) with
  | Absent -> None
  | Binding {k = _; v} -> Some v

let remove h key =
  let i = key_index h key in
  ignore (remove_bucket h i key Empty h.buckets.(i))

let filter_map_inplace f h = filter_map_inplace ~key_index f h

let rec find_rec h key = function
  | Empty ->
      raise Not_found
  | Cons {id; key = k; next} ->
      if compare key k = 0 then get_data h id
      else find_rec h key next

let find h key =
  match h.buckets.(key_index h key) with
  | Empty -> raise Not_found
  | Cons {id = id1; key = key1; next = next1} ->
      if compare key key1 = 0 then get_data h id1
      else match next1 with
      | Empty -> raise Not_found
      | Cons {id = id2; key = key2; next = next2} ->
          if compare key key2 = 0 then get_data h id2
          else match next2 with
          | Empty -> raise Not_found
          | Cons {id = id3; key = key3; next = next3} ->
              if compare key key3 = 0 then get_data h id3
              else find_rec h key next3

let rec find_rec_opt h key = function
| Empty -> None
| Cons {id; key = k; next} ->
  if compare key k = 0 then Some (get_data h id)
  else find_rec_opt h key next

let find_opt h key =
  match h.buckets.(key_index h key) with
  | Empty -> None
  | Cons {id = id1; key = key1; next = next1} ->
      if compare key key1 = 0 then Some (get_data h id1)
      else match next1 with
      | Empty -> None
      | Cons {id = id2; key = key2; next = next2} ->
          if compare key key2 = 0 then Some (get_data h id2)
          else match next2 with
          | Empty -> None
          | Cons {id = id3; key = key3; next = next3} ->
              if compare key key3 = 0 then Some (get_data h id3)
              else find_rec_opt h key next3

let find_all h key =
  let[@tail_mod_cons] rec find_in_bucket = function
  | Empty ->
      []
  | Cons {id; key = k; next} ->
      if compare k key = 0 then get_data h id :: find_in_bucket next
      else find_in_bucket next in
  find_in_bucket h.buckets.(key_index h key)

let rec retrieve_bucket h key bucket =
  match bucket with
  | Empty ->
      bucket
  | Cons {key = k; next; _} ->
      if compare k key = 0 then bucket
      else retrieve_bucket h key next

let replace_bucket h key i l data bucket =
  match bucket with
  | Empty ->
    h.buckets.(i) <- Cons {id = h.size; key; next=l};
    add_binding ~key_index h (Binding {k = key; v = data});
  | Cons ({id; _} as slot) ->
    slot.key <- key;
    set_binding h id key data

let find_and_replace h key data =
  let i = key_index h key in
  let l = h.buckets.(i) in
  let bucket = retrieve_bucket h key l in
  let old_data = match bucket with
    | Empty -> None
    | Cons {id; _} -> Some (get_data h id)
  in
  replace_bucket h key i l data bucket;
  old_data

let replace h key data =
  let i = key_index h key in
  let l = h.buckets.(i) in
  let bucket = retrieve_bucket h key l in
  replace_bucket h key i l data bucket

let rec mem_in_bucket h key = function
  | Empty ->
      false
  | Cons {key = k; next; _} ->
      compare k key = 0 || mem_in_bucket h key next

let mem h key =
  mem_in_bucket h key h.buckets.(key_index h key)

let add_seq tbl i =
  Seq.iter (fun (k,v) -> add tbl k v) i

let replace_seq tbl i =
  Seq.iter (fun (k,v) -> replace tbl k v) i

let of_seq i =
  let tbl = create 16 in
  replace_seq tbl i;
  tbl

let rebuild ?(random = Atomic.get randomized) h =
  let s = power_2_above 16 (Array.length h.buckets) in
  let seed =
    if random then Random.State.bits (Domain.DLS.get prng_key)
    else if Obj.size (Obj.repr h) >= 4 then h.seed
    else 0 in
  let h' = {
    size = h.size;
    buckets = Array.make s Empty;
    bindings = Array.make s Absent;
    seed = seed;
    initial_size = if Obj.size (Obj.repr h) >= 4 then h.initial_size else s
  } in
  insert_all_buckets ~key_index h' h.buckets h'.buckets;
  h'
