module Obj_opt : sig
  type t
  val none : t
  val some : 'a -> t
  val is_some : t -> bool

  (** [unsafe_get obj] may only be called safely
      if [is_some] is true.

      [unsafe_get (some v)] is equivalent to
      [Obj.obj (Obj.repr v)]. *)
  val unsafe_get : t -> 'a
end = struct
  type t = Obj.t
  let none = Obj.repr (ref 0)
  let some v = Obj.repr v
  let is_some obj = (obj != none)
  let unsafe_get obj = Obj.obj obj
end

module type Storage_interface = sig
    type 'a key

    val new_key : ?split_from_parent:('a -> 'a) -> (unit -> 'a) -> 'a key

    val get : 'a key -> 'a

    val set : 'a key -> 'a -> unit

    type key_value = KV : 'a key * 'a -> key_value
    val get_initial_keys : unit -> key_value list
    val set_initial_keys : key_value list -> unit
end

module DLS : Storage_interface = struct

  type dls_state = Obj_opt.t array

  external get_dls_state : unit -> dls_state = "%dls_get"

  external compare_and_set_dls_state : dls_state -> dls_state -> bool =
    "caml_domain_dls_compare_and_set" [@@noalloc]

  type 'a key = int * (unit -> 'a)

  (* Manipulating existing keys. *)

  (* If necessary, grow the current domain's local state array such that [idx]
   * is a valid index in the array. *)
  let rec maybe_grow idx =
    let st = get_dls_state () in
    let sz = Array.length st in
    if idx < sz then st
    else begin
      let rec compute_new_size s =
        if idx < s then s else compute_new_size (2 * s)
      in
      let new_sz = compute_new_size (max sz 8) in
      let new_st = Array.make new_sz Obj_opt.none in
      Array.blit st 0 new_st 0 sz;
      (* We want a implementation that is safe with respect to
         single-domain multi-threading: retry if the DLS state has
         changed under our feet.
         Note that the number of retries will be very small in
         contended scenarios, as the array only grows, with
         exponential resizing. *)
      if compare_and_set_dls_state st new_st
      then new_st
      else maybe_grow idx
    end

  let set (type a) (idx, _init) (x : a) =
    let st = maybe_grow idx in
    (* [Sys.opaque_identity] ensures that flambda does not look at the type of
     * [x], which may be a [float] and conclude that the [st] is a float array.
     * We do not want OCaml's float array optimisation kicking in here. *)
    st.(idx) <- Obj_opt.some (Sys.opaque_identity x)

  let[@inline never] array_compare_and_set a i oldval newval =
    (* Note: we cannot use [@poll error] due to the
       allocations on a.(i) in the Double_array case. *)
    let curval = a.(i) in
    if curval == oldval then (
      Array.unsafe_set a i newval;
      true
    ) else false

  let get (type a) ((idx, init) : a key) : a =
    let st = maybe_grow idx in
    let obj = st.(idx) in
    if Obj_opt.is_some obj
    then (Obj_opt.unsafe_get obj : a)
    else begin
      let v : a = init () in
      let new_obj = Obj_opt.some (Sys.opaque_identity v) in
      (* At this point, [st] or [st.(idx)] may have been changed
         by another thread on the same domain.

         If [st] changed, it was resized into a larger value,
         we can just reuse the new value.

         If [st.(idx)] changed, we drop the current value to avoid
         letting other threads observe a 'revert' that forgets
         previous modifications. *)
      let st = get_dls_state () in
      if array_compare_and_set st idx obj new_obj
      then v
      else begin
        (* if st.(idx) changed, someone must have initialized
           the key in the meantime. *)
        let updated_obj = st.(idx) in
        if Obj_opt.is_some updated_obj
        then (Obj_opt.unsafe_get updated_obj : a)
        else assert false
      end
    end

  (* Creating new keys. *)

  let key_counter = Atomic.make 0

  let make init =
    let idx = Atomic.fetch_and_add key_counter 1 in
    (idx, init)

  (* Keys initialized by the parent. *)

  type key_initializer =
    KI: 'a key * ('a -> 'a) -> key_initializer

  let parent_keys = Atomic.make ([] : key_initializer list)

  let rec add_parent_key ki =
    let l = Atomic.get parent_keys in
    if not (Atomic.compare_and_set parent_keys l (ki :: l))
    then add_parent_key ki

  let new_key ?split_from_parent init_orphan =
    let k = make init_orphan in
    begin match split_from_parent with
    | None -> ()
    | Some split -> add_parent_key (KI(k, split))
    end;
    k

  type key_value = KV : 'a key * 'a -> key_value

  let get_initial_keys () : key_value list =
    List.map
      (fun (KI (k, split)) -> KV (k, (split (get k))))
      (Atomic.get parent_keys)

  let set_initial_keys (l: key_value list) =
    List.iter (fun (KV (k, v)) -> set k v) l

end
