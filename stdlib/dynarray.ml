(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                            Simon Cruanes                               *)
(*                                                                        *)
(*   Copyright 2022 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

type 'a t = {
  mutable length : int;
  mutable arr : 'a slot array;
}
(* {2 The type ['a t]}

   A dynamic array is represented using a backing array [arr] and
   a [length]. It behaves as an array of size [length] -- the indices
   from [0] to [length - 1] included contain user-provided values and
   can be [get] and [set] -- but the length may also change in the
   future by adding or removing elements at the end.

   We use the following concepts;
   - capacity: the length of the backing array:
     [Array.length  arr]
   - live space: the portion of the backing array with
     indices from [0] to [length] excluded.
   - empty space: the portion of the backing array
     from [length] to the end of the backing array.

   {2 The type ['a slot]}

   We should not keep a user-provided value in the empty space, as
   this could extend its lifetime and may result in memory leaks of
   arbitrary size. Functions that remove elements from the dynamic
   array, such as [pop_last] or [truncate], must really erase the
   element from the backing array.

   This constraint makes it difficult to represent an dynamic array of
   elements of type ['a] with a backing array of type ['a array]: what
   valid value of type ['a] would we use in the empty space? Typical
   choices include:
   - accepting scenarios where we actually leak user-provided values
     (but this can blowup memory usage in some cases, and is hard to debug)
   - requiring a "dummy" value at creation of the dynamic array
     or in the parts of the API that grow the empty space
     (but users find this very inconvenient)
   - using arcane Obj.magic tricks
     (but experts don't agree on which tricks are safe to use and/or
      should be used here)
   - using a backing array of ['a option] values, using [None]
     in the empty space
     (but this gives a noticeably less efficient memory representation)

   In the present implementation, we use the ['a option] approach,
   with a twist. With ['a option], calling [set a i x] must reallocate
   a new [Some x] block:
{[
   let set a i x =
     if i < 0 || i >= a.length then error "out of bounds";
     a.arr.(i) <- Some x
]}
   Instead we use the type ['a slot] below,
   which behaves as an option whose [Some] constructor
   (called [Elem] here) has a _mutable_ argument.
*)
and 'a slot =
| Empty
| Elem of { mutable v: 'a }
(*
   This gives an allocation-free implementation of [set] that calls
   [Array.get] (instead of [Array.set]) on the backing array and then
   mutates the [v] parameter. In pseudo-code:
{[
   let set a i x =
     if i < 0 || i >= a.length then error "out of bounds";
     match a.arr.(i) with
     | Empty -> error "invalid state: missing element"
     | Elem s -> s.v <- x
]}
   With this approach, accessing an element still pays the cost of an
   extra indirection (compared to approaches that do not box elements
   in the backing array), but only operations that add new elements at
   the end of the array pay extra allocations.

   There are some situations where ['a option] is better: it makes
   [pop_last_opt] more efficient as the underlying option can be
   returned directly, and it also lets us use [Array.blit] to
   implement [append]. We believe that optimzing [get] and [set] is
   more important for dynamic arrays.

   {2 Invariants and valid states}

   We enforce the invariant that [length >= 0] at all times.
   we rely on this invariant for optimization.

   The following conditions define what we call a "valid" dynarray:
   - valid length: [length <= Array.length arr]
   - no missing element in the live space:
     forall i, [0 <= i <=length] implies [arr.(i) <> Empty]
   - no element in the empty space:
     forall i, [0 <= i < length] implies [arr.(i) = Empty]

   Unfortunately, we cannot easily enforce validity as an invariant in
   presence of concurrent udpates. We can thus observe dynarrays in
   "invalid states". Our implementation may raise exceptions or return
   incorrect results on observing invalid states, but of course it
   must preserve memory safety.
*)

module Error = struct
  let index_out_of_bounds f ~i ~length =
    Printf.ksprintf invalid_arg
      "Dynarray.%s: index %d out of bounds (0..%d)"
      f i length

  let negative_length f n =
    Printf.ksprintf invalid_arg
      "Dynarray.%s: negative length %d"
      f n

  let negative_capacity f n =
    Printf.ksprintf invalid_arg
      "Dynarray.%s: negative capacity %d"
      f n

  let requested_length_out_of_bounds f requested_length =
    (* We do not consider this error as a programming error,
       so we raise [Failure] instead of [Invalid_argument]. *)
    Printf.ksprintf failwith
      "Dynarray.%s: cannot grow to requested length %d (max_array_length is %d)"
      f requested_length Sys.max_array_length

  (* When observing an invalid state ([missing_element],
     [invalid_length]), we do not give the name of the calling function
     in the error message, as the error is related to invalid operations
     performed earlier, and not to the callsite of the function
     itself. *)

  let missing_element ~i ~length =
    Printf.ksprintf invalid_arg
      "Dynarray: invalid array (missing element at position %d < length %d)"
      i length

  let invalid_length ~length ~capacity =
    Printf.ksprintf invalid_arg
      "Dynarray: invalid array (length %d > capacity %d)"
      length capacity

  (* When an [Empty] element is observed unexpectedly at index [i],
     it may be either an out-of-bounds access or an invalid-state situation
     depending on whether [i <= length]. *)
  let unexpected_empty_element f ~i ~length =
    if i <= length then
      missing_element ~i ~length
    else
      index_out_of_bounds f ~i ~length
end

(** Careful unsafe access. *)

(* Postcondition on non-exceptional return:
   [length <= Array.length arr] *)
let check_valid_length length arr =
  let capacity = Array.length arr in
  if length > capacity then
    Error.invalid_length ~length ~capacity

(* Precondition: [0 <= i < length <= Array.length arr]

   This precondition is typically guaranteed by knowing
   [0 <= i < length] and calling [check_valid_length length arr].*)
let unsafe_get arr ~i ~length =
  match Array.unsafe_get arr i with
  | Empty -> Error.missing_element ~i ~length
  | Elem {v} -> v


(** {1:dynarrays Dynamic arrays} *)

let create () = {
  length = 0;
  arr = [| |];
}

let make n x =
  if n < 0 then Error.negative_length "make" n;
  {
    length = n;
    arr = Array.init n (fun _ -> Elem {v = x});
  }

let init n f =
  if n < 0 then Error.negative_length "init" n;
  {
    length = n;
    arr = Array.init n (fun i -> Elem {v = f i});
  }

let get a i =
  (* This implementation will propagate an [Invalid_arg] exception
     from array lookup if the index is out of the backing array,
     instead of using our own [Error.index_out_of_bounds]. This is
     allowed by our specification, and more efficient -- no need to
     check that [length a <= capacity a] in the fast path. *)
  match a.arr.(i) with
  | Elem s -> s.v
  | Empty ->
      Error.unexpected_empty_element "get" ~i ~length:a.length

let set a i x =
  (* See {!get} comment on the use of checked array
     access without our own bound checking. *)
  match a.arr.(i) with
  | Elem s -> s.v <- x
  | Empty ->
      Error.unexpected_empty_element "set" ~i ~length:a.length

let length a = a.length

let is_empty a = (a.length = 0)

let copy {length; arr} = {
  length;
  arr =
    Array.map (function
      | Empty -> Empty
      | Elem {v} -> Elem {v}
    ) arr;
}

(** {1:removing Removing elements} *)

let pop_last a =
  let {arr; length} = a in
  if length = 0 then raise Not_found;
  let last = length - 1 in
  (* We know [length > 0] so [last >= 0].
     See {!get} comment on the use of checked array
     access without our own bound checking.
  *)
  match arr.(last) with
  (* At this point we know that [last] is a valid index in [arr]. *)
  | Empty ->
      Error.missing_element ~i:last ~length
  | Elem s ->
      Array.unsafe_set arr last Empty;
      a.length <- last;
      s.v

let pop_last_opt a =
  match pop_last a with
  | exception Not_found -> None
  | x -> Some x

let remove_last a =
  let last = length a - 1 in
  if last >= 0 then begin
    a.length <- last;
    a.arr.(last) <- Empty;
  end

let truncate a n =
  if n < 0 then Error.negative_length "truncate" n;
  let {arr; length} = a in
  if length <= n then ()
  else begin
    a.length <- n;
    Array.fill arr n (length - n) Empty;
  end

let clear a = truncate a 0


(** {1:capacity Backing array and capacity} *)

let next_capacity n =
  let n' =
    (* For large values of n, we use 1.5 as our growth factor.

       For smaller values of n, we grow more aggressively to avoid
       reallocating too much when accumulating elements into an empty
       array.

       The constants "512 words" and "8 words" below are taken from
         https://github.com/facebook/folly/blob/
           c06c0f41d91daf1a6a5f3fc1cd465302ac260459/folly/FBVector.h#L1128-L1157
    *)
    if n <= 512 then n * 2
    else n + n / 2
  in
  (* jump directly from 0 to 8 *)
  min (max 8 n') Sys.max_array_length

let ensure_capacity a requested_length =
  let arr = a.arr in
  let cur_capacity = Array.length arr in
  if cur_capacity >= requested_length then
    (* This is the fast path, the code up to here must do as little as
       possible. (This is why we don't use [let {arr; length} = a] as
       usual, the length is not needed in the fast path.)*)
    ()
  else begin
    if requested_length < 0 then
      Error.negative_capacity "ensure_capacity" requested_length;
    if requested_length > Sys.max_array_length then
      Error.requested_length_out_of_bounds "ensure_capacity" requested_length;
    let new_capacity = ref cur_capacity in
    while !new_capacity < requested_length do
      new_capacity := next_capacity !new_capacity
    done;
    let new_capacity = !new_capacity in
    assert (new_capacity >= requested_length);
    let new_arr = Array.make new_capacity Empty in
    Array.blit arr 0 new_arr 0 a.length;
    a.arr <- new_arr;
    assert (0 <= requested_length);
    assert (requested_length <= Array.length new_arr);
  end

let fit_capacity a =
  if Array.length a.arr = a.length
  then ()
  else a.arr <- Array.sub a.arr 0 a.length

let reset a =
  clear a;
  fit_capacity a


(** {1:adding Adding elements} *)

(* We chose an implementation of [add_last a x] that behaves correctly
   in presence of aynchronous code execution around allocations and
   poll points: if another thread or a callback gets executed on
   allocation, we add the element at the new end of the dynamic array.

   (We do not give the same guarantees in presence of concurrent
   updates, which are much more expansive to protect against.)
*)

(* [add_last_if_room a elem] only writes the slot if there is room, and
   returns [false] otherwise.

   It is sequentially atomic -- in absence of unsychronized concurrent
   uses, the fields of [a.arr] and [a.length] will not be mutated
   by any other code during execution of this function.
*)
let[@inline] add_last_if_room a elem =
  (* BEGIN ATOMIC *)
  let {arr; length} = a in
  (* we know [0 <= length] *)
  if length >= Array.length arr then false
  else begin
    (* we know [0 <= length < Array.length arr] *)
    Array.unsafe_set arr length elem;
    a.length <- length + 1;
    true
  end
  (* END ATOMIC *)

let add_last a x =
  let elem = Elem {v = x} in
  if add_last_if_room a elem then ()
  else begin
    (* slow path *)
    let rec grow_and_add a elem =
      ensure_capacity a (length a + 1);
      if not (add_last_if_room a elem)
      then grow_and_add a elem
    in grow_and_add a elem
  end

let append_iter a iter b =
  iter (fun x -> add_last a x) b

let append_list a li =
  append_iter a List.iter li

let append_seq a seq =
  append_iter a Seq.iter seq

(* append_array: same [..._if_room] and loop logic as [add_last]. *)

let append_array_if_room a b =
  (* BEGIN ATOMIC *)
  let {arr; length = length_a} = a in
  let length_b = Array.length b in
  if length_a + length_b > Array.length arr then false
  else begin
    a.length <- length_a + length_b;
    (* END ATOMIC *)
    (* Note: we intentionally update the length *before* filling the
       elements. This "reserve before fill" approach provides better
       behavior than "fill then notify" in presence of reentrant
       modifications (which may occur below, on a poll point in the loop or
       the [Elem] allocation):

       - If some code asynchronously adds new elements after this
         length update, they will go after the space we just reserved,
         and in particular no addition will be lost. If instead we
         updated the length after the loop, any asynchronous addition
         during the loop could be erased or erase one of our additions,
         silently, without warning the user.

       - If some code asynchronously iterates on the dynarray, or
         removes elements, or otherwise tries to access the
         reserved-but-not-yet-filled space, it will get a clean "missing
         element" error. This is worse than with the fill-then-notify
         approach where the new elements would only become visible
         (to iterators, for removal, etc.) alltogether at the end of
         loop.

       To summarise, "reserve before fill" is better on add-add races,
       and "fill then notify" is better on add-remove or add-iterate
       races. But the key difference is the failure mode:
       reserve-before fails on add-remove or add-iterate races with
       a clean error, while notify-after fails on add-add races with
       silently disappearing data. *)
    for i = 0 to length_b - 1 do
      let x = Array.unsafe_get b i in
      Array.unsafe_set arr (length_a + i) (Elem {v = x})
    done;
    true
  end

let append_array a b =
  if append_array_if_room a b then ()
  else begin
    (* slow path *)
    let rec grow_and_append a b =
      ensure_capacity a (length a + Array.length b);
      if not (append_array_if_room a b)
      then grow_and_append a b
    in grow_and_append a b
  end

(* append: same [..._if_room] and loop logic as [add_last],
   same reserve-before-fill logic as [append_array]. *)

(* Note: unlike [add_last_if_room], [append_if_room] is *not* atomic. *)
let append_if_room a b =
  (* BEGIN ATOMIC *)
  let {arr = arr_a; length = length_a} = a in
  let {arr = arr_b; length = length_b} = b in
  if length_a + length_b > Array.length arr_a then false
  else begin
    a.length <- length_a + length_b;
    (* END ATOMIC *)
    check_valid_length length_b arr_b;
    for i = 0 to length_b - 1 do
      let x = unsafe_get arr_b ~i ~length:length_b in
      Array.unsafe_set arr_a (length_a + i) (Elem {v = x})
    done;
    true
  end

let append a b =
  if append_if_room a b then ()
  else begin
    (* slow path *)
    let rec grow_and_append a b =
      ensure_capacity a (length a + length b);
      if not (append_if_room a b)
      then grow_and_append a b
    in grow_and_append a b
  end



(** {1:iteration Iteration} *)

(* The implementation choice that we made for iterators is the one
   that maximizes efficiency by avoiding repeated bound checking: we
   check the length of the dynamic array once at the beginning, and
   then only operate on that portion of the dynarray, ignoring
   elements added in the meantime.

   The specification says that it is unspecified which updates to the
   dynarray happening during iteration will be observed by the
   iterator. With our current implementation, they in fact have
   a clear characterization, we:
   - ignore all elements added during the iteration
   - fail with a clean error if a removal occurs during iteration
   - observe all [set] updates on the initial elements that have not
     been visited yet.

   This is slightly stronger/simpler than typical unboxed
   implementation, where "observing [set] updates" stops after the
   first reallocation of the backing array. It is a coincidence that
   our implementation shares the mutable Elem references between the
   initial and the reallocated backing array, and thus also observes
   update happening after reallocation.
*)

let iter k a =
  let {arr; length} = a in
  check_valid_length length arr;
  for i = 0 to length - 1 do
    k (unsafe_get arr ~i ~length)
  done

let iteri k a =
  let {arr; length} = a in
  check_valid_length length arr;
  for i = 0 to length - 1 do
    k i (unsafe_get arr ~i ~length)
  done

let map f a =
  let {arr; length} = a in
  check_valid_length length arr;
  {
    length;
    arr = Array.init length (fun i ->
      Elem {v = f (unsafe_get arr ~i ~length)});
  }

let mapi f a =
  let {arr; length} = a in
  check_valid_length length arr;
  {
    length;
    arr = Array.init length (fun i ->
      Elem {v = f i (unsafe_get arr ~i ~length)});
  }

let fold_left f acc a =
  let {arr; length} = a in
  check_valid_length length arr;
  let rec fold acc arr i length =
    if i = length then acc
    else
      let v = unsafe_get arr ~i ~length in
      fold (f acc v) arr (i+1) length
  in fold acc arr 0 length

let exists p a =
  let {arr; length} = a in
  check_valid_length length arr;
  let rec loop p arr i length =
    if i = length then false
    else
      p (unsafe_get arr ~i ~length)
      || loop p arr (i + 1) length
  in loop p arr 0 length

let for_all p a =
  let {arr; length} = a in
  check_valid_length length arr;
  let rec loop p arr i length =
    if i = length then true
    else
      p (unsafe_get arr ~i ~length)
      && loop p arr (i + 1) length
  in loop p arr 0 length

let filter f a =
  let b = create () in
  iter (fun x -> if f x then add_last b x) a;
  b

let filter_map f a =
  let b = create() in
  iter (fun x ->
    match f x with
    | None -> ()
    | Some y -> add_last b y
  ) a;
  b


(** {1:conversions Conversions to other data structures} *)

(* The eager [to_*] conversion functions behave similarly to iterators
   in presence of updates during computation. The [to_seq*] functions
   obey their more permissive specification, which tolerates any
   concurrent update. *)

let of_array a =
  let length = Array.length a in
  {
    length;
    arr = Array.init length (fun i -> Elem {v = Array.unsafe_get a i});
  }

let to_array a =
  let {arr; length} = a in
  check_valid_length length arr;
  Array.init length (fun i -> unsafe_get arr ~i ~length)

let of_list li =
  let a = create () in
  List.iter (fun x -> add_last a x) li;
  a

let to_list a =
  let {arr; length} = a in
  check_valid_length length arr;
  let l = ref [] in
  for i = length - 1 downto 0 do
    l := unsafe_get arr ~i ~length :: !l
  done;
  !l

let of_seq seq =
  let init = create() in
  append_seq init seq;
  init

let to_seq a =
  let rec aux i () =
    if i >= length a then Seq.Nil
    else begin
      Seq.Cons (get a i, aux (i + 1))
    end
  in
  aux 0

let to_seq_rev a =
  let rec aux i () =
    if i < 0 then Seq.Nil
    else if i >= length a then
      (* If some elements have been removed in the meantime, we skip
         those elements and continue with the new end of the array. *)
      aux (length a - 1) ()
    else Seq.Cons (get a i, aux (i - 1))
  in
  aux (length a - 1)
