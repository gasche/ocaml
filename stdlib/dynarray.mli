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

(** Dynamic arrays.

    The {!Array} module provide arrays of fixed length. In contrast,
    the length of a dynamic array can change over time, we can add
    more elements or remove elements at the end of the array.

    This is typically used to accumulate elements whose number is not
    known in advance or changes during computation, while also
    providing fast access to elements at arbitrary positions.

{[
    let dynarray_of_list li =
      let arr = Dynarray.create () in
      List.iter (fun v -> Dynarray.add_last arr v) li;
      arr
]}

    The {!Buffer} module provides similar features, but it is
    specialized for accumulating characters into a dynamically-growing
    string.

    The {!Stack} module provides a last-in first-out data structure
    that can be easily implemented on top of dynamic arrays.

    @since 5.1
*)

(** {b Unsynchronized accesses} *)

[@@@alert unsynchronized_accesses
    "Unsynchronized accesses to dynamic arrays are a programming error."
]

(**
   Unsynchronized accesses to a dynamic array may lead to an invalid
   dynamic array state. Thus, concurrent accesses to dynamic arrays
   must be synchronized (for instance with a {!Mutex.t}).
*)

(** {1:dynarrays Dynamic arrays} *)

type 'a t
(** A dynamic array containing values of type ['a].

    A dynamic array [a] is an array, that is, it provides
    constant-time [get] and [set] operation on indices between [0] and
    [Dynarray.length a - 1] included. Its {b length} may change over
    time by adding or removing elements to the end of the array.
*)

val create : unit -> 'a t
(** [create ()] is a new, empty array. *)

val make : int -> 'a -> 'a t
(** [make n x] makes a array of length [n], filled with [x]. *)

val init : int -> (int -> 'a) -> 'a t
(** [init n f] is a new array [a] of length [n],
    such that [get a i] is [f i]. In other words,
    [a] is the the array whose elements are
    [f 0; f 1; f 2; ...; f (n - 1)].

    This is similar to {!Array.init}. *)

val get : 'a t -> int -> 'a
(** [get a i] is the [i]-th element of [a], starting with index [0].

    @raise Invalid_argument if the index is
      invalid (not in [0 .. length a-1]). *)

val set : 'a t -> int -> 'a -> unit
(** [set a i x] sets the [i]-th element of [a] to be [x].

    Just like {!get}, [i] must be between [0] and [length a - 1]
    included. [set] does not add new elements to the array -- see
    {!add_last} to add an element.

    @raise Invalid_argument if the index is invalid. *)

val length : _ t -> int
(** [length a] is the number of elements in the array.
    The last element of [a], if not empty, is [get a (length a - 1)].
    This operation is constant time. *)

val is_empty : 'a t -> bool
(** [is_empty a] is [true] if [a] is empty, that is, if [length a = 0]. *)

val copy : 'a t -> 'a t
(** [copy a] is a shallow copy of [a], that can be modified independently. *)


(** {1:adding Adding elements}

    Note: all operations adding elements can raise [Failure] if the
    length would need to grow beyond {!Sys.max_array_length}.

    It is a programming error to mutate the dynamic array during the
    execution of one of the [append*] functions, and the result is
    unspecified in this case, in particular the array may end up in an
    invalid state and the [append*] functions may raise
    [Invalid_argument] in this situation.
*)

val add_last : 'a t -> 'a -> unit
(** [add_last a x] adds the element [x] at the end of the array [a].
    The length of [a] increases by [1]. *)

val append_array : 'a t -> 'a array -> unit
(** [append_array a b] adds all elements of [b] at the end of [a],
    in the order they appear in [b].

    For example, [a] will contain [1,2,3,4,5,6] after this code runs:
    {[
      let a = of_list [1;2;3];;
      let () = append a [|4; 5; 6|];;
    ]}
*)

val append_list : 'a t -> 'a list -> unit
(** Like {!append_array} but with a list. *)

val append : 'a t -> 'a t -> unit
(** [append a b] is like [append_array a b],
    but [b] is itself a dynamic arreay instead of a fixed-size array.

    Beware! Calling [append a a] iterates on [a] and adds elements to
    it at the same time; it is a programming error and its behavior is
    unspecified. In particular, if elements coming from
    [a]-on-the-right become visible in [a]-on-the-left during the
    iteration on [a], they may added again and again, resulting in an
    infinite loop.
*)

val append_seq : 'a t -> 'a Seq.t -> unit
(** Like {!append_array} but with a sequence.

    Beware! Calling [append_seq a (to_seq a)] is unspecified and may
    result in an infinite loop, see the {!append} comment above.
*)

val append_iter :
  'a t ->
  (('a -> unit) -> 'iter-> unit) ->
  'iter -> unit
(** [append_iter a iter x] adds to [a] each element in [x]. It uses [iter]
    to iterate over [x].

    For example, [append_iter a List.iter [1;2;3]] would add elements
    [1], [2], and [3] at the end of [a].
    [append_iter a Queue.iter q] adds elements from the queue [q]. *)


(** {1:removing Removing elements} *)

val pop_last_opt : 'a t -> 'a option
(** [pop_last_opt a] removes and returns the last element of [a],
    or [None] if the array is empty. *)

val pop_last : 'a t -> 'a
(** [pop_last a] removes and returns the last element of [a].

    @raise Not_found on an empty array. *)

val remove_last : 'a t -> unit
(** [remove_last a] removes the last element of [a] , or does nothing
    if [is_empty a].
*)

val clear : 'a t -> unit
(** [clear a] removes all the elements of [a].

    It is equivalent to [truncate a 0].

    Similar to {!Buffer.clear}.
*)

val truncate : 'a t -> int -> unit
(** [truncate a n] truncates [a] to have at most [n] elements.

    It removes elements whose index is great or equal than [n].
    It does nothing if [n >= length a].

    It is equivalent to:
    {[
      while length a > n do
        remove_last a
      done
    ]}

    Similar to {!Buffer.truncate}.
*)


(** {1:iteration Iteration}

    The iteration functions traverse the elements of a dynamic array.

    It is a programming error to mutate the dynamic array during the
    traversal, and the result is unspecified in this case. In
    particular, each mutation may or may not be observed by the
    iteration function, the array may end up in an invalid state and
    iterators may raise [Invalid_argument] in this situation.
*)

val iter : ('a -> unit) -> 'a t -> unit
(** [iter f a] calls [f] on each element of [a], in increasing index order. *)

val iteri : (int -> 'a -> unit) -> 'a t -> unit
(** [iteri f a] calls [f i x] for each [x] at index [i] in [a]. *)

val map : ('a -> 'b) -> 'a t -> 'b t
(** [map f a] is a new array of length [length a], with elements mapped
    from [a] using [f]. *)

val mapi : (int -> 'a -> 'b) -> 'a t -> 'b t
(** [mapi f v] is just like {!map}, but it also passes in the index
    of each element as the first argument to the function [f]. *)

val fold_left : ('acc -> 'a -> 'acc) -> 'acc -> 'a t -> 'acc
(** [fold_left f acc a] folds [f] over [a] starting with accumulator [acc]. *)

val exists : ('a -> bool) -> 'a t -> bool
(** [exists f a] returns [true] if some element of [a] satisfies [f]. *)

val for_all : ('a -> bool) -> 'a t -> bool
(** [for_all f a] returns [true] if all elements of [a] satisfie [f].
    This includes the case where [a] is empty. *)

val filter : ('a -> bool) -> 'a t -> 'a t
(** [filter f a] is an array containing all elements of [a] that satisfy [f] *)

val filter_map : ('a -> 'b option) -> 'a t -> 'b t
(** [filter_map f a] is a new array [b], such that for each item [x] in [a]:
  - if [f x = Some y], then [y] is in [b]
  - if [f x = None], then no element is added to [b]. *)


(** {1:conversions Conversions to other data structures}

    Note: the [of_*] functions can raise [Failure] if the length would
    need to grow beyond {!Sys.max_array_length}.

    The [to_*] functions iterate on their dynarray argument. In
    particular, except for [to_seq], it is a programming error
    if the dynarray is mutated during their execution -- see the
    (un)specification in the {!section:Iteration} section.
*)

val of_array : 'a array -> 'a t
(** [of_array arr] returns a dynamic array corresponding to the fixed-sized array [a].
    Operates in [O(n)] time by making a copy. *)

val to_array : 'a t -> 'a array
(** [to_array a] returns a fixed-sized array corresponding to the dynamic array [a].
    This always allocate a new array and copies item into it. *)

val of_list : 'a list -> 'a t
(** [of_list l] is the array containing the elements of [l] in
    the same order. *)

val to_list : 'a t -> 'a list
(** [to_list a] is a list with the elements contained in the array [a]. *)

val of_seq : 'a Seq.t -> 'a t
(** [of_seq seq] is an array containing the same elements as [seq].

    It traverses [seq] once and will terminate only if [seq] is finite. *)

val to_seq : 'a t -> 'a Seq.t
(** [to_seq a] is the sequence of items
    [get a 0], [get a 1]... [get a (length a - 1)].

    Because sequences are computed on-demand, we have to assume that
    the array may be modified in the meantime, and give a precise
    specification for this case below.

    Demanding the [i]-th element of the resulting sequence (which can
    happen zero, one or several times) will access the [i]-th element
    of [a] at the time of the demand. The sequence stops if [a] has
    less than [i] elements at this point.
*)

val to_seq_rev : 'a t -> 'a Seq.t
(** [to_seq_rev a] is the sequence of items
    [get a (l - 1)], [get a (l - 2)]... [get a 0],
    where [l] is [length a] at the time [to_seq_rev] is invoked.

    Elements that have been removed from the array by the time they
    are demanded in the sequence are skipped.
*)


(** {1:capacity Backing array and capacity}

    Internally, a dynamic array uses a {b backing array} (a fixed-size
    array as provided by the {!Array} module) whose length is greater
    or equal to the length of the dynamic array. We call {b capacity}
    the length of the backing array.

    The capacity of a dynamic array is relevant in advanced scenarios,
    when reasoning about the performance of dynamic array programs:
    {ul
    {- The memory usage of a dynamic array is proportional to its capacity,
       rather than its length.}
    {- Adding elements to the end of a dynamic array may require
       allocating a new, larger backing array when its length
       is already equal to its capacity, so there is no room
       for more elements in the current backing array.}}

    The implementation uses a standard exponential reallocation
    strategy which guarantees amortized constant-time operation: the
    total capacity of all backing arrays allocated over the lifetime
    of a dynamic array is proportional to the total number of elements
    added or removed.
    In other words, users need not care about capacity and reallocations,
    and they will get reasonable behavior by default. However, in some
    performance-sensitive scenarios the functions below can help control
    memory usage or guarantee an optimal number of reallocations.
*)

val ensure_capacity : 'a t -> int -> unit
(** [ensure_capacity a n] makes sure that [a] has capacity has least [n].

    @raise Invalid_argument if the requested capacity is negative.
    (We consider that this is a programming error.)

    @raise Failure if the requested capacity is above
      {!Sys.max_array_length}.
    (We consider that this is a valid failure mode in some exceptional
    scenarios. In particular, all functions adding elements to a dynamic
    array may propagate this exception.)

    An example use-case would be to implement [append_array]:
{[
    let append_array a arr =
      ensure_capacity a (length a + Array.length arr);
      Array.iter (fun v -> add_last a v) arr
]}

    Using [ensure_capacity] guarantees that at most one reallocation
    will take place, instead of possibly several.

    Without this [ensure_capacity] hint, the number of resizes would
    be logarithmic in the length of [arr], creating a constant-factor
    slowdown noticeable when [a] is small and [arr] is large.
*)

val fit_capacity : 'a t -> unit
(** [fit_capacity a] shrinks the backing array so that its capacity is
    exactly [length a], with no additional empty space at the
    end. This can be useful to make sure there is no memory wasted on
    a long-lived array.

    Note that calling [fit_capacity] breaks the amortized complexity
    guarantees provided by the default reallocation strategy, and may
    result in more reallocations in the future.

    If you know that a dynamic array has reached its final length,
    which will remain fixed in the future, it is sufficient to call
    [to_array] and only keep the resulting fixed-size
    array. [fit_capacity] is useful when you need to keep a dynamic
    array for eventual future resizes.
*)

val reset : 'a t -> unit
(** [reset a] clears [a] and replaces its backing array by an empty array.

    It is equivalent to [clear a; fit_capacity a].

    Similar to {!Buffer.reset}. *)

(** {b No leaks: preservation of memory liveness}

    The user-provided values reachable from a dynamic array [a] are
    exactly the elements in the positions [0] to [length a - 1]. In
    particular, no user-provided values are "leaked" by being present
    in the backing array in position [length a] or later.
*)
