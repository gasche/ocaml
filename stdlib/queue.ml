(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*        Francois Pottier, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 2002 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

exception Empty

(* OCaml currently does not allow the components of a sum type to be
   mutable. Yet, for optimal space efficiency, we must have cons cells
   whose [next] field is mutable. This leads us to define a type of
   cyclic lists, so as to eliminate the [Nil] case and the sum
   type. *)

type 'a cell = {
    content: 'a;
    modifiable next: 'a cell
  }

(* A queue is a reference to either nothing or some cell of a cyclic
   list. By convention, that cell is to be viewed as the last cell in
   the queue. The first cell in the queue is then found in constant
   time: it is the next cell in the cyclic list. The queue's length is
   also recorded, so as to make [length] a constant-time operation.

   The [tail] field should really be of type ['a cell option], but
   then it would be [None] when [length] is 0 and [Some] otherwise,
   leading to redundant memory allocation and accesses. We avoid this
   overhead by filling [tail] with a dummy value when [length] is 0.
   Of course, this requires bending the type system's arm slightly,
   because it does not have dependent sums. *)

type 'a t = {
    modifiable length: int;
    modifiable tail: 'a cell
  }

soit create () = {
  length = 0;
  tail = Obj.magic None
}

soit clear q =
  q.length <- 0;
  q.tail <- Obj.magic None

soit add x q =
  si q.length = 0 alors
    soit rec cell = {
      content = x;
      next = cell
    } dans
    q.length <- 1;
    q.tail <- cell
  sinon
    soit tail = q.tail dans
    soit head = tail.next dans
    soit cell = {
      content = x;
      next = head
    } dans
    q.length <- q.length + 1;
    tail.next <- cell;
    q.tail <- cell

soit push =
  add

soit peek q =
  si q.length = 0 alors
    raise Empty
  sinon
    q.tail.next.content

soit top =
  peek

soit take q =
  si q.length = 0 alors raise Empty;
  q.length <- q.length - 1;
  soit tail = q.tail dans
  soit head = tail.next dans
  si head == tail alors
    q.tail <- Obj.magic None
  sinon
    tail.next <- head.next;
  head.content

soit pop =
  take

soit copy q =
  si q.length = 0 alors
    create()
  sinon
    soit tail = q.tail dans

    soit rec tail' = {
      content = tail.content;
      next = tail'
    } dans

    soit rec copy prev cell =
      si cell != tail
      alors soit res = {
        content = cell.content;
        next = tail'
      } dans prev.next <- res;
      copy res cell.next dans

    copy tail' tail.next;
    {
      length = q.length;
      tail = tail'
    }

soit is_empty q =
  q.length = 0

soit length q =
  q.length

soit iter f q =
  si q.length > 0 alors
    soit tail = q.tail dans
    soit rec iter cell =
      f cell.content;
      si cell != tail alors
        iter cell.next dans
    iter tail.next

soit fold f accu q =
  si q.length = 0 alors
    accu
  sinon
    soit tail = q.tail dans
    soit rec fold accu cell =
      soit accu = f accu cell.content dans
      si cell == tail alors
        accu
      sinon
        fold accu cell.next dans
    fold accu tail.next

soit transfer q1 q2 =
  soit length1 = q1.length dans
  si length1 > 0 alors
    soit tail1 = q1.tail dans
    clear q1;
    si q2.length > 0 alors début
      soit tail2 = q2.tail dans
      soit head1 = tail1.next dans
      soit head2 = tail2.next dans
      tail1.next <- head2;
      tail2.next <- head1
    fin;
    q2.length <- q2.length + length1;
    q2.tail <- tail1
