(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*  David Nowak and Xavier Leroy, projet Cristal, INRIA Rocquencourt   *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../../LICENSE.  *)
(*                                                                     *)
(***********************************************************************)

(* Events *)
type 'a basic_event =
  { poll: unit -> bool;
      (* If communication can take place immediately, return true. *)
    suspend: unit -> unit;
      (* Offer the communication on the channel and get ready
         to suspend current process. *)
    result: unit -> 'a }
      (* Return the result of the communication *)

type 'a behavior = int ref -> Condition.t -> int -> 'a basic_event

type 'a event =
    Communication de 'a behavior
  | Choose de 'a event list
  | WrapAbort de 'a event * (unit -> unit)
  | Guard de (unit -> 'a event)

(* Communication channels *)
type 'a channel =
  { modifiable writes_pending: 'a communication Queue.t;
                        (* All offers to write on it *)
    modifiable reads_pending:  'a communication Queue.t }
                        (* All offers to read from it *)

(* Communication offered *)
et 'a communication =
  { performed: int ref;  (* -1 if not performed yet, set to the number *)
                         (* of the matching communication after rendez-vous. *)
    condition: Condition.t;             (* To restart the blocked thread. *)
    modifiable data: 'a option;            (* The data sent or received. *)
    event_number: int }                 (* Event number in select *)

(* Create a channel *)

soit new_channel () =
  { writes_pending = Queue.create();
    reads_pending = Queue.create() }

(* Basic synchronization function *)

soit masterlock = Mutex.create()

soit do_aborts abort_env genev performed =
  si abort_env <> [] alors début
    si performed >= 0 alors début
      soit ids_done = snd genev.(performed) dans
      List.iter
        (fonc (id,f) -> si not (List.mem id ids_done) alors f ())
        abort_env
    fin sinon début
      List.iter (fonc (_,f) -> f ()) abort_env
    fin
  fin

soit basic_sync abort_env genev =
  soit performed = ref (-1) dans
  soit condition = Condition.create() dans
  soit bev = Array.create (Array.length genev)
                         (fst (genev.(0)) performed condition 0) dans
  pour i = 1 à Array.length genev - 1 faire
    bev.(i) <- (fst genev.(i)) performed condition i
  fait;
  (* See if any of the events is already activable *)
  soit rec poll_events i =
    si i >= Array.length bev
    alors faux
    sinon bev.(i).poll() || poll_events (i+1) dans
  Mutex.lock masterlock;
  si not (poll_events 0) alors début
    (* Suspend on all events *)
    pour i = 0 à Array.length bev - 1 faire bev.(i).suspend() fait;
    (* Wait until the condition is signalled *)
    Condition.wait condition masterlock
  fin;
  Mutex.unlock masterlock;
  (* Extract the result *)
  si abort_env = [] alors
    (* Preserve tail recursion *)
    bev.(!performed).result()
  sinon début
    soit num = !performed dans
    soit result = bev.(num).result() dans
    (* Handle the aborts and return the result *)
    do_aborts abort_env genev num;
    result
  fin

(* Apply a random permutation on an array *)

soit scramble_array a =
  soit len = Array.length a dans
  si len = 0 alors invalid_arg "Event.choose";
  pour i = len - 1 descendant_jusqu'a 1 faire
    soit j = Random.int (i + 1) dans
    soit temp = a.(i) dans a.(i) <- a.(j); a.(j) <- temp
  fait;
  a

(* Main synchronization function *)

soit gensym = soit count = ref 0 dans fonc () -> incr count; !count

soit rec flatten_event
      (abort_list : int list)
      (accu : ('a behavior * int list) list)
      (accu_abort : (int * (unit -> unit)) list)
      ev =
  filtre ev avec
     Communication bev -> ((bev,abort_list) :: accu) , accu_abort
  | WrapAbort (ev,fn) ->
      soit id = gensym () dans
      flatten_event (id :: abort_list) accu ((id,fn)::accu_abort) ev
  | Choose evl ->
      soit rec flatten_list accu' accu_abort'= fonction
         ev :: l ->
           soit (accu'',accu_abort'') =
             flatten_event abort_list accu' accu_abort' ev dans
           flatten_list accu'' accu_abort'' l
       | [] -> (accu',accu_abort') dans
      flatten_list accu accu_abort evl
  | Guard fn -> flatten_event abort_list accu accu_abort (fn ())

soit sync ev =
  soit (evl,abort_env) = flatten_event [] [] [] ev dans
  basic_sync abort_env (scramble_array(Array.of_list evl))

(* Event polling -- like sync, but non-blocking *)

soit basic_poll abort_env genev =
  soit performed = ref (-1) dans
  soit condition = Condition.create() dans
  soit bev = Array.create(Array.length genev)
                        (fst genev.(0) performed condition 0) dans
  pour i = 1 à Array.length genev - 1 faire
    bev.(i) <- fst genev.(i) performed condition i
  fait;
  (* See if any of the events is already activable *)
  soit rec poll_events i =
    si i >= Array.length bev
    alors faux
    sinon bev.(i).poll() || poll_events (i+1) dans
  Mutex.lock masterlock;
  soit ready = poll_events 0 dans
  si ready alors début
    (* Extract the result *)
    Mutex.unlock masterlock;
    soit result = Some(bev.(!performed).result()) dans
    do_aborts abort_env genev !performed; result
  fin sinon début
    (* Cancel the communication offers *)
    performed := 0;
    Mutex.unlock masterlock;
    do_aborts abort_env genev (-1);
    None
  fin

soit poll ev =
  soit (evl,abort_env) = flatten_event [] [] [] ev dans
  basic_poll abort_env (scramble_array(Array.of_list evl))

(* Remove all communication opportunities already synchronized *)

soit cleanup_queue q =
  soit q' = Queue.create() dans
  Queue.iter (fonc c -> si !(c.performed) = -1 alors Queue.add c q') q;
  q'

(* Event construction *)

soit always data =
  Communication(fonc performed condition evnum ->
    { poll = (fonc () -> performed := evnum; vrai);
      suspend = (fonc () -> ());
      result = (fonc () -> data) })

soit send channel data =
  Communication(fonc performed condition evnum ->
    soit wcomm =
      { performed = performed;
        condition = condition;
        data = Some data;
        event_number = evnum } dans
    { poll = (fonc () ->
        soit rec poll () =
          soit rcomm = Queue.take channel.reads_pending dans
          si !(rcomm.performed) >= 0 alors
            poll ()
          sinon début
            rcomm.data <- wcomm.data;
            performed := evnum;
            rcomm.performed := rcomm.event_number;
            Condition.signal rcomm.condition
          fin dans
        essaie
          poll();
          vrai
        avec Queue.Empty ->
          faux);
      suspend = (fonc () ->
        channel.writes_pending <- cleanup_queue channel.writes_pending;
        Queue.add wcomm channel.writes_pending);
      result = (fonc () -> ()) })

soit receive channel =
  Communication(fonc performed condition evnum ->
    soit rcomm =
      { performed = performed;
        condition = condition;
        data = None;
        event_number = evnum } dans
    { poll = (fonc () ->
        soit rec poll () =
          soit wcomm = Queue.take channel.writes_pending dans
          si !(wcomm.performed) >= 0 alors
            poll ()
          sinon début
            rcomm.data <- wcomm.data;
            performed := evnum;
            wcomm.performed := wcomm.event_number;
            Condition.signal wcomm.condition
          fin dans
        essaie
          poll();
          vrai
        avec Queue.Empty ->
          faux);
    suspend = (fonc () ->
      channel.reads_pending <- cleanup_queue channel.reads_pending;
      Queue.add rcomm channel.reads_pending);
    result = (fonc () ->
      filtre rcomm.data avec
        None -> invalid_arg "Event.receive"
      | Some res -> res) })

soit choose evl = Choose evl

soit wrap_abort ev fn = WrapAbort(ev,fn)

soit guard fn = Guard fn

soit rec wrap ev fn =
  filtre ev avec
    Communication genev ->
      Communication(fonc performed condition evnum ->
        soit bev = genev performed condition evnum dans
        { poll = bev.poll;
          suspend = bev.suspend;
          result = (fonc () -> fn(bev.result())) })
  | Choose evl ->
      Choose(List.map (fonc ev -> wrap ev fn) evl)
  | WrapAbort (ev, f') ->
      WrapAbort (wrap ev fn, f')
  | Guard gu ->
      Guard(fonc () -> wrap (gu()) fn)

(* Convenience functions *)

soit select evl = sync(Choose evl)
