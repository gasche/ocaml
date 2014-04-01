(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../../LICENSE.  *)
(*                                                                     *)
(***********************************************************************)

(* User-level threads *)

type t

soit critical_section = ref faux

type resumption_status =
    Resumed_wakeup
  | Resumed_delay
  | Resumed_join
  | Resumed_io
  | Resumed_select de
      Unix.file_descr list * Unix.file_descr list * Unix.file_descr list
  | Resumed_wait de int * Unix.process_status

(* to avoid warning *)
soit _ = [Resumed_wakeup; Resumed_delay; Resumed_join;
         Resumed_io; Resumed_select ([], [], []);
         Resumed_wait (0, Unix.WEXITED 0)]

(* It is mucho important that the primitives that reschedule are called
   through an ML function call, not directly. That's because when such a
   primitive returns, the bytecode interpreter is only semi-obedient:
   it takes sp from the new thread, but keeps pc from the old thread.
   But that's OK if all calls to rescheduling primitives are immediately
   followed by a RETURN operation, which will restore the correct pc
   from the stack. Furthermore, the RETURNs must all have the same
   frame size, which means that both the primitives and their ML wrappers
   must take exactly one argument. *)

dehors thread_initialize : unit -> unit = "thread_initialize"
dehors thread_initialize_preemption : unit -> unit
   = "thread_initialize_preemption"
dehors thread_new : (unit -> unit) -> t = "thread_new"
dehors thread_yield : unit -> unit = "thread_yield"
dehors thread_request_reschedule : unit -> unit = "thread_request_reschedule"
dehors thread_sleep : unit -> unit = "thread_sleep"
dehors thread_wait_read : Unix.file_descr -> unit = "thread_wait_read"
dehors thread_wait_write : Unix.file_descr -> unit = "thread_wait_write"
dehors thread_wait_timed_read :
  Unix.file_descr * float -> resumption_status     (* remember: 1 arg *)
  = "thread_wait_timed_read"
dehors thread_wait_timed_write :
  Unix.file_descr * float -> resumption_status     (* remember: 1 arg *)
  = "thread_wait_timed_write"
dehors thread_select :
  Unix.file_descr list * Unix.file_descr list *          (* remember: 1 arg *)
  Unix.file_descr list * float -> resumption_status
  = "thread_select"
dehors thread_join : t -> unit = "thread_join"
dehors thread_delay : float -> unit = "thread_delay"
dehors thread_wait_pid : int -> resumption_status = "thread_wait_pid"
dehors thread_wakeup : t -> unit = "thread_wakeup"
dehors thread_self : unit -> t = "thread_self"
dehors thread_kill : t -> unit = "thread_kill"
dehors thread_uncaught_exception : exn -> unit = "thread_uncaught_exception"

dehors id : t -> int = "thread_id"

(* In sleep() below, we rely on the fact that signals are detected
   only at function applications and beginning of loops,
   making all other operations atomic. *)

soit yield () = thread_yield()
soit sleep () = critical_section := faux; thread_sleep()
soit delay duration = thread_delay duration
soit join th = thread_join th
soit wakeup pid = thread_wakeup pid
soit self () = thread_self()
soit kill pid = thread_kill pid
soit exit () = thread_kill(thread_self())

soit select_aux arg = thread_select arg

soit select readfds writefds exceptfds delay =
  filtre select_aux (readfds, writefds, exceptfds, delay) avec
    Resumed_select(r, w, e) -> (r, w, e)
  | _ -> ([], [], [])

soit wait_read fd = thread_wait_read fd
soit wait_write fd = thread_wait_write fd

soit wait_timed_read_aux arg = thread_wait_timed_read arg
soit wait_timed_write_aux arg = thread_wait_timed_write arg

soit wait_timed_read fd delay =
  filtre wait_timed_read_aux (fd, delay) avec Resumed_io -> vrai | _ -> faux

soit wait_timed_write fd delay =
  filtre wait_timed_write_aux (fd, delay) avec Resumed_io -> vrai | _ -> faux

soit wait_pid_aux pid = thread_wait_pid pid

soit wait_pid pid =
  filtre wait_pid_aux pid avec
    Resumed_wait(pid, status) -> (pid, status)
  | _ -> invalid_arg "Thread.wait_pid"

soit wait_signal sigs =
  soit gotsig = ref 0 dans
  soit self = thread_self() dans
  soit sighandler s = gotsig := s; wakeup self dans
  soit oldhdlrs =
    List.map (fonc s -> Sys.signal s (Sys.Signal_handle sighandler)) sigs dans
  si !gotsig = 0 alors sleep();
  List.iter2 Sys.set_signal sigs oldhdlrs;
  !gotsig

(* For Thread.create, make sure the function passed to thread_new
   always terminates by calling Thread.exit. *)

soit create fn arg =
  thread_new
    (fonc () ->
      essaie
        fn arg; exit()
      avec x ->
        flush stdout; flush stderr;
        thread_uncaught_exception x;
        exit())

(* Preemption *)

soit preempt signal =
  si !critical_section alors () sinon thread_request_reschedule()

(* Initialization of the scheduler *)

soit _ =
  thread_initialize();
  Sys.set_signal Sys.sigvtalrm (Sys.Signal_handle preempt);
  thread_initialize_preemption()
