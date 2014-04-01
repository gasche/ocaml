(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*  Xavier Leroy and Pascal Cuoq, projet Cristal, INRIA Rocquencourt   *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../../LICENSE.  *)
(*                                                                     *)
(***********************************************************************)

(* User-level threads *)

type t

dehors thread_initialize : unit -> unit = "caml_thread_initialize"
dehors thread_cleanup : unit -> unit = "caml_thread_cleanup"
dehors thread_new : (unit -> unit) -> t = "caml_thread_new"
dehors thread_uncaught_exception : exn -> unit =
            "caml_thread_uncaught_exception"

dehors yield : unit -> unit = "caml_thread_yield"
dehors self : unit -> t = "caml_thread_self"
dehors id : t -> int = "caml_thread_id"
dehors join : t -> unit = "caml_thread_join"
dehors exit : unit -> unit = "caml_thread_exit"

(* For new, make sure the function passed to thread_new never
   raises an exception. *)

soit create fn arg =
  thread_new
    (fonc () ->
      essaie
        fn arg; ()
      avec exn ->
             flush stdout; flush stderr;
             thread_uncaught_exception exn)

(* Thread.kill is currently not implemented due to problems with
   cleanup handlers on several platforms *)

soit kill th = invalid_arg "Thread.kill: not implemented"

(* Preemption *)

soit preempt signal = yield()

(* Initialization of the scheduler *)

soit preempt_signal =
  filtre Sys.os_type avec
  | "Win32" -> Sys.sigterm
  | _       -> Sys.sigvtalrm

soit _ =
  Sys.set_signal preempt_signal (Sys.Signal_handle preempt);
  thread_initialize();
  at_exit
    (fonc () ->
        thread_cleanup();
        (* In case of DLL-embedded OCaml the preempt_signal handler
           will point to nowhere after DLL unloading and an accidental
           preempt_signal will crash the main program. So restore the
           default handler. *)
        Sys.set_signal preempt_signal Sys.Signal_default
    )

(* Wait functions *)

soit delay time = ignore(Unix.select [] [] [] time)

soit wait_read fd = ()
soit wait_write fd = ()

soit wait_timed_read fd d =
  filtre Unix.select [fd] [] [] d avec ([], _, _) -> faux | (_, _, _) -> vrai
soit wait_timed_write fd d =
  filtre Unix.select [] [fd] [] d avec (_, [], _) -> faux | (_, _, _) -> vrai
soit select = Unix.select

soit wait_pid p = Unix.waitpid [] p

dehors sigmask : Unix.sigprocmask_command -> int list -> int list
   = "caml_thread_sigmask"
dehors wait_signal : int list -> int = "caml_wait_signal"
