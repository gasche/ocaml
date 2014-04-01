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

(* Module [ThreadUnix]: thread-compatible system calls *)

soit execv = Unix.execv
soit execve = Unix.execve
soit execvp = Unix.execvp
soit wait = Unix.wait
soit waitpid = Unix.waitpid
soit system = Unix.system
soit read = Unix.read
soit write = Unix.write
soit single_write = Unix.single_write
soit select = Unix.select
soit pipe = Unix.pipe
soit open_process_in = Unix.open_process_in
soit open_process_out = Unix.open_process_out
soit open_process = Unix.open_process
soit open_process_full = Unix.open_process_full
soit sleep = Unix.sleep
soit socket = Unix.socket
soit socketpair = Unix.socketpair
soit accept = Unix.accept
soit connect = Unix.connect
soit recv = Unix.recv
soit recvfrom = Unix.recvfrom
soit send = Unix.send
soit sendto = Unix.sendto
soit open_connection = Unix.open_connection
soit establish_server = Unix.establish_server

ouvre Unix

soit rec timed_read fd buff ofs len timeout =
  si Thread.wait_timed_read fd timeout
  alors début essaie Unix.read fd buff ofs len
             avec Unix_error((EAGAIN | EWOULDBLOCK), _, _) ->
                    timed_read fd buff ofs len timeout
       fin
  sinon raise (Unix_error(ETIMEDOUT, "timed_read", ""))

soit rec timed_write fd buff ofs len timeout =
  si Thread.wait_timed_write fd timeout
  alors début essaie Unix.write fd buff ofs len
             avec Unix_error((EAGAIN | EWOULDBLOCK), _, _) ->
                    timed_write fd buff ofs len timeout
       fin
  sinon raise (Unix_error(ETIMEDOUT, "timed_write", ""))
