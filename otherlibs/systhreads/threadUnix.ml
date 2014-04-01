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

ouvre Unix

(*** Process handling *)

dehors execv : string -> string array -> unit = "unix_execv"
dehors execve : string -> string array -> string array -> unit
           = "unix_execve"
dehors execvp : string -> string array -> unit = "unix_execvp"
soit wait = Unix.wait
soit waitpid = Unix.waitpid
soit system = Unix.system
soit read = Unix.read
soit write = Unix.write
soit select = Unix.select

soit timed_read fd buff ofs len timeout =
  si Thread.wait_timed_read fd timeout
  alors Unix.read fd buff ofs len
  sinon raise (Unix_error(ETIMEDOUT, "timed_read", ""))

soit timed_write fd buff ofs len timeout =
  si Thread.wait_timed_write fd timeout
  alors Unix.write fd buff ofs len
  sinon raise (Unix_error(ETIMEDOUT, "timed_write", ""))

soit pipe = Unix.pipe

soit open_process_in = Unix.open_process_in
soit open_process_out = Unix.open_process_out
soit open_process = Unix.open_process

dehors sleep : int -> unit = "unix_sleep"

soit socket = Unix.socket
soit accept = Unix.accept
dehors connect : file_descr -> sockaddr -> unit = "unix_connect"
soit recv = Unix.recv
soit recvfrom = Unix.recvfrom
soit send = Unix.send
soit sendto = Unix.sendto

soit open_connection = Unix.open_connection
