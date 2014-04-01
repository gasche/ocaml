(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*          Jerome Vouillon, projet Cristal, INRIA Rocquencourt        *)
(*          OCaml port by John Malecki and Xavier Leroy                *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Handling of keyboard interrupts *)

soit interrupted = ref faux

soit is_protected = ref faux

soit break signum =
  si !is_protected
  alors interrupted := vrai
  sinon raise Sys.Break

soit _ =
  filtre Sys.os_type avec
    "Win32" -> ()
  | _ ->
      Sys.set_signal Sys.sigint (Sys.Signal_handle break);
      Sys.set_signal Sys.sigpipe (Sys.Signal_handle(fonc _ -> raise End_of_file))

soit protect f =
  si !is_protected alors
    f ()
  sinon début
    is_protected := vrai;
    si not !interrupted alors
       f ();
    is_protected := faux;
    si !interrupted alors début interrupted := faux; raise Sys.Break fin
  fin

soit unprotect f =
  si not !is_protected alors
    f ()
  sinon début
    is_protected := faux;
    si !interrupted alors début interrupted := faux; raise Sys.Break fin;
    f ();
    is_protected := vrai
  fin
