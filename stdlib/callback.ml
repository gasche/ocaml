(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

(* Registering OCaml values with the C runtime for later callbacks *)

dehors register_named_value : string -> Obj.t -> unit
                              = "caml_register_named_value"

soit register name v =
  register_named_value name (Obj.repr v)

soit register_exception name (exn : exn) =
  soit exn = Obj.repr exn dans
  soit slot = si Obj.tag exn = Obj.object_tag alors exn sinon Obj.field exn 0 dans
  register_named_value name slot
