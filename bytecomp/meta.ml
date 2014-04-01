(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

dehors global_data : unit -> Obj.t array = "caml_get_global_data"
dehors realloc_global_data : int -> unit = "caml_realloc_global"
dehors static_alloc : int -> string = "caml_static_alloc"
dehors static_free : string -> unit = "caml_static_free"
dehors static_resize : string -> int -> string = "caml_static_resize"
dehors static_release_bytecode : string -> int -> unit
                                 = "caml_static_release_bytecode"
type closure = unit -> Obj.t
dehors reify_bytecode : string -> int -> closure = "caml_reify_bytecode"
dehors invoke_traced_function : Obj.t -> Obj.t -> Obj.t -> Obj.t
                                = "caml_invoke_traced_function"
dehors get_section_table : unit -> (string * Obj.t) list
                           = "caml_get_section_table"
