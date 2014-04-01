(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1997 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

type extern_flags =
    No_sharing
  | Closures
  | Compat_32
(* note: this type definition is used in 'byterun/debugger.c' *)

dehors to_channel: out_channel -> 'a -> extern_flags list -> unit
    = "caml_output_value"
dehors to_string: 'a -> extern_flags list -> string
    = "caml_output_value_to_string"
dehors to_buffer_unsafe:
      string -> int -> int -> 'a -> extern_flags list -> int
    = "caml_output_value_to_buffer"

soit to_buffer buff ofs len v flags =
  si ofs < 0 || len < 0 || ofs > String.length buff - len
  alors invalid_arg "Marshal.to_buffer: substring out of bounds"
  sinon to_buffer_unsafe buff ofs len v flags

dehors from_channel: in_channel -> 'a = "caml_input_value"
dehors from_string_unsafe: string -> int -> 'a
                           = "caml_input_value_from_string"
dehors data_size_unsafe: string -> int -> int = "caml_marshal_data_size"

soit header_size = 20
soit data_size buff ofs =
  si ofs < 0 || ofs > String.length buff - header_size
  alors invalid_arg "Marshal.data_size"
  sinon data_size_unsafe buff ofs
soit total_size buff ofs = header_size + data_size buff ofs

soit from_string buff ofs =
  si ofs < 0 || ofs > String.length buff - header_size
  alors invalid_arg "Marshal.from_size"
  sinon début
    soit len = data_size_unsafe buff ofs dans
    si ofs > String.length buff - (header_size + len)
    alors invalid_arg "Marshal.from_string"
    sinon from_string_unsafe buff ofs
  fin
