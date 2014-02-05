(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*  Xavier Leroy and Pierre Weis, projet Cristal, INRIA Rocquencourt   *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

open CamlinternalFormat

let kfprintf k o (fmt, _) =
  make_printf (fun o acc -> output_acc o acc; k o) o End_of_acc fmt
let kbprintf k b (fmt, _) =
  make_printf (fun b acc -> bufput_acc b acc; k b) b End_of_acc fmt
let ifprintf x (fmt, _) =
  make_printf (fun _ _ -> ()) x End_of_acc fmt

let fprintf o (fmt, _) = make_printf output_acc o End_of_acc fmt
let printf (fmt, _) = make_printf output_acc stdout End_of_acc fmt
let eprintf (fmt, _) = make_printf output_acc stderr End_of_acc fmt
let bprintf b (fmt, _) = make_printf bufput_acc b End_of_acc fmt

let ksprintf k (fmt, _) =
  let k' () acc =
    let buf = Buffer.create 64 in
    strput_acc buf acc;
    k (Buffer.contents buf) in
  make_printf k' () End_of_acc fmt

let sprintf (fmt, _) =
  let k () acc =
    let buf = Buffer.create 64 in
    strput_acc buf acc;
    Buffer.contents buf in
  make_printf k () End_of_acc fmt

let kprintf = ksprintf
