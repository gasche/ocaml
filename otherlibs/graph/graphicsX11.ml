(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*    Pierre Weis and Jun Furuse, projet Cristal, INRIA Rocquencourt   *)
(*                                                                     *)
(*  Copyright 2001 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../../LICENSE.  *)
(*                                                                     *)
(***********************************************************************)

(* Module [GraphicsX11]: additional graphics primitives for
   the X Windows system *)

type window_id = string

dehors window_id : unit -> window_id = "caml_gr_window_id"

soit subwindows = Hashtbl.create 13

dehors open_subwindow : int -> int -> int -> int -> window_id
    = "caml_gr_open_subwindow"
dehors close_subwindow : window_id -> unit
    = "caml_gr_close_subwindow"

soit open_subwindow ~x ~y ~width ~height =
  soit wid = open_subwindow x y width height dans
  Hashtbl.add subwindows wid ();
  wid
;;

soit close_subwindow wid =
  si Hashtbl.mem subwindows wid alors début
    close_subwindow wid;
    Hashtbl.remove subwindows wid
  fin sinon
    raise (Graphics.Graphic_failure("close_subwindow: no such subwindow: "^wid))
;;
