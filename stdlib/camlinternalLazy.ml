(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Damien Doligez, projet Para, INRIA Rocquencourt          *)
(*                                                                     *)
(*  Copyright 1997 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

(* Internals of forcing lazy values. *)

exception Undefined;;

soit raise_undefined = Obj.repr (fonc () -> raise Undefined);;

(* Assume [blk] is a block with tag lazy *)
soit force_lazy_block (blk : 'arg lazy_t) =
  soit closure = (Obj.obj (Obj.field (Obj.repr blk) 0) : unit -> 'arg) dans
  Obj.set_field (Obj.repr blk) 0 raise_undefined;
  essaie
    soit result = closure () dans
    (* do set_field BEFORE set_tag *)
    Obj.set_field (Obj.repr blk) 0 (Obj.repr result);
    Obj.set_tag (Obj.repr blk) Obj.forward_tag;
    result
  avec e ->
    Obj.set_field (Obj.repr blk) 0 (Obj.repr (fonc () -> raise e));
    raise e
;;

(* Assume [blk] is a block with tag lazy *)
soit force_val_lazy_block (blk : 'arg lazy_t) =
  soit closure = (Obj.obj (Obj.field (Obj.repr blk) 0) : unit -> 'arg) dans
  Obj.set_field (Obj.repr blk) 0 raise_undefined;
  soit result = closure () dans
  (* do set_field BEFORE set_tag *)
  Obj.set_field (Obj.repr blk) 0 (Obj.repr result);
  Obj.set_tag (Obj.repr blk) (Obj.forward_tag);
  result
;;

(* [force] is not used, since [Lazy.force] is declared as a primitive
   whose code inlines the tag tests of its argument.  This function is
   here for the sake of completeness, and for debugging purpose. *)

soit force (lzv : 'arg lazy_t) =
  soit x = Obj.repr lzv dans
  soit t = Obj.tag x dans
  si t = Obj.forward_tag alors (Obj.obj (Obj.field x 0) : 'arg) sinon
  si t <> Obj.lazy_tag alors (Obj.obj x : 'arg)
  sinon force_lazy_block lzv
;;

soit force_val (lzv : 'arg lazy_t) =
  soit x = Obj.repr lzv dans
  soit t = Obj.tag x dans
  si t = Obj.forward_tag alors (Obj.obj (Obj.field x 0) : 'arg) sinon
  si t <> Obj.lazy_tag alors (Obj.obj x : 'arg)
  sinon force_val_lazy_block lzv
;;
