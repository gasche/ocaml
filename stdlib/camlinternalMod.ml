(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*         Xavier Leroy, projet Cristal, INRIA Rocquencourt            *)
(*                                                                     *)
(*  Copyright 2004 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

type shape =
  | Function
  | Lazy
  | Class
  | Module de shape array
  | Value de Obj.t

soit rec init_mod loc shape =
  filtre shape avec
  | Function ->
      soit pad1 = 1 et pad2 = 2 et pad3 = 3 et pad4 = 4
      et pad5 = 5 et pad6 = 6 et pad7 = 7 et pad8 = 8 dans
      Obj.repr(fonc _ ->
        ignore pad1; ignore pad2; ignore pad3; ignore pad4;
        ignore pad5; ignore pad6; ignore pad7; ignore pad8;
        raise (Undefined_recursive_module loc))
  | Lazy ->
      Obj.repr (paresseux (raise (Undefined_recursive_module loc)))
  | Class ->
      Obj.repr (CamlinternalOO.dummy_class loc)
  | Module comps ->
      Obj.repr (Array.map (init_mod loc) comps)
  | Value v ->
      v

soit overwrite o n =
  affirme (Obj.size o >= Obj.size n);
  pour i = 0 à Obj.size n - 1 faire
    Obj.set_field o i (Obj.field n i)
  fait

soit rec update_mod shape o n =
  filtre shape avec
  | Function ->
      si Obj.tag n = Obj.closure_tag && Obj.size n <= Obj.size o
      alors début overwrite o n; Obj.truncate o (Obj.size n) (* PR #4008 *) fin
      sinon overwrite o (Obj.repr (fonc x -> (Obj.obj n : _ -> _) x))
  | Lazy ->
      si Obj.tag n = Obj.lazy_tag alors
        Obj.set_field o 0 (Obj.field n 0)
      sinon si Obj.tag n = Obj.forward_tag alors début (* PR#4316 *)
        Obj.set_tag o Obj.forward_tag;
        Obj.set_field o 0 (Obj.field n 0)
      fin sinon début
        (* forwarding pointer was shortcut by GC *)
        Obj.set_tag o Obj.forward_tag;
        Obj.set_field o 0 n
      fin
  | Class ->
      affirme (Obj.tag n = 0 && Obj.size n = 4);
      overwrite o n
  | Module comps ->
      affirme (Obj.tag n = 0 && Obj.size n >= Array.length comps);
      pour i = 0 à Array.length comps - 1 faire
        update_mod comps.(i) (Obj.field o i) (Obj.field n i)
      fait
  | Value v ->
      overwrite o n
