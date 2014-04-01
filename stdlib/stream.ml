(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*        Daniel de Rauglaudre, projet Cristal, INRIA Rocquencourt     *)
(*                                                                     *)
(*  Copyright 1997 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

(* The fields of type t are not mutable to preserve polymorphism of
   the empty stream. This is type safe because the empty stream is never
   patched. *)

type 'a t = { count : int; data : 'a data }
et 'a data =
    Sempty
  | Scons de 'a * 'a data
  | Sapp de 'a data * 'a data
  | Slazy de 'a data Lazy.t
  | Sgen de 'a gen
  | Sbuffio de buffio
et 'a gen = { modifiable curr : 'a option option; func : int -> 'a option }
et buffio =
  { ic : in_channel; buff : string; modifiable len : int; modifiable ind : int }
;;
exception Failure;;
exception Error de string;;

dehors count : 'a t -> int = "%field0";;
dehors set_count : 'a t -> int -> unit = "%setfield0";;
soit set_data (s : 'a t) (d : 'a data) =
  Obj.set_field (Obj.repr s) 1 (Obj.repr d)
;;

soit fill_buff b =
  b.len <- input b.ic b.buff 0 (String.length b.buff); b.ind <- 0
;;

soit rec get_data count d = filtre d avec
 (* Returns either Sempty or Scons(a, _) even when d is a generator
    or a buffer. In those cases, the item a is seen as extracted from
 the generator/buffer.
 The count parameter is used for calling `Sgen-functions'.  *)
   Sempty | Scons (_, _) -> d
 | Sapp (d1, d2) ->
     début filtre get_data count d1 avec
       Scons (a, d11) -> Scons (a, Sapp (d11, d2))
     | Sempty -> get_data count d2
     | _ -> affirme faux
     fin
 | Sgen {curr = Some None; func = _ } -> Sempty
 | Sgen ({curr = Some(Some a); func = f} tel g) ->
     g.curr <- None; Scons(a, d)
 | Sgen g ->
     début filtre g.func count avec
       None -> g.curr <- Some(None); Sempty
     | Some a -> Scons(a, d)
         (* Warning: anyone using g thinks that an item has been read *)
     fin
 | Sbuffio b ->
     si b.ind >= b.len alors fill_buff b;
     si b.len == 0 alors Sempty sinon
       soit r = Obj.magic (String.unsafe_get b.buff b.ind) dans
       (* Warning: anyone using g thinks that an item has been read *)
       b.ind <- succ b.ind; Scons(r, d)
 | Slazy f -> get_data count (Lazy.force f)
;;

soit rec peek s =
 (* consult the first item of s *)
 filtre s.data avec
   Sempty -> None
 | Scons (a, _) -> Some a
 | Sapp (_, _) ->
     début filtre get_data s.count s.data avec
       Scons(a, _) tel d -> set_data s d; Some a
     | Sempty -> None
     | _ -> affirme faux
     fin
 | Slazy f -> set_data s (Lazy.force f); peek s
 | Sgen {curr = Some a} -> a
 | Sgen g -> soit x = g.func s.count dans g.curr <- Some x; x
 | Sbuffio b ->
     si b.ind >= b.len alors fill_buff b;
     si b.len == 0 alors début set_data s Sempty; None fin
     sinon Some (Obj.magic (String.unsafe_get b.buff b.ind))
;;

soit rec junk s =
  filtre s.data avec
    Scons (_, d) -> set_count s (succ s.count); set_data s d
  | Sgen ({curr = Some _} tel g) -> set_count s (succ s.count); g.curr <- None
  | Sbuffio b -> set_count s (succ s.count); b.ind <- succ b.ind
  | _ ->
      filtre peek s avec
        None -> ()
      | Some _ -> junk s
;;

soit rec nget n s =
  si n <= 0 alors [], s.data, 0
  sinon
    filtre peek s avec
      Some a ->
        junk s;
        soit (al, d, k) = nget (pred n) s dans a :: al, Scons (a, d), succ k
    | None -> [], s.data, 0
;;

soit npeek n s =
  soit (al, d, len) = nget n s dans set_count s (s.count - len); set_data s d; al
;;

soit next s =
  filtre peek s avec
    Some a -> junk s; a
  | None -> raise Failure
;;

soit empty s =
  filtre peek s avec
    Some _ -> raise Failure
  | None -> ()
;;

soit iter f strm =
  soit rec do_rec () =
    filtre peek strm avec
      Some a -> junk strm; ignore(f a); do_rec ()
    | None -> ()
  dans
  do_rec ()
;;

(* Stream building functions *)

soit from f = {count = 0; data = Sgen {curr = None; func = f}};;

soit of_list l =
  {count = 0; data = List.fold_right (fonc x l -> Scons (x, l)) l Sempty}
;;

soit of_string s =
  soit count = ref 0 dans
  from (fonc _ ->
    (* We cannot use the index passed by the [from] function directly
       because it returns the current stream count, with absolutely no
       guarantee that it will start from 0. For example, in the case
       of [Stream.icons 'c' (Stream.from_string "ab")], the first
       access to the string will be made with count [1] already.
    *)
    soit c = !count dans
    si c < String.length s
    alors (incr count; Some s.[c])
    sinon None)
;;

soit of_channel ic =
  {count = 0;
   data = Sbuffio {ic = ic; buff = String.create 4096; len = 0; ind = 0}}
;;

(* Stream expressions builders *)

soit iapp i s = {count = 0; data = Sapp (i.data, s.data)};;
soit icons i s = {count = 0; data = Scons (i, s.data)};;
soit ising i = {count = 0; data = Scons (i, Sempty)};;

soit lapp f s =
  {count = 0; data = Slazy (paresseux(Sapp ((f ()).data, s.data)))}
;;
soit lcons f s = {count = 0; data = Slazy (paresseux(Scons (f (), s.data)))};;
soit lsing f = {count = 0; data = Slazy (paresseux(Scons (f (), Sempty)))};;

soit sempty = {count = 0; data = Sempty};;
soit slazy f = {count = 0; data = Slazy (paresseux(f ()).data)};;

(* For debugging use *)

soit rec dump f s =
  print_string "{count = ";
  print_int s.count;
  print_string "; data = ";
  dump_data f s.data;
  print_string "}";
  print_newline ()
et dump_data f =
  fonction
    Sempty -> print_string "Sempty"
  | Scons (a, d) ->
      print_string "Scons (";
      f a;
      print_string ", ";
      dump_data f d;
      print_string ")"
  | Sapp (d1, d2) ->
      print_string "Sapp (";
      dump_data f d1;
      print_string ", ";
      dump_data f d2;
      print_string ")"
  | Slazy _ -> print_string "Slazy"
  | Sgen _ -> print_string "Sgen"
  | Sbuffio b -> print_string "Sbuffio"
;;
