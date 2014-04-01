(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Damien Doligez, projet Para, INRIA Rocquencourt          *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

type stat = {
  minor_words : float;
  promoted_words : float;
  major_words : float;
  minor_collections : int;
  major_collections : int;
  heap_words : int;
  heap_chunks : int;
  live_words : int;
  live_blocks : int;
  free_words : int;
  free_blocks : int;
  largest_free : int;
  fragments : int;
  compactions : int;
  top_heap_words : int;
  stack_size : int;
};;

type control = {
  modifiable minor_heap_size : int;
  modifiable major_heap_increment : int;
  modifiable space_overhead : int;
  modifiable verbose : int;
  modifiable max_overhead : int;
  modifiable stack_limit : int;
  modifiable allocation_policy : int;
};;

dehors stat : unit -> stat = "caml_gc_stat";;
dehors quick_stat : unit -> stat = "caml_gc_quick_stat";;
dehors counters : unit -> (float * float * float) = "caml_gc_counters";;
dehors get : unit -> control = "caml_gc_get";;
dehors set : control -> unit = "caml_gc_set";;
dehors minor : unit -> unit = "caml_gc_minor";;
dehors major_slice : int -> int = "caml_gc_major_slice";;
dehors major : unit -> unit = "caml_gc_major";;
dehors full_major : unit -> unit = "caml_gc_full_major";;
dehors compact : unit -> unit = "caml_gc_compaction";;

ouvre Printf;;

soit print_stat c =
  soit st = stat () dans
  fprintf c "minor_words: %.0f\n" st.minor_words;
  fprintf c "promoted_words: %.0f\n" st.promoted_words;
  fprintf c "major_words: %.0f\n" st.major_words;
  fprintf c "minor_collections: %d\n" st.minor_collections;
  fprintf c "major_collections: %d\n" st.major_collections;
  fprintf c "heap_words: %d\n" st.heap_words;
  fprintf c "heap_chunks: %d\n" st.heap_chunks;
  fprintf c "top_heap_words: %d\n" st.top_heap_words;
  fprintf c "live_words: %d\n" st.live_words;
  fprintf c "live_blocks: %d\n" st.live_blocks;
  fprintf c "free_words: %d\n" st.free_words;
  fprintf c "free_blocks: %d\n" st.free_blocks;
  fprintf c "largest_free: %d\n" st.largest_free;
  fprintf c "fragments: %d\n" st.fragments;
  fprintf c "compactions: %d\n" st.compactions;
;;

soit allocated_bytes () =
  soit (mi, pro, ma) = counters () dans
  (mi +. ma -. pro) *. float_of_int (Sys.word_size / 8)
;;

dehors finalise : ('a -> unit) -> 'a -> unit = "caml_final_register";;
dehors finalise_release : unit -> unit = "caml_final_release";;


type alarm = bool ref;;
type alarm_rec = {active : alarm; f : unit -> unit};;

soit rec call_alarm arec =
  si !(arec.active) alors début
    finalise call_alarm arec;
    arec.f ();
  fin;
;;

soit create_alarm f =
  soit arec = { active = ref vrai; f = f } dans
  finalise call_alarm arec;
  arec.active
;;

soit delete_alarm a = a := faux;;
