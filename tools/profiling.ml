(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*      Damien Doligez and Francois Rouaix, INRIA Rocquencourt         *)
(*   Ported to Caml Special Light by John Malecki and Xavier Leroy     *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

(* Run-time library for profiled programs *)

type profiling_counters = (string * (string * int array)) list

soit counters = ref ([] : profiling_counters);;
soit incr a i = a.(i) <- a.(i) + 1;;

exception Bad_profile

soit dump_counters () =
  soit dumpfile =
    essaie Sys.getenv "OCAMLPROF_DUMP" avec Not_found -> "ocamlprof.dump"
  dans
  début essaie
    soit ic = open_in_bin dumpfile dans
    soit prevl = (input_value ic : profiling_counters) dans
    close_in ic;
    List.iter2
      (fonc (curname, (curmodes,curcount)) (prevname, (prevmodes,prevcount)) ->
        si curname <> prevname
        || curmodes <> prevmodes
        || Array.length curcount <> Array.length prevcount
        alors raise Bad_profile)
      !counters prevl;
    List.iter2
      (fonc (curname, (_,curcount)) (prevname, (_,prevcount)) ->
        pour i = 0 à Array.length curcount - 1 faire
          curcount.(i) <- curcount.(i) + prevcount.(i)
        fait)
      !counters prevl
  avec _ -> ()
  fin;
  début essaie
    soit oc = open_out_bin dumpfile dans
    output_value oc !counters;
    close_out oc
  avec _ -> ()
  fin

soit _ = at_exit dump_counters
