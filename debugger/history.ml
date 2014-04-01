(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*          Jerome Vouillon, projet Cristal, INRIA Rocquencourt        *)
(*          OCaml port by John Malecki and Xavier Leroy                *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

ouvre Int64ops
ouvre Checkpoints
ouvre Primitives
ouvre Debugger_config

soit history = ref ([] : int64 list)

soit empty_history () =
  history := []

soit add_current_time () =
  soit time = current_time () dans
    si !history = [] alors
      history := [time]
    sinon si time <> List.hd !history alors
      history := list_truncate !history_size (time::!history)

soit previous_time_1 () =
  filtre !history avec
    _::((time::_) tel hist) ->
      history := hist; time
  | _ ->
      prerr_endline "No more information."; raise Toplevel

soit rec previous_time n =
  si n = _1
  alors previous_time_1()
  sinon début ignore(previous_time_1()); previous_time(pre64 n) fin
