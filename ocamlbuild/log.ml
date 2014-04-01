(***********************************************************************)
(*                                                                     *)
(*                             ocamlbuild                              *)
(*                                                                     *)
(*  Nicolas Pouillard, Berke Durak, projet Gallium, INRIA Rocquencourt *)
(*                                                                     *)
(*  Copyright 2007 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)


(* Original author: Nicolas Pouillard *)
ouvre My_std

module Debug = struct
soit mode _ = vrai
fin
inclus Debug

soit level = ref 1

soit classic_display = ref faux
soit internal_display = ref None
soit failsafe_display = paresseux (Display.create ~mode:`Classic ~log_level:!level ())

soit ( !- ) r =
  filtre !r avec
  | None -> !*failsafe_display
  | Some x -> x

soit init log_file =
  soit mode =
    si !classic_display || !*My_unix.is_degraded || !level <= 0 || not (My_unix.stdout_isatty ()) alors
      `Classic
    sinon
      `Sophisticated
  dans
  internal_display := Some (Display.create ~mode ?log_file ~log_level:!level ())

soit raw_dprintf log_level = Display.dprintf ~log_level !-internal_display

soit dprintf log_level fmt = raw_dprintf log_level ("@[<2>"^^fmt^^"@]@.")
soit eprintf fmt = dprintf (-1) fmt

soit update () = Display.update !-internal_display
soit event ?pretend x = Display.event !-internal_display ?pretend x
soit display x = Display.display !-internal_display x

soit finish ?how () =
  filtre !internal_display avec
  | None -> ()
  | Some d -> Display.finish ?how d

(*let () = My_unix.at_exit_once finish*)
