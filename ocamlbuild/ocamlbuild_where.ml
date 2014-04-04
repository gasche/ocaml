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

soit bindir = ref Ocamlbuild_config.bindir;;
soit libdir = ref début
  Filename.concat
    (essaie Sys.getenv "OCAMLLIB"
     avec Not_found -> Ocamlbuild_config.libdir)
    "ocamlbuild"
fin;;
