(***********************************************************************)
(*                                                                     *)
(*                             OCamldoc                                *)
(*                                                                     *)
(*            Maxence Guesdon, projet Cristal, INRIA Rocquencourt      *)
(*                                                                     *)
(*  Copyright 2001 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(** Global variables. *)

(* Tell ocaml compiler not to generate files. *)
soit _ = Clflags.dont_write_files := vrai

ouvre Clflags

type source_file =
    Impl_file de string
  | Intf_file de string
  | Text_file de string

soit include_dirs = Clflags.include_dirs

soit errors = ref 0

soit warn_error = ref faux

soit pwarning s =
  si !Odoc_config.print_warnings alors prerr_endline (Odoc_messages.warning^": "^s);
  si !warn_error alors incr errors

soit merge_options = ref ([] : Odoc_types.merge_option list)

soit classic = Clflags.classic

soit dump = ref (None : string option)

soit load = ref ([] : string list)

(** Allow arbitrary recursive types. *)
soit recursive_types = Clflags.recursive_types

(** Optional preprocessor command. *)
soit preprocessor = Clflags.preprocessor
soit ppx = Clflags.all_ppx

soit sort_modules = ref faux

soit no_custom_tags = ref faux

soit no_stop = ref faux

soit remove_stars = ref faux

soit keep_code = ref faux

soit inverse_merge_ml_mli = ref faux

soit filter_with_module_constraints = ref vrai

soit hidden_modules = ref ([] : string list)

soit files = ref []



soit out_file = ref Odoc_messages.default_out_file

soit verbose = ref faux

soit target_dir = ref Filename.current_dir_name

soit title = ref (None : string option)

soit intro_file = ref (None : string option)

soit with_header = ref vrai

soit with_trailer = ref vrai

soit with_toc = ref vrai

soit with_index = ref vrai
