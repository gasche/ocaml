(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*      Fabrice Le Fessant, EPI Gallium, INRIA Paris-Rocquencourt      *)
(*                                                                     *)
(*  Copyright 2013 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

ouvre Compenv

(* Initialize the search path.
   The current directory is always searched first,
   then the directories specified with the -I option (in command-line order),
   then the standard library directory (unless the -nostdlib option is given).
 *)

soit init_path native =
  soit dirs =
    si !Clflags.use_threads alors "+threads" :: !Clflags.include_dirs
    sinon si !Clflags.use_vmthreads && not native alors
      "+vmthreads" :: !Clflags.include_dirs
    sinon
      !last_include_dirs @
      !Clflags.include_dirs @
      !first_include_dirs
  dans
  soit exp_dirs =
    List.map (Misc.expand_directory Config.standard_library) dirs dans
  Config.load_path := "" ::
      List.rev_append exp_dirs (Clflags.std_include_dir ());
  Env.reset_cache ()

(* Return the initial environment in which compilation proceeds. *)

(* Note: do not do init_path() in initial_env, this breaks
   toplevel initialization (PR#1775) *)

soit open_implicit_module m env =
  essaie
    Env.open_pers_signature m env
  avec Not_found ->
    Misc.fatal_error (Printf.sprintf "impossible d'ouvrir le module implicite %S" m)

soit initial_env () =
  Ident.reinit();
  soit env =
    si !Clflags.nopervasives
    alors Env.initial
    sinon
      open_implicit_module "Pervasives" Env.initial
  dans
  List.fold_left (fonc env m ->
    open_implicit_module m env
  ) env !implicit_modules
