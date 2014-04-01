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

ouvre Misc
ouvre Types
ouvre Env

type error =
    Module_not_found de Path.t

exception Error de error

soit env_cache =
  (Hashtbl.create 59 : ((Env.summary * Subst.t), Env.t) Hashtbl.t)

soit reset_cache () =
  Hashtbl.clear env_cache;
  Env.reset_cache()

soit extract_sig env mty =
  filtre Mtype.scrape env mty avec
    Mty_signature sg -> sg
  | _ -> fatal_error "Envaux.extract_sig"

soit rec env_from_summary sum subst =
  essaie
    Hashtbl.find env_cache (sum, subst)
  avec Not_found ->
    soit env =
      filtre sum avec
        Env_empty ->
          Env.empty
      | Env_value(s, id, desc) ->
          Env.add_value id (Subst.value_description subst desc)
                        (env_from_summary s subst)
      | Env_type(s, id, desc) ->
          Env.add_type ~check:faux id
            (Subst.type_declaration subst desc)
            (env_from_summary s subst)
      | Env_exception(s, id, desc) ->
          Env.add_exception ~check:faux id
            (Subst.exception_declaration subst desc)
            (env_from_summary s subst)
      | Env_module(s, id, desc) ->
          Env.add_module_declaration id
            (Subst.module_declaration subst desc)
            (env_from_summary s subst)
      | Env_modtype(s, id, desc) ->
          Env.add_modtype id (Subst.modtype_declaration subst desc)
                          (env_from_summary s subst)
      | Env_class(s, id, desc) ->
          Env.add_class id (Subst.class_declaration subst desc)
                        (env_from_summary s subst)
      | Env_cltype (s, id, desc) ->
          Env.add_cltype id (Subst.cltype_declaration subst desc)
                         (env_from_summary s subst)
      | Env_open(s, path) ->
          soit env = env_from_summary s subst dans
          soit path' = Subst.module_path subst path dans
          soit md =
            essaie
              Env.find_module path' env
            avec Not_found ->
              raise (Error (Module_not_found path'))
          dans
          Env.open_signature Asttypes.Override path'
            (extract_sig env md.md_type) env
      | Env_functor_arg(Env_module(s, id, desc), id') quand Ident.same id id' ->
          Env.add_module_declaration id (Subst.module_declaration subst desc)
            ~arg:vrai (env_from_summary s subst)
      | Env_functor_arg _ -> affirme faux
    dans
      Hashtbl.add env_cache (sum, subst) env;
      env

soit env_of_only_summary env =
  Env.env_of_only_summary env_from_summary env

(* Error report *)

ouvre Format

soit report_error ppf = fonction
  | Module_not_found p ->
      fprintf ppf "@[Impossible de trouver le module %a@].@." Printtyp.path p
