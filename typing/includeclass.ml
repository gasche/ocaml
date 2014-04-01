(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*          Jerome Vouillon, projet Cristal, INRIA Rocquencourt        *)
(*                                                                     *)
(*  Copyright 1997 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Inclusion checks for the class language *)

ouvre Types

soit class_types env cty1 cty2 =
  Ctype.match_class_types env cty1 cty2

soit class_type_declarations env cty1 cty2 =
  Ctype.match_class_declarations env
    cty1.clty_params cty1.clty_type
    cty2.clty_params cty2.clty_type

soit class_declarations env cty1 cty2 =
  filtre cty1.cty_new, cty2.cty_new avec
    None, Some _ ->
      [Ctype.CM_Virtual_class]
  | _ ->
      Ctype.match_class_declarations env
        cty1.cty_params cty1.cty_type
        cty2.cty_params cty2.cty_type

ouvre Format
ouvre Ctype

(*
let rec hide_params = function
    Tcty_arrow ("*", _, cty) -> hide_params cty
  | cty -> cty
*)

soit include_err ppf =
  fonction
  | CM_Virtual_class ->
      fprintf ppf "Une classe ne peut pas être transformée de virtuelle à concrète"
  | CM_Parameter_arity_mismatch (ls, lp) ->
      fprintf ppf
        "Les classes n'ont pas le même nombre de paramètres"
  | CM_Type_parameter_mismatch (env, trace) ->
      Printtyp.report_unification_error ppf env ~unif:faux trace
        (fonction ppf ->
          fprintf ppf "Un paramètre de type a le type")
        (fonction ppf ->
          fprintf ppf "mais son type attendu est")
  | CM_Class_type_mismatch (env, cty1, cty2) ->
      Printtyp.wrap_printing_env env (fonc () ->
        fprintf ppf
          "@[Le type de classe@;<1 2>%a@ %s@;<1 2>%a@]"
          Printtyp.class_type cty1
          "ne correspond pas au type de classe"
          Printtyp.class_type cty2)
  | CM_Parameter_mismatch (env, trace) ->
      Printtyp.report_unification_error ppf env ~unif:faux trace
        (fonction ppf ->
          fprintf ppf "Un paramètre a le type")
        (fonction ppf ->
          fprintf ppf "mais son type attendu est")
  | CM_Val_type_mismatch (lab, env, trace) ->
      Printtyp.report_unification_error ppf env ~unif:faux trace
        (fonction ppf ->
          fprintf ppf "La variable d'instance %s@ a le type" lab)
        (fonction ppf ->
          fprintf ppf "mais son type attendu est")
  | CM_Meth_type_mismatch (lab, env, trace) ->
      Printtyp.report_unification_error ppf env ~unif:faux trace
        (fonction ppf ->
          fprintf ppf "La méthodde %s@ a le type" lab)
        (fonction ppf ->
          fprintf ppf "mais son type attendu est")
  | CM_Non_mutable_value lab ->
      fprintf ppf
       "@[La variable d'instance non mutable %s ne peut pas devenir mutable@]" lab
  | CM_Non_concrete_value lab ->
      fprintf ppf
       "@[La variable d'instance virtuelle %s ne peut pas devenir concrète@]" lab
  | CM_Missing_value lab ->
      fprintf ppf "@[Le premier type de classe n'a pas de variable d'instance %s@]" lab
  | CM_Missing_method lab ->
      fprintf ppf "@[Le premmier type de classe n'a pas de méthode %s@]" lab
  | CM_Hide_public lab ->
     fprintf ppf "@[La méthode publique %s ne peut pas être cachée@]" lab
  | CM_Hide_virtual (k, lab) ->
      fprintf ppf "@[La %s virtuelle %s ne peut pas être cachée@]" k lab
  | CM_Public_method lab ->
      fprintf ppf "@[La méthode publique %s ne peut pas devenir privée" lab
  | CM_Virtual_method lab ->
      fprintf ppf "@[La méthode virtuelle %s ne peut pas devenir concrète" lab
  | CM_Private_method lab ->
      fprintf ppf "La méthode privée %s ne peut pas devenir publique" lab

soit report_error ppf = fonction
  |  [] -> ()
  | err :: errs ->
      soit print_errs ppf errs =
         List.iter (fonc err -> fprintf ppf "@ %a" include_err err) errs dans
      fprintf ppf "@[<v>%a%a@]" include_err err print_errs errs
