(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1997 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Auxiliary type for reporting syntax errors *)

type error =
    Unclosed of Location.t * string * Location.t * string
  | Expecting of Location.t * string
  | Not_expecting of Location.t * string
  | Applicative_path of Location.t
  | Variable_in_scope of Location.t * string
  | Other of Location.t

exception Error of error
exception Escape_error

let prepare_error = function
  | Unclosed(opening_loc, opening, closing_loc, closing) ->
      Location.errorf ~loc:closing_loc
        ~sub:[
          Location.error ~loc:opening_loc
            (Printf.sprintf "Erreur: Ce '%s' pourrait être un orphelin" opening)
        ]
        ~if_highlight:
          (Printf.sprintf "Erreur de syntaxe: '%s' attendu, \
                           le '%s' souligné pourrait être orphelin"
             closing opening)
        "Erreur: erreur de syntaxe: '%s' attendu" closing

  | Expecting (loc, nonterm) ->
      Location.errorf ~loc "Erreur: erreur de syntaxe: '%s' attendu" nonterm
  | Not_expecting (loc, nonterm) ->
      Location.errorf ~loc "Erreur: erreur de syntaxe: '%s' inattendu" nonterm
  | Applicative_path loc ->
      Location.errorf ~loc
        "Erreur: erreur de syntaxe: les chemins applicatifs de la forme F(X).t \
         ne sont pas tolérés quand l'option -no-app-func est activée."
  | Variable_in_scope (loc, var) ->
      Location.errorf ~loc
        "Erreur: Dans ce type téléscopé, la variable '%s \
         est réservée pour le type local %s."
        var var
  | Other loc ->
      Location.error ~loc "Erreur: erreur de syntaxe"

let () =
  Location.register_error_of_exn
    (function
      | Error err -> Some (prepare_error err)
      | _ -> None
    )


let report_error ppf err =
  Location.report_error ppf (prepare_error err)

let location_of_error = function
  | Unclosed(l,_,_,_)
  | Applicative_path l
  | Variable_in_scope(l,_)
  | Other l
  | Not_expecting (l, _)
  | Expecting (l, _) -> l
