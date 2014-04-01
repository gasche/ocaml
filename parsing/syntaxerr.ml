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
    Unclosed de Location.t * string * Location.t * string
  | Expecting de Location.t * string
  | Not_expecting de Location.t * string
  | Applicative_path de Location.t
  | Variable_in_scope de Location.t * string
  | Other de Location.t

exception Error de error
exception Escape_error

soit prepare_error = fonction
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

soit () =
  Location.register_error_of_exn
    (fonction
      | Error err -> Some (prepare_error err)
      | _ -> None
    )


soit report_error ppf err =
  Location.report_error ppf (prepare_error err)

soit location_of_error = fonction
  | Unclosed(l,_,_,_)
  | Applicative_path l
  | Variable_in_scope(l,_)
  | Other l
  | Not_expecting (l, _)
  | Expecting (l, _) -> l
