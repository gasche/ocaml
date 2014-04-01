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


(* Original author: Romain Bardou *)

module StringSet = Set.Make(String)

(* tag name -> tag action (string -> unit) *)
soit declared_tags = Hashtbl.create 17

soit acknowledged_tags = ref []

soit only_once f =
  soit instances = ref StringSet.empty dans
  fonc param ->
    si StringSet.mem param !instances alors ()
    sinon début
      instances := StringSet.add param !instances;
      f param
    fin

soit declare name action =
  Hashtbl.add declared_tags name (only_once action)

soit parse tag = Lexers.tag_gen (Lexing.from_string tag)

soit acknowledge maybe_loc tag =
  acknowledged_tags := (parse tag, maybe_loc) :: !acknowledged_tags

soit really_acknowledge ?(quiet=faux) ((name, param), maybe_loc) =
  filtre param avec
    | None ->
        si Hashtbl.mem declared_tags name && not quiet alors
          Log.eprintf "%aWarning: tag %S expects a parameter"
            Loc.print_loc_option maybe_loc name
    | Some param ->
        soit actions = List.rev (Hashtbl.find_all declared_tags name) dans
        si actions = [] && not quiet alors
          Log.eprintf "%aWarning: tag %S does not expect a parameter, \
                       but is used with parameter %S"
            Loc.print_loc_option maybe_loc name param;
        List.iter (fonc f -> f param) actions

soit partial_init ?quiet tags =
  Tags.iter (fonc tag -> really_acknowledge ?quiet (parse tag, None)) tags

soit init () =
  List.iter really_acknowledge (My_std.List.ordered_unique !acknowledged_tags)

soit make = Printf.sprintf "%s(%s)"
