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
ouvre Log
ouvre Lexers

type t = Lexers.conf

soit acknowledge_config config =
  soit ack (tag, loc) = Param_tags.acknowledge (Some loc) tag dans
  List.iter (fonc (_, config) -> List.iter ack config.plus_tags) config

soit cache = Hashtbl.create 107
soit (configs, add_config) =
  soit configs = ref [] dans
  (fonc () -> !configs),
  (fonc config ->
     acknowledge_config config;
     configs := config :: !configs;
     Hashtbl.clear cache)

soit parse_lexbuf ?dir source lexbuf =
  lexbuf.Lexing.lex_curr_p <-
    { lexbuf.Lexing.lex_curr_p avec Lexing.pos_fname = source };
  soit conf = Lexers.conf_lines dir lexbuf dans
  add_config conf

soit parse_string s =
  parse_lexbuf (Printf.sprintf "STRING(%s)" s) (Lexing.from_string s)

soit parse_file ?dir file =
  with_input_file file début fonc ic ->
    parse_lexbuf ?dir file (Lexing.from_channel ic)
  fin

soit key_match = Glob.eval

soit apply_config s (config : t) init =
  soit add (tag, _loc) = Tags.add tag dans
  soit remove (tag, _loc) = Tags.remove tag dans
  List.fold_left début fonc tags (key, v) ->
    si key_match key s alors
      List.fold_right add v.plus_tags (List.fold_right remove v.minus_tags tags)
    sinon tags
  fin init config

soit apply_configs s = List.fold_right (apply_config s) (configs ()) Tags.empty

soit tags_of_filename s =
  essaie Hashtbl.find cache s
  avec Not_found ->
    soit res = apply_configs s dans
    soit () = Hashtbl.replace cache s res dans
    res

soit global_tags () = tags_of_filename ""
soit has_tag tag = Tags.mem tag (global_tags ())

soit tag_file file tags =
  si tags <> [] alors parse_string (Printf.sprintf "%S: %s" file (String.concat ", " tags));;

soit tag_any tags =
  si tags <> [] alors parse_string (Printf.sprintf "true: %s" (String.concat ", " tags));;

soit check_tags_usage useful_tags =
  soit check_tag (tag, loc) =
    si not (Tags.mem tag useful_tags) alors
      Log.eprintf "%aWarning: the tag %S is not used in any flag declaration, \
                   so it will have no effect; it may be a typo. Otherwise use \
                   `mark_tag_used` in your myocamlbuild.ml to disable \
                   this warning."
        Loc.print_loc loc tag
  dans
  soit check_conf (_, values) =
    List.iter check_tag values.plus_tags;
    List.iter check_tag values.minus_tags;
  dans
  List.iter (List.iter check_conf) (configs ())
