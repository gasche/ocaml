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
ouvre Command
ouvre Bool (* FIXME remove me *)
ouvre Tags.Operators

type decl = {
  tags: Tags.t;
  flags: Command.spec;
  deprecated: bool;
}
soit flags_of_decl { flags; _ } = flags
soit tags_of_decl { tags; _ } = tags

soit all_decls = ref []

soit of_tags matched_tags =
  S début
    List.fold_left début fonc acc { tags; flags; _ } ->
      si Tags.does_match matched_tags tags alors flags :: acc
      sinon acc
    fin [] !all_decls
  fin

soit () = Command.tag_handler := of_tags

soit of_tag_list x = of_tags (Tags.of_list x)

soit add_decl decl =
  all_decls := decl :: !all_decls

soit flag ?(deprecated=faux) tags flags =
  soit tags = Tags.of_list tags dans
  add_decl { tags; flags; deprecated }

soit pflag tags ptag flags =
  Param_tags.declare ptag
    (fonc param -> flag (Param_tags.make ptag param :: tags) (flags param))

soit add x xs = x :: xs
soit remove me = List.filter (fonc x -> me <> x)

soit pretty_print { tags; flags; deprecated } =
  soit sflag = Command.string_of_command_spec flags dans
  soit header = si deprecated alors "deprecated flag" sinon "flag" dans
  soit pp fmt = Log.raw_dprintf (-1) fmt dans
  pp "@[<2>%s@ {. %a .}@ %S@]@\n@\n" header Tags.print tags sflag

soit show_documentation () =
  List.iter
    (fonc decl -> si not decl.deprecated alors pretty_print decl)
    !all_decls;
  List.iter
    (fonc decl -> si decl.deprecated alors pretty_print decl)
    !all_decls;
  soit pp fmt = Log.raw_dprintf (-1) fmt dans
  pp "@."

soit used_tags = ref Tags.empty

soit mark_tag_used tag =
  used_tags := Tags.add tag !used_tags

soit get_used_tags () =
  List.fold_left (fonc acc decl -> Tags.union acc decl.tags)
    !used_tags !all_decls
