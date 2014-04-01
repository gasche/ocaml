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
ouvre Format
ouvre Log

type t = string

inclus Filename

soit print_strings = List.print String.print

soit concat = filename_concat

soit compare (x:t) y = compare x y

soit print = pp_print_string

soit mk s = s

soit pwd = Sys.getcwd ()

soit add_extension ext x = x ^ "." ^ ext

soit check_extension x ext =
  soit lx = String.length x et lext = String.length ext dans
  lx > lext + 1 && x.[lx - lext - 1] = '.' && String.is_suffix x ext

module Operators = struct
  soit ( / ) = concat
  soit ( -.- ) file ext = add_extension ext file
fin
ouvre Operators

soit equal x y = x = y

soit to_string x = x

soit is_link = Shell.is_link
soit readlink = Shell.readlink
soit is_directory x =
  essaie (My_unix.stat x).My_unix.stat_file_kind = My_unix.FK_dir
  avec Sys_error _ -> faux
soit readdir x = Outcome.good (sys_readdir x)

soit dir_seps = ['/';'\\'] (* FIXME add more *)
soit not_normal_form_re = Glob.parse "<**/{,.,..}/**>"

soit parent x = concat parent_dir_name x

soit split p =
  soit rec go p acc =
    soit dir = dirname p dans
    si dir = p alors dir, acc
    sinon go dir (basename p :: acc)
  dans go p []

soit join root paths =
  soit root = si root = current_dir_name alors "" sinon root dans
  List.fold_left (/) root paths

soit _H1 = affirme (current_dir_name = ".")
soit _H2 = affirme (parent_dir_name = "..")

(* Use H1, H2 *)
soit rec normalize_list = fonction
  | [] -> []
  | "." :: xs -> normalize_list xs
  | ".." :: _ -> failwith "Pathname.normalize_list: .. est interdit ici"
  | _ :: ".." :: xs -> normalize_list xs
  | x :: xs -> x :: normalize_list xs

soit normalize x =
  si Glob.eval not_normal_form_re x alors
    soit root, paths = split x dans
    join root (normalize_list paths)
  sinon x

(* [is_prefix x y] is [x] a pathname prefix of [y] *)
soit is_prefix x y =
  soit lx = String.length x et ly = String.length y dans
  si lx = ly alors x = (String.before y lx)
  sinon si lx < ly alors x = (String.before y lx) && List.mem y.[lx] dir_seps
  sinon faux

soit link_to_dir p dir = is_link p && is_prefix dir (readlink p)

soit remove_extension x =
  essaie chop_extension x
  avec Invalid_argument _ -> x
soit get_extension x =
  essaie
    soit pos = String.rindex x '.' dans
    String.after x (pos + 1)
  avec Not_found -> ""
soit update_extension ext x =
  add_extension ext (chop_extension x)

soit chop_extensions x =
  soit dirname = dirname x et basename = basename x dans
  essaie
    soit pos = String.index basename '.' dans
    dirname / (String.before basename pos)
  avec Not_found -> invalid_arg "chop_extensions: pas d'extensions"
soit remove_extensions x =
  essaie chop_extensions x
  avec Invalid_argument _ -> x
soit get_extensions x =
  soit basename = basename x dans
  essaie
    soit pos = String.index basename '.' dans
    String.after basename (pos + 1)
  avec Not_found -> ""
soit update_extensions ext x =
  add_extension ext (chop_extensions x)

soit exists = sys_file_exists

soit copy = Shell.cp
soit remove = Shell.rm
soit try_remove x = si exists x alors Shell.rm x
soit read = read_file

soit with_input_file = with_input_file

soit with_output_file = with_output_file

soit print_path_list = List.print print

soit context_table = Hashtbl.create 107

soit rec include_dirs_of dir =
  essaie Hashtbl.find context_table dir
  avec Not_found -> dir :: List.filter (fonc dir' -> dir <> dir') !Options.include_dirs

(*
let include_dirs_of s =
  let res = include_dirs_of s in
  let () = dprintf 0 "include_dirs_of %S ->@ %a" s (List.print print) res
  in res
*)

soit define_context dir context =
  soit dir = si dir = "" alors current_dir_name sinon dir dans
  Hashtbl.replace context_table dir& List.union context& include_dirs_of dir

soit same_contents x y = Digest.file x = Digest.file y
