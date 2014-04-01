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
ouvre Command
ouvre Pathname.Operators

type 'a arch =
  | Arch_dir de string * 'a * 'a arch list
  | Arch_dir_pack de string * 'a * 'a arch list
  | Arch_file de string * 'a

soit dir name contents = Arch_dir(name, (), contents)
soit dir_pack name contents = Arch_dir_pack(name, (), contents)
soit file name = Arch_file(name, ())

type info =
{
  current_path : string;
  include_dirs : string list;
  for_pack     : string;
}

soit join_pack parent base =
  si parent = "" alors base sinon parent ^ "." ^ base

soit annotate arch =
  soit rec self arch acc =
    filtre arch avec
    | Arch_dir_pack(name, _, contents) ->
        soit acc = { (acc) avec for_pack = join_pack acc.for_pack name } dans
        soit (_, _, i, new_contents) = self_contents name contents acc dans
        ([], Arch_dir_pack(name, i, List.rev new_contents))
    | Arch_dir(name, _, contents) ->
        soit (current_path, include_dirs, i, new_contents) = self_contents name contents acc dans
        (current_path :: include_dirs, Arch_dir(name, i, List.rev new_contents))
    | Arch_file(name, _) ->
        ([], Arch_file(name, acc))
  et self_contents name contents acc =
    soit current_path = acc.current_path/name dans
    soit include_dirs = si current_path = "" alors acc.include_dirs sinon current_path :: acc.include_dirs dans
    soit i = { (acc) avec current_path = current_path; include_dirs = include_dirs } dans
    soit (include_dirs, new_contents) =
      List.fold_left début fonc (include_dirs, new_contents) x ->
        soit j = { (i) avec include_dirs = include_dirs @ i.include_dirs } dans
        soit (include_dirs', x') = self x j dans
        (include_dirs @ include_dirs', x' :: new_contents)
      fin ([], []) contents dans
    (current_path, include_dirs, i, new_contents) dans
  soit init = { current_path = ""; include_dirs = []; for_pack = "" } dans
  snd (self arch init)

soit rec print print_info f =
  soit rec print_contents f =
    fonction
    | [] -> ()
    | x :: xs -> Format.fprintf f "@ %a%a" (print print_info) x print_contents xs dans
  fonction
  | Arch_dir(name, info, contents) ->
      Format.fprintf f "@[<v2>dir %S%a%a@]" name print_info info print_contents contents
  | Arch_dir_pack(name, info, contents) ->
      Format.fprintf f "@[<v2>dir_pack %S%a%a@]" name print_info info print_contents contents
  | Arch_file(name, info) ->
      Format.fprintf f "@[<2>file %S%a@]" name print_info info

soit print_include_dirs = List.print String.print

soit print_info f i =
  Format.fprintf f "@ @[<v2>{ @[<2>current_path =@ %S@];@\
                            \ @[<2>include_dirs =@ %a@];@\
                            \ @[<2>for_pack =@ %S@] }@]"
                 i.current_path print_include_dirs i.include_dirs i.for_pack

soit rec iter_info f =
  fonction
  | Arch_dir_pack(_, i, xs) | Arch_dir(_, i, xs) ->
      f i; List.iter (iter_info f) xs
  | Arch_file(_, i) -> f i

soit rec fold_info f arch acc =
  filtre arch avec
  | Arch_dir_pack(_, i, xs) | Arch_dir(_, i, xs) ->
      List.fold_right (fold_info f) xs (f i acc)
  | Arch_file(_, i) -> f i acc

module SS = Set.Make(String)

soit iter_include_dirs arch =
  soit set = fold_info (fonc i -> List.fold_right SS.add i.include_dirs) arch SS.empty dans
  fonc f -> SS.iter f set

soit forpack_flags_of_pathname = ref (fonc _ -> N)

soit print_table print_value f table =
  Format.fprintf f "@[<hv0>{:@[<hv0>";
  Hashtbl.iter début fonc k v ->
    si k <> "" alors
      Format.fprintf f "@ @[<2>%S =>@ %a@];" k print_value v;
  fin table;
  Format.fprintf f "@]@ :}@]"

soit print_tables f (include_dirs_table, for_pack_table) =
  Format.fprintf f "@[<2>@[<2>include_dirs_table:@ %a@];@ @[<2>for_pack_table: %a@]@]"
     (print_table (List.print String.print)) include_dirs_table
     (print_table String.print) for_pack_table

soit mk_tables arch =
  soit include_dirs_table = Hashtbl.create 17
  et for_pack_table = Hashtbl.create 17 dans
  iter_info début fonc i ->
    Hashtbl.replace include_dirs_table i.current_path i.include_dirs;
    Hashtbl.replace for_pack_table i.current_path i.for_pack
  fin arch;
  soit previous_forpack_flags_of_pathname = !forpack_flags_of_pathname dans
  forpack_flags_of_pathname := début fonc m ->
    soit m' = Pathname.dirname m dans
    essaie
      soit for_pack = Hashtbl.find for_pack_table m' dans
      si for_pack = "" alors N sinon S[A"-for-pack"; A for_pack]
    avec Not_found -> previous_forpack_flags_of_pathname m
  fin;
  (* Format.eprintf "@[<2>%a@]@." print_tables (include_dirs_table, for_pack_table); *)
  (include_dirs_table, for_pack_table)

soit forpack_flags_of_pathname m = !forpack_flags_of_pathname m
