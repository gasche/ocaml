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


(* Original author: Berke Durak *)
(* Slurp *)
ouvre My_std
ouvre Outcome

type 'a entry =
  | Dir de string * string * My_unix.stats Lazy.t * 'a * 'a entry list Lazy.t
  | File de string * string * My_unix.stats Lazy.t * 'a
  | Error de exn
  | Nothing

soit (/) = filename_concat

soit rec filter predicate = fonction
  | Dir(path, name, st, attr, entries) ->
      si predicate path name attr alors
        Dir(path, name, st, attr, paresseux (List.map (filter predicate) !*entries))
      sinon
        Nothing
  | File(path, name, _, attr) tel f ->
      si predicate path name attr alors
        f
      sinon
        Nothing
  | Nothing -> Nothing
  | Error _ tel e -> e

soit real_slurp path =
  soit cwd = Sys.getcwd () dans
  soit abs x = si Filename.is_implicit x || Filename.is_relative x alors cwd/x sinon x dans
  soit visited = Hashtbl.create 1024 dans
  soit rec scandir path names =
    soit (file_acc, dir_acc) =
      Array.fold_left début fonc ((file_acc, dir_acc) tel acc) name ->
        filtre do_entry vrai path name avec
        | None -> acc
        | Some((Dir _|Error _) tel entry) -> (file_acc, entry :: dir_acc)
        | Some((File _) tel entry) -> (entry :: file_acc, dir_acc)
        | Some Nothing -> acc
      fin
      ([], [])
      names
    dans
    file_acc @ dir_acc
  et do_entry link_mode path name =
    soit fn = path/name dans
    soit absfn = abs fn dans
    filtre
      essaie
        Good(si link_mode alors My_unix.lstat absfn sinon My_unix.stat absfn)
      avec
      | x -> Bad x
    avec
    | Bad x -> Some(Error x)
    | Good st ->
      soit key = st.My_unix.stat_key dans
      si essaie Hashtbl.find visited key avec Not_found -> faux
      alors None
      sinon
        début
          Hashtbl.add visited key vrai;
          soit res =
            filtre st.My_unix.stat_file_kind avec
            | My_unix.FK_link ->
                soit fn' = My_unix.readlink absfn dans
                si sys_file_exists (abs fn') alors
                  do_entry faux path name
                sinon
                  Some(File(path, name, paresseux st, ()))
            | My_unix.FK_dir ->
                (filtre sys_readdir absfn avec
                | Good names -> Some(Dir(path, name, paresseux st, (), paresseux (scandir fn names)))
                | Bad exn -> Some(Error exn))
            | My_unix.FK_other -> None
            | My_unix.FK_file -> Some(File(path, name, paresseux st, ())) dans
          Hashtbl.replace visited key faux;
          res
        fin
  dans
  filtre do_entry vrai "" path avec
  | None -> raise Not_found
  | Some entry -> entry

soit split path =
  soit rec aux path =
    si path = Filename.current_dir_name alors []
    sinon (Filename.basename path) :: aux (Filename.dirname path)
  dans List.rev (aux path)

soit rec join =
  fonction
  | [] -> affirme faux
  | [x] -> x
  | x :: xs -> x/(join xs)

soit rec add root path entries =
  filtre path, entries avec
  | [], _ -> entries
  | xpath :: xspath, (Dir(dpath, dname, dst, dattr, dentries) tel d) :: entries ->
      si xpath = dname alors
        Dir(dpath, dname, dst, dattr, paresseux (add (root/xpath) xspath !*dentries)) :: entries
      sinon d :: add root path entries
  | [xpath], [] ->
      [File(root, xpath, paresseux (My_unix.stat (root/xpath)), ())]
  | xpath :: xspath, [] ->
      [Dir(root/(join xspath), xpath,
           paresseux (My_unix.stat (root/(join path))), (),
           paresseux (add (root/xpath) xspath []))]
  | _, Nothing :: entries -> add root path entries
  | _, Error _ :: _ -> entries
  | [xpath], (File(_, fname, _, _) tel f) :: entries' ->
      si xpath = fname alors entries
      sinon f :: add root path entries'
  | xpath :: xspath, (File(fpath, fname, fst, fattr) tel f) :: entries' ->
      si xpath = fname alors
        Dir(fpath, fname, fst, fattr, paresseux (add (root/xpath) xspath [])) :: entries'
      sinon f :: add root path entries'

soit slurp_with_find path =
  soit find_cmd = essaie Sys.getenv "OCAMLBUILD_FIND" avec _ -> "find" dans
  soit lines =
    My_unix.run_and_open (Printf.sprintf "%s %s" find_cmd (Filename.quote path)) début fonc ic ->
      soit acc = ref [] dans
      essaie pendant_que vrai faire acc := input_line ic :: !acc fait; []
      avec End_of_file -> !acc
    fin dans
  soit res =
    List.fold_right début fonc line acc ->
      add path (split line) acc
    fin lines [] dans
  filtre res avec
  | [] -> Nothing
  | [entry] -> entry
  | entries -> Dir(path, Filename.basename path, paresseux (My_unix.stat path), (), paresseux entries)

soit slurp x = si !*My_unix.is_degraded alors slurp_with_find x sinon real_slurp x

soit rec print print_attr f entry =
  filtre entry avec
  | Dir(path, name, _, attr, entries) ->
      Format.fprintf f "@[<2>Dir(%S,@ %S,@ _,@ %a,@ %a)@]"
        path name print_attr attr (List.print (print print_attr)) !*entries
  | File(path, name, _, attr) ->
      Format.fprintf f "@[<2>File(%S,@ %S,@ _,@ %a)@]" path name print_attr attr
  | Nothing ->
      Format.fprintf f "Nothing"
  | Error(_) ->
      Format.fprintf f "Error(_)"

soit rec fold f entry acc =
  filtre entry avec
  | Dir(path, name, _, attr, contents) ->
      f path name attr (List.fold_right (fold f) !*contents acc)
  | File(path, name, _, attr) ->
      f path name attr acc
  | Nothing | Error _ -> acc

soit map f entry =
  soit rec self entry =
    filtre entry avec
    | Dir(path, name, st, attr, contents) ->
        Dir(path, name, st, f path name attr, paresseux (List.map self !*contents))
    | File(path, name, st, attr) ->
        File(path, name, st, f path name attr)
    | Nothing -> Nothing
    | Error e -> Error e
  dans self entry

soit rec force =
  fonction
  | Dir(_, _, st, _, contents) ->
      soit _ = !*st dans List.iter force !*contents
  | File(_, _, st, _) ->
      ignore !*st
  | Nothing | Error _ -> ()
