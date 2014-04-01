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
ouvre Pathname.Operators

module Resources = Set.Make(Pathname)

soit print = Pathname.print

soit equal = (=)
soit compare = compare

soit in_source_dir p =
  si Pathname.is_implicit p alors Pathname.pwd/p sinon invalid_arg (Printf.sprintf "in_source_dir: %S" p)

soit in_build_dir p =
  si Pathname.is_relative p alors p
  sinon invalid_arg (Printf.sprintf "in_build_dir: %S" p)

soit clean_up_links entry =
  si not !Options.make_links alors entry sinon
  Slurp.filter début fonc path name _ ->
    soit pathname = in_source_dir (path/name) dans
    si Pathname.link_to_dir pathname !Options.build_dir alors
      soit z = Pathname.readlink pathname dans
      (* Here is one exception where one can use Sys.file_exists directly *)
      (si not (Sys.file_exists z) alors
        Shell.rm pathname; faux)
    sinon vrai
  fin entry

soit clean_up_link_to_build () =
  Options.entry := Some(clean_up_links (the !Options.entry))

soit source_dir_path_set_without_links_to_build =
  paresseux début
    clean_up_link_to_build ();
    Slurp.fold (fonc path name _ -> StringSet.add (path/name))
               (the !Options.entry) StringSet.empty
  fin

soit clean_links () =
  si !*My_unix.is_degraded alors
    ()
  sinon
    ignore (clean_up_link_to_build ())

soit exists_in_source_dir p =
  si !*My_unix.is_degraded alors sys_file_exists (in_source_dir p)
  sinon StringSet.mem p !*source_dir_path_set_without_links_to_build

soit clean p = Shell.rm_f p

module Cache = struct

  soit clean () = Shell.chdir Pathname.pwd; Shell.rm_rf !Options.build_dir

  type knowledge =
    | Yes
    | No
    | Unknown

  type suspension = (Command.t * (unit -> unit))

  type build_status =
    | Bbuilt
    | Bcannot_be_built
    | Bnot_built_yet
    | Bsuspension de suspension

  type cache_entry =
    { modifiable built        : build_status;
      modifiable changed      : knowledge;
      modifiable dependencies : Resources.t }

  soit empty () =
    { built        = Bnot_built_yet;
      changed      = Unknown;
      dependencies = Resources.empty }

  soit print_knowledge f =
    fonction
    | Yes -> pp_print_string f "Yes"
    | No  -> pp_print_string f "No"
    | Unknown -> pp_print_string f "Unknown"

  soit print_build_status f =
    fonction
    | Bbuilt -> pp_print_string f "Bbuilt"
    | Bnot_built_yet -> pp_print_string f "Bnot_built_yet"
    | Bcannot_be_built -> pp_print_string f "Bcannot_be_built"
    | Bsuspension(cmd, _) ->
        fprintf f "@[<2>Bsuspension(%a,@ (<fun> : unit -> unit))@]" Command.print cmd

  soit print_cache_entry f e =
    fprintf f "@[<2>{ @[<2>built =@ %a@];@ @[<2>changed =@ %a@];@ @[<2>dependencies =@ %a@]@ }@]"
      print_build_status e.built print_knowledge e.changed Resources.print e.dependencies

  soit cache = Hashtbl.create 103

  soit get r =
    essaie Hashtbl.find cache r
    avec Not_found ->
      soit cache_entry = empty () dans
      Hashtbl.add cache r cache_entry; cache_entry

  soit fold_cache f x = Hashtbl.fold f cache x

  soit print_cache f () =
    fprintf f "@[<hv0>@[<hv2>{:";
    fold_cache début fonc k v () ->
      fprintf f "@ @[<2>%a =>@ %a@];" print k print_cache_entry v
    fin ();
    fprintf f "@]:}@]"

  soit print_graph f () =
    fprintf f "@[<hv0>@[<hv2>{:";
    fold_cache début fonc k v () ->
      si not (Resources.is_empty v.dependencies) alors
        fprintf f "@ @[<2>%a =>@ %a@];" print k Resources.print v.dependencies
    fin ();
    fprintf f "@]@ :}@]"

  soit resource_changed r =
    dprintf 10 "resource_changed:@ %a" print r;
    (get r).changed <- Yes

  soit external_is_up_to_date absolute_path =
    soit key = "Resource: " ^ absolute_path dans
    soit digest = Digest.file absolute_path dans
    soit is_up_to_date =
      essaie
        soit digest' = Digest_cache.get key dans
        digest = digest'
      avec Not_found ->
        faux
    dans
    is_up_to_date || (Digest_cache.put key digest; faux)

  soit source_is_up_to_date r_in_source_dir r_in_build_dir =
    soit key = "Resource: " ^ r_in_source_dir dans
    soit digest = Digest.file r_in_source_dir dans
    soit r_is_up_to_date =
      Pathname.exists r_in_build_dir &&
      essaie
        soit digest' = Digest_cache.get key dans
        digest = digest'
      avec Not_found ->
        faux
    dans
    r_is_up_to_date || (Digest_cache.put key digest; faux)

  soit prod_is_up_to_date p =
    soit x = in_build_dir p dans
    not (exists_in_source_dir p) || Pathname.exists x && Pathname.same_contents x (in_source_dir p)

  soit rec resource_has_changed r =
    soit cache_entry = get r dans
    filtre cache_entry.changed avec
    | Yes -> vrai
    | No -> faux
    | Unknown ->
      soit res =
        filtre cache_entry.built avec
        | Bbuilt -> faux
        | Bsuspension _ -> affirme faux
        | Bcannot_be_built -> faux
        | Bnot_built_yet -> not (prod_is_up_to_date r) dans
      soit () = cache_entry.changed <- si res alors Yes sinon No dans res

  soit resource_state r = (get r).built

  soit resource_built r = (get r).built <- Bbuilt

  soit resource_failed r = (get r).built <- Bcannot_be_built

  soit import_in_build_dir r =
    soit cache_entry = get r dans
    soit r_in_build_dir = in_build_dir r dans
    soit r_in_source_dir = in_source_dir r dans
    si source_is_up_to_date r_in_source_dir r_in_build_dir alors début
      dprintf 5 "%a exists and up to date" print r;
    fin sinon début
      dprintf 5 "%a exists in source dir -> import it" print r;
      Shell.mkdir_p (Pathname.dirname r);
      Pathname.copy r_in_source_dir r_in_build_dir;
      cache_entry.changed <- Yes;
    fin;
    cache_entry.built <- Bbuilt

  soit suspend_resource r cmd kont prods =
    soit cache_entry = get r dans
    filtre cache_entry.built avec
    | Bsuspension _ -> ()
    | Bbuilt -> ()
    | Bcannot_be_built -> affirme faux
    | Bnot_built_yet ->
        soit kont = début fonc () ->
          kont ();
          List.iter début fonc prod ->
            (get prod).built <- Bbuilt
          fin prods
        fin dans cache_entry.built <- Bsuspension(cmd, kont)

  soit resume_suspension (cmd, kont) =
    Command.execute cmd;
    kont ()

  soit resume_resource r =
    soit cache_entry = get r dans
    filtre cache_entry.built avec
    | Bsuspension(s) -> resume_suspension s
    | Bbuilt -> ()
    | Bcannot_be_built -> ()
    | Bnot_built_yet -> ()

  soit get_optional_resource_suspension r =
    filtre (get r).built avec
    | Bsuspension cmd_kont -> Some cmd_kont
    | Bbuilt | Bcannot_be_built | Bnot_built_yet -> None

  soit clear_resource_failed r = (get r).built <- Bnot_built_yet

  soit dependencies r = (get r).dependencies

  soit fold_dependencies f =
    fold_cache (fonc k v -> Resources.fold (f k) v.dependencies)

  soit add_dependency r s =
    soit cache_entry = get r dans
    cache_entry.dependencies <- Resources.add s cache_entry.dependencies

  soit print_dependencies = print_graph

fin

soit digest p =
  soit f = Pathname.to_string (in_build_dir p) dans
  soit buf = Buffer.create 1024 dans
  Buffer.add_string buf f;
  (si sys_file_exists f alors Buffer.add_string buf (Digest.file f));
  Digest.string (Buffer.contents buf)

soit exists_in_build_dir p = Pathname.exists (in_build_dir p)

(*
type env = string

let split_percent s =
  try
    let pos = String.index s '%' in
    Some (String.before s pos, String.after s (pos + 1))
  with Not_found -> None

let extract prefix suffix s =
  let lprefix = String.length prefix in
  let lsuffix = String.length suffix in
  let ls = String.length s in
  if lprefix + lsuffix > ls then None else
  let s' = String.sub s lprefix (ls - lsuffix - lprefix) in
  if equal (prefix ^ s' ^ suffix) s then Some s' else None

let matchit r1 r2 =
  match split_percent r1 with
  | Some (x, y) -> extract x y r2
  | _ -> if equal r1 r2 then Some "" else None

let rec subst percent r =
  match split_percent r with
  | Some (x, y) -> x ^ percent ^ y
  | _ -> r

let print_env = pp_print_string
*)

(* Should normalize *)
soit import x = Pathname.normalize x

module MetaPath : sig

        type t
        type env

        val mk : (bool * string) -> t
        val matchit : t -> string -> env option
        val subst : env -> t -> string
        val print_env : Format.formatter -> env -> unit

fin = struct
        ouvre Glob_ast

        type atoms = A de string | V de string * Glob.globber
        type t = atoms list
        type env = (string * string) list

        exception No_solution

        soit mk (pattern_allowed, s) = List.map début fonction
          | `Var(var_name, globber) -> V(var_name, globber)
          | `Word s -> A s
        fin (Lexers.path_scheme pattern_allowed (Lexing.from_string s))

        soit mk = memo mk

        soit match_prefix s pos prefix =
                filtre String.contains_string s pos prefix avec
                | Some(pos') -> si pos = pos' alors pos' + String.length prefix sinon raise No_solution
                | None -> raise No_solution

        soit matchit p s =
          soit sl = String.length s dans
                soit rec loop xs pos acc delta =
                        filtre xs avec
                        | [] -> si pos = sl alors acc sinon raise No_solution
                        | A prefix :: xs -> loop xs (match_prefix s pos prefix) acc 0
                        | V(var, patt) :: A s2 :: xs' ->
                            début filtre String.contains_string s (pos + delta) s2 avec
                            | Some(pos') ->
                                soit matched = String.sub s pos (pos' - pos) dans
                                si Glob.eval patt matched
                                alors
                                  essaie loop xs' (pos' + String.length s2) ((var, matched) :: acc) 0
                                  avec No_solution -> loop xs  pos acc (pos' - pos + 1)
                                sinon loop xs  pos acc (pos' - pos + 1)
                            | None -> raise No_solution
                            fin
                        | [V(var, patt)] ->
                            soit matched = String.sub s pos (sl - pos) dans
                            si Glob.eval patt matched alors (var, matched) :: acc sinon raise No_solution
                        | V _ :: _ -> affirme faux
                dans
                essaie     Some (loop p 0 [] 0)
                avec No_solution -> None

  soit pp_opt pp_elt f =
    fonction
    | None -> pp_print_string f "None"
    | Some x -> Format.fprintf f "Some(%a)" pp_elt x

  soit print_env f env =
    List.iter début fonc (k, v) ->
      si k = "" alors Format.fprintf f "%%=%s " v
      sinon Format.fprintf f "%%(%s)=%s " k v
    fin env

  (* let matchit p s =
    let res = matchit p s in
      Format.eprintf "matchit %S %S = %a@." p s (pp_opt print_env) res;
    res

  let _ = begin
    assert (matchit "%(path)lib%(libname).a" "libfoo.a" <> None);
    assert (matchit "%(path)lib%(libname).a" "path/libfoo.a" <> None);
    assert (matchit "libfoo.a" "libfoo.a" <> None);
    assert (matchit "lib%(libname).a" "libfoo.a" <> None);
    assert (matchit "%(path)libfoo.a" "path/libfoo.a" <> None);
    assert (matchit "foo%" "foobar" <> None);
    exit 42
  end;; *)

  soit subst env s =
    String.concat "" début
      List.map début fonc x ->
        filtre x avec
        | A atom -> atom
        | V(var, _) -> essaie List.assoc var env avec Not_found -> (* unbound variable *) ""
      fin s
    fin
fin

type env = MetaPath.env
type resource_pattern = (Pathname.t * MetaPath.t)

soit print_pattern f (x, _) = Pathname.print f x

soit import_pattern x = x, MetaPath.mk (vrai, x)
soit matchit (_, p) x = MetaPath.matchit p x

soit subst env s = MetaPath.subst env (MetaPath.mk (faux, s))
soit subst_any env s = MetaPath.subst env (MetaPath.mk (vrai, s))
soit subst_pattern env (_, p) = MetaPath.subst env p

soit print_env = MetaPath.print_env
