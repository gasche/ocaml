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
ouvre Tools
ouvre Ocaml_utils

soit mydprintf fmt = dprintf 10 fmt

exception Circular_dependencies de string list * string

module type INPUT = sig
  val fold_dependencies : (string -> string -> 'a -> 'a) -> 'a -> 'a
  val fold_libraries : (string -> string list -> 'a -> 'a) -> 'a -> 'a
  val fold_packages : (string -> string list -> 'a -> 'a) -> 'a -> 'a
fin

module Make (I : INPUT) = struct
  ouvre I

  module SMap = Map.Make(String)

  module Resources = Resource.Resources

  module Utils = struct
    soit add = SMap.add

    soit empty = SMap.empty

    soit find_all_set x acc =
      essaie SMap.find x acc avec Not_found -> Resources.empty

    soit smap_add_set src dst acc =
      SMap.add src (Resources.add dst (find_all_set src acc)) acc

    soit print_smap pp f smap =
      Format.fprintf f "@[<hv0>{:@[<hv2>";
      SMap.iter début fonc k v ->
        Format.fprintf f "@ @[<2>%S =>@ %a@];" k pp v
      fin smap;
      Format.fprintf f "@]@,:}@]"

    soit print_smap_list = print_smap pp_l

    soit print_smap_set = print_smap Resources.print

    soit print_lazy pp f l = pp f !*l

    soit find_all_list x acc =
      essaie SMap.find x acc avec Not_found -> []

    soit find_all_rec xs map =
      soit visited = Hashtbl.create 32 dans
      soit rec self x acc =
        essaie
          Hashtbl.find visited x; acc
        avec Not_found ->
          Hashtbl.replace visited x ();
          soit acc = Resources.add x acc dans
          essaie Resources.fold self (SMap.find x map) acc
          avec Not_found -> acc
      dans List.fold_right self xs Resources.empty

    soit mkindex fold filter =
      fold début fonc name contents acc ->
        si filter name alors
          List.fold_right début fonc elt acc ->
            add elt (name :: (find_all_list elt acc)) acc
          fin contents acc
        sinon
          acc
      fin empty

  fin
  ouvre Utils

  soit caml_transitive_closure
        ?(caml_obj_ext="cmo")
        ?(caml_lib_ext="cma")
        ?(pack_mode=faux)
        ?(used_libraries=[])
        ?(hidden_packages=[]) fns =

    soit valid_link_exts =
      si pack_mode alors [caml_obj_ext; "cmi"]
      sinon [caml_obj_ext; caml_lib_ext] dans

    mydprintf "caml_transitive_closure@ ~caml_obj_ext:%S@ ~pack_mode:%b@ ~used_libraries:%a@ %a"
      caml_obj_ext pack_mode pp_l used_libraries pp_l fns;

    soit packages = fold_packages (fonc name _ -> Resources.add name) Resources.empty dans
    mydprintf "packages:@ %a" Resources.print packages;

    soit caml_obj_ext_of_cmi x =
      si Filename.check_suffix x ".cmi" alors
        Pathname.update_extensions caml_obj_ext x
      sinon x dans

    soit maybe_caml_obj_ext_of_cmi x =
      si pack_mode alors
        si Filename.check_suffix x ".cmi" alors
          soit caml_obj = Pathname.update_extensions caml_obj_ext x dans
          si Resource.exists_in_build_dir caml_obj alors
            caml_obj
          sinon
            x
        sinon
          x
      sinon
        si Filename.check_suffix x ".cmi" alors
          Pathname.update_extensions caml_obj_ext x
        sinon x dans

    soit not_linkable x =
      not (List.exists (Pathname.check_extension x) valid_link_exts) dans

    soit dependency_map =
      fold_dependencies début fonc x y acc ->
        soit x = maybe_caml_obj_ext_of_cmi x
        et y = maybe_caml_obj_ext_of_cmi y dans
        si x = y || not_linkable x || not_linkable y alors acc
        sinon smap_add_set x y acc
      fin SMap.empty dans
    mydprintf "dependency_map:@ %a" print_smap_set dependency_map;

    soit used_files = find_all_rec fns dependency_map dans
    mydprintf "used_files:@ %a" Resources.print used_files;

    soit open_packages =
      Resources.fold début fonc file acc ->
        si Resources.mem file packages && not (List.mem file hidden_packages)
        alors file :: acc sinon acc
      fin used_files [] dans
    mydprintf "open_packages:@ %a" pp_l open_packages;

    soit index_filter ext list x =
      Pathname.check_extension x ext && List.mem x list dans

    soit lib_index =
      paresseux (mkindex fold_libraries (index_filter caml_lib_ext used_libraries)) dans
    mydprintf "lib_index:@ %a" (print_lazy print_smap_list) lib_index;

    soit package_index =
      paresseux (mkindex fold_packages (index_filter caml_obj_ext open_packages)) dans

    soit rec resolve_packages x =
      filtre find_all_list x !*package_index avec
      | [] -> x
      | [x] -> resolve_packages x
      | pkgs ->
          failwith (sbprintf "le fichier %S est inclus dans plus d'un paquet actif (%a)"
                             x pp_l pkgs) dans

    soit libs_of x = find_all_list x !*lib_index dans

    soit lib_of x =
      filtre libs_of x avec
      | [] -> None
      | [lib] -> Some(lib)
      | libs ->
          failwith (sbprintf "le fichier %S est inclus dans plus d'une biliothèque active (%a)"
                             x pp_l libs) dans

    soit convert_dependency src dst acc =
      soit src = resolve_packages src dans
      soit dst = resolve_packages dst dans
      soit add_if_diff x y = si x = y alors acc sinon smap_add_set x y acc dans
      filtre (lib_of src, lib_of dst) avec
      | None, None -> add_if_diff src dst
      | Some(liba), Some(libb) -> add_if_diff liba libb
      | Some(lib), None -> add_if_diff lib dst
      | None, Some(lib) -> add_if_diff src lib dans

    soit dependencies = paresseux début
      SMap.fold début fonc k ->
        Resources.fold (convert_dependency k)
      fin dependency_map empty
    fin dans

    mydprintf "dependencies:@ %a" (print_lazy print_smap_set) dependencies;

    soit dependencies_of x =
      essaie SMap.find x !*dependencies avec Not_found -> Resources.empty dans

    soit needed = ref [] dans
    soit seen = ref [] dans
    soit rec aux fn =
      si sys_file_exists fn && not (List.mem fn !needed) alors début
        si List.mem fn !seen alors raise (Circular_dependencies (!seen, fn));
        seen := fn :: !seen;
        Resources.iter début fonc f ->
          si sys_file_exists f alors
            si Filename.check_suffix f ".cmi" alors
              soit f' = caml_obj_ext_of_cmi f dans
              si f' <> fn alors
                si sys_file_exists f' alors aux f'
                sinon si pack_mode alors aux f sinon ()
              sinon ()
            sinon aux f
        fin (dependencies_of fn);
        needed := fn :: !needed
      fin
    dans
    List.iter aux fns;
    mydprintf "caml_transitive_closure:@ %a ->@ %a" pp_l fns pp_l !needed;
    List.rev !needed

fin
