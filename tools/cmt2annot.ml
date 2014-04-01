(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*                  Fabrice Le Fessant, INRIA Saclay                   *)
(*                                                                     *)
(*  Copyright 2012 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Generate an .annot file from a .cmt file. *)

ouvre Asttypes
ouvre Typedtree

soit bind_variables scope =
  objet
    hérite Tast_iter.iter tel super

    méthode! pattern pat =
      super # pattern pat;
      filtre pat.pat_desc avec
      | Tpat_var (id, _) | Tpat_alias (_, id, _) ->
          Stypes.record (Stypes.An_ident (pat.pat_loc,
                                          Ident.name id,
                                          Annot.Idef scope))
      | _ -> ()
  fin

soit bind_bindings scope bindings =
  soit o = bind_variables scope dans
  List.iter (fonc x -> o # pattern x.vb_pat) bindings

soit bind_cases l =
  List.iter
    (fonc {c_lhs; c_guard; c_rhs} ->
      soit loc =
        soit ouvre Location dans
        filtre c_guard avec
        | None -> c_rhs.exp_loc
        | Some g -> {c_rhs.exp_loc avec loc_start=g.exp_loc.loc_start}
      dans
      (bind_variables loc) # pattern c_lhs) l

soit iterator rebuild_env =
  objet(this)
    val scope = Location.none  (* scope of the surrounding structure *)

    hérite Tast_iter.iter tel super

    méthode! class_expr node =
      Stypes.record (Stypes.Ti_class node);
      super # class_expr node

    méthode! module_expr node =
      Stypes.record (Stypes.Ti_mod node);
      Tast_iter.module_expr {< scope = node.mod_loc >} node

    méthode! expression exp =
      début filtre exp.exp_desc avec
      | Texp_ident (path, _, _) ->
          soit full_name = Path.name ~paren:Oprint.parenthesized_ident path dans
          soit env =
            si rebuild_env alors
              essaie
                Env.env_of_only_summary Envaux.env_from_summary exp.exp_env
              avec Envaux.Error err ->
                Format.eprintf "%a@." Envaux.report_error err;
                exit 2
            sinon
              exp.exp_env
          dans
          soit annot =
            essaie
              soit desc = Env.find_value path env dans
              soit dloc = desc.Types.val_loc dans
              si dloc.Location.loc_ghost alors Annot.Iref_external
              sinon Annot.Iref_internal dloc
            avec Not_found ->
              Annot.Iref_external
          dans
          Stypes.record
            (Stypes.An_ident (exp.exp_loc, full_name , annot))
      | Texp_let (Recursive, bindings, _) ->
          bind_bindings exp.exp_loc bindings
      | Texp_let (Nonrecursive, bindings, body) ->
          bind_bindings body.exp_loc bindings
      | Texp_function (_, f, _)
      | Texp_match (_, f, _)
      | Texp_try (_, f) ->
          bind_cases f
      | _ -> ()
      fin;
      Stypes.record (Stypes.Ti_expr exp);
      super # expression exp

    méthode! pattern pat =
      super # pattern pat;
      Stypes.record (Stypes.Ti_pat pat)

    méthode privée structure_item_rem s rem =
      début filtre s avec
      | {str_desc = Tstr_value (rec_flag, bindings); str_loc = loc} ->
          soit ouvre Location dans
          soit doit loc_start = bind_bindings {scope avec loc_start} bindings dans
          début filtre rec_flag, rem avec
          | Recursive, _ -> doit loc.loc_start
          | Nonrecursive, [] -> doit loc.loc_end
          | Nonrecursive,  {str_loc = loc2} :: _ -> doit loc2.loc_start
          fin
      | _ ->
          ()
      fin;
      Stypes.record_phrase s.str_loc;
      super # structure_item s

    méthode! structure_item s =
      (* This will be used for Partial_structure_item.
         We don't have here the location of the "next" item,
         this will give a slightly different scope for the non-recursive
         binding case. *)
      this # structure_item_rem s []

    méthode! structure l =
      soit rec loop = fonction
        | str :: rem -> this # structure_item_rem str rem; loop rem
        | [] -> ()
      dans
      loop l.str_items

(* TODO: support binding for Tcl_fun, Tcl_let, etc *)
  fin

soit binary_part iter x =
  soit ouvre Cmt_format dans
  filtre x avec
  | Partial_structure x -> iter # structure x
  | Partial_structure_item x -> iter # structure_item x
  | Partial_expression x -> iter # expression x
  | Partial_pattern x -> iter # pattern x
  | Partial_class_expr x -> iter # class_expr x
  | Partial_signature x -> iter # signature x
  | Partial_signature_item x -> iter # signature_item x
  | Partial_module_type x -> iter # module_type x

soit gen_annot target_filename filename
              {Cmt_format.cmt_loadpath; cmt_annots; cmt_use_summaries; _} =
  soit ouvre Cmt_format dans
  Envaux.reset_cache ();
  Config.load_path := cmt_loadpath;
  soit target_filename =
    filtre target_filename avec
    | None -> Some (filename ^ ".annot")
    | Some "-" -> None
    | Some filename -> target_filename
  dans
  soit iterator = iterator cmt_use_summaries dans
  filtre cmt_annots avec
  | Implementation typedtree ->
      iterator # structure typedtree;
      Stypes.dump target_filename
  | Interface _ ->
      Printf.eprintf "Cannot generate annotations for interface file\n%!";
      exit 2
  | Partial_implementation parts ->
      Array.iter (binary_part iterator) parts;
      Stypes.dump target_filename
  | _ ->
      Printf.fprintf stderr "File was generated with an error\n%!";
      exit 2



soit gen_ml target_filename filename cmt =
  soit (printer, ext) =
    filtre cmt.Cmt_format.cmt_annots avec
      | Cmt_format.Implementation typedtree ->
        (fonc ppf -> Pprintast.structure ppf (Untypeast.untype_structure typedtree)), ".ml"
      | Cmt_format.Interface typedtree ->
        (fonc ppf -> Pprintast.signature ppf (Untypeast.untype_signature typedtree)), ".mli"
      | _ ->
        Printf.fprintf stderr "File was generated with an error\n%!";
        exit 2
  dans
  soit target_filename = filtre target_filename avec
      None -> Some (filename ^ ext)
    | Some "-" -> None
    | Some filename -> target_filename
  dans
  soit oc = filtre target_filename avec
      None -> None
    | Some filename -> Some (open_out filename) dans
  soit ppf = filtre oc avec
      None -> Format.std_formatter
    | Some oc -> Format.formatter_of_out_channel oc dans
  printer ppf;
  Format.pp_print_flush ppf ();
  filtre oc avec
      None -> flush stdout
    | Some oc -> close_out oc
