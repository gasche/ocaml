(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Inclusion checks for the module language *)

ouvre Misc
ouvre Path
ouvre Typedtree
ouvre Types

type symptom =
    Missing_field de Ident.t * Location.t * string (* kind *)
  | Value_descriptions de Ident.t * value_description * value_description
  | Type_declarations de Ident.t * type_declaration
        * type_declaration * Includecore.type_mismatch list
  | Exception_declarations de
      Ident.t * exception_declaration * exception_declaration
  | Module_types de module_type * module_type
  | Modtype_infos de Ident.t * modtype_declaration * modtype_declaration
  | Modtype_permutation
  | Interface_mismatch de string * string
  | Class_type_declarations de
      Ident.t * class_type_declaration * class_type_declaration *
      Ctype.class_match_failure list
  | Class_declarations de
      Ident.t * class_declaration * class_declaration *
      Ctype.class_match_failure list
  | Unbound_modtype_path de Path.t
  | Unbound_module_path de Path.t

type pos =
    Module de Ident.t | Modtype de Ident.t | Arg de Ident.t | Body de Ident.t
type error = pos list * Env.t * symptom

exception Error de error list

(* All functions "blah env x1 x2" check that x1 is included in x2,
   i.e. that x1 is the type of an implementation that fulfills the
   specification x2. If not, Error is raised with a backtrace of the error. *)

(* Inclusion between value descriptions *)

soit value_descriptions env cxt subst id vd1 vd2 =
  Cmt_format.record_value_dependency vd1 vd2;
  Env.mark_value_used (Ident.name id) vd1;
  soit vd2 = Subst.value_description subst vd2 dans
  essaie
    Includecore.value_descriptions env vd1 vd2
  avec Includecore.Dont_match ->
    raise(Error[cxt, env, Value_descriptions(id, vd1, vd2)])

(* Inclusion between type declarations *)

soit type_declarations env cxt subst id decl1 decl2 =
  Env.mark_type_used (Ident.name id) decl1;
  soit decl2 = Subst.type_declaration subst decl2 dans
  soit err = Includecore.type_declarations env (Ident.name id) decl1 id decl2 dans
  si err <> [] alors
    raise(Error[cxt, env, Type_declarations(id, decl1, decl2, err)])

(* Inclusion between exception declarations *)

soit exception_declarations env cxt subst id decl1 decl2 =
  Env.mark_exception_used Env.Positive decl1 (Ident.name id);
  soit decl2 = Subst.exception_declaration subst decl2 dans
  si Includecore.exception_declarations env decl1 decl2
  alors ()
  sinon raise(Error[cxt, env, Exception_declarations(id, decl1, decl2)])

(* Inclusion between class declarations *)

soit class_type_declarations env cxt subst id decl1 decl2 =
  soit decl2 = Subst.cltype_declaration subst decl2 dans
  filtre Includeclass.class_type_declarations env decl1 decl2 avec
    []     -> ()
  | reason ->
      raise(Error[cxt, env, Class_type_declarations(id, decl1, decl2, reason)])

soit class_declarations env cxt subst id decl1 decl2 =
  soit decl2 = Subst.class_declaration subst decl2 dans
  filtre Includeclass.class_declarations env decl1 decl2 avec
    []     -> ()
  | reason ->
      raise(Error[cxt, env, Class_declarations(id, decl1, decl2, reason)])

(* Expand a module type identifier when possible *)

exception Dont_match

soit may_expand_module_path env path =
  essaie ignore (Env.find_modtype_expansion path env); vrai
  avec Not_found -> faux

soit expand_module_path env cxt path =
  essaie
    Env.find_modtype_expansion path env
  avec Not_found ->
    raise(Error[cxt, env, Unbound_modtype_path path])

soit expand_module_alias env cxt path =
  essaie (Env.find_module path env).md_type
  avec Not_found ->
    raise(Error[cxt, env, Unbound_module_path path])

(*
let rec normalize_module_path env cxt path =
  match expand_module_alias env cxt path with
    Mty_alias path' -> normalize_module_path env cxt path'
  | _ -> path
*)

(* Extract name, kind and ident from a signature item *)

type field_desc =
    Field_value de string
  | Field_type de string
  | Field_exception de string
  | Field_module de string
  | Field_modtype de string
  | Field_class de string
  | Field_classtype de string

soit kind_of_field_desc = fonction
  | Field_value _ -> "valeur"
  | Field_type _ -> "type"
  | Field_exception _ -> "exception"
  | Field_module _ -> "module"
  | Field_modtype _ -> "type de module"
  | Field_class _ -> "classe"
  | Field_classtype _ -> "type de classe"

soit item_ident_name = fonction
    Sig_value(id, d) -> (id, d.val_loc, Field_value(Ident.name id))
  | Sig_type(id, d, _) -> (id, d.type_loc, Field_type(Ident.name id))
  | Sig_exception(id, d) -> (id, d.exn_loc, Field_exception(Ident.name id))
  | Sig_module(id, d, _) -> (id, d.md_loc, Field_module(Ident.name id))
  | Sig_modtype(id, d) -> (id, d.mtd_loc, Field_modtype(Ident.name id))
  | Sig_class(id, d, _) -> (id, d.cty_loc, Field_class(Ident.name id))
  | Sig_class_type(id, d, _) -> (id, d.clty_loc, Field_classtype(Ident.name id))

soit is_runtime_component = fonction
  | Sig_value(_,{val_kind = Val_prim _})
  | Sig_type(_,_,_)
  | Sig_modtype(_,_)
  | Sig_class_type(_,_,_) -> faux
  | Sig_value(_,_)
  | Sig_exception(_,_)
  | Sig_module(_,_,_)
  | Sig_class(_, _,_) -> vrai

(* Simplify a structure coercion *)

soit simplify_structure_coercion cc id_pos_list =
  soit rec is_identity_coercion pos = fonction
  | [] ->
      vrai
  | (n, c) :: rem ->
      n = pos && c = Tcoerce_none && is_identity_coercion (pos + 1) rem dans
  si is_identity_coercion 0 cc
  alors Tcoerce_none
  sinon Tcoerce_structure (cc, id_pos_list)

(* Inclusion between module types.
   Return the restriction that transforms a value of the smaller type
   into a value of the bigger type. *)

soit rec modtypes env cxt subst mty1 mty2 =
  essaie
    try_modtypes env cxt subst mty1 mty2
  avec
    Dont_match ->
      raise(Error[cxt, env, Module_types(mty1, Subst.modtype subst mty2)])
  | Error reasons tel err ->
      filtre mty1, mty2 avec
        Mty_alias _, _
      | _, Mty_alias _ -> raise err
      | _ ->
          raise(Error((cxt, env, Module_types(mty1, Subst.modtype subst mty2))
                      :: reasons))

et try_modtypes env cxt subst mty1 mty2 =
  filtre (mty1, mty2) avec
    (Mty_alias p1, Mty_alias p2) ->
      si Path.same p1 p2 alors Tcoerce_none sinon
      soit p1 = Env.normalize_path None env p1
      et p2 = Env.normalize_path None env (Subst.module_path subst p2) dans
      (* Should actually be Tcoerce_ignore, if it existed *)
      si Path.same p1 p2 alors Tcoerce_none sinon raise Dont_match
  | (Mty_alias p1, _) ->
      soit p1 = essaie
        Env.normalize_path (Some Location.none) env p1
      avec Env.Error (Env.Missing_module (_, _, path)) ->
        raise (Error[cxt, env, Unbound_module_path path])
      dans
      soit mty1 = Mtype.strengthen env (expand_module_alias env cxt p1) p1 dans
      Tcoerce_alias (p1, modtypes env cxt subst mty1 mty2)
  | (Mty_ident p1, _) quand may_expand_module_path env p1 ->
      try_modtypes env cxt subst (expand_module_path env cxt p1) mty2
  | (_, Mty_ident p2) ->
      try_modtypes2 env cxt mty1 (Subst.modtype subst mty2)
  | (Mty_signature sig1, Mty_signature sig2) ->
      signatures env cxt subst sig1 sig2
  | (Mty_functor(param1, None, res1), Mty_functor(param2, None, res2)) ->
      début filtre modtypes env (Body param1::cxt) subst res1 res2 avec
        Tcoerce_none -> Tcoerce_none
      | cc -> Tcoerce_functor (Tcoerce_none, cc)
      fin
  | (Mty_functor(param1, Some arg1, res1),
     Mty_functor(param2, Some arg2, res2)) ->
      soit arg2' = Subst.modtype subst arg2 dans
      soit cc_arg = modtypes env (Arg param1::cxt) Subst.identity arg2' arg1 dans
      soit cc_res =
        modtypes (Env.add_module param1 arg2' env) (Body param1::cxt)
          (Subst.add_module param2 (Pident param1) subst) res1 res2 dans
      début filtre (cc_arg, cc_res) avec
          (Tcoerce_none, Tcoerce_none) -> Tcoerce_none
        | _ -> Tcoerce_functor(cc_arg, cc_res)
      fin
  | (_, _) ->
      raise Dont_match

et try_modtypes2 env cxt mty1 mty2 =
  (* mty2 is an identifier *)
  filtre (mty1, mty2) avec
    (Mty_ident p1, Mty_ident p2) quand Path.same p1 p2 ->
      Tcoerce_none
  | (_, Mty_ident p2) ->
      try_modtypes env cxt Subst.identity mty1 (expand_module_path env cxt p2)
  | (_, _) ->
      affirme faux

(* Inclusion between signatures *)

et signatures env cxt subst sig1 sig2 =
  (* Environment used to check inclusion of components *)
  soit new_env =
    Env.add_signature sig1 (Env.in_signature env) dans
  (* Keep ids for module aliases *)
  soit (id_pos_list,_) =
    List.fold_left
      (fonc (l,pos) -> fonction
          Sig_module (id, _, _) ->
            ((id,pos,Tcoerce_none)::l , pos+1)
        | item -> (l, si is_runtime_component item alors pos+1 sinon pos))
      ([], 0) sig1 dans
  (* Build a table of the components of sig1, along with their positions.
     The table is indexed by kind and name of component *)
  soit rec build_component_table pos tbl = fonction
      [] -> pos, tbl
    | item :: rem ->
        soit (id, _loc, name) = item_ident_name item dans
        soit nextpos = si is_runtime_component item alors pos + 1 sinon pos dans
        build_component_table nextpos
                              (Tbl.add name (id, item, pos) tbl) rem dans
  soit len1, comps1 =
    build_component_table 0 Tbl.empty sig1 dans
  soit len2 =
    List.fold_left
      (fonc n i -> si is_runtime_component i alors n + 1 sinon n)
      0
      sig2
  dans
  (* Pair each component of sig2 with a component of sig1,
     identifying the names along the way.
     Return a coercion list indicating, for all run-time components
     of sig2, the position of the matching run-time components of sig1
     and the coercion to be applied to it. *)
  soit rec pair_components subst paired unpaired = fonction
      [] ->
        début filtre unpaired avec
            [] ->
              soit cc =
                signature_components new_env cxt subst (List.rev paired)
              dans
              si len1 = len2 alors (* see PR#5098 *)
                simplify_structure_coercion cc id_pos_list
              sinon
                Tcoerce_structure (cc, id_pos_list)
          | _  -> raise(Error unpaired)
        fin
    | item2 :: rem ->
        soit (id2, loc, name2) = item_ident_name item2 dans
        soit name2, report =
          filtre item2, name2 avec
            Sig_type (_, {type_manifest=None}, _), Field_type s
            quand soit l = String.length s dans
            l >= 4 && String.sub s (l-4) 4 = "#row" ->
              (* Do not report in case of failure,
                 as the main type will generate an error *)
              Field_type (String.sub s 0 (String.length s - 4)), faux
          | _ -> name2, vrai
        dans
        début essaie
          soit (id1, item1, pos1) = Tbl.find name2 comps1 dans
          soit new_subst =
            filtre item2 avec
              Sig_type _ ->
                Subst.add_type id2 (Pident id1) subst
            | Sig_module _ ->
                Subst.add_module id2 (Pident id1) subst
            | Sig_modtype _ ->
                Subst.add_modtype id2 (Mty_ident (Pident id1)) subst
            | Sig_value _ | Sig_exception _ | Sig_class _ | Sig_class_type _ ->
                subst
          dans
          pair_components new_subst
            ((item1, item2, pos1) :: paired) unpaired rem
        avec Not_found ->
          soit unpaired =
            si report alors
              (cxt, env, Missing_field (id2, loc, kind_of_field_desc name2)) ::
              unpaired
            sinon unpaired dans
          pair_components subst paired unpaired rem
        fin dans
  (* Do the pairing and checking, and return the final coercion *)
  pair_components subst [] [] sig2

(* Inclusion between signature components *)

et signature_components env cxt subst = fonction
    [] -> []
  | (Sig_value(id1, valdecl1), Sig_value(id2, valdecl2), pos) :: rem ->
      soit cc = value_descriptions env cxt subst id1 valdecl1 valdecl2 dans
      début filtre valdecl2.val_kind avec
        Val_prim p -> signature_components env cxt subst rem
      | _ -> (pos, cc) :: signature_components env cxt subst rem
      fin
  | (Sig_type(id1, tydecl1, _), Sig_type(id2, tydecl2, _), pos) :: rem ->
      type_declarations env cxt subst id1 tydecl1 tydecl2;
      signature_components env cxt subst rem
  | (Sig_exception(id1, excdecl1), Sig_exception(id2, excdecl2), pos)
    :: rem ->
      exception_declarations env cxt subst id1 excdecl1 excdecl2;
      (pos, Tcoerce_none) :: signature_components env cxt subst rem
  | (Sig_module(id1, mty1, _), Sig_module(id2, mty2, _), pos) :: rem ->
      soit cc =
        modtypes env (Module id1::cxt) subst
          (Mtype.strengthen env mty1.md_type (Pident id1)) mty2.md_type dans
      (pos, cc) :: signature_components env cxt subst rem
  | (Sig_modtype(id1, info1), Sig_modtype(id2, info2), pos) :: rem ->
      modtype_infos env cxt subst id1 info1 info2;
      signature_components env cxt subst rem
  | (Sig_class(id1, decl1, _), Sig_class(id2, decl2, _), pos) :: rem ->
      class_declarations env cxt subst id1 decl1 decl2;
      (pos, Tcoerce_none) :: signature_components env cxt subst rem
  | (Sig_class_type(id1, info1, _),
     Sig_class_type(id2, info2, _), pos) :: rem ->
      class_type_declarations env cxt subst id1 info1 info2;
      signature_components env cxt subst rem
  | _ ->
      affirme faux

(* Inclusion between module type specifications *)

et modtype_infos env cxt subst id info1 info2 =
  soit info2 = Subst.modtype_declaration subst info2 dans
  soit cxt' = Modtype id :: cxt dans
  essaie
    filtre (info1.mtd_type, info2.mtd_type) avec
      (None, None) -> ()
    | (Some mty1, None) -> ()
    | (Some mty1, Some mty2) ->
        check_modtype_equiv env cxt' mty1 mty2
    | (None, Some mty2) ->
        check_modtype_equiv env cxt' (Mty_ident(Pident id)) mty2
  avec Error reasons ->
    raise(Error((cxt, env, Modtype_infos(id, info1, info2)) :: reasons))

et check_modtype_equiv env cxt mty1 mty2 =
  filtre
    (modtypes env cxt Subst.identity mty1 mty2,
     modtypes env cxt Subst.identity mty2 mty1)
  avec
    (Tcoerce_none, Tcoerce_none) -> ()
  | (_, _) -> raise(Error [cxt, env, Modtype_permutation])

(* Simplified inclusion check between module types (for Env) *)

soit check_modtype_inclusion env mty1 path1 mty2 =
  essaie
    ignore(modtypes env [] Subst.identity
                    (Mtype.strengthen env mty1 path1) mty2)
  avec Error reasons ->
    raise Not_found

soit _ = Env.check_modtype_inclusion := check_modtype_inclusion

(* Check that an implementation of a compilation unit meets its
   interface. *)

soit compunit impl_name impl_sig intf_name intf_sig =
  essaie
    signatures Env.initial [] Subst.identity impl_sig intf_sig
  avec Error reasons ->
    raise(Error(([], Env.empty,Interface_mismatch(impl_name, intf_name))
                :: reasons))

(* Hide the context and substitution parameters to the outside world *)

soit modtypes env mty1 mty2 = modtypes env [] Subst.identity mty1 mty2
soit signatures env sig1 sig2 = signatures env [] Subst.identity sig1 sig2
soit type_declarations env id decl1 decl2 =
  type_declarations env [] Subst.identity id decl1 decl2

(* Error report *)

ouvre Format
ouvre Printtyp

soit show_loc msg ppf loc =
  soit pos = loc.Location.loc_start dans
  si List.mem pos.Lexing.pos_fname [""; "_none_"; "//toplevel//"] alors ()
  sinon fprintf ppf "@\n@[<2>%a:@ %s@]" Location.print_loc loc msg

soit show_locs ppf (loc1, loc2) =
  show_loc "Déclaration attendue" ppf loc2;
  show_loc "Déclaration effective" ppf loc1

soit include_err ppf = fonction
  | Missing_field (id, loc, kind) ->
      fprintf ppf "Le %s `%a' est requis mais pas fourni" kind ident id;
      show_loc "Déclaration attendue" ppf loc
  | Value_descriptions(id, d1, d2) ->
      fprintf ppf
        "@[<hv 2>Les valeurs ne correspondent pas :@ %a@;<1 -2>n'est pas incluse dans@ %a@]"
        (value_description id) d1 (value_description id) d2;
      show_locs ppf (d1.val_loc, d2.val_loc);
  | Type_declarations(id, d1, d2, errs) ->
      fprintf ppf "@[<v>@[<hv>%s:@;<1 2>%a@ %s@;<1 2>%a@]%a%a@]"
        "Les déclaration de type ne correspondent pas"
        (type_declaration id) d1
        "n'est pas inclus dans"
        (type_declaration id) d2
        show_locs (d1.type_loc, d2.type_loc)
        (Includecore.report_type_mismatch
           "la première déclaration" "la seconde déclaration") errs
  | Exception_declarations(id, d1, d2) ->
      fprintf ppf
       "@[<hv 2>Les déclarations d'exception ne correspondent pas:@ \
        %a@;<1 -2>is not included in@ %a@]"
        (exception_declaration id) d1
        (exception_declaration id) d2;
      show_locs ppf (d1.exn_loc, d2.exn_loc)
  | Module_types(mty1, mty2)->
      fprintf ppf
       "@[<hv 2>Les modules ne correspondent pas : @ \
        %a@;<1 -2>n'est pas inclus dans@ %a@]"
      modtype mty1
      modtype mty2
  | Modtype_infos(id, d1, d2) ->
      fprintf ppf
       "@[<hv 2>Les déclarations de type de module ne correspondent pas :@ \
        %a@;<1 -2>ne correspond pas à@ %a@]"
      (modtype_declaration id) d1
      (modtype_declaration id) d2
  | Modtype_permutation ->
      fprintf ppf "Permutation illégale des champs d'une structure"
  | Interface_mismatch(impl_name, intf_name) ->
      fprintf ppf "@[L'implémentation %s@ ne correspond pas à l'interface %s:"
       impl_name intf_name
  | Class_type_declarations(id, d1, d2, reason) ->
      fprintf ppf
       "@[<hv 2>Les déclarations de type de classe ne correspondent pas :@ \
        %a@;<1 -2>ne correspond pas à@ %a@]@ %a"
      (Printtyp.cltype_declaration id) d1
      (Printtyp.cltype_declaration id) d2
      Includeclass.report_error reason
  | Class_declarations(id, d1, d2, reason) ->
      fprintf ppf
       "@[<hv 2>Les déclarations de classes ne correspondent pas :@ \
        %a@;<1 -2>ne correspond pas à@ %a@]@ %a"
      (Printtyp.class_declaration id) d1
      (Printtyp.class_declaration id) d2
      Includeclass.report_error reason
  | Unbound_modtype_path path ->
      fprintf ppf "Type de module non lié %a" Printtyp.path path
  | Unbound_module_path path ->
      fprintf ppf "Module non lié %a" Printtyp.path path

soit rec context ppf = fonction
    Module id :: rem ->
      fprintf ppf "@[<2>module %a%a@]" ident id args rem
  | Modtype id :: rem ->
      fprintf ppf "@[<2>module type %a =@ %a@]" ident id context_mty rem
  | Body x :: rem ->
      fprintf ppf "foncteur (%a) ->@ %a" ident x context_mty rem
  | Arg x :: rem ->
      fprintf ppf "foncteur (%a : %a) -> ..." ident x context_mty rem
  | [] ->
      fprintf ppf "<ici>"
et context_mty ppf = fonction
    (Module _ | Modtype _) :: _ tel rem ->
      fprintf ppf "@[<2>sig@ %a@;<1 -2>fin@]" context rem
  | cxt -> context ppf cxt
et args ppf = fonction
    Body x :: rem ->
      fprintf ppf "(%a)%a" ident x args rem
  | Arg x :: rem ->
      fprintf ppf "(%a :@ %a) : ..." ident x context_mty rem
  | cxt ->
      fprintf ppf " :@ %a" context_mty cxt

soit path_of_context = fonction
    Module id :: rem ->
      soit rec subm path = fonction
          [] -> path
        | Module id :: rem -> subm (Pdot (path, Ident.name id, -1)) rem
        | _ -> affirme faux
      dans subm (Pident id) rem
  | _ -> affirme faux

soit context ppf cxt =
  si cxt = [] alors () sinon
  si List.for_all (fonction Module _ -> vrai | _ -> faux) cxt alors
    fprintf ppf "Dans le module %a:@ " path (path_of_context cxt)
  sinon
    fprintf ppf "@[<hv 2>À la position@ %a@]@ " context cxt

soit include_err ppf (cxt, env, err) =
  Printtyp.wrap_printing_env env (fonc () ->
    fprintf ppf "@[<v>%a%a@]" context (List.rev cxt) include_err err)

soit buffer = ref ""
soit is_big obj =
  soit size = !Clflags.error_size dans
  size > 0 &&
  début
    si String.length !buffer < size alors buffer := String.create size;
    essaie ignore (Marshal.to_buffer !buffer 0 size obj []); faux
    avec _ -> vrai
  fin

soit report_error ppf errs =
  si errs = [] alors () sinon
  soit (errs , err) = split_last errs dans
  soit pe = ref vrai dans
  soit include_err' ppf (_,_,obj tel err) =
    si not (is_big obj) alors fprintf ppf "%a@ " include_err err
    sinon si !pe alors (fprintf ppf "...@ "; pe := faux)
  dans
  soit print_errs ppf = List.iter (include_err' ppf) dans
  fprintf ppf "@[<v>%a%a@]" print_errs errs include_err err


(* We could do a better job to split the individual error items
   as sub-messages of the main interface mismatch on the whole unit. *)
soit () =
  Location.register_error_of_exn
    (fonction
      | Error err -> Some (Location.error_of_printer_file report_error err)
      | _ -> None
    )

