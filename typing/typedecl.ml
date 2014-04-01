(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(* Xavier Leroy and Jerome Vouillon, projet Cristal, INRIA Rocquencourt*)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(**** Typing of type definitions ****)

ouvre Misc
ouvre Asttypes
ouvre Parsetree
ouvre Primitive
ouvre Types
ouvre Typetexp

type error =
    Repeated_parameter
  | Duplicate_constructor de string
  | Too_many_constructors
  | Duplicate_label de string
  | Recursive_abbrev de string
  | Definition_mismatch de type_expr * Includecore.type_mismatch list
  | Constraint_failed de type_expr * type_expr
  | Inconsistent_constraint de Env.t * (type_expr * type_expr) list
  | Type_clash de Env.t * (type_expr * type_expr) list
  | Parameters_differ de Path.t * type_expr * type_expr
  | Null_arity_external
  | Missing_native_external
  | Unbound_type_var de type_expr * type_declaration
  | Unbound_exception de Longident.t
  | Not_an_exception de Longident.t
  | Bad_variance de int * (bool * bool * bool) * (bool * bool * bool)
  | Unavailable_type_constructor de Path.t
  | Bad_fixed_type de string
  | Unbound_type_var_exc de type_expr * type_expr
  | Varying_anonymous
  | Exception_constructor_with_result

ouvre Typedtree

exception Error de Location.t * error

(* Enter all declared types in the environment as abstract types *)

soit enter_type env sdecl id =
  soit decl =
    { type_params =
        List.map (fonc _ -> Btype.newgenvar ()) sdecl.ptype_params;
      type_arity = List.length sdecl.ptype_params;
      type_kind = Type_abstract;
      type_private = sdecl.ptype_private;
      type_manifest =
        début filtre sdecl.ptype_manifest avec None -> None
        | Some _ -> Some(Ctype.newvar ()) fin;
      type_variance = List.map (fonc _ -> Variance.full) sdecl.ptype_params;
      type_newtype_level = None;
      type_loc = sdecl.ptype_loc;
      type_attributes = sdecl.ptype_attributes;
    }
  dans
  Env.add_type ~check:vrai id decl env

soit update_type temp_env env id loc =
  soit path = Path.Pident id dans
  soit decl = Env.find_type path temp_env dans
  filtre decl.type_manifest avec None -> ()
  | Some ty ->
      soit params = List.map (fonc _ -> Ctype.newvar ()) decl.type_params dans
      essaie Ctype.unify env (Ctype.newconstr path params) ty
      avec Ctype.Unify trace ->
        raise (Error(loc, Type_clash (env, trace)))

(* Determine if a type is (an abbreviation for) the type "float" *)
(* We use the Ctype.expand_head_opt version of expand_head to get access
   to the manifest type of private abbreviations. *)
soit is_float env ty =
  filtre Ctype.repr (Ctype.expand_head_opt env ty) avec
    {desc = Tconstr(p, _, _)} -> Path.same p Predef.path_float
  | _ -> faux

(* Determine if a type definition defines a fixed type. (PW) *)
soit is_fixed_type sd =
  soit rec has_row_var sty =
    filtre sty.ptyp_desc avec
      Ptyp_alias (sty, _) -> has_row_var sty
    | Ptyp_class _
    | Ptyp_object (_, Open)
    | Ptyp_variant (_, Open, _)
    | Ptyp_variant (_, Closed, Some _) -> vrai
    | _ -> faux
  dans
  filtre sd.ptype_manifest avec
    None -> faux
  | Some sty ->
      sd.ptype_kind = Ptype_abstract &&
      sd.ptype_private = Private &&
      has_row_var sty

(* Set the row variable in a fixed type *)
soit set_fixed_row env loc p decl =
  soit tm =
    filtre decl.type_manifest avec
      None -> affirme faux
    | Some t -> Ctype.expand_head env t
  dans
  soit rv =
    filtre tm.desc avec
      Tvariant row ->
        soit row = Btype.row_repr row dans
        tm.desc <- Tvariant {row avec row_fixed = vrai};
        si Btype.static_row row alors Btype.newgenty Tnil
        sinon row.row_more
    | Tobject (ty, _) ->
        snd (Ctype.flatten_fields ty)
    | _ ->
        raise (Error (loc, Bad_fixed_type "n'est pas un objet ou variant"))
  dans
  si not (Btype.is_Tvar rv) alors
    raise (Error (loc, Bad_fixed_type "n'a pas de variable de rangée"));
  rv.desc <- Tconstr (p, decl.type_params, ref Mnil)

(* Translate one type declaration *)

module StringSet =
  Set.Make(struct
    type t = string
    soit compare (x:t) y = compare x y
  fin)

soit make_params sdecl =
  essaie
    List.map
      (fonc (x, _) ->
        filtre x avec
        | None -> Ctype.new_global_var ~name:"_" ()
        | Some x -> enter_type_variable x)
      sdecl.ptype_params
  avec Already_bound loc ->
    raise(Error(loc, Repeated_parameter))

soit transl_declaration env sdecl id =
  (* Bind type parameters *)
  reset_type_variables();
  Ctype.begin_def ();
  soit params = make_params sdecl dans
  soit cstrs = List.map
    (fonc (sty, sty', loc) ->
      transl_simple_type env faux sty,
      transl_simple_type env faux sty', loc)
    sdecl.ptype_cstrs
  dans
  soit (tkind, kind) =
    filtre sdecl.ptype_kind avec
        Ptype_abstract -> Ttype_abstract, Type_abstract
      | Ptype_variant cstrs ->
        soit all_constrs = ref StringSet.empty dans
        List.iter
          (fonc {pcd_name = {txt = name}} ->
            si StringSet.mem name !all_constrs alors
              raise(Error(sdecl.ptype_loc, Duplicate_constructor name));
            all_constrs := StringSet.add name !all_constrs)
          cstrs;
        si List.length
          (List.filter (fonc cd -> cd.pcd_args <> []) cstrs)
          > (Config.max_tag + 1) alors
          raise(Error(sdecl.ptype_loc, Too_many_constructors));
        soit make_cstr {pcd_name = lid; pcd_args = args; pcd_res = ret_type; pcd_loc = loc; pcd_attributes = attrs} =
          soit name = Ident.create lid.txt dans
          filtre ret_type avec
            | None ->
              (name, lid, List.map (transl_simple_type env vrai) args,
               None, None, loc, attrs)
            | Some sty ->
              (* if it's a generalized constructor we must first narrow and
                 then widen so as to not introduce any new constraints *)
              soit z = narrow () dans
              reset_type_variables ();
              soit args = List.map (transl_simple_type env faux) args dans
              soit cty = transl_simple_type env faux sty dans
              soit ret_type =
                soit ty = cty.ctyp_type dans
                soit p = Path.Pident id dans
                filtre (Ctype.repr ty).desc avec
                  Tconstr (p', _, _) quand Path.same p p' -> ty
                | _ ->
                    raise (Error (sty.ptyp_loc, Constraint_failed
                                    (ty, Ctype.newconstr p params)))
              dans
              widen z;
              (name, lid, args, Some cty, Some ret_type, loc, attrs)
        dans
        soit cstrs = List.map make_cstr cstrs dans
        Ttype_variant (List.map (fonc (name, lid, ctys, res, _, loc, attrs) ->
          {cd_id = name; cd_name = lid; cd_args = ctys; cd_res = res;
           cd_loc = loc; cd_attributes = attrs}
        ) cstrs),
        Type_variant (List.map (fonc (name, name_loc, ctys, _, option, loc, attrs) ->
            {Types.cd_id = name; cd_args = List.map (fonc cty -> cty.ctyp_type) ctys;
             cd_res = option;
             cd_loc = loc; cd_attributes = attrs}
          ) cstrs)

      | Ptype_record lbls ->
        soit all_labels = ref StringSet.empty dans
        List.iter
          (fonc {pld_name = {txt=name}} ->
            si StringSet.mem name !all_labels alors
              raise(Error(sdecl.ptype_loc, Duplicate_label name));
            all_labels := StringSet.add name !all_labels)
          lbls;
        soit lbls = List.map (fonc {pld_name=name;pld_mutable=mut;pld_type=arg;pld_loc=loc;pld_attributes=attrs} ->
          soit arg = Ast_helper.Typ.force_poly arg dans
          soit cty = transl_simple_type env vrai arg dans
          {ld_id = Ident.create name.txt; ld_name = name; ld_mutable = mut; ld_type = cty;
           ld_loc = loc; ld_attributes = attrs}
          ) lbls dans
        soit lbls' =
          List.map
            (fonc ld ->
              soit ty = ld.ld_type.ctyp_type dans
              soit ty = filtre ty.desc avec Tpoly(t,[]) -> t | _ -> ty dans
              {Types.ld_id = ld.ld_id;
               ld_mutable = ld.ld_mutable;
               ld_type = ty;
               ld_loc = ld.ld_loc;
               ld_attributes = ld.ld_attributes
              }
            )
            lbls dans
        soit rep =
          si List.for_all (fonc l -> is_float env l.Types.ld_type) lbls'
          alors Record_float
          sinon Record_regular dans
        Ttype_record lbls, Type_record(lbls', rep)
      dans
    soit (tman, man) = filtre sdecl.ptype_manifest avec
        None -> None, None
      | Some sty ->
        soit no_row = not (is_fixed_type sdecl) dans
        soit cty = transl_simple_type env no_row sty dans
        Some cty, Some cty.ctyp_type
    dans
    soit decl =
      { type_params = params;
        type_arity = List.length params;
        type_kind = kind;
        type_private = sdecl.ptype_private;
        type_manifest = man;
        type_variance = List.map (fonc _ -> Variance.full) params;
        type_newtype_level = None;
        type_loc = sdecl.ptype_loc;
        type_attributes = sdecl.ptype_attributes;
      } dans

  (* Check constraints *)
    List.iter
      (fonc (cty, cty', loc) ->
        soit ty = cty.ctyp_type dans
        soit ty' = cty'.ctyp_type dans
        essaie Ctype.unify env ty ty' avec Ctype.Unify tr ->
          raise(Error(loc, Inconsistent_constraint (env, tr))))
      cstrs;
    Ctype.end_def ();
  (* Add abstract row *)
    si is_fixed_type sdecl alors début
      soit (p, _) =
        essaie Env.lookup_type (Longident.Lident(Ident.name id ^ "#row")) env
        avec Not_found -> affirme faux dans
      set_fixed_row env sdecl.ptype_loc p decl
    fin;
  (* Check for cyclic abbreviations *)
    début filtre decl.type_manifest avec None -> ()
      | Some ty ->
        si Ctype.cyclic_abbrev env id ty alors
          raise(Error(sdecl.ptype_loc, Recursive_abbrev sdecl.ptype_name.txt));
    fin;
    {
      typ_id = id;
      typ_name = sdecl.ptype_name;
      typ_params = sdecl.ptype_params;
      typ_type = decl;
      typ_cstrs = cstrs;
      typ_loc = sdecl.ptype_loc;
      typ_manifest = tman;
      typ_kind = tkind;
      typ_private = sdecl.ptype_private;
      typ_attributes = sdecl.ptype_attributes;
    }

(* Generalize a type declaration *)

soit generalize_decl decl =
  List.iter Ctype.generalize decl.type_params;
  début filtre decl.type_kind avec
    Type_abstract ->
      ()
  | Type_variant v ->
      List.iter
        (fonc c ->
          List.iter Ctype.generalize c.Types.cd_args;
          may Ctype.generalize c.Types.cd_res)
        v
  | Type_record(r, rep) ->
      List.iter (fonc l -> Ctype.generalize l.Types.ld_type) r
  fin;
  début filtre decl.type_manifest avec
  | None    -> ()
  | Some ty -> Ctype.generalize ty
  fin

(* Check that all constraints are enforced *)

module TypeSet = Btype.TypeSet

soit rec check_constraints_rec env loc visited ty =
  soit ty = Ctype.repr ty dans
  si TypeSet.mem ty !visited alors () sinon début
  visited := TypeSet.add ty !visited;
  filtre ty.desc avec
  | Tconstr (path, args, _) ->
      soit args' = List.map (fonc _ -> Ctype.newvar ()) args dans
      soit ty' = Ctype.newconstr path args' dans
      début essaie Ctype.enforce_constraints env ty'
      avec Ctype.Unify _ -> affirme faux
      | Not_found -> raise (Error(loc, Unavailable_type_constructor path))
      fin;
      si not (Ctype.matches env ty ty') alors
        raise (Error(loc, Constraint_failed (ty, ty')));
      List.iter (check_constraints_rec env loc visited) args
  | Tpoly (ty, tl) ->
      soit _, ty = Ctype.instance_poly faux tl ty dans
      check_constraints_rec env loc visited ty
  | _ ->
      Btype.iter_type_expr (check_constraints_rec env loc visited) ty
  fin

module SMap = Map.Make(String)

soit check_constraints env sdecl (_, decl) =
  soit visited = ref TypeSet.empty dans
  début filtre decl.type_kind avec
  | Type_abstract -> ()
  | Type_variant l ->
      soit find_pl = fonction
          Ptype_variant pl -> pl
        | Ptype_record _ | Ptype_abstract -> affirme faux
      dans
      soit pl = find_pl sdecl.ptype_kind dans
      soit pl_index =
        soit foldf acc x =
          SMap.add x.pcd_name.txt x acc
        dans
        List.fold_left foldf SMap.empty pl
      dans
      List.iter
        (fonc {Types.cd_id=name; cd_args=tyl; cd_res=ret_type} ->
          soit {pcd_args = styl; pcd_res = sret_type; _} =
            essaie SMap.find (Ident.name name) pl_index
            avec Not_found -> affirme faux dans
          List.iter2
            (fonc sty ty ->
              check_constraints_rec env sty.ptyp_loc visited ty)
            styl tyl;
          filtre sret_type, ret_type avec
          | Some sr, Some r ->
              check_constraints_rec env sr.ptyp_loc visited r
          | _ ->
              () )
        l
  | Type_record (l, _) ->
      soit find_pl = fonction
          Ptype_record pl -> pl
        | Ptype_variant _ | Ptype_abstract -> affirme faux
      dans
      soit pl = find_pl sdecl.ptype_kind dans
      soit rec get_loc name = fonction
          [] -> affirme faux
        | pld :: tl ->
            si name = pld.pld_name.txt alors pld.pld_type.ptyp_loc sinon get_loc name tl
      dans
      List.iter
        (fonc {Types.ld_id=name; ld_type=ty} ->
          check_constraints_rec env (get_loc (Ident.name name) pl) visited ty)
        l
  fin;
  début filtre decl.type_manifest avec
  | None -> ()
  | Some ty ->
      soit sty =
        filtre sdecl.ptype_manifest avec Some sty -> sty | _ -> affirme faux
      dans
      check_constraints_rec env sty.ptyp_loc visited ty
  fin

(*
   If both a variant/record definition and a type equation are given,
   need to check that the equation refers to a type of the same kind
   with the same constructors and labels.
*)
soit check_coherence env loc id decl =
  filtre decl avec
    {type_kind = (Type_variant _ | Type_record _); type_manifest = Some ty} ->
      début filtre (Ctype.repr ty).desc avec
        Tconstr(path, args, _) ->
          début essaie
            soit decl' = Env.find_type path env dans
            soit err =
              si List.length args <> List.length decl.type_params
              alors [Includecore.Arity]
              sinon si not (Ctype.equal env faux args decl.type_params)
              alors [Includecore.Constraint]
              sinon
                Includecore.type_declarations ~equality:vrai env
                  (Path.last path)
                  decl'
                  id
                  (Subst.type_declaration
                     (Subst.add_type id path Subst.identity) decl)
            dans
            si err <> [] alors
              raise(Error(loc, Definition_mismatch (ty, err)))
          avec Not_found ->
            raise(Error(loc, Unavailable_type_constructor path))
          fin
      | _ -> raise(Error(loc, Definition_mismatch (ty, [])))
      fin
  | _ -> ()

soit check_abbrev env sdecl (id, decl) =
  check_coherence env sdecl.ptype_loc id decl

(* Check that recursion is well-founded *)

soit check_well_founded env loc path decl =
  Misc.may
    (fonc body ->
      essaie Ctype.correct_abbrev env path decl.type_params body avec
      | Ctype.Recursive_abbrev ->
          raise(Error(loc, Recursive_abbrev (Path.name path)))
      | Ctype.Unify trace -> raise(Error(loc, Type_clash (env, trace))))
    decl.type_manifest

(* Check for ill-defined abbrevs *)

soit check_recursion env loc path decl to_check =
  (* to_check is true for potentially mutually recursive paths.
     (path, decl) is the type declaration to be checked. *)

  si decl.type_params = [] alors () sinon

  soit visited = ref [] dans

  soit rec check_regular cpath args prev_exp ty =
    soit ty = Ctype.repr ty dans
    si not (List.memq ty !visited) alors début
      visited := ty :: !visited;
      filtre ty.desc avec
      | Tconstr(path', args', _) ->
          si Path.same path path' alors début
            si not (Ctype.equal env faux args args') alors
              raise (Error(loc,
                     Parameters_differ(cpath, ty, Ctype.newconstr path args)))
          fin
          (* Attempt to expand a type abbreviation if:
              1- [to_check path'] holds
                 (otherwise the expansion cannot involve [path]);
              2- we haven't expanded this type constructor before
                 (otherwise we could loop if [path'] is itself
                 a non-regular abbreviation). *)
          sinon si to_check path' && not (List.mem path' prev_exp) alors début
            essaie
              (* Attempt expansion *)
              soit (params0, body0, _) = Env.find_type_expansion path' env dans
              soit (params, body) =
                Ctype.instance_parameterized_type params0 body0 dans
              début
                essaie List.iter2 (Ctype.unify env) params args'
                avec Ctype.Unify _ ->
                  raise (Error(loc, Constraint_failed
                                 (ty, Ctype.newconstr path' params0)));
              fin;
              check_regular path' args (path' :: prev_exp) body
            avec Not_found -> ()
          fin;
          List.iter (check_regular cpath args prev_exp) args'
      | Tpoly (ty, tl) ->
          soit (_, ty) = Ctype.instance_poly ~keep_names:vrai faux tl ty dans
          check_regular cpath args prev_exp ty
      | _ ->
          Btype.iter_type_expr (check_regular cpath args prev_exp) ty
    fin dans

  Misc.may
    (fonc body ->
      soit (args, body) =
        Ctype.instance_parameterized_type
          ~keep_names:vrai decl.type_params body dans
      check_regular path args [] body)
    decl.type_manifest

soit check_abbrev_recursion env id_loc_list tdecl =
  soit decl = tdecl.typ_type dans
  soit id = tdecl.typ_id dans
  check_recursion env (List.assoc id id_loc_list) (Path.Pident id) decl
    (fonction Path.Pident id -> List.mem_assoc id id_loc_list | _ -> faux)

(* Compute variance *)

module TypeMap = Btype.TypeMap

soit get_variance ty visited =
  essaie TypeMap.find ty !visited avec Not_found -> Variance.null

soit compute_variance env visited vari ty =
  soit rec compute_variance_rec vari ty =
    (* Format.eprintf "%a: %x@." Printtyp.type_expr ty (Obj.magic vari); *)
    soit ty = Ctype.repr ty dans
    soit vari' = get_variance ty visited dans
    si Variance.subset vari vari' alors () sinon
    soit vari = Variance.union vari vari' dans
    visited := TypeMap.add ty vari !visited;
    soit compute_same = compute_variance_rec vari dans
    filtre ty.desc avec
      Tarrow (_, ty1, ty2, _) ->
        soit ouvre Variance dans
        soit v = conjugate vari dans
        soit v1 =
          si mem May_pos v || mem May_neg v
          alors set May_weak vrai v sinon v
        dans
        compute_variance_rec v1 ty1;
        compute_same ty2
    | Ttuple tl ->
        List.iter compute_same tl
    | Tconstr (path, tl, _) ->
        soit ouvre Variance dans
        si tl = [] alors () sinon début
          essaie
            soit decl = Env.find_type path env dans
            soit cvari f = mem f vari dans
            List.iter2
              (fonc ty v ->
                soit cv f = mem f v dans
                soit strict =
                  cvari Inv && cv Inj || (cvari Pos || cvari Neg) && cv Inv
                dans
                si strict alors compute_variance_rec full ty sinon
                soit p1 = inter v vari
                et n1 = inter v (conjugate vari) dans
                soit v1 =
                  union (inter covariant (union p1 (conjugate p1)))
                    (inter (conjugate covariant) (union n1 (conjugate n1)))
                et weak =
                  cvari May_weak && (cv May_pos || cv May_neg) ||
                  (cvari May_pos || cvari May_neg) && cv May_weak
                dans
                soit v2 = set May_weak weak v1 dans
                compute_variance_rec v2 ty)
              tl decl.type_variance
          avec Not_found ->
            List.iter (compute_variance_rec may_inv) tl
        fin
    | Tobject (ty, _) ->
        compute_same ty
    | Tfield (_, _, ty1, ty2) ->
        compute_same ty1;
        compute_same ty2
    | Tsubst ty ->
        compute_same ty
    | Tvariant row ->
        soit row = Btype.row_repr row dans
        List.iter
          (fonc (_,f) ->
            filtre Btype.row_field_repr f avec
              Rpresent (Some ty) ->
                compute_same ty
            | Reither (_, tyl, _, _) ->
                soit ouvre Variance dans
                soit upper =
                  List.fold_left (fonc s f -> set f vrai s)
                    null [May_pos; May_neg; May_weak]
                dans
                soit v = inter vari upper dans
                List.iter (compute_variance_rec v) tyl
            | _ -> ())
          row.row_fields;
        compute_same row.row_more
    | Tpoly (ty, _) ->
        compute_same ty
    | Tvar _ | Tnil | Tlink _ | Tunivar _ -> ()
    | Tpackage (_, _, tyl) ->
        soit v =
          Variance.(si mem Pos vari || mem Neg vari alors full sinon may_inv)
        dans
        List.iter (compute_variance_rec v) tyl
  dans
  compute_variance_rec vari ty

soit make_variance ty = (ty, ref Variance.null)

soit make p n i =
  soit ouvre Variance dans
  set May_pos p (set May_neg n (set May_weak n (set Inj i null)))

soit flags (v, i) =
  soit (c, n) =
    filtre v avec
    | Covariant -> (vrai, faux)
    | Contravariant -> (faux, vrai)
    | Invariant -> (vrai, vrai)
  dans
  (c, n, i)

soit compute_variance_type env check (required, loc) decl tyl =
  (* Requirements *)
  soit required =
    List.map (fonc (c,n,i) -> si c || n alors (c,n,i) sinon (vrai,vrai,i))
      required
  dans
  (* Prepare *)
  soit params = List.map Btype.repr decl.type_params dans
  soit tvl = ref TypeMap.empty dans
  (* Compute occurences in body *)
  soit ouvre Variance dans
  List.iter
    (fonc (cn,ty) ->
      compute_variance env tvl (si cn alors full sinon covariant) ty)
    tyl;
  si check alors début
    (* Check variance of parameters *)
    soit pos = ref 0 dans
    List.iter2
      (fonc ty (c, n, i) ->
        incr pos;
        soit var = get_variance ty tvl dans
        soit (co,cn) = get_upper var et ij = mem Inj var dans
        si Btype.is_Tvar ty && (co && not c || cn && not n || not ij && i)
        alors raise (Error(loc, Bad_variance (!pos, (co,cn,ij), (c,n,i)))))
      params required;
    (* Check propagation from constrained parameters *)
    soit args = Btype.newgenty (Ttuple params) dans
    soit fvl = Ctype.free_variables args dans
    soit fvl = List.filter (fonc v -> not (List.memq v params)) fvl dans
    (* If there are no extra variables there is nothing to do *)
    si fvl = [] alors () sinon
    soit tvl2 = ref TypeMap.empty dans
    List.iter2
      (fonc ty (p,n,i) ->
        si Btype.is_Tvar ty alors () sinon
        soit v =
          si p alors si n alors full sinon covariant sinon conjugate covariant dans
        compute_variance env tvl2 v ty)
      params required;
    soit visited = ref TypeSet.empty dans
    soit rec check ty =
      soit ty = Ctype.repr ty dans
      si TypeSet.mem ty !visited alors () sinon
      soit visited' = TypeSet.add ty !visited dans
      visited := visited';
      soit v1 = get_variance ty tvl dans
      soit snap = Btype.snapshot () dans
      soit v2 =
        TypeMap.fold
          (fonc t vt v ->
            si Ctype.equal env faux [ty] [t] alors union vt v sinon v)
          !tvl2 null dans
      Btype.backtrack snap;
      soit (c1,n1) = get_upper v1 et (c2,n2,_,i2) = get_lower v2 dans
      si c1 && not c2 || n1 && not n2 alors
        si List.memq ty fvl alors
          soit code = si not i2 alors -2 sinon si c2 || n2 alors -1 sinon -3 dans
          raise (Error (loc, Bad_variance (code, (c1,n1,faux), (c2,n2,faux))))
        sinon
          Btype.iter_type_expr check ty
    dans
    List.iter (fonc (_,ty) -> check ty) tyl;
  fin;
  List.map2
    (fonc ty (p, n, i) ->
      soit v = get_variance ty tvl dans
      soit tr = decl.type_private dans
      (* Use required variance where relevant *)
      soit concr = decl.type_kind <> Type_abstract (*|| tr = Type_new*) dans
      soit (p, n) =
        si tr = Private || not (Btype.is_Tvar ty) alors (p, n) (* set *)
        sinon (faux, faux) (* only check *)
      et i = concr  || i && tr = Private dans
      soit v = union v (make p n i) dans
      soit v =
        si not concr alors v sinon
        si mem Pos v && mem Neg v alors full sinon
        si Btype.is_Tvar ty alors v sinon
        union v
          (si p alors si n alors full sinon covariant sinon conjugate covariant)
      dans
      si decl.type_kind = Type_abstract && tr = Public alors v sinon
      set May_weak (mem May_neg v) v)
    params required

soit add_false = List.map (fonc ty -> faux, ty)

(* A parameter is constrained if either is is instantiated,
   or it is a variable appearing in another parameter *)
soit constrained env vars ty =
  filtre ty.desc avec
  | Tvar _ -> List.exists (fonc tl -> List.memq ty tl) vars
  | _ -> vrai

soit compute_variance_gadt env check (required, loc tel rloc) decl
    (tl, ret_type_opt) =
  filtre ret_type_opt avec
  | None ->
      compute_variance_type env check rloc {decl avec type_private = Private}
        (add_false tl)
  | Some ret_type ->
      filtre Ctype.repr ret_type avec
      | {desc=Tconstr (path, tyl, _)} ->
          (* let tyl = List.map (Ctype.expand_head env) tyl in *)
          soit tyl = List.map Ctype.repr tyl dans
          soit fvl = List.map (Ctype.free_variables ?env:None) tyl dans
          soit _ =
            List.fold_left2
              (fonc (fv1,fv2) ty (c,n,i) ->
                filtre fv2 avec [] -> affirme faux
                | fv :: fv2 ->
                    (* fv1 @ fv2 = free_variables of other parameters *)
                    si (c||n) && constrained env (fv1 @ fv2) ty alors
                      raise (Error(loc, Varying_anonymous));
                    (fv :: fv1, fv2))
              ([], fvl) tyl required
          dans
          compute_variance_type env check rloc
            {decl avec type_params = tyl; type_private = Private}
            (add_false tl)
      | _ -> affirme faux

soit compute_variance_decl env check decl (required, loc tel rloc) =
  si decl.type_kind = Type_abstract && decl.type_manifest = None alors
    List.map
      (fonc (c, n, i) ->
        make (not n) (not c) (i (*|| decl.type_transparence = Type_new*)))
      required
  sinon
  soit mn =
    filtre decl.type_manifest avec
      None -> []
    | Some ty -> [faux, ty]
  dans
  filtre decl.type_kind avec
    Type_abstract ->
      compute_variance_type env check rloc decl mn
  | Type_variant tll ->
      si List.for_all (fonc c -> c.Types.cd_res = None) tll alors
        compute_variance_type env check rloc decl
          (mn @ add_false (List.flatten (List.map (fonc c -> c.Types.cd_args) tll)))
      sinon début
        soit mn =
          List.map (fonc (_,ty) -> ([ty],None)) mn dans
        soit tll = mn @ List.map (fonc c -> c.Types.cd_args, c.Types.cd_res) tll dans
        filtre List.map (compute_variance_gadt env check rloc decl) tll avec
        | vari :: rem ->
            soit varl = List.fold_left (List.map2 Variance.union) vari rem dans
            List.map
              Variance.(fonc v -> si mem Pos v && mem Neg v alors full sinon v)
              varl
        | _ -> affirme faux
      fin
  | Type_record (ftl, _) ->
      compute_variance_type env check rloc decl
        (mn @ List.map (fonc {Types.ld_mutable; ld_type} ->
             (ld_mutable = Mutable, ld_type)) ftl)

soit is_sharp id =
  soit s = Ident.name id dans
  String.length s > 0 && s.[0] = '#'

soit rec compute_variance_fixpoint env decls required variances =
  soit new_decls =
    List.map2
      (fonc (id, decl) variance -> id, {decl avec type_variance = variance})
      decls variances
  dans
  soit new_env =
    List.fold_right
      (fonc (id, decl) env -> Env.add_type ~check:vrai id decl env)
      new_decls env
  dans
  soit new_variances =
    List.map2
      (fonc (id, decl) -> compute_variance_decl new_env faux decl)
      new_decls required
  dans
  soit new_variances =
    List.map2 (List.map2 Variance.union) new_variances variances dans
  si new_variances <> variances alors
    compute_variance_fixpoint env decls required new_variances
  sinon début
    (* List.iter (fun (id, decl) ->
      Printf.eprintf "%s:" (Ident.name id);
      List.iter (fun (v : Variance.t) ->
        Printf.eprintf " %x" (Obj.magic v : int))
        decl.type_variance;
      prerr_endline "")
      new_decls; *)
    List.iter2
      (fonc (id, decl) req -> si not (is_sharp id) alors
        ignore (compute_variance_decl new_env vrai decl req))
      new_decls required;
    new_decls, new_env
  fin

soit init_variance (id, decl) =
  List.map (fonc _ -> Variance.null) decl.type_params

soit add_injectivity =
  List.map
    (fonction
      | Covariant -> (vrai, faux, faux)
      | Contravariant -> (faux, vrai, faux)
      | Invariant -> (faux, faux, faux)
    )

(* for typeclass.ml *)
soit compute_variance_decls env cldecls =
  soit decls, required =
    List.fold_right
      (fonc (obj_id, obj_abbr, cl_abbr, clty, cltydef, ci) (decls, req) ->
        soit variance = List.map snd ci.ci_params dans
        (obj_id, obj_abbr) :: decls,
        (add_injectivity variance, ci.ci_loc) :: req)
      cldecls ([],[])
  dans
  soit variances = List.map init_variance decls dans
  soit (decls, _) = compute_variance_fixpoint env decls required variances dans
  List.map2
    (fonc (_,decl) (_, _, cl_abbr, clty, cltydef, _) ->
      soit variance = decl.type_variance dans
      (decl, {cl_abbr avec type_variance = variance},
       {clty avec cty_variance = variance},
       {cltydef avec clty_variance = variance}))
    decls cldecls

(* Check multiple declarations of labels/constructors *)

soit check_duplicates sdecl_list =
  soit labels = Hashtbl.create 7 et constrs = Hashtbl.create 7 dans
  List.iter
    (fonc sdecl -> filtre sdecl.ptype_kind avec
      Ptype_variant cl ->
        List.iter
          (fonc pcd ->
            essaie
              soit name' = Hashtbl.find constrs pcd.pcd_name.txt dans
              Location.prerr_warning pcd.pcd_loc
                (Warnings.Duplicate_definitions
                   ("constructeur", pcd.pcd_name.txt, name', sdecl.ptype_name.txt))
            avec Not_found -> Hashtbl.add constrs pcd.pcd_name.txt sdecl.ptype_name.txt)
          cl
    | Ptype_record fl ->
        List.iter
          (fonc {pld_name=cname;pld_loc=loc} ->
            essaie
              soit name' = Hashtbl.find labels cname.txt dans
              Location.prerr_warning loc
                (Warnings.Duplicate_definitions
                   ("label", cname.txt, name', sdecl.ptype_name.txt))
            avec Not_found -> Hashtbl.add labels cname.txt sdecl.ptype_name.txt)
          fl
    | Ptype_abstract -> ())
    sdecl_list

(* Force recursion to go through id for private types*)
soit name_recursion sdecl id decl =
  filtre decl avec
  | { type_kind = Type_abstract;
      type_manifest = Some ty;
      type_private = Private; } quand is_fixed_type sdecl ->
    soit ty = Ctype.repr ty dans
    soit ty' = Btype.newty2 ty.level ty.desc dans
    si Ctype.deep_occur ty ty' alors
      soit td = Tconstr(Path.Pident id, decl.type_params, ref Mnil) dans
      Btype.link_type ty (Btype.newty2 ty.level td);
      {decl avec type_manifest = Some ty'}
    sinon decl
  | _ -> decl

(* Translate a set of mutually recursive type declarations *)
soit transl_type_decl env sdecl_list =
  (* Add dummy types for fixed rows *)
  soit fixed_types = List.filter is_fixed_type sdecl_list dans
  soit sdecl_list =
    List.map
      (fonc sdecl ->
        soit ptype_name =  mkloc (sdecl.ptype_name.txt ^"#row") sdecl.ptype_name.loc dans
        {sdecl avec ptype_name; ptype_kind = Ptype_abstract; ptype_manifest = None})
      fixed_types
    @ sdecl_list
  dans
  (* Create identifiers. *)
  soit id_list =
    List.map (fonc sdecl -> Ident.create sdecl.ptype_name.txt) sdecl_list
  dans
  (*
     Since we've introduced fresh idents, make sure the definition
     level is at least the binding time of these events. Otherwise,
     passing one of the recursively-defined type constrs as argument
     to an abbreviation may fail.
  *)
  Ctype.init_def(Ident.current_time());
  Ctype.begin_def();
  (* Enter types. *)
  soit temp_env = List.fold_left2 enter_type env sdecl_list id_list dans
  (* Translate each declaration. *)
  soit current_slot = ref None dans
  soit warn_unused = Warnings.is_active (Warnings.Unused_type_declaration "") dans
  soit id_slots id =
    si not warn_unused alors id, None
    sinon
      (* See typecore.ml for a description of the algorithm used
         to detect unused declarations in a set of recursive definitions. *)
      soit slot = ref [] dans
      soit td = Env.find_type (Path.Pident id) temp_env dans
      soit name = Ident.name id dans
      Env.set_type_used_callback
        name td
        (fonc old_callback ->
          filtre !current_slot avec
          | Some slot -> slot := (name, td) :: !slot
          | None ->
              List.iter (fonc (name, d) -> Env.mark_type_used name d)
                (get_ref slot);
              old_callback ()
        );
      id, Some slot
  dans
  soit transl_declaration name_sdecl (id, slot) =
    current_slot := slot; transl_declaration temp_env name_sdecl id dans
  soit tdecls =
    List.map2 transl_declaration sdecl_list (List.map id_slots id_list) dans
  soit decls =
    List.map (fonc tdecl -> (tdecl.typ_id, tdecl.typ_type)) tdecls dans
  current_slot := None;
  (* Check for duplicates *)
  check_duplicates sdecl_list;
  (* Build the final env. *)
  soit newenv =
    List.fold_right
      (fonc (id, decl) env -> Env.add_type ~check:vrai id decl env)
      decls env
  dans
  (* Update stubs *)
  List.iter2
    (fonc id sdecl -> update_type temp_env newenv id sdecl.ptype_loc)
    id_list sdecl_list;
  (* Generalize type declarations. *)
  Ctype.end_def();
  List.iter (fonc (_, decl) -> generalize_decl decl) decls;
  (* Check for ill-formed abbrevs *)
  soit id_loc_list =
    List.map2 (fonc id sdecl -> (id, sdecl.ptype_loc))
      id_list sdecl_list
  dans
  List.iter (fonc (id, decl) ->
    check_well_founded newenv (List.assoc id id_loc_list) (Path.Pident id) decl)
    decls;
  List.iter (check_abbrev_recursion newenv id_loc_list) tdecls;
  (* Check that all type variable are closed *)
  List.iter2
    (fonc sdecl tdecl ->
      soit decl = tdecl.typ_type dans
       filtre Ctype.closed_type_decl decl avec
         Some ty -> raise(Error(sdecl.ptype_loc, Unbound_type_var(ty,decl)))
       | None   -> ())
    sdecl_list tdecls;
  (* Check that constraints are enforced *)
  List.iter2 (check_constraints newenv) sdecl_list decls;
  (* Name recursion *)
  soit decls =
    List.map2 (fonc sdecl (id, decl) -> id, name_recursion sdecl id decl)
      sdecl_list decls
  dans
  (* Add variances to the environment *)
  soit required =
    List.map
      (fonc sdecl ->
         add_injectivity (List.map snd sdecl.ptype_params),
         sdecl.ptype_loc
      )
      sdecl_list
  dans
  soit final_decls, final_env =
    compute_variance_fixpoint env decls required (List.map init_variance decls)
  dans
  (* Check re-exportation *)
  List.iter2 (check_abbrev final_env) sdecl_list final_decls;
  (* Keep original declaration *)
  soit final_decls =
    List.map2
      (fonc tdecl (id2, decl) ->
        { tdecl avec typ_type = decl }
      ) tdecls final_decls
  dans
  (* Done *)
  (final_decls, final_env)

(* Translate an exception declaration *)
soit transl_closed_type env sty =
  soit cty = transl_simple_type env vrai sty dans
  soit ty = cty.ctyp_type dans
  soit ty =
  filtre Ctype.free_variables ty avec
  | []      -> ty
  | tv :: _ -> raise (Error (sty.ptyp_loc, Unbound_type_var_exc (tv, ty)))
  dans
  { cty avec ctyp_type = ty }

soit transl_exception env excdecl =
  soit loc = excdecl.pcd_loc dans
  si excdecl.pcd_res <> None alors raise (Error (loc, Exception_constructor_with_result));
  reset_type_variables();
  Ctype.begin_def();
  soit ttypes = List.map (transl_closed_type env) excdecl.pcd_args dans
  Ctype.end_def();
  soit types = List.map (fonc cty -> cty.ctyp_type) ttypes dans
  List.iter Ctype.generalize types;
  soit exn_decl =
    {
      exn_args = types;
      exn_attributes = excdecl.pcd_attributes;
      Types.exn_loc = loc;
    }
  dans
  soit (id, newenv) = Env.enter_exception excdecl.pcd_name.txt exn_decl env dans
  soit cd =
    { cd_id = id;
      cd_name = excdecl.pcd_name;
      cd_args = ttypes;
      cd_loc = loc;
      cd_res = None;
      cd_attributes = excdecl.pcd_attributes;
     }
  dans
  cd, exn_decl, newenv

(* Translate an exception rebinding *)
soit transl_exn_rebind env loc lid =
  soit cdescr =
    essaie
      Env.lookup_constructor lid env
    avec Not_found ->
      raise(Error(loc, Unbound_exception lid)) dans
  Env.mark_constructor Env.Positive env (Longident.last lid) cdescr;
  filtre cdescr.cstr_tag avec
    Cstr_exception (path, _) ->
      (path, {exn_args = cdescr.cstr_args;
              exn_attributes = [];
              Types.exn_loc = loc})
  | _ -> raise(Error(loc, Not_an_exception lid))

(* Translate a value declaration *)
soit transl_value_decl env loc valdecl =
  soit cty = Typetexp.transl_type_scheme env valdecl.pval_type dans
  soit ty = cty.ctyp_type dans
  soit v =
  filtre valdecl.pval_prim avec
    [] ->
      { val_type = ty; val_kind = Val_reg; Types.val_loc = loc;
        val_attributes = valdecl.pval_attributes }
  | decl ->
      soit arity = Ctype.arity ty dans
      si arity = 0 alors
        raise(Error(valdecl.pval_type.ptyp_loc, Null_arity_external));
      soit prim = Primitive.parse_declaration arity decl dans
      si !Clflags.native_code
      && prim.prim_arity > 5
      && prim.prim_native_name = ""
      alors raise(Error(valdecl.pval_type.ptyp_loc, Missing_native_external));
      { val_type = ty; val_kind = Val_prim prim; Types.val_loc = loc;
        val_attributes = valdecl.pval_attributes }
  dans
  soit (id, newenv) =
    Env.enter_value valdecl.pval_name.txt v env
      ~check:(fonc s -> Warnings.Unused_value_declaration s)
  dans
  soit desc =
    {
     val_id = id;
     val_name = valdecl.pval_name;
     val_desc = cty; val_val = v;
     val_prim = valdecl.pval_prim;
     val_loc = valdecl.pval_loc;
     val_attributes = valdecl.pval_attributes;
    }
  dans
  desc, newenv

(* Translate a "with" constraint -- much simplified version of
    transl_type_decl. *)
soit transl_with_constraint env id row_path orig_decl sdecl =
  Env.mark_type_used (Ident.name id) orig_decl;
  reset_type_variables();
  Ctype.begin_def();
  soit params = make_params sdecl dans
  soit orig_decl = Ctype.instance_declaration orig_decl dans
  soit arity_ok = List.length params = orig_decl.type_arity dans
  si arity_ok alors
    List.iter2 (Ctype.unify_var env) params orig_decl.type_params;
  soit constraints = List.map
    (fonction (ty, ty', loc) ->
       essaie
         soit cty = transl_simple_type env faux ty dans
         soit cty' = transl_simple_type env faux ty' dans
         soit ty = cty.ctyp_type dans
         soit ty' = cty'.ctyp_type dans
         Ctype.unify env ty ty';
         (cty, cty', loc)
       avec Ctype.Unify tr ->
         raise(Error(loc, Inconsistent_constraint (env, tr))))
    sdecl.ptype_cstrs
  dans
  soit no_row = not (is_fixed_type sdecl) dans
  soit (tman, man) =  filtre sdecl.ptype_manifest avec
      None -> None, None
    | Some sty ->
        soit cty = transl_simple_type env no_row sty dans
        Some cty, Some cty.ctyp_type
  dans
  soit priv =
    si sdecl.ptype_private = Private alors Private sinon
    si arity_ok && orig_decl.type_kind <> Type_abstract
    alors orig_decl.type_private sinon sdecl.ptype_private
  dans
  si arity_ok && orig_decl.type_kind <> Type_abstract
  && sdecl.ptype_private = Private alors
    Location.prerr_warning sdecl.ptype_loc
      (Warnings.Deprecated "utilisation de privé étrange");
  soit decl =
    { type_params = params;
      type_arity = List.length params;
      type_kind =
        si arity_ok && man <> None alors orig_decl.type_kind sinon Type_abstract;
      type_private = priv;
      type_manifest = man;
      type_variance = [];
      type_newtype_level = None;
      type_loc = sdecl.ptype_loc;
      type_attributes = sdecl.ptype_attributes;
    }
  dans
  début filtre row_path avec None -> ()
  | Some p -> set_fixed_row env sdecl.ptype_loc p decl
  fin;
  début filtre Ctype.closed_type_decl decl avec None -> ()
  | Some ty -> raise(Error(sdecl.ptype_loc, Unbound_type_var(ty,decl)))
  fin;
  soit decl = name_recursion sdecl id decl dans
  soit decl =
    {decl avec type_variance =
     compute_variance_decl env faux decl
       (add_injectivity (List.map snd sdecl.ptype_params), sdecl.ptype_loc)} dans
  Ctype.end_def();
  generalize_decl decl;
  {
    typ_id = id;
    typ_name = sdecl.ptype_name;
    typ_params = sdecl.ptype_params;
    typ_type = decl;
    typ_cstrs = constraints;
    typ_loc = sdecl.ptype_loc;
    typ_manifest = tman;
    typ_kind = Ttype_abstract;
    typ_private = sdecl.ptype_private;
    typ_attributes = sdecl.ptype_attributes;
  }

(* Approximate a type declaration: just make all types abstract *)

soit abstract_type_decl arity =
  soit rec make_params n =
    si n <= 0 alors [] sinon Ctype.newvar() :: make_params (n-1) dans
  Ctype.begin_def();
  soit decl =
    { type_params = make_params arity;
      type_arity = arity;
      type_kind = Type_abstract;
      type_private = Public;
      type_manifest = None;
      type_variance = replicate_list Variance.full arity;
      type_newtype_level = None;
      type_loc = Location.none;
      type_attributes = [];
     } dans
  Ctype.end_def();
  generalize_decl decl;
  decl

soit approx_type_decl env sdecl_list =
  List.map
    (fonc sdecl ->
      (Ident.create sdecl.ptype_name.txt,
       abstract_type_decl (List.length sdecl.ptype_params)))
    sdecl_list

(* Variant of check_abbrev_recursion to check the well-formedness
   conditions on type abbreviations defined within recursive modules. *)

soit check_recmod_typedecl env loc recmod_ids path decl =
  (* recmod_ids is the list of recursively-defined module idents.
     (path, decl) is the type declaration to be checked. *)
  check_well_founded env loc path decl;
  check_recursion env loc path decl
    (fonc path -> List.exists (fonc id -> Path.isfree id path) recmod_ids)


(**** Error report ****)

ouvre Format

soit explain_unbound ppf tv tl typ kwd lab =
  essaie
    soit ti = List.find (fonc ti -> Ctype.deep_occur tv (typ ti)) tl dans
    soit ty0 = (* Hack to force aliasing when needed *)
      Btype.newgenty (Tobject(tv, ref None)) dans
    Printtyp.reset_and_mark_loops_list [typ ti; ty0];
    fprintf ppf
      ".@.@[<hov2>Dans %s@ %s%a@;<1 -2>la variable %a n'est pas liée@]"
      kwd (lab ti) Printtyp.type_expr (typ ti) Printtyp.type_expr tv
  avec Not_found -> ()

soit explain_unbound_single ppf tv ty =
  soit trivial ty =
    explain_unbound ppf tv [ty] (fonc t -> t) "type" (fonc _ -> "") dans
  filtre (Ctype.repr ty).desc avec
    Tobject(fi,_) ->
      soit (tl, rv) = Ctype.flatten_fields fi dans
      si rv == tv alors trivial ty sinon
      explain_unbound ppf tv tl (fonc (_,_,t) -> t)
        "method" (fonc (lab,_,_) -> lab ^ ": ")
  | Tvariant row ->
      soit row = Btype.row_repr row dans
      si row.row_more == tv alors trivial ty sinon
      explain_unbound ppf tv row.row_fields
        (fonc (l,f) -> filtre Btype.row_field_repr f avec
          Rpresent (Some t) -> t
        | Reither (_,[t],_,_) -> t
        | Reither (_,tl,_,_) -> Btype.newgenty (Ttuple tl)
        | _ -> Btype.newgenty (Ttuple[]))
        "case" (fonc (lab,_) -> "`" ^ lab ^ " of ")
  | _ -> trivial ty

soit report_error ppf = fonction
  | Repeated_parameter ->
      fprintf ppf "Un paramètre de type apparaît plusieurs fois"
  | Duplicate_constructor s ->
      fprintf ppf "Deux constructeurs sont nommés %s" s
  | Too_many_constructors ->
      fprintf ppf
        "@[Trop de constructeurs non constants@ -- le maximum est is %i %s@]"
        (Config.max_tag + 1) "constructeurs non constants"
  | Duplicate_label s ->
      fprintf ppf "Deux labels sont nommés %s" s
  | Recursive_abbrev s ->
      fprintf ppf "L'abréviation de type %s est cyclique" s
  | Definition_mismatch (ty, errs) ->
      Printtyp.reset_and_mark_loops ty;
      fprintf ppf "@[<v>@[<hov>%s@ %s@;<1 2>%a@]%a@]"
        "Cette définition de type somme ou d'enregistrement"
        "ne correspond pas à celle du type"
        Printtyp.type_expr ty
        (Includecore.report_type_mismatch "la définition originale" "cette définition")
        errs
  | Constraint_failed (ty, ty') ->
      Printtyp.reset_and_mark_loops ty;
      Printtyp.mark_loops ty';
      fprintf ppf "@[%s@ @[<hv>Le type@ %a@ devrait être une instance de@ %a@]@]"
        "Les contraintes ne soint pas satisfaites dans ce type."
        Printtyp.type_expr ty Printtyp.type_expr ty'
  | Parameters_differ (path, ty, ty') ->
      Printtyp.reset_and_mark_loops ty;
      Printtyp.mark_loops ty';
      fprintf ppf
        "@[<hv>Dans la définition de %s, le type@ %a@ devrait être@ %a@]"
        (Path.name path) Printtyp.type_expr ty Printtyp.type_expr ty'
  | Inconsistent_constraint (env, trace) ->
      fprintf ppf "Les contraintes de type ne sont pas consistentes.@.";
      Printtyp.report_unification_error ppf env trace
        (fonc ppf -> fprintf ppf "Type")
        (fonc ppf -> fprintf ppf "is not compatible with type")
  | Type_clash (env, trace) ->
      Printtyp.report_unification_error ppf env trace
        (fonction ppf ->
           fprintf ppf "Ce constructeur de type s'étend au type")
        (fonction ppf ->
           fprintf ppf "mais est utilisé ici avec le type")
  | Null_arity_external ->
      fprintf ppf "Les identifiants externes doivent être des fonctions"
  | Missing_native_external ->
      fprintf ppf "@[<hv>Une fonction externe de plus de 5 arguments \
                   requiert une seconde fonction talon@ \
                   pour la compilation en code natif@]"
  | Unbound_type_var (ty, decl) ->
      fprintf ppf "Une variable de type n'est pas liée dans cette déclaration de type";
      soit ty = Ctype.repr ty dans
      début filtre decl.type_kind, decl.type_manifest avec
      | Type_variant tl, _ ->
          explain_unbound ppf ty tl (fonc c ->
            Btype.newgenty (Ttuple c.Types.cd_args))
            "le cas" (fonc c -> Ident.name c.Types.cd_id ^ " de ")
      | Type_record (tl, _), _ ->
          explain_unbound ppf ty tl (fonc l -> l.Types.ld_type)
            "le champ" (fonc l -> Ident.name l.Types.ld_id ^ ": ")
      | Type_abstract, Some ty' ->
          explain_unbound_single ppf ty ty'
      | _ -> ()
      fin
  | Unbound_type_var_exc (tv, ty) ->
      fprintf ppf "Une variable de type n'est pas liée dans cette déclaration d'exception";
      explain_unbound_single ppf (Ctype.repr tv) ty
  | Unbound_exception lid ->
      fprintf ppf "Constructeur d'exception non lié@ %a" Printtyp.longident lid
  | Not_an_exception lid ->
      fprintf ppf "Le constructeur@ %a@ n'est pas une exception"
        Printtyp.longident lid
  | Bad_variance (n, v1, v2) ->
      soit variance (p,n,i) =
        soit inj = si i alors "injective " sinon "" dans
        filtre p, n avec
          vrai,  vrai  -> inj ^ "invariante"
        | vrai,  faux -> inj ^ "covariante"
        | faux, vrai  -> inj ^ "contravariante"
        | faux, faux -> si inj = "" alors "non restreinte" sinon inj
      dans
      soit suffix n =
        filtre n avec
        | 1 -> "er"
        | _ -> "ème"
      dans
      si n = -1 alors
        fprintf ppf "@[%s@ %s@ Elle"
          "Dans cette définition, une variable de type a une variance qui"
          "n'est pas reflétée par son occurence dans les paramètres de type."
      sinon si n = -2 alors
        fprintf ppf "@[%s@ %s@ Elle"
          "Dans cette définition, une variable de type ne peut pas être déduite"
          "des paramètres de type."
      sinon si n = -3 alors
        fprintf ppf "@[%s@ %s@ Elle"
          "In this definition, a type variable has a variance that"
          "cannot be deduced from the type parameters."
      sinon
        fprintf ppf "@[%s@ %s@ Le %d%s paramètre de type"
          "Dans cette définition, les variances des paramètres"
          "ne sont pas satisfaites."
          n (suffix n);
      si n <> -2 alors
        fprintf ppf " devait être %s,@ mais elle est %s.@]"
          (variance v2) (variance v1)
  | Unavailable_type_constructor p ->
      fprintf ppf "La définition du type %a@ n'est pas disponible" Printtyp.path p
  | Bad_fixed_type r ->
      fprintf ppf "Ce type fixé %s" r
  | Varying_anonymous ->
      fprintf ppf "@[%s@ %s@ %s@]"
        "Dans cette définition de TDAG," "la variance d'un paramètre"
        "ne peut pas être vérifiée"
  | Exception_constructor_with_result ->
      fprintf ppf "Les constructeurs d'exception ne peuvent pas spécifier un type de retour"

soit () =
  Location.register_error_of_exn
    (fonction
      | Error (loc, err) ->
        Some (Location.error_of_printer loc report_error err)
      | _ ->
        None
    )
