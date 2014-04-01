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

(* typetexp.ml,v 1.34.4.9 2002/01/07 08:39:16 garrigue Exp *)

(* Typechecking of type expressions for the core language *)

ouvre Asttypes
ouvre Misc
ouvre Parsetree
ouvre Typedtree
ouvre Types
ouvre Ctype

exception Already_bound de Location.t

type error =
    Unbound_type_variable de string
  | Unbound_type_constructor de Longident.t
  | Unbound_type_constructor_2 de Path.t
  | Type_arity_mismatch de Longident.t * int * int
  | Bound_type_variable de string
  | Recursive_type
  | Unbound_row_variable de Longident.t
  | Type_mismatch de (type_expr * type_expr) list
  | Alias_type_mismatch de (type_expr * type_expr) list
  | Present_has_conjunction de string
  | Present_has_no_type de string
  | Constructor_mismatch de type_expr * type_expr
  | Not_a_variant de type_expr
  | Variant_tags de string * string
  | Invalid_variable_name de string
  | Cannot_quantify de string * type_expr
  | Multiple_constraints_on_type de Longident.t
  | Repeated_method_label de string
  | Unbound_value de Longident.t
  | Unbound_constructor de Longident.t
  | Unbound_label de Longident.t
  | Unbound_module de Longident.t
  | Unbound_class de Longident.t
  | Unbound_modtype de Longident.t
  | Unbound_cltype de Longident.t
  | Ill_typed_functor_application de Longident.t
  | Illegal_reference_to_recursive_module
  | Extension de string

exception Error de Location.t * Env.t * error

soit check_deprecated loc attrs s =
  si
    List.exists
      (fonction ({txt = "deprecated"; _}, _) -> vrai | _ ->  faux)
      attrs
  alors
    Location.prerr_warning loc (Warnings.Deprecated s)

soit warning_attribute attrs =
  soit prev_warnings = ref None dans
  List.iter
    (fonction
      | ({txt = "warning"; loc}, payload) ->
          début filtre payload avec
          | PStr [{pstr_desc=Pstr_eval
                     ({pexp_desc=Pexp_constant(Const_string(s, _))}, _)}] ->
              si !prev_warnings = None alors
                prev_warnings := Some (Warnings.backup ());
              début essaie Warnings.parse_options faux s
              avec Arg.Bad _ ->
                Location.prerr_warning loc
                  (Warnings.Attribute_payload
                     ("warning",
                      "Liste d'avertissements malformée"))
              fin
          | _ ->
              Location.prerr_warning loc
                (Warnings.Attribute_payload
                   ("warning",
                    "Un littéral de chaîne simple est attendu"))
          fin
      | _ ->
          ()
    )
    attrs;
  !prev_warnings



type variable_context = int * (string, type_expr) Tbl.t

(* Local definitions *)

soit instance_list = Ctype.instance_list Env.empty

(* Narrowing unbound identifier errors. *)

soit rec narrow_unbound_lid_error : 'a. _ -> _ -> _ -> _ -> 'a =
  fonc env loc lid make_error ->
  soit check_module mlid =
    essaie ignore (Env.lookup_module mlid env)
    avec Not_found ->
      narrow_unbound_lid_error env loc mlid
        (fonc lid -> Unbound_module lid)
       | Env.Recmodule ->
         raise (Error (loc, env, Illegal_reference_to_recursive_module))
  dans
  début filtre lid avec
  | Longident.Lident _ -> ()
  | Longident.Ldot (mlid, _) -> check_module mlid
  | Longident.Lapply (flid, mlid) ->
      check_module flid;
      check_module mlid;
      raise (Error (loc, env, Ill_typed_functor_application lid))
  fin;
  raise (Error (loc, env, make_error lid))

soit find_component lookup make_error env loc lid =
  essaie
    filtre lid avec
    | Longident.Ldot (Longident.Lident "*predef*", s) ->
        lookup (Longident.Lident s) Env.initial
    | _ -> lookup lid env
  avec Not_found ->
    narrow_unbound_lid_error env loc lid make_error
  | Env.Recmodule ->
    raise (Error (loc, env, Illegal_reference_to_recursive_module))

soit find_type env loc lid =
  soit (path, decl) tel r =
    find_component Env.lookup_type (fonc lid -> Unbound_type_constructor lid)
      env loc lid
  dans
  check_deprecated loc decl.type_attributes (Path.name path);
  r

soit find_constructor =
  find_component Env.lookup_constructor (fonc lid -> Unbound_constructor lid)
soit find_all_constructors =
  find_component Env.lookup_all_constructors
    (fonc lid -> Unbound_constructor lid)
soit find_label =
  find_component Env.lookup_label (fonc lid -> Unbound_label lid)
soit find_all_labels =
  find_component Env.lookup_all_labels (fonc lid -> Unbound_label lid)

soit find_class env loc lid =
  soit (path, decl) tel r =
    find_component Env.lookup_class (fonc lid -> Unbound_class lid) env loc lid
  dans
  check_deprecated loc decl.cty_attributes (Path.name path);
  r

soit find_value env loc lid =
  soit (path, decl) tel r =
    find_component Env.lookup_value (fonc lid -> Unbound_value lid) env loc lid
  dans
  check_deprecated loc decl.val_attributes (Path.name path);
  r

soit find_module env loc lid =
  soit (path, decl) tel r =
    find_component (fonc lid env -> (Env.lookup_module lid env, ()))
      (fonc lid -> Unbound_module lid) env loc lid
  dans
  (* check_deprecated loc decl.md_attributes (Path.name path); *)
  path

soit find_modtype env loc lid =
  soit (path, decl) tel r =
    find_component Env.lookup_modtype (fonc lid -> Unbound_modtype lid)
      env loc lid
  dans
  check_deprecated loc decl.mtd_attributes (Path.name path);
  r

soit find_class_type env loc lid =
  soit (path, decl) tel r =
    find_component Env.lookup_cltype (fonc lid -> Unbound_cltype lid)
      env loc lid
  dans
  check_deprecated loc decl.clty_attributes (Path.name path);
  r

soit unbound_constructor_error env lid =
  narrow_unbound_lid_error env lid.loc lid.txt
    (fonc lid -> Unbound_constructor lid)

soit unbound_label_error env lid =
  narrow_unbound_lid_error env lid.loc lid.txt
    (fonc lid -> Unbound_label lid)

(* Support for first-class modules. *)

soit transl_modtype_longident = ref (fonc _ -> affirme faux)
soit transl_modtype = ref (fonc _ -> affirme faux)

soit create_package_mty fake loc env (p, l) =
  soit l =
    List.sort
      (fonc (s1, t1) (s2, t2) ->
         si s1.txt = s2.txt alors
           raise (Error (loc, env, Multiple_constraints_on_type s1.txt));
         compare s1.txt s2.txt)
      l
  dans
  l,
  List.fold_left
    (fonc mty (s, t) ->
      soit d = {ptype_name = mkloc (Longident.last s.txt) s.loc;
               ptype_params = [];
               ptype_cstrs = [];
               ptype_kind = Ptype_abstract;
               ptype_private = Asttypes.Public;
               ptype_manifest = si fake alors None sinon Some t;
               ptype_attributes = [];
               ptype_loc = loc} dans
      Ast_helper.Mty.mk ~loc
        (Pmty_with (mty, [ Pwith_type ({ txt = s.txt; loc }, d) ]))
    )
    (Ast_helper.Mty.mk ~loc (Pmty_ident p))
    l

(* Translation of type expressions *)

soit type_variables = ref (Tbl.empty : (string, type_expr) Tbl.t)
soit univars        = ref ([] : (string * type_expr) list)
soit pre_univars    = ref ([] : type_expr list)
soit used_variables = ref (Tbl.empty : (string, type_expr * Location.t) Tbl.t)

soit reset_type_variables () =
  reset_global_level ();
  type_variables := Tbl.empty

soit narrow () =
  (increase_global_level (), !type_variables)

soit widen (gl, tv) =
  restore_global_level gl;
  type_variables := tv

soit strict_lowercase c = (c = '_' || c >= 'a' && c <= 'z')

soit validate_name = fonction
    None -> None
  | Some name tel s ->
      si name <> "" && strict_lowercase name.[0] alors s sinon None

soit new_global_var ?name () =
  new_global_var ?name:(validate_name name) ()
soit newvar ?name () =
  newvar ?name:(validate_name name) ()

soit enter_type_variable {Location.txt=name; loc} =
  essaie
    si name <> "" && name.[0] = '_' alors
      raise (Error (loc, Env.empty, Invalid_variable_name ("'" ^ name)));
    soit v = Tbl.find name !type_variables dans
    raise (Already_bound loc);
    v
  avec Not_found ->
    soit v = new_global_var ~name () dans
    type_variables := Tbl.add name v !type_variables;
    v

soit type_variable loc name =
  essaie
    Tbl.find name !type_variables
  avec Not_found ->
    raise(Error(loc, Env.empty, Unbound_type_variable ("'" ^ name)))

soit wrap_method ty =
  filtre (Ctype.repr ty).desc avec
    Tpoly _ -> ty
  | _ -> Ctype.newty (Tpoly (ty, []))

soit new_pre_univar ?name () =
  soit v = newvar ?name () dans pre_univars := v :: !pre_univars; v

soit rec swap_list = fonction
    x :: y :: l -> y :: x :: swap_list l
  | l -> l

type policy = Fixed | Extensible | Univars

soit rec transl_type env policy styp =
  soit loc = styp.ptyp_loc dans
  soit ctyp ctyp_desc ctyp_type =
    { ctyp_desc; ctyp_type; ctyp_env = env;
      ctyp_loc = loc; ctyp_attributes = styp.ptyp_attributes }
  dans
  filtre styp.ptyp_desc avec
    Ptyp_any ->
      soit ty =
        si policy = Univars alors new_pre_univar () sinon
          si policy = Fixed alors
            raise (Error (styp.ptyp_loc, env, Unbound_type_variable "_"))
          sinon newvar ()
      dans
      ctyp Ttyp_any ty
  | Ptyp_var name ->
    soit ty =
      si name <> "" && name.[0] = '_' alors
        raise (Error (styp.ptyp_loc, env, Invalid_variable_name ("'" ^ name)));
      début essaie
        instance env (List.assoc name !univars)
      avec Not_found -> essaie
        instance env (fst(Tbl.find name !used_variables))
      avec Not_found ->
        soit v =
          si policy = Univars alors new_pre_univar ~name () sinon newvar ~name ()
        dans
        used_variables := Tbl.add name (v, styp.ptyp_loc) !used_variables;
        v
      fin
    dans
    ctyp (Ttyp_var name) ty
  | Ptyp_arrow(l, st1, st2) ->
    soit cty1 = transl_type env policy st1 dans
    soit cty2 = transl_type env policy st2 dans
    soit ty = newty (Tarrow(l, cty1.ctyp_type, cty2.ctyp_type, Cok)) dans
    ctyp (Ttyp_arrow (l, cty1, cty2)) ty
  | Ptyp_tuple stl ->
    soit ctys = List.map (transl_type env policy) stl dans
    soit ty = newty (Ttuple (List.map (fonc ctyp -> ctyp.ctyp_type) ctys)) dans
    ctyp (Ttyp_tuple ctys) ty
  | Ptyp_constr(lid, stl) ->
      soit (path, decl) = find_type env styp.ptyp_loc lid.txt dans
      si List.length stl <> decl.type_arity alors
        raise(Error(styp.ptyp_loc, env,
		    Type_arity_mismatch(lid.txt, decl.type_arity,
                                        List.length stl)));
      soit args = List.map (transl_type env policy) stl dans
      soit params = instance_list decl.type_params dans
      soit unify_param =
        filtre decl.type_manifest avec
          None -> unify_var
        | Some ty ->
            si (repr ty).level = Btype.generic_level alors unify_var sinon unify
      dans
      List.iter2
        (fonc (sty, cty) ty' ->
           essaie unify_param env ty' cty.ctyp_type avec Unify trace ->
             raise (Error(sty.ptyp_loc, env, Type_mismatch (swap_list trace))))
        (List.combine stl args) params;
      soit constr =
        newconstr path (List.map (fonc ctyp -> ctyp.ctyp_type) args) dans
      début essaie
        Ctype.enforce_constraints env constr
      avec Unify trace ->
        raise (Error(styp.ptyp_loc, env, Type_mismatch trace))
      fin;
      ctyp (Ttyp_constr (path, lid, args)) constr
  | Ptyp_object (fields, o) ->
      soit fields =
        List.map (fonc (s, t) -> (s, transl_poly_type env policy t))
          fields
      dans
      soit ty = newobj (transl_fields loc env policy [] o fields) dans
      ctyp (Ttyp_object (fields, o)) ty
  | Ptyp_class(lid, stl) ->
      soit (path, decl, is_variant) =
        essaie
          soit (path, decl) = Env.lookup_type lid.txt env dans
          soit rec check decl =
            filtre decl.type_manifest avec
              None -> raise Not_found
            | Some ty ->
                filtre (repr ty).desc avec
                  Tvariant row quand Btype.static_row row -> ()
                | Tconstr (path, _, _) ->
                    check (Env.find_type path env)
                | _ -> raise Not_found
          dans check decl;
          Location.prerr_warning styp.ptyp_loc
            (Warnings.Deprecated "ancienne syntaxe pour les types sommes polymorphes");
          (path, decl,vrai)
        avec Not_found -> essaie
          soit lid2 =
            filtre lid.txt avec
              Longident.Lident s     -> Longident.Lident ("#" ^ s)
            | Longident.Ldot(r, s)   -> Longident.Ldot (r, "#" ^ s)
            | Longident.Lapply(_, _) -> fatal_error "Typetexp.transl_type"
          dans
          soit (path, decl) = Env.lookup_type lid2 env dans
          (path, decl, faux)
        avec Not_found ->
          raise(Error(styp.ptyp_loc, env, Unbound_class lid.txt))
      dans
      si List.length stl <> decl.type_arity alors
        raise(Error(styp.ptyp_loc, env,
                    Type_arity_mismatch(lid.txt, decl.type_arity,
                                        List.length stl)));
      soit args = List.map (transl_type env policy) stl dans
      soit params = instance_list decl.type_params dans
      List.iter2
        (fonc (sty, cty) ty' ->
           essaie unify_var env ty' cty.ctyp_type avec Unify trace ->
             raise (Error(sty.ptyp_loc, env, Type_mismatch (swap_list trace))))
        (List.combine stl args) params;
        soit ty_args = List.map (fonc ctyp -> ctyp.ctyp_type) args dans
      soit ty =
        essaie Ctype.expand_head env (newconstr path ty_args)
        avec Unify trace ->
          raise (Error(styp.ptyp_loc, env, Type_mismatch trace))
      dans
      soit ty = filtre ty.desc avec
        Tvariant row ->
          soit row = Btype.row_repr row dans
          soit fields =
            List.map
              (fonc (l,f) -> l,
                filtre Btype.row_field_repr f avec
                | Rpresent (Some ty) ->
                    Reither(faux, [ty], faux, ref None)
                | Rpresent None ->
                    Reither (vrai, [], faux, ref None)
                | _ -> f)
              row.row_fields
          dans
          soit row = { row_closed = vrai; row_fields = fields;
                      row_bound = (); row_name = Some (path, ty_args);
                      row_fixed = faux; row_more = newvar () } dans
          soit static = Btype.static_row row dans
          soit row =
            si static alors { row avec row_more = newty Tnil }
            sinon si policy <> Univars alors row
            sinon { row avec row_more = new_pre_univar () }
          dans
          newty (Tvariant row)
      | Tobject (fi, _) ->
          soit _, tv = flatten_fields fi dans
          si policy = Univars alors pre_univars := tv :: !pre_univars;
          ty
      | _ ->
          affirme faux
      dans
      ctyp (Ttyp_class (path, lid, args)) ty
  | Ptyp_alias(st, alias) ->
      soit cty =
        essaie
          soit t =
            essaie List.assoc alias !univars
            avec Not_found ->
              instance env (fst(Tbl.find alias !used_variables))
          dans
          soit ty = transl_type env policy st dans
          début essaie unify_var env t ty.ctyp_type avec Unify trace ->
            soit trace = swap_list trace dans
            raise(Error(styp.ptyp_loc, env, Alias_type_mismatch trace))
          fin;
          ty
        avec Not_found ->
          si !Clflags.principal alors begin_def ();
          soit t = newvar () dans
          used_variables := Tbl.add alias (t, styp.ptyp_loc) !used_variables;
          soit ty = transl_type env policy st dans
          début essaie unify_var env t ty.ctyp_type avec Unify trace ->
            soit trace = swap_list trace dans
            raise(Error(styp.ptyp_loc, env, Alias_type_mismatch trace))
          fin;
          si !Clflags.principal alors début
            end_def ();
            generalize_structure t;
          fin;
          soit t = instance env t dans
          soit px = Btype.proxy t dans
          début filtre px.desc avec
          | Tvar None -> Btype.log_type px; px.desc <- Tvar (Some alias)
          | Tunivar None -> Btype.log_type px; px.desc <- Tunivar (Some alias)
          | _ -> ()
          fin;
          { ty avec ctyp_type = t }
      dans
      ctyp (Ttyp_alias (cty, alias)) cty.ctyp_type
  | Ptyp_variant(fields, closed, present) ->
      soit name = ref None dans
      soit mkfield l f =
        newty (Tvariant {row_fields=[l,f]; row_more=newvar();
                         row_bound=(); row_closed=vrai;
                         row_fixed=faux; row_name=None}) dans
      soit hfields = Hashtbl.create 17 dans
      soit add_typed_field loc l f =
        soit h = Btype.hash_variant l dans
        essaie
          soit (l',f') = Hashtbl.find hfields h dans
          (* Check for tag conflicts *)
          si l <> l' alors raise(Error(styp.ptyp_loc, env, Variant_tags(l, l')));
          soit ty = mkfield l f et ty' = mkfield l f' dans
          si equal env faux [ty] [ty'] alors () sinon
          essaie unify env ty ty'
          avec Unify trace ->
            raise(Error(loc, env, Constructor_mismatch (ty,ty')))
        avec Not_found ->
          Hashtbl.add hfields h (l,f)
      dans
      soit add_field = fonction
          Rtag (l, c, stl) ->
            name := None;
            soit tl = List.map (transl_type env policy) stl dans
            soit f = filtre present avec
              Some present quand not (List.mem l present) ->
                soit ty_tl = List.map (fonc cty -> cty.ctyp_type) tl dans
                Reither(c, ty_tl, faux, ref None)
            | _ ->
                si List.length stl > 1 || c && stl <> [] alors
                  raise(Error(styp.ptyp_loc, env, Present_has_conjunction l));
                filtre tl avec [] -> Rpresent None
                | st :: _ ->
                      Rpresent (Some st.ctyp_type)
            dans
            add_typed_field styp.ptyp_loc l f;
              Ttag (l,c,tl)
        | Rinherit sty ->
            soit cty = transl_type env policy sty dans
            soit ty = cty.ctyp_type dans
            soit nm =
              filtre repr cty.ctyp_type avec
                {desc=Tconstr(p, tl, _)} -> Some(p, tl)
              | _                        -> None
            dans
            début essaie
              (* Set name if there are no fields yet *)
              Hashtbl.iter (fonc _ _ -> raise Exit) hfields;
              name := nm
            avec Exit ->
              (* Unset it otherwise *)
              name := None
            fin;
            soit fl = filtre expand_head env cty.ctyp_type, nm avec
              {desc=Tvariant row}, _ quand Btype.static_row row ->
                soit row = Btype.row_repr row dans
                row.row_fields
            | {desc=Tvar _}, Some(p, _) ->
                raise(Error(sty.ptyp_loc, env, Unbound_type_constructor_2 p))
            | _ ->
                raise(Error(sty.ptyp_loc, env, Not_a_variant ty))
            dans
            List.iter
              (fonc (l, f) ->
                soit f = filtre present avec
                  Some present quand not (List.mem l present) ->
                    début filtre f avec
                      Rpresent(Some ty) ->
                        Reither(faux, [ty], faux, ref None)
                    | Rpresent None ->
                        Reither(vrai, [], faux, ref None)
                    | _ ->
                        affirme faux
                    fin
                | _ -> f
                dans
                add_typed_field sty.ptyp_loc l f)
              fl;
              Tinherit cty
      dans
      soit tfields = List.map add_field fields dans
      soit fields = Hashtbl.fold (fonc _ p l -> p :: l) hfields [] dans
      début filtre present avec None -> ()
      | Some present ->
          List.iter
            (fonc l -> si not (List.mem_assoc l fields) alors
              raise(Error(styp.ptyp_loc, env, Present_has_no_type l)))
            present
      fin;
      soit row =
        { row_fields = List.rev fields; row_more = newvar ();
          row_bound = (); row_closed = (closed = Closed);
          row_fixed = faux; row_name = !name } dans
      soit static = Btype.static_row row dans
      soit row =
        si static alors { row avec row_more = newty Tnil }
        sinon si policy <> Univars alors row
        sinon { row avec row_more = new_pre_univar () }
      dans
      soit ty = newty (Tvariant row) dans
      ctyp (Ttyp_variant (tfields, closed, present)) ty
   | Ptyp_poly(vars, st) ->
      begin_def();
      soit new_univars = List.map (fonc name -> name, newvar ~name ()) vars dans
      soit old_univars = !univars dans
      univars := new_univars @ !univars;
      soit cty = transl_type env policy st dans
      soit ty = cty.ctyp_type dans
      univars := old_univars;
      end_def();
      generalize ty;
      soit ty_list =
        List.fold_left
          (fonc tyl (name, ty1) ->
            soit v = Btype.proxy ty1 dans
            si deep_occur v ty alors début
              filtre v.desc avec
                Tvar name quand v.level = Btype.generic_level ->
                  v.desc <- Tunivar name;
                  v :: tyl
              | _ ->
                raise (Error (styp.ptyp_loc, env, Cannot_quantify (name, v)))
            fin sinon tyl)
          [] new_univars
      dans
      soit ty' = Btype.newgenty (Tpoly(ty, List.rev ty_list)) dans
      unify_var env (newvar()) ty';
      ctyp (Ttyp_poly (vars, cty)) ty'
  | Ptyp_package (p, l) ->
      soit l, mty = create_package_mty vrai styp.ptyp_loc env (p, l) dans
      soit z = narrow () dans
      soit mty = !transl_modtype env mty dans
      widen z;
      soit ptys = List.map (fonc (s, pty) ->
                             s, transl_type env policy pty
                          ) l dans
      soit path = !transl_modtype_longident styp.ptyp_loc env p.txt dans
      soit ty = newty (Tpackage (path,
                       List.map (fonc (s, pty) -> s.txt) l,
                       List.map (fonc (_,cty) -> cty.ctyp_type) ptys))
      dans
      ctyp (Ttyp_package {
            pack_name = path;
            pack_type = mty.mty_type;
            pack_fields = ptys;
            pack_txt = p;
           }) ty
  | Ptyp_extension (s, _arg) ->
      raise (Error (s.loc, env, Extension s.txt))

et transl_poly_type env policy t =
  transl_type env policy (Ast_helper.Typ.force_poly t)

et transl_fields loc env policy seen o =
  fonction
    [] ->
      début filtre o, policy avec
      | Closed, _ -> newty Tnil
      | Open, Univars -> new_pre_univar ()
      | Open, _ -> newvar ()
      fin
  | (s, ty1) :: l ->
      si List.mem s seen alors raise (Error (loc, env, Repeated_method_label s));
      soit ty2 = transl_fields loc env policy (s :: seen) o l dans
      newty (Tfield (s, Fpresent, ty1.ctyp_type, ty2))

(* Make the rows "fixed" in this type, to make universal check easier *)
soit rec make_fixed_univars ty =
  soit ty = repr ty dans
  si ty.level >= Btype.lowest_level alors début
    Btype.mark_type_node ty;
    filtre ty.desc avec
    | Tvariant row ->
        soit row = Btype.row_repr row dans
        si Btype.is_Tunivar (Btype.row_more row) alors
          ty.desc <- Tvariant
              {row avec row_fixed=vrai;
               row_fields = List.map
                 (fonc (s,f tel p) -> filtre Btype.row_field_repr f avec
                   Reither (c, tl, m, r) -> s, Reither (c, tl, vrai, r)
                 | _ -> p)
                 row.row_fields};
        Btype.iter_row make_fixed_univars row
    | _ ->
        Btype.iter_type_expr make_fixed_univars ty
  fin

soit make_fixed_univars ty =
  make_fixed_univars ty;
  Btype.unmark_type ty

soit create_package_mty = create_package_mty faux

soit globalize_used_variables env fixed =
  soit r = ref [] dans
  Tbl.iter
    (fonc name (ty, loc) ->
      soit v = new_global_var () dans
      soit snap = Btype.snapshot () dans
      si essaie unify env v ty; vrai avec _ -> Btype.backtrack snap; faux
      alors essaie
        r := (loc, v,  Tbl.find name !type_variables) :: !r
      avec Not_found ->
        si fixed && Btype.is_Tvar (repr ty) alors
          raise(Error(loc, env, Unbound_type_variable ("'"^name)));
        soit v2 = new_global_var () dans
        r := (loc, v, v2) :: !r;
        type_variables := Tbl.add name v2 !type_variables)
    !used_variables;
  used_variables := Tbl.empty;
  fonc () ->
    List.iter
      (fonction (loc, t1, t2) ->
        essaie unify env t1 t2 avec Unify trace ->
          raise (Error(loc, env, Type_mismatch trace)))
      !r

soit transl_simple_type env fixed styp =
  univars := []; used_variables := Tbl.empty;
  soit typ = transl_type env (si fixed alors Fixed sinon Extensible) styp dans
  globalize_used_variables env fixed ();
  make_fixed_univars typ.ctyp_type;
  typ

soit transl_simple_type_univars env styp =
  univars := []; used_variables := Tbl.empty; pre_univars := [];
  begin_def ();
  soit typ = transl_type env Univars styp dans
  (* Only keep already global variables in used_variables *)
  soit new_variables = !used_variables dans
  used_variables := Tbl.empty;
  Tbl.iter
    (fonc name p ->
      si Tbl.mem name !type_variables alors
        used_variables := Tbl.add name p !used_variables)
    new_variables;
  globalize_used_variables env faux ();
  end_def ();
  generalize typ.ctyp_type;
  soit univs =
    List.fold_left
      (fonc acc v ->
        soit v = repr v dans
        filtre v.desc avec
          Tvar name quand v.level = Btype.generic_level ->
            v.desc <- Tunivar name; v :: acc
        | _ -> acc)
      [] !pre_univars
  dans
  make_fixed_univars typ.ctyp_type;
    { typ avec ctyp_type =
        instance env (Btype.newgenty (Tpoly (typ.ctyp_type, univs))) }

soit transl_simple_type_delayed env styp =
  univars := []; used_variables := Tbl.empty;
  soit typ = transl_type env Extensible styp dans
  make_fixed_univars typ.ctyp_type;
  (typ, globalize_used_variables env faux)

soit transl_type_scheme env styp =
  reset_type_variables();
  begin_def();
  soit typ = transl_simple_type env faux styp dans
  end_def();
  generalize typ.ctyp_type;
  typ


(* Error report *)

ouvre Format
ouvre Printtyp

soit spellcheck ppf fold env lid =
  soit cutoff =
    filtre String.length (Longident.last lid) avec
      | 1 | 2 -> 0
      | 3 | 4 -> 1
      | 5 | 6 -> 2
      | _ -> 3
  dans
  soit compare target head acc =
    soit (best_choice, best_dist) = acc dans
    filtre Misc.edit_distance target head cutoff avec
      | None -> (best_choice, best_dist)
      | Some dist ->
        soit choice =
          si dist < best_dist alors [head]
          sinon si dist = best_dist alors head :: best_choice
          sinon best_choice dans
        (choice, min dist best_dist)
  dans
  soit init = ([], max_int) dans
  soit handle (choice, _dist) =
    filtre List.rev choice avec
      | [] -> ()
      | last :: rev_rest ->
        fprintf ppf "@\nIndice : vouliez-vous dire %s%s%s?"
          (String.concat ", " (List.rev rev_rest))
          (si rev_rest = [] alors "" sinon " or ")
          last
  dans
  (* flush now to get the error report early, in the (unheard of) case
     where the linear search would take a bit of time; in the worst
     case, the user has seen the error, she can interrupt the process
     before the spell-checking terminates. *)
  fprintf ppf "@?";
  filtre lid avec
    | Longident.Lapply _ -> ()
    | Longident.Lident s ->
      handle (fold (compare s) None env init)
    | Longident.Ldot (r, s) ->
      handle (fold (compare s) (Some r) env init)

soit spellcheck_simple ppf fold extr =
  spellcheck ppf (fonc f -> fold (fonc decl x -> f (extr decl) x))

soit spellcheck ppf fold =
  spellcheck ppf (fonc f -> fold (fonc s _ _ x -> f s x))

type cd = string list * int

soit report_error env ppf = fonction
  | Unbound_type_variable name ->
    fprintf ppf "Paramètre de type non lié %s@." name
  | Unbound_type_constructor lid ->
    fprintf ppf "Constructeur de type non lié %a" longident lid;
    spellcheck ppf Env.fold_types env lid;
  | Unbound_type_constructor_2 p ->
    fprintf ppf "Le constructeur de type@ %a@ n'est pas encore complètement défini"
      path p
  | Type_arity_mismatch(lid, expected, provided) ->
    fprintf ppf
      "@[Le constructeur de type %a@ attend %i argument(s),@ \
        mais est appliqué ici à %i argument(s)@]"
      longident lid expected provided
  | Bound_type_variable name ->
    fprintf ppf "Le paramètre de type '%s est déjà lié" name
  | Recursive_type ->
    fprintf ppf "Ce type est récursif"
  | Unbound_row_variable lid ->
      (* we don't use "spellcheck" here: this error is not raised
         anywhere so it's unclear how it should be handled *)
      fprintf ppf "Variable de rangée non liée dans #%a" longident lid
  | Type_mismatch trace ->
      Printtyp.report_unification_error ppf Env.empty trace
        (fonction ppf ->
           fprintf ppf "Le type")
        (fonction ppf ->
           fprintf ppf "devrait être une instance du type")
  | Alias_type_mismatch trace ->
      Printtyp.report_unification_error ppf Env.empty trace
        (fonction ppf ->
           fprintf ppf "Cet alias est lié au type")
        (fonction ppf ->
           fprintf ppf "mais est utilisé comme instance du type")
  | Present_has_conjunction l ->
      fprintf ppf "Le constructeur présent %s a un type conjonctif" l
  | Present_has_no_type l ->
      fprintf ppf "Le constructeur présent %s n'a pas de type" l
  | Constructor_mismatch (ty, ty') ->
      wrap_printing_env env (fonc ()  ->
	Printtyp.reset_and_mark_loops_list [ty; ty'];
	fprintf ppf "@[<hov>%s %a@ %s@ %a@]"
          "Ce type somme contient un constructeur"
          Printtyp.type_expr ty
          "qui devrait être"
          Printtyp.type_expr ty')
  | Not_a_variant ty ->
      Printtyp.reset_and_mark_loops ty;
      fprintf ppf "@[Le type %a@ n'est pas un type somme polymorphe@]"
        Printtyp.type_expr ty
  | Variant_tags (lab1, lab2) ->
      fprintf ppf
        "@[Les tags de type somme `%s@ et `%s ont la même valeur de hachage.@ %s@]"
        lab1 lab2 "Changez l'un d'entre eux."
  | Invalid_variable_name name ->
      fprintf ppf "Le nom de varible de type %s n'est pas autorisé dans les programmes" name
  | Cannot_quantify (name, v) ->
      fprintf ppf
        "@[<hov>La variable de type universelle '%s ne peut pas être généralisée :@ %s.@]"
        name
        (si Btype.is_Tvar v alors "elle s'échappe de sa portée" sinon
         si Btype.is_Tunivar v alors "elle est déjà liée a une autre variable"
         sinon "elle n'est pas une variable")
  | Multiple_constraints_on_type s ->
      fprintf ppf "Plusieurs contraintes pour le type %a" longident s
  | Repeated_method_label s ->
      fprintf ppf "@[Ceci est la seconde méthode `%s' de ce type d'objet.@ %s@]"
        s "Les occurences multiples ne sont pas autorisées."
  | Unbound_value lid ->
      fprintf ppf "Valeur non liée %a" longident lid;
      spellcheck ppf Env.fold_values env lid;
  | Unbound_module lid ->
      fprintf ppf "Module non lié %a" longident lid;
      spellcheck ppf Env.fold_modules env lid;
  | Unbound_constructor lid ->
      fprintf ppf "Constructeur non lié %a" longident lid;
      spellcheck_simple ppf Env.fold_constructors (fonc d -> d.cstr_name)
	env lid;
  | Unbound_label lid ->
      fprintf ppf "Champ d'enregistrement non lié %a" longident lid;
      spellcheck_simple ppf Env.fold_labels (fonc d -> d.lbl_name) env lid;
  | Unbound_class lid ->
      fprintf ppf "Classe non liée %a" longident lid;
      spellcheck ppf Env.fold_classs env lid;
  | Unbound_modtype lid ->
      fprintf ppf "Type de module non lié %a" longident lid;
      spellcheck ppf Env.fold_modtypes env lid;
  | Unbound_cltype lid ->
      fprintf ppf "Type de classe non lié %a" longident lid;
      spellcheck ppf Env.fold_cltypes env lid;
  | Ill_typed_functor_application lid ->
      fprintf ppf "Application de foncteur mal typée %a" longident lid
  | Illegal_reference_to_recursive_module ->
      fprintf ppf "Référence à un module récursif illégale"
  | Extension s ->
      fprintf ppf "Extension non interprétée '%s'." s

soit () =
  Location.register_error_of_exn
    (fonction
      | Error (loc, env, err) ->
        Some (Location.error_of_printer loc (report_error env) err)
      | _ ->
        None
    )

