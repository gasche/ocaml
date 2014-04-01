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

(* Typechecking for the core language *)

ouvre Misc
ouvre Asttypes
ouvre Parsetree
ouvre Types
ouvre Typedtree
ouvre Btype
ouvre Ctype

type error =
    Polymorphic_label de Longident.t
  | Constructor_arity_mismatch de Longident.t * int * int
  | Label_mismatch de Longident.t * (type_expr * type_expr) list
  | Pattern_type_clash de (type_expr * type_expr) list
  | Or_pattern_type_clash de Ident.t * (type_expr * type_expr) list
  | Multiply_bound_variable de string
  | Orpat_vars de Ident.t
  | Expr_type_clash de (type_expr * type_expr) list
  | Apply_non_function de type_expr
  | Apply_wrong_label de label * type_expr
  | Label_multiply_defined de string
  | Label_missing de Ident.t list
  | Label_not_mutable de Longident.t
  | Wrong_name de string * type_expr * string * Path.t * Longident.t
  | Name_type_mismatch de
      string * Longident.t * (Path.t * Path.t) * (Path.t * Path.t) list
  | Incomplete_format de string
  | Bad_conversion de string * int * char
  | Undefined_method de type_expr * string
  | Undefined_inherited_method de string
  | Virtual_class de Longident.t
  | Private_type de type_expr
  | Private_label de Longident.t * type_expr
  | Unbound_instance_variable de string
  | Instance_variable_not_mutable de bool * string
  | Not_subtype de (type_expr * type_expr) list * (type_expr * type_expr) list
  | Outside_class
  | Value_multiply_overridden de string
  | Coercion_failure de
      type_expr * type_expr * (type_expr * type_expr) list * bool
  | Too_many_arguments de bool * type_expr
  | Abstract_wrong_label de label * type_expr
  | Scoping_let_module de string * type_expr
  | Masked_instance_variable de Longident.t
  | Not_a_variant_type de Longident.t
  | Incoherent_label_order
  | Less_general de string * (type_expr * type_expr) list
  | Modules_not_allowed
  | Cannot_infer_signature
  | Not_a_packed_module de type_expr
  | Recursive_local_constraint de (type_expr * type_expr) list
  | Unexpected_existential
  | Unqualified_gadt_pattern de Path.t * string
  | Invalid_interval
  | Invalid_for_loop_index
  | Extension de string

exception Error de Location.t * Env.t * error

(* Forward declaration, to be filled in by Typemod.type_module *)

soit type_module =
  ref ((fonc env md -> affirme faux) :
       Env.t -> Parsetree.module_expr -> Typedtree.module_expr)

(* Forward declaration, to be filled in by Typemod.type_open *)

soit type_open =
  ref (fonc _ -> affirme faux)

(* Forward declaration, to be filled in by Typemod.type_package *)

soit type_package =
  ref (fonc _ -> affirme faux)

(* Forward declaration, to be filled in by Typeclass.class_structure *)
soit type_object =
  ref (fonc env s -> affirme faux :
       Env.t -> Location.t -> Parsetree.class_structure ->
         Typedtree.class_structure * Types.class_signature * string list)

(*
  Saving and outputting type information.
  We keep these function names short, because they have to be
  called each time we create a record of type [Typedtree.expression]
  or [Typedtree.pattern] that will end up in the typed AST.
*)
soit re node =
  Cmt_format.add_saved_type (Cmt_format.Partial_expression node);
  Stypes.record (Stypes.Ti_expr node);
  node
;;
soit rp node =
  Cmt_format.add_saved_type (Cmt_format.Partial_pattern node);
  Stypes.record (Stypes.Ti_pat node);
  node
;;


soit fst3 (x, _, _) = x
soit snd3 (_,x,_) = x

soit case lhs rhs =
  {c_lhs = lhs; c_guard = None; c_rhs = rhs}

(* Upper approximation of free identifiers on the parse tree *)

soit iter_expression f e =

  soit rec expr e =
    f e;
    filtre e.pexp_desc avec
    | Pexp_extension _ (* we don't iterate under extension point *)
    | Pexp_ident _
    | Pexp_new _
    | Pexp_constant _ -> ()
    | Pexp_function pel -> List.iter case pel
    | Pexp_fun (_, eo, _, e) -> may expr eo; expr e
    | Pexp_apply (e, lel) -> expr e; List.iter (fonc (_, e) -> expr e) lel
    | Pexp_let (_, pel, e) ->  expr e; List.iter binding pel
    | Pexp_match (e, pel)
    | Pexp_try (e, pel) -> expr e; List.iter case pel
    | Pexp_array el
    | Pexp_tuple el -> List.iter expr el
    | Pexp_construct (_, eo)
    | Pexp_variant (_, eo) -> may expr eo
    | Pexp_record (iel, eo) ->
        may expr eo; List.iter (fonc (_, e) -> expr e) iel
    | Pexp_open (_, _, e)
    | Pexp_newtype (_, e)
    | Pexp_poly (e, _)
    | Pexp_lazy e
    | Pexp_assert e
    | Pexp_setinstvar (_, e)
    | Pexp_send (e, _)
    | Pexp_constraint (e, _)
    | Pexp_coerce (e, _, _)
    | Pexp_field (e, _) -> expr e
    | Pexp_while (e1, e2)
    | Pexp_sequence (e1, e2)
    | Pexp_setfield (e1, _, e2) -> expr e1; expr e2
    | Pexp_ifthenelse (e1, e2, eo) -> expr e1; expr e2; may expr eo
    | Pexp_for (_, e1, e2, _, e3) -> expr e1; expr e2; expr e3
    | Pexp_override sel -> List.iter (fonc (_, e) -> expr e) sel
    | Pexp_letmodule (_, me, e) -> expr e; module_expr me
    | Pexp_object { pcstr_fields = fs } -> List.iter class_field fs
    | Pexp_pack me -> module_expr me

  et case {pc_lhs = _; pc_guard; pc_rhs} =
    may expr pc_guard;
    expr pc_rhs

  et binding x =
    expr x.pvb_expr

  et module_expr me =
    filtre me.pmod_desc avec
    | Pmod_extension _
    | Pmod_ident _ -> ()
    | Pmod_structure str -> List.iter structure_item str
    | Pmod_constraint (me, _)
    | Pmod_functor (_, _, me) -> module_expr me
    | Pmod_apply (me1, me2) -> module_expr me1; module_expr me2
    | Pmod_unpack e -> expr e


  et structure_item str =
    filtre str.pstr_desc avec
    | Pstr_eval (e, _) -> expr e
    | Pstr_value (_, pel) -> List.iter binding pel
    | Pstr_primitive _
    | Pstr_type _
    | Pstr_exception _
    | Pstr_modtype _
    | Pstr_open _
    | Pstr_class_type _
    | Pstr_attribute _
    | Pstr_extension _
    | Pstr_exn_rebind _ -> ()
    | Pstr_include (me, _)
    | Pstr_module {pmb_expr = me} -> module_expr me
    | Pstr_recmodule l -> List.iter (fonc x -> module_expr x.pmb_expr) l
    | Pstr_class cdl -> List.iter (fonc c -> class_expr c.pci_expr) cdl

  et class_expr ce =
    filtre ce.pcl_desc avec
    | Pcl_constr _ -> ()
    | Pcl_structure { pcstr_fields = fs } -> List.iter class_field fs
    | Pcl_fun (_, eo, _,  ce) -> may expr eo; class_expr ce
    | Pcl_apply (ce, lel) ->
        class_expr ce; List.iter (fonc (_, e) -> expr e) lel
    | Pcl_let (_, pel, ce) ->
        List.iter binding pel; class_expr ce
    | Pcl_constraint (ce, _) -> class_expr ce
    | Pcl_extension _ -> ()

  et class_field cf =
    filtre cf.pcf_desc avec
    | Pcf_inherit (_, ce, _) -> class_expr ce
    | Pcf_val (_, _, Cfk_virtual _)
    | Pcf_method (_, _, Cfk_virtual _ ) | Pcf_constraint _ -> ()
    | Pcf_val (_, _, Cfk_concrete (_, e))
    | Pcf_method (_, _, Cfk_concrete (_, e)) -> expr e
    | Pcf_initializer e -> expr e
    | Pcf_extension _ -> ()

  dans
  expr e


soit all_idents_cases el =
  soit idents = Hashtbl.create 8 dans
  soit f = fonction
    | {pexp_desc=Pexp_ident { txt = Longident.Lident id; _ }; _} ->
        Hashtbl.replace idents id ()
    | _ -> ()
  dans
  List.iter
    (fonc cp ->
      may (iter_expression f) cp.pc_guard;
      iter_expression f cp.pc_rhs
    )
    el;
  Hashtbl.fold (fonc x () rest -> x :: rest) idents []


(* Typing of constants *)

soit type_constant = fonction
    Const_int _ -> instance_def Predef.type_int
  | Const_char _ -> instance_def Predef.type_char
  | Const_string _ -> instance_def Predef.type_string
  | Const_float _ -> instance_def Predef.type_float
  | Const_int32 _ -> instance_def Predef.type_int32
  | Const_int64 _ -> instance_def Predef.type_int64
  | Const_nativeint _ -> instance_def Predef.type_nativeint

(* Specific version of type_option, using newty rather than newgenty *)

soit type_option ty =
  newty (Tconstr(Predef.path_option,[ty], ref Mnil))

soit mkexp exp_desc exp_type exp_loc exp_env =
  { exp_desc; exp_type; exp_loc; exp_env; exp_extra = []; exp_attributes = [] }

soit option_none ty loc =
  soit lid = Longident.Lident "None" dans
  soit cnone = Env.lookup_constructor lid Env.initial dans
  mkexp (Texp_construct(mknoloc lid, cnone, []))
    ty loc Env.initial

soit option_some texp =
  soit lid = Longident.Lident "Some" dans
  soit csome = Env.lookup_constructor lid Env.initial dans
  mkexp ( Texp_construct(mknoloc lid , csome, [texp]) )
    (type_option texp.exp_type) texp.exp_loc texp.exp_env

soit extract_option_type env ty =
  filtre expand_head env ty avec {desc = Tconstr(path, [ty], _)}
    quand Path.same path Predef.path_option -> ty
  | _ -> affirme faux

soit extract_concrete_record env ty =
  filtre extract_concrete_typedecl env ty avec
    (p0, p, {type_kind=Type_record (fields, _)}) -> (p0, p, fields)
  | _ -> raise Not_found

soit extract_concrete_variant env ty =
  filtre extract_concrete_typedecl env ty avec
    (* exclude exceptions *)
    (p0, p, {type_kind=Type_variant (_::_ tel cstrs)}) -> (p0, p, cstrs)
  | _ -> raise Not_found

soit extract_label_names sexp env ty =
  essaie
    soit (_, _,fields) = extract_concrete_record env ty dans
    List.map (fonc l -> l.Types.ld_id) fields
  avec Not_found ->
    affirme faux

(* Typing of patterns *)

(* unification inside type_pat*)
soit unify_pat_types loc env ty ty' =
  essaie
    unify env ty ty'
  avec
    Unify trace ->
      raise(Error(loc, env, Pattern_type_clash(trace)))
  | Tags(l1,l2) ->
      raise(Typetexp.Error(loc, env, Typetexp.Variant_tags (l1, l2)))

(* unification inside type_exp and type_expect *)
soit unify_exp_types loc env ty expected_ty =
  (* Format.eprintf "@[%a@ %a@]@." Printtyp.raw_type_expr exp.exp_type
    Printtyp.raw_type_expr expected_ty; *)
  essaie
    unify env ty expected_ty
  avec
    Unify trace ->
      raise(Error(loc, env, Expr_type_clash(trace)))
  | Tags(l1,l2) ->
      raise(Typetexp.Error(loc, env, Typetexp.Variant_tags (l1, l2)))

(* level at which to create the local type declarations *)
soit newtype_level = ref None
soit get_newtype_level () =
  filtre !newtype_level avec
    Some y -> y
  | None -> affirme faux

soit unify_pat_types_gadt loc env ty ty' =
  soit newtype_level =
    filtre !newtype_level avec
    | None -> affirme faux
    | Some x -> x
  dans
  essaie
    unify_gadt ~newtype_level env ty ty'
  avec
    Unify trace ->
      raise(Error(loc, !env, Pattern_type_clash(trace)))
  | Tags(l1,l2) ->
      raise(Typetexp.Error(loc, !env, Typetexp.Variant_tags (l1, l2)))
  | Unification_recursive_abbrev trace ->
      raise(Error(loc, !env, Recursive_local_constraint trace))


(* Creating new conjunctive types is not allowed when typing patterns *)

soit unify_pat env pat expected_ty =
  unify_pat_types pat.pat_loc env pat.pat_type expected_ty

(* make all Reither present in open variants *)
soit finalize_variant pat =
  filtre pat.pat_desc avec
    Tpat_variant(tag, opat, r) ->
      soit row =
        filtre expand_head pat.pat_env pat.pat_type avec
          {desc = Tvariant row} -> r := row; row_repr row
        | _ -> affirme faux
      dans
      début filtre row_field tag row avec
      | Rabsent -> () (* assert false *)
      | Reither (vrai, [], _, e) quand not row.row_closed ->
          set_row_field e (Rpresent None)
      | Reither (faux, ty::tl, _, e) quand not row.row_closed ->
          set_row_field e (Rpresent (Some ty));
          début filtre opat avec None -> affirme faux
          | Some pat -> List.iter (unify_pat pat.pat_env pat) (ty::tl)
          fin
      | Reither (c, l, vrai, e) quand not (row_fixed row) ->
          set_row_field e (Reither (c, [], faux, ref None))
      | _ -> ()
      fin;
      (* Force check of well-formedness   WHY? *)
      (* unify_pat pat.pat_env pat
        (newty(Tvariant{row_fields=[]; row_more=newvar(); row_closed=false;
                        row_bound=(); row_fixed=false; row_name=None})); *)
  | _ -> ()

soit rec iter_pattern f p =
  f p;
  iter_pattern_desc (iter_pattern f) p.pat_desc

soit has_variants p =
  essaie
    iter_pattern (fonction {pat_desc=Tpat_variant _} -> raise Exit | _ -> ())
      p;
    faux
  avec Exit ->
    vrai


(* pattern environment *)
soit pattern_variables = ref ([] :
 (Ident.t * type_expr * string loc * Location.t * bool (* as-variable *)) list)
soit pattern_force = ref ([] : (unit -> unit) list)
soit pattern_scope = ref (None : Annot.ident option);;
soit allow_modules = ref faux
soit module_variables = ref ([] : (string loc * Location.t) list)
soit reset_pattern scope allow =
  pattern_variables := [];
  pattern_force := [];
  pattern_scope := scope;
  allow_modules := allow;
  module_variables := [];
;;

soit enter_variable ?(is_module=faux) ?(is_as_variable=faux) loc name ty =
  si List.exists (fonc (id, _, _, _, _) -> Ident.name id = name.txt)
      !pattern_variables
  alors raise(Error(loc, Env.empty, Multiply_bound_variable name.txt));
  soit id = Ident.create name.txt dans
  pattern_variables :=
    (id, ty, name, loc, is_as_variable) :: !pattern_variables;
  si is_module alors début
    (* Note: unpack patterns enter a variable of the same name *)
    si not !allow_modules alors
      raise (Error (loc, Env.empty, Modules_not_allowed));
    module_variables := (name, loc) :: !module_variables
  fin sinon
    (* moved to genannot *)
    may (fonc s -> Stypes.record (Stypes.An_ident (name.loc, name.txt, s)))
        !pattern_scope;
  id

soit sort_pattern_variables vs =
  List.sort
    (fonc (x,_,_,_,_) (y,_,_,_,_) ->
      Pervasives.compare (Ident.name x) (Ident.name y))
    vs

soit enter_orpat_variables loc env  p1_vs p2_vs =
  (* unify_vars operate on sorted lists *)

  soit p1_vs = sort_pattern_variables p1_vs
  et p2_vs = sort_pattern_variables p2_vs dans

  soit rec unify_vars p1_vs p2_vs = filtre p1_vs, p2_vs avec
      | (x1,t1,_,l1,a1)::rem1, (x2,t2,_,l2,a2)::rem2 quand Ident.equal x1 x2 ->
          si x1==x2 alors
            unify_vars rem1 rem2
          sinon début
            début essaie
              unify env t1 t2
            avec
            | Unify trace ->
                raise(Error(loc, env, Or_pattern_type_clash(x1, trace)))
            fin;
          (x2,x1)::unify_vars rem1 rem2
          fin
      | [],[] -> []
      | (x,_,_,_,_)::_, [] -> raise (Error (loc, env, Orpat_vars x))
      | [],(x,_,_,_,_)::_  -> raise (Error (loc, env, Orpat_vars x))
      | (x,_,_,_,_)::_, (y,_,_,_,_)::_ ->
          soit min_var =
            si Ident.name x < Ident.name y alors x
            sinon y dans
          raise (Error (loc, env, Orpat_vars min_var)) dans
  unify_vars p1_vs p2_vs

soit rec build_as_type env p =
  filtre p.pat_desc avec
    Tpat_alias(p1,_, _) -> build_as_type env p1
  | Tpat_tuple pl ->
      soit tyl = List.map (build_as_type env) pl dans
      newty (Ttuple tyl)
  | Tpat_construct(_, cstr, pl) ->
      soit keep = cstr.cstr_private = Private || cstr.cstr_existentials <> [] dans
      si keep alors p.pat_type sinon
      soit tyl = List.map (build_as_type env) pl dans
      soit ty_args, ty_res = instance_constructor cstr dans
      List.iter2 (fonc (p,ty) -> unify_pat env {p avec pat_type = ty})
        (List.combine pl tyl) ty_args;
      ty_res
  | Tpat_variant(l, p', _) ->
      soit ty = may_map (build_as_type env) p' dans
      newty (Tvariant{row_fields=[l, Rpresent ty]; row_more=newvar();
                      row_bound=(); row_name=None;
                      row_fixed=faux; row_closed=faux})
  | Tpat_record (lpl,_) ->
      soit lbl = snd3 (List.hd lpl) dans
      si lbl.lbl_private = Private alors p.pat_type sinon
      soit ty = newvar () dans
      soit ppl = List.map (fonc (_, l, p) -> l.lbl_pos, p) lpl dans
      soit do_label lbl =
        soit _, ty_arg, ty_res = instance_label faux lbl dans
        unify_pat env {p avec pat_type = ty} ty_res;
        soit refinable =
          lbl.lbl_mut = Immutable && List.mem_assoc lbl.lbl_pos ppl &&
          filtre (repr lbl.lbl_arg).desc avec Tpoly _ -> faux | _ -> vrai dans
        si refinable alors début
          soit arg = List.assoc lbl.lbl_pos ppl dans
          unify_pat env {arg avec pat_type = build_as_type env arg} ty_arg
        fin sinon début
          soit _, ty_arg', ty_res' = instance_label faux lbl dans
          unify env ty_arg ty_arg';
          unify_pat env p ty_res'
        fin dans
      Array.iter do_label lbl.lbl_all;
      ty
  | Tpat_or(p1, p2, row) ->
      début filtre row avec
        None ->
          soit ty1 = build_as_type env p1 et ty2 = build_as_type env p2 dans
          unify_pat env {p2 avec pat_type = ty2} ty1;
          ty1
      | Some row ->
          soit row = row_repr row dans
          newty (Tvariant{row avec row_closed=faux; row_more=newvar()})
      fin
  | Tpat_any | Tpat_var _ | Tpat_constant _
  | Tpat_array _ | Tpat_lazy _ -> p.pat_type

soit build_or_pat env loc lid =
  soit path, decl = Typetexp.find_type env loc lid
  dans
  soit tyl = List.map (fonc _ -> newvar()) decl.type_params dans
  soit row0 =
    soit ty = expand_head env (newty(Tconstr(path, tyl, ref Mnil))) dans
    filtre ty.desc avec
      Tvariant row quand static_row row -> row
    | _ -> raise(Error(loc, env, Not_a_variant_type lid))
  dans
  soit pats, fields =
    List.fold_left
      (fonc (pats,fields) (l,f) ->
        filtre row_field_repr f avec
          Rpresent None ->
            (l,None) :: pats,
            (l, Reither(vrai,[], vrai, ref None)) :: fields
        | Rpresent (Some ty) ->
            (l, Some {pat_desc=Tpat_any; pat_loc=Location.none; pat_env=env;
                      pat_type=ty; pat_extra=[]; pat_attributes=[]})
            :: pats,
            (l, Reither(faux, [ty], vrai, ref None)) :: fields
        | _ -> pats, fields)
      ([],[]) (row_repr row0).row_fields dans
  soit row =
    { row_fields = List.rev fields; row_more = newvar(); row_bound = ();
      row_closed = faux; row_fixed = faux; row_name = Some (path, tyl) }
  dans
  soit ty = newty (Tvariant row) dans
  soit gloc = {loc avec Location.loc_ghost=vrai} dans
  soit row' = ref {row avec row_more=newvar()} dans
  soit pats =
    List.map
      (fonc (l,p) ->
        {pat_desc=Tpat_variant(l,p,row'); pat_loc=gloc;
         pat_env=env; pat_type=ty; pat_extra=[]; pat_attributes=[]})
      pats
  dans
  filtre pats avec
    [] -> raise(Error(loc, env, Not_a_variant_type lid))
  | pat :: pats ->
      soit r =
        List.fold_left
          (fonc pat pat0 ->
            {pat_desc=Tpat_or(pat0,pat,Some row0); pat_extra=[];
             pat_loc=gloc; pat_env=env; pat_type=ty; pat_attributes=[]})
          pat pats dans
      (path, rp { r avec pat_loc = loc },ty)

(* Type paths *)

soit rec expand_path env p =
  soit decl =
    essaie Some (Env.find_type p env) avec Not_found -> None
  dans
  filtre decl avec
    Some {type_manifest = Some ty} ->
      début filtre repr ty avec
        {desc=Tconstr(p,_,_)} -> expand_path env p
      | _ -> affirme faux
      fin
  | _ ->
      soit p' = Env.normalize_path None env p dans
      si Path.same p p' alors p sinon expand_path env p'

soit compare_type_path env tpath1 tpath2 =
  Path.same (expand_path env tpath1) (expand_path env tpath2)

(* Records *)

module NameChoice(Name : sig
  type t
  val type_kind: string
  val get_name: t -> string
  val get_type: t -> type_expr
  val get_descrs: Env.type_descriptions -> t list
  val fold: (t -> 'a -> 'a) -> Longident.t option -> Env.t -> 'a -> 'a
  val unbound_name_error: Env.t -> Longident.t loc -> 'a
fin) = struct
  ouvre Name

  soit get_type_path env d =
    filtre (get_type d).desc avec
    | Tconstr(p, _, _) -> p
    | _ -> affirme faux

  soit spellcheck ppf env p lid =
    Typetexp.spellcheck_simple ppf fold
      (fonc d ->
        si compare_type_path env p (get_type_path env d)
        alors get_name d sinon "") env lid

  soit lookup_from_type env tpath lid =
    soit descrs = get_descrs (Env.find_type_descrs tpath env) dans
    Env.mark_type_used (Path.last tpath) (Env.find_type tpath env);
    filtre lid.txt avec
      Longident.Lident s -> début
        essaie
          List.find (fonc nd -> get_name nd = s) descrs
        avec Not_found ->
          raise (Error (lid.loc, env,
                        Wrong_name ("", newvar (), type_kind, tpath, lid.txt)))
      fin
    | _ -> raise Not_found

  soit rec unique eq acc = fonction
      [] -> List.rev acc
    | x :: rem ->
        si List.exists (eq x) acc alors unique eq acc rem
        sinon unique eq (x :: acc) rem

  soit ambiguous_types env lbl others =
    soit tpath = get_type_path env lbl dans
    soit others =
      List.map (fonc (lbl, _) -> get_type_path env lbl) others dans
    soit tpaths = unique (compare_type_path env) [tpath] others dans
    filtre tpaths avec
      [_] -> []
    | _ -> List.map Printtyp.string_of_path tpaths

  soit disambiguate_by_type env tpath lbls =
    soit check_type (lbl, _) =
      soit lbl_tpath = get_type_path env lbl dans
      compare_type_path env tpath lbl_tpath
    dans
    List.find check_type lbls

  soit disambiguate ?(warn=Location.prerr_warning) ?(check_lk=fonc _ _ -> ())
      ?scope lid env opath lbls =
    soit scope = filtre scope avec None -> lbls | Some l -> l dans
    soit lbl = filtre opath avec
      None ->
        début filtre lbls avec
          [] -> unbound_name_error env lid
        | (lbl, use) :: rest ->
            use ();
            soit paths = ambiguous_types env lbl rest dans
            si paths <> [] alors
              warn lid.loc
                (Warnings.Ambiguous_name ([Longident.last lid.txt],
                                          paths, faux));
            lbl
        fin
    | Some(tpath0, tpath, pr) ->
        soit warn_pr () =
          soit kind = si type_kind = "enregistrement" alors "champ" sinon "constructeur" dans
          warn lid.loc
            (Warnings.Not_principal
               ("cette désambiguïsation de " ^ kind ^ " utilisant les types"))
        dans
        essaie
          soit lbl, use = disambiguate_by_type env tpath scope dans
          use ();
          si not pr alors début
            (* Check if non-principal type is affecting result *)
            filtre lbls avec
              [] -> warn_pr ()
            | (lbl', use') :: rest ->
                soit lbl_tpath = get_type_path env lbl' dans
                si not (compare_type_path env tpath lbl_tpath) alors warn_pr ()
                sinon
                  soit paths = ambiguous_types env lbl rest dans
                  si paths <> [] alors
                    warn lid.loc
                      (Warnings.Ambiguous_name ([Longident.last lid.txt],
                                                paths, faux))
          fin;
          lbl
        avec Not_found -> essaie
          soit lbl = lookup_from_type env tpath lid dans
          check_lk tpath lbl;
          soit s = Printtyp.string_of_path tpath dans
          warn lid.loc
            (Warnings.Name_out_of_scope (s, [Longident.last lid.txt], faux));
          si not pr alors warn_pr ();
          lbl
        avec Not_found ->
          si lbls = [] alors unbound_name_error env lid sinon
          soit tp = (tpath0, expand_path env tpath) dans
          soit tpl =
            List.map
              (fonc (lbl, _) ->
                soit tp0 = get_type_path env lbl dans
                soit tp = expand_path env tp0 dans
                  (tp0, tp))
              lbls
          dans
          raise (Error (lid.loc, env,
                        Name_type_mismatch (type_kind, lid.txt, tp, tpl)))
    dans
    début filtre scope avec
      (lab1,_)::_ quand lab1 == lbl -> ()
    | _ ->
        Location.prerr_warning lid.loc
          (Warnings.Disambiguated_name(get_name lbl))
    fin;
    lbl
fin

soit wrap_disambiguate kind ty f x =
  essaie f x avec Error (loc, env, Wrong_name (_,_,tk,tp,lid)) ->
    raise (Error (loc, env, Wrong_name (kind,ty,tk,tp,lid)))

module Label = NameChoice (struct
  type t = label_description
  soit type_kind = "enregistrement"
  soit get_name lbl = lbl.lbl_name
  soit get_type lbl = lbl.lbl_res
  soit get_descrs = snd
  soit fold = Env.fold_labels
  soit unbound_name_error = Typetexp.unbound_label_error
fin)

soit disambiguate_label_by_ids keep env closed ids labels =
  soit check_ids (lbl, _) =
    soit lbls = Hashtbl.create 8 dans
    Array.iter (fonc lbl -> Hashtbl.add lbls lbl.lbl_name ()) lbl.lbl_all;
    List.for_all (Hashtbl.mem lbls) ids
  et check_closed (lbl, _) =
    (not closed || List.length ids = Array.length lbl.lbl_all)
  dans
  soit labels' = List.filter check_ids labels dans
  si keep && labels' = [] alors (faux, labels) sinon
  soit labels'' = List.filter check_closed labels' dans
  si keep && labels'' = [] alors (faux, labels') sinon (vrai, labels'')

(* Only issue warnings once per record constructor/pattern *)
soit disambiguate_lid_a_list loc closed env opath lid_a_list =
  soit ids = List.map (fonc (lid, _) -> Longident.last lid.txt) lid_a_list dans
  soit w_pr = ref faux et w_amb = ref []
  et w_scope = ref [] et w_scope_ty = ref "" dans
  soit warn loc msg =
    soit ouvre Warnings dans
    filtre msg avec
    | Not_principal _ -> w_pr := vrai
    | Ambiguous_name([s], l, _) -> w_amb := (s, l) :: !w_amb
    | Name_out_of_scope(ty, [s], _) ->
        w_scope := s :: !w_scope; w_scope_ty := ty
    | _ -> Location.prerr_warning loc msg
  dans
  soit process_label lid =
    (* Strategy for each field:
       * collect all the labels in scope for that name
       * if the type is known and principal, just eventually warn
         if the real label was not in scope
       * fail if there is no known type and no label found
       * otherwise use other fields to reduce the list of candidates
       * if there is no known type reduce it incrementally, so that
         there is still at least one candidate (for error message)
       * if the reduced list is valid, call Label.disambiguate
     *)
    soit scope = Typetexp.find_all_labels env lid.loc lid.txt dans
    si opath = None && scope = [] alors
      Typetexp.unbound_label_error env lid;
    soit (ok, labels) =
      filtre opath avec
        Some (_, _, vrai) -> (vrai, scope) (* disambiguate only checks scope *)
      | _  -> disambiguate_label_by_ids (opath=None) env closed ids scope
    dans
    si ok alors Label.disambiguate lid env opath labels ~warn ~scope
          sinon fst (List.hd labels) (* will fail later *)
  dans
  soit lbl_a_list =
    List.map (fonc (lid,a) -> lid, process_label lid, a) lid_a_list dans
  si !w_pr alors
    Location.prerr_warning loc
      (Warnings.Not_principal "cette désambiguïsation d'enregistrement utilisant les types")
  sinon début
    filtre List.rev !w_amb avec
      (_,types)::others tel amb ->
        soit paths =
          List.map (fonc (_,lbl,_) -> Label.get_type_path env lbl) lbl_a_list dans
        soit path = List.hd paths dans
        si List.for_all (compare_type_path env path) (List.tl paths) alors
          Location.prerr_warning loc
            (Warnings.Ambiguous_name (List.map fst amb, types, vrai))
        sinon
          List.iter
            (fonc (s,l) -> Location.prerr_warning loc
                (Warnings.Ambiguous_name ([s],l,faux)))
            amb
    | _ -> ()
  fin;
  si !w_scope <> [] alors
    Location.prerr_warning loc
      (Warnings.Name_out_of_scope (!w_scope_ty, List.rev !w_scope, vrai));
  lbl_a_list

soit rec find_record_qual = fonction
  | [] -> None
  | ({ txt = Longident.Ldot (modname, _) }, _) :: _ -> Some modname
  | _ :: rest -> find_record_qual rest

soit type_label_a_list ?labels loc closed env type_lbl_a opath lid_a_list =
  soit lbl_a_list =
    filtre lid_a_list, labels avec
      ({txt=Longident.Lident s}, _)::_, Some labels quand Hashtbl.mem labels s ->
        (* Special case for rebuilt syntax trees *)
        List.map
          (fonction lid, a -> filtre lid.txt avec
            Longident.Lident s -> lid, Hashtbl.find labels s, a
          | _ -> affirme faux)
          lid_a_list
    | _ ->
        soit lid_a_list =
          filtre find_record_qual lid_a_list avec
            None -> lid_a_list
          | Some modname ->
              List.map
                (fonc (lid, a tel lid_a) ->
                  filtre lid.txt avec Longident.Lident s ->
                    {lid avec txt=Longident.Ldot (modname, s)}, a
                  | _ -> lid_a)
                lid_a_list
        dans
        disambiguate_lid_a_list loc closed env opath lid_a_list
  dans
  (* Invariant: records are sorted in the typed tree *)
  soit lbl_a_list =
    List.sort
      (fonc (_,lbl1,_) (_,lbl2,_) -> compare lbl1.lbl_pos lbl2.lbl_pos)
      lbl_a_list
  dans
  List.map type_lbl_a lbl_a_list
;;

(* Checks over the labels mentioned in a record pattern:
   no duplicate definitions (error); properly closed (warning) *)

soit check_recordpat_labels loc lbl_pat_list closed =
  filtre lbl_pat_list avec
  | [] -> ()                            (* should not happen *)
  | (_, label1, _) :: _ ->
      soit all = label1.lbl_all dans
      soit defined = Array.make (Array.length all) faux dans
      soit check_defined (_, label, _) =
        si defined.(label.lbl_pos)
        alors raise(Error(loc, Env.empty, Label_multiply_defined label.lbl_name))
        sinon defined.(label.lbl_pos) <- vrai dans
      List.iter check_defined lbl_pat_list;
      si closed = Closed
      && Warnings.is_active (Warnings.Non_closed_record_pattern "")
      alors début
        soit undefined = ref [] dans
        pour i = 0 à Array.length all - 1 faire
          si not defined.(i) alors undefined := all.(i).lbl_name :: !undefined
        fait;
        si !undefined <> [] alors début
          soit u = String.concat ", " (List.rev !undefined) dans
          Location.prerr_warning loc (Warnings.Non_closed_record_pattern u)
        fin
      fin

(* Constructors *)

soit lookup_constructor_from_type env tpath lid =
  soit (constructors, _) = Env.find_type_descrs tpath env dans
    filtre lid avec
      Longident.Lident s ->
        List.find (fonc cstr -> cstr.cstr_name = s) constructors
    | _ -> raise Not_found

module Constructor = NameChoice (struct
  type t = constructor_description
  soit type_kind = "variant"
  soit get_name cstr = cstr.cstr_name
  soit get_type cstr = cstr.cstr_res
  soit get_descrs = fst
  soit fold = Env.fold_constructors
  soit unbound_name_error = Typetexp.unbound_constructor_error
fin)

(* unification of a type with a tconstr with
   freshly created arguments *)
soit unify_head_only loc env ty constr =
  soit (_, ty_res) = instance_constructor constr dans
  filtre (repr ty_res).desc avec
  | Tconstr(p,args,m) ->
      ty_res.desc <- Tconstr(p,List.map (fonc _ -> newvar ()) args,m);
      enforce_constraints env ty_res;
      unify_pat_types loc env ty ty_res
  | _ -> affirme faux

(* Typing of patterns *)

(* type_pat does not generate local constraints inside or patterns *)
type type_pat_mode =
  | Normal
  | Inside_or

(* type_pat propagates the expected type as well as maps for
   constructors and labels.
   Unification may update the typing environment. *)
soit rec type_pat ~constrs ~labels ~no_existentials ~mode ~env sp expected_ty =
  soit type_pat ?(mode=mode) ?(env=env) =
    type_pat ~constrs ~labels ~no_existentials ~mode ~env dans
  soit loc = sp.ppat_loc dans
  filtre sp.ppat_desc avec
    Ppat_any ->
      rp {
        pat_desc = Tpat_any;
        pat_loc = loc; pat_extra=[];
        pat_type = expected_ty;
        pat_attributes = sp.ppat_attributes;
        pat_env = !env }
  | Ppat_var name ->
      soit id = enter_variable loc name expected_ty dans
      rp {
        pat_desc = Tpat_var (id, name);
        pat_loc = loc; pat_extra=[];
        pat_type = expected_ty;
        pat_attributes = sp.ppat_attributes;
        pat_env = !env }
  | Ppat_unpack name ->
      soit id = enter_variable loc name expected_ty ~is_module:vrai dans
      rp {
        pat_desc = Tpat_var (id, name);
        pat_loc = sp.ppat_loc;
        pat_extra=[Tpat_unpack, loc, sp.ppat_attributes];
        pat_type = expected_ty;
        pat_attributes = [];
        pat_env = !env }
  | Ppat_constraint({ppat_desc=Ppat_var name; ppat_loc=lloc},
                    ({ptyp_desc=Ptyp_poly _} tel sty)) ->
      (* explicitly polymorphic type *)
      soit cty, force = Typetexp.transl_simple_type_delayed !env sty dans
      soit ty = cty.ctyp_type dans
      unify_pat_types lloc !env ty expected_ty;
      pattern_force := force :: !pattern_force;
      début filtre ty.desc avec
      | Tpoly (body, tyl) ->
          begin_def ();
          soit _, ty' = instance_poly ~keep_names:vrai faux tyl body dans
          end_def ();
          generalize ty';
          soit id = enter_variable lloc name ty' dans
          rp {
            pat_desc = Tpat_var (id, name);
            pat_loc = lloc;
            pat_extra = [Tpat_constraint cty, loc, sp.ppat_attributes];
            pat_type = ty;
            pat_attributes = [];
            pat_env = !env
          }
      | _ -> affirme faux
      fin
  | Ppat_alias(sq, name) ->
      soit q = type_pat sq expected_ty dans
      begin_def ();
      soit ty_var = build_as_type !env q dans
      end_def ();
      generalize ty_var;
      soit id = enter_variable ~is_as_variable:vrai loc name ty_var dans
      rp {
        pat_desc = Tpat_alias(q, id, name);
        pat_loc = loc; pat_extra=[];
        pat_type = q.pat_type;
        pat_attributes = sp.ppat_attributes;
        pat_env = !env }
  | Ppat_constant cst ->
      unify_pat_types loc !env (type_constant cst) expected_ty;
      rp {
        pat_desc = Tpat_constant cst;
        pat_loc = loc; pat_extra=[];
        pat_type = expected_ty;
        pat_attributes = sp.ppat_attributes;
        pat_env = !env }
  | Ppat_interval (Const_char c1, Const_char c2) ->
      soit ouvre Ast_helper.Pat dans
      soit gloc = {loc avec Location.loc_ghost=vrai} dans
      soit rec loop c1 c2 =
        si c1 = c2 alors constant ~loc:gloc (Const_char c1)
        sinon
          or_ ~loc:gloc
            (constant ~loc:gloc (Const_char c1))
            (loop (Char.chr(Char.code c1 + 1)) c2)
      dans
      soit p = si c1 <= c2 alors loop c1 c2 sinon loop c2 c1 dans
      soit p = {p avec ppat_loc=loc} dans
      type_pat p expected_ty
        (* TODO: record 'extra' to remember about interval *)
  | Ppat_interval _ ->
      raise (Error (loc, !env, Invalid_interval))
  | Ppat_tuple spl ->
      soit spl_ann = List.map (fonc p -> (p,newvar ())) spl dans
      soit ty = newty (Ttuple(List.map snd spl_ann)) dans
      unify_pat_types loc !env ty expected_ty;
      soit pl = List.map (fonc (p,t) -> type_pat p t) spl_ann dans
      rp {
        pat_desc = Tpat_tuple pl;
        pat_loc = loc; pat_extra=[];
        pat_type = expected_ty;
        pat_attributes = sp.ppat_attributes;
        pat_env = !env }
  | Ppat_construct(lid, sarg) ->
      soit opath =
        essaie
          soit (p0, p, _) = extract_concrete_variant !env expected_ty dans
            Some (p0, p, vrai)
        avec Not_found -> None
      dans
      soit constrs =
        filtre lid.txt, constrs avec
          Longident.Lident s, Some constrs quand Hashtbl.mem constrs s ->
            [Hashtbl.find constrs s, (fonc () -> ())]
        | _ ->  Typetexp.find_all_constructors !env lid.loc lid.txt
      dans
      soit check_lk tpath constr =
        si constr.cstr_generalized alors
          raise (Error (lid.loc, !env,
                        Unqualified_gadt_pattern (tpath, constr.cstr_name)))
      dans
      soit constr =
        wrap_disambiguate "Ce motif de type somme doit avoir" expected_ty
          (Constructor.disambiguate lid !env opath ~check_lk) constrs
      dans
      Env.mark_constructor Env.Pattern !env (Longident.last lid.txt) constr;
      Typetexp.check_deprecated loc constr.cstr_attributes constr.cstr_name;
      si no_existentials && constr.cstr_existentials <> [] alors
        raise (Error (loc, !env, Unexpected_existential));
      (* if constructor is gadt, we must verify that the expected type has the
         correct head *)
      si constr.cstr_generalized alors
        unify_head_only loc !env expected_ty constr;
      soit sargs =
        filtre sarg avec
          None -> []
        | Some {ppat_desc = Ppat_tuple spl} quand constr.cstr_arity > 1 -> spl
        | Some({ppat_desc = Ppat_any} tel sp) quand constr.cstr_arity <> 1 ->
            si constr.cstr_arity = 0 alors
              Location.prerr_warning sp.ppat_loc
                                     Warnings.Wildcard_arg_to_constant_constr;
            replicate_list sp constr.cstr_arity
        | Some sp -> [sp] dans
      si List.length sargs <> constr.cstr_arity alors
        raise(Error(loc, !env, Constructor_arity_mismatch(lid.txt,
                                     constr.cstr_arity, List.length sargs)));
      soit (ty_args, ty_res) =
        instance_constructor ~in_pattern:(env, get_newtype_level ()) constr
      dans
      si constr.cstr_generalized && mode = Normal alors
        unify_pat_types_gadt loc env ty_res expected_ty
      sinon
        unify_pat_types loc !env ty_res expected_ty;
      soit args = List.map2 (fonc p t -> type_pat p t) sargs ty_args dans
      rp {
        pat_desc=Tpat_construct(lid, constr, args);
        pat_loc = loc; pat_extra=[];
        pat_type = expected_ty;
        pat_attributes = sp.ppat_attributes;
        pat_env = !env }
  | Ppat_variant(l, sarg) ->
      soit arg_type = filtre sarg avec None -> [] | Some _ -> [newvar()] dans
      soit row = { row_fields =
                    [l, Reither(sarg = None, arg_type, vrai, ref None)];
                  row_bound = ();
                  row_closed = faux;
                  row_more = newvar ();
                  row_fixed = faux;
                  row_name = None } dans
      unify_pat_types loc !env (newty (Tvariant row)) expected_ty;
      soit arg =
        (* PR#6235: propagate type information *)
        filtre sarg, arg_type avec
          Some p, [ty] -> Some (type_pat p ty)
        | _            -> None
      dans
      rp {
        pat_desc = Tpat_variant(l, arg, ref {row avec row_more = newvar()});
        pat_loc = loc; pat_extra=[];
        pat_type =  expected_ty;
        pat_attributes = sp.ppat_attributes;
        pat_env = !env }
  | Ppat_record(lid_sp_list, closed) ->
      soit opath, record_ty =
        essaie
          soit (p0, p,_) = extract_concrete_record !env expected_ty dans
          Some (p0, p, vrai), expected_ty
        avec Not_found -> None, newvar ()
      dans
      soit type_label_pat (label_lid, label, sarg) =
        begin_def ();
        soit (vars, ty_arg, ty_res) = instance_label faux label dans
        si vars = [] alors end_def ();
        début essaie
          unify_pat_types loc !env ty_res record_ty
        avec Unify trace ->
          raise(Error(label_lid.loc, !env,
                      Label_mismatch(label_lid.txt, trace)))
        fin;
        soit arg = type_pat sarg ty_arg dans
        si vars <> [] alors début
          end_def ();
          generalize ty_arg;
          List.iter generalize vars;
          soit instantiated tv =
            soit tv = expand_head !env tv dans
            not (is_Tvar tv) || tv.level <> generic_level dans
          si List.exists instantiated vars alors
            raise (Error(label_lid.loc, !env, Polymorphic_label label_lid.txt))
        fin;
        (label_lid, label, arg)
      dans
      soit lbl_pat_list =
        wrap_disambiguate "Ce motif d'enregistrement doit avoir" expected_ty
          (type_label_a_list ?labels loc faux !env type_label_pat opath)
          lid_sp_list
      dans
      check_recordpat_labels loc lbl_pat_list closed;
      unify_pat_types loc !env record_ty expected_ty;
      rp {
        pat_desc = Tpat_record (lbl_pat_list, closed);
        pat_loc = loc; pat_extra=[];
        pat_type = expected_ty;
        pat_attributes = sp.ppat_attributes;
        pat_env = !env }
  | Ppat_array spl ->
      soit ty_elt = newvar() dans
      unify_pat_types
        loc !env (instance_def (Predef.type_array ty_elt)) expected_ty;
      soit spl_ann = List.map (fonc p -> (p,newvar())) spl dans
      soit pl = List.map (fonc (p,t) -> type_pat p ty_elt) spl_ann dans
      rp {
        pat_desc = Tpat_array pl;
        pat_loc = loc; pat_extra=[];
        pat_type = expected_ty;
        pat_attributes = sp.ppat_attributes;
        pat_env = !env }
  | Ppat_or(sp1, sp2) ->
      soit initial_pattern_variables = !pattern_variables dans
      soit p1 = type_pat ~mode:Inside_or sp1 expected_ty dans
      soit p1_variables = !pattern_variables dans
      pattern_variables := initial_pattern_variables;
      soit p2 = type_pat ~mode:Inside_or sp2 expected_ty dans
      soit p2_variables = !pattern_variables dans
      soit alpha_env =
        enter_orpat_variables loc !env p1_variables p2_variables dans
      pattern_variables := p1_variables;
      rp {
        pat_desc = Tpat_or(p1, alpha_pat alpha_env p2, None);
        pat_loc = loc; pat_extra=[];
        pat_type = expected_ty;
        pat_attributes = sp.ppat_attributes;
        pat_env = !env }
  | Ppat_lazy sp1 ->
      soit nv = newvar () dans
      unify_pat_types loc !env (instance_def (Predef.type_lazy_t nv))
        expected_ty;
      soit p1 = type_pat sp1 nv dans
      rp {
        pat_desc = Tpat_lazy p1;
        pat_loc = loc; pat_extra=[];
        pat_type = expected_ty;
        pat_attributes = sp.ppat_attributes;
        pat_env = !env }
  | Ppat_constraint(sp, sty) ->
      (* Separate when not already separated by !principal *)
      soit separate = vrai dans
      si separate alors begin_def();
      soit cty, force = Typetexp.transl_simple_type_delayed !env sty dans
      soit ty = cty.ctyp_type dans
      soit ty, expected_ty' =
        si separate alors début
          end_def();
          generalize_structure ty;
          instance !env ty, instance !env ty
        fin sinon ty, ty
      dans
      unify_pat_types loc !env ty expected_ty;
      soit p = type_pat sp expected_ty' dans
      (*Format.printf "%a@.%a@."
        Printtyp.raw_type_expr ty
        Printtyp.raw_type_expr p.pat_type;*)
      pattern_force := force :: !pattern_force;
      soit extra = (Tpat_constraint cty, loc, sp.ppat_attributes) dans
      si separate alors
        filtre p.pat_desc avec
          Tpat_var (id,s) ->
            {p avec pat_type = ty;
             pat_desc = Tpat_alias
               ({p avec pat_desc = Tpat_any; pat_attributes = []}, id,s);
             pat_extra = [extra];
            }
        | _ -> {p avec pat_type = ty;
                pat_extra = extra :: p.pat_extra}
      sinon p
  | Ppat_type lid ->
      soit (path, p,ty) = build_or_pat !env loc lid.txt dans
      unify_pat_types loc !env ty expected_ty;
      { p avec pat_extra =
        (Tpat_type (path, lid), loc, sp.ppat_attributes) :: p.pat_extra }
  | Ppat_extension (s, _arg) ->
      raise (Error (s.loc, !env, Extension s.txt))

soit type_pat ?(allow_existentials=faux) ?constrs ?labels
    ?(lev=get_current_level()) env sp expected_ty =
  newtype_level := Some lev;
  essaie
    soit r =
      type_pat ~no_existentials:(not allow_existentials) ~constrs ~labels
        ~mode:Normal ~env sp expected_ty dans
    iter_pattern (fonc p -> p.pat_env <- !env) r;
    newtype_level := None;
    r
  avec e ->
    newtype_level := None;
    raise e


(* this function is passed to Partial.parmatch
   to type check gadt nonexhaustiveness *)
soit partial_pred ~lev env expected_ty constrs labels p =
  soit snap = snapshot () dans
  essaie
    reset_pattern None vrai;
    soit typed_p =
      type_pat ~allow_existentials:vrai ~lev
        ~constrs ~labels (ref env) p expected_ty
    dans
    backtrack snap;
    (* types are invalidated but we don't need them here *)
    Some typed_p
  avec _ ->
    backtrack snap;
    None

soit rec iter3 f lst1 lst2 lst3 =
  filtre lst1,lst2,lst3 avec
  | x1::xs1,x2::xs2,x3::xs3 ->
      f x1 x2 x3;
      iter3 f xs1 xs2 xs3
  | [],[],[] ->
      ()
  | _ ->
      affirme faux

soit add_pattern_variables ?check ?check_as env =
  soit pv = get_ref pattern_variables dans
  (List.fold_right
     (fonc (id, ty, name, loc, as_var) env ->
       soit check = si as_var alors check_as sinon check dans
       Env.add_value ?check id
         {val_type = ty; val_kind = Val_reg; Types.val_loc = loc;
          val_attributes = [];
         } env
     )
     pv env,
   get_ref module_variables)

soit type_pattern ~lev env spat scope expected_ty =
  reset_pattern scope vrai;
  soit new_env = ref env dans
  soit pat = type_pat ~allow_existentials:vrai ~lev new_env spat expected_ty dans
  soit new_env, unpacks =
    add_pattern_variables !new_env
      ~check:(fonc s -> Warnings.Unused_var_strict s)
      ~check_as:(fonc s -> Warnings.Unused_var s) dans
  (pat, new_env, get_ref pattern_force, unpacks)

soit type_pattern_list env spatl scope expected_tys allow =
  reset_pattern scope allow;
  soit new_env = ref env dans
  soit patl = List.map2 (type_pat new_env) spatl expected_tys dans
  soit new_env, unpacks = add_pattern_variables !new_env dans
  (patl, new_env, get_ref pattern_force, unpacks)

soit type_class_arg_pattern cl_num val_env met_env l spat =
  reset_pattern None faux;
  soit nv = newvar () dans
  soit pat = type_pat (ref val_env) spat nv dans
  si has_variants pat alors début
    Parmatch.pressure_variants val_env [pat];
    iter_pattern finalize_variant pat
  fin;
  List.iter (fonc f -> f()) (get_ref pattern_force);
  si is_optional l alors unify_pat val_env pat (type_option (newvar ()));
  soit (pv, met_env) =
    List.fold_right
      (fonc (id, ty, name, loc, as_var) (pv, env) ->
         soit check s =
           si as_var alors Warnings.Unused_var s
           sinon Warnings.Unused_var_strict s dans
         soit id' = Ident.create (Ident.name id) dans
         ((id', name, id, ty)::pv,
          Env.add_value id' {val_type = ty;
                             val_kind = Val_ivar (Immutable, cl_num);
                             val_attributes = [];
                             Types.val_loc = loc;
                            } ~check
            env))
      !pattern_variables ([], met_env)
  dans
  soit val_env, _ = add_pattern_variables val_env dans
  (pat, pv, val_env, met_env)

soit type_self_pattern cl_num privty val_env met_env par_env spat =
  soit ouvre Ast_helper dans
  soit spat =
    Pat.mk (Ppat_alias (Pat.mk(Ppat_alias (spat, mknoloc "selfpat-*")),
                        mknoloc ("selfpat-" ^ cl_num)))
  dans
  reset_pattern None faux;
  soit nv = newvar() dans
  soit pat = type_pat (ref val_env) spat nv dans
  List.iter (fonc f -> f()) (get_ref pattern_force);
  soit meths = ref Meths.empty dans
  soit vars = ref Vars.empty dans
  soit pv = !pattern_variables dans
  pattern_variables := [];
  soit (val_env, met_env, par_env) =
    List.fold_right
      (fonc (id, ty, name, loc, as_var) (val_env, met_env, par_env) ->
         (Env.add_value id {val_type = ty;
                            val_kind = Val_unbound;
                            val_attributes = [];
                            Types.val_loc = loc;
                           } val_env,
          Env.add_value id {val_type = ty;
                            val_kind = Val_self (meths, vars, cl_num, privty);
                            val_attributes = [];
                            Types.val_loc = loc;
                           }
            ~check:(fonc s -> si as_var alors Warnings.Unused_var s
                             sinon Warnings.Unused_var_strict s)
            met_env,
          Env.add_value id {val_type = ty; val_kind = Val_unbound;
                            val_attributes = [];
                            Types.val_loc = loc;
                           } par_env))
      pv (val_env, met_env, par_env)
  dans
  (pat, meths, vars, val_env, met_env, par_env)

soit delayed_checks = ref []
soit reset_delayed_checks () = delayed_checks := []
soit add_delayed_check f = delayed_checks := f :: !delayed_checks
soit force_delayed_checks () =
  (* checks may change type levels *)
  soit snap = Btype.snapshot () dans
  List.iter (fonc f -> f ()) (List.rev !delayed_checks);
  reset_delayed_checks ();
  Btype.backtrack snap

soit rec final_subexpression sexp =
  filtre sexp.pexp_desc avec
    Pexp_let (_, _, e)
  | Pexp_sequence (_, e)
  | Pexp_try (e, _)
  | Pexp_ifthenelse (_, e, _)
  | Pexp_match (_, {pc_rhs=e} :: _)
    -> final_subexpression e
  | _ -> sexp

(* Generalization criterion for expressions *)

soit rec is_nonexpansive exp =
  filtre exp.exp_desc avec
    Texp_ident(_,_,_) -> vrai
  | Texp_constant _ -> vrai
  | Texp_let(rec_flag, pat_exp_list, body) ->
      List.for_all (fonc vb -> is_nonexpansive vb.vb_expr) pat_exp_list &&
      is_nonexpansive body
  | Texp_function _ -> vrai
  | Texp_apply(e, (_,None,_)::el) ->
      is_nonexpansive e && List.for_all is_nonexpansive_opt (List.map snd3 el)
  | Texp_match(e, cases, _) ->
      is_nonexpansive e &&
      List.for_all
        (fonc {c_lhs = _; c_guard; c_rhs} ->
           is_nonexpansive_opt c_guard && is_nonexpansive c_rhs
        ) cases
  | Texp_tuple el ->
      List.for_all is_nonexpansive el
  | Texp_construct( _, _, el) ->
      List.for_all is_nonexpansive el
  | Texp_variant(_, arg) -> is_nonexpansive_opt arg
  | Texp_record(lbl_exp_list, opt_init_exp) ->
      List.for_all
        (fonc (_, lbl, exp) -> lbl.lbl_mut = Immutable && is_nonexpansive exp)
        lbl_exp_list
      && is_nonexpansive_opt opt_init_exp
  | Texp_field(exp, lbl, _) -> is_nonexpansive exp
  | Texp_array [] -> vrai
  | Texp_ifthenelse(cond, ifso, ifnot) ->
      is_nonexpansive ifso && is_nonexpansive_opt ifnot
  | Texp_sequence (e1, e2) -> is_nonexpansive e2  (* PR#4354 *)
  | Texp_new (_, _, cl_decl) quand Ctype.class_type_arity cl_decl.cty_type > 0 ->
      vrai
  (* Note: nonexpansive only means no _observable_ side effects *)
  | Texp_lazy e -> is_nonexpansive e
  | Texp_object ({cstr_fields=fields; cstr_type = { csig_vars=vars}}, _) ->
      soit count = ref 0 dans
      List.for_all
        (fonc field -> filtre field.cf_desc avec
            Tcf_method _ -> vrai
          | Tcf_val (_, _, _, Tcfk_concrete (_, e), _) ->
              incr count; is_nonexpansive e
          | Tcf_val (_, _, _, Tcfk_virtual _, _) ->
              incr count; vrai
          | Tcf_initializer e -> is_nonexpansive e
          | Tcf_constraint _ -> vrai
          | Tcf_inherit _ -> faux)
        fields &&
      Vars.fold (fonc _ (mut,_,_) b -> decr count; b && mut = Immutable)
        vars vrai &&
      !count = 0
  | Texp_letmodule (_, _, mexp, e) ->
      is_nonexpansive_mod mexp && is_nonexpansive e
  | Texp_pack mexp ->
      is_nonexpansive_mod mexp
  | _ -> faux

et is_nonexpansive_mod mexp =
  filtre mexp.mod_desc avec
  | Tmod_ident _ -> vrai
  | Tmod_functor _ -> vrai
  | Tmod_unpack (e, _) -> is_nonexpansive e
  | Tmod_constraint (m, _, _, _) -> is_nonexpansive_mod m
  | Tmod_structure str ->
      List.for_all
        (fonc item -> filtre item.str_desc avec
          | Tstr_eval _ | Tstr_primitive _ | Tstr_type _ | Tstr_modtype _
          | Tstr_open _ | Tstr_class_type _ | Tstr_exn_rebind _ -> vrai
          | Tstr_value (_, pat_exp_list) ->
              List.for_all (fonc vb -> is_nonexpansive vb.vb_expr) pat_exp_list
          | Tstr_module {mb_expr=m;_}
          | Tstr_include (m, _, _) -> is_nonexpansive_mod m
          | Tstr_recmodule id_mod_list ->
              List.for_all (fonc {mb_expr=m;_} -> is_nonexpansive_mod m)
                id_mod_list
          | Tstr_exception _ -> faux (* true would be unsound *)
          | Tstr_class _ -> faux (* could be more precise *)
          | Tstr_attribute _ -> vrai
        )
        str.str_items
  | Tmod_apply _ -> faux

et is_nonexpansive_opt = fonction
    None -> vrai
  | Some e -> is_nonexpansive e

(* Typing format strings for printing or reading.

   These format strings are used by functions in modules Printf, Format, and
   Scanf.

   (Handling of * modifiers contributed by Thorsten Ohl.) *)

dehors string_to_format :
 string -> ('a, 'b, 'c, 'd, 'e, 'f) format6 = "%identity"
dehors format_to_string :
 ('a, 'b, 'c, 'd, 'e, 'f) format6 -> string = "%identity"

soit type_format loc fmt =

  soit ty_arrow gty ty = newty (Tarrow ("", instance_def gty, ty, Cok)) dans

  soit bad_conversion fmt i c =
    raise (Error (loc, Env.empty, Bad_conversion (fmt, i, c))) dans
  soit incomplete_format fmt =
    raise (Error (loc, Env.empty, Incomplete_format fmt)) dans

  soit rec type_in_format fmt =

    soit len = String.length fmt dans

    soit ty_input = newvar ()
    et ty_result = newvar ()
    et ty_aresult = newvar ()
    et ty_uresult = newvar () dans

    soit meta = ref 0 dans

    soit rec scan_format i =
      si i >= len alors
        si !meta = 0
        alors ty_uresult, ty_result
        sinon incomplete_format fmt sinon
      filtre fmt.[i] avec
      | '%' -> scan_opts i (i + 1)
      | _ -> scan_format (i + 1)
    et scan_opts i j =
      si j >= len alors incomplete_format fmt sinon
      filtre fmt.[j] avec
      | '_' -> scan_rest vrai i (j + 1)
      | _ -> scan_rest faux i j
    et scan_rest skip i j =
      soit rec scan_flags i j =
        si j >= len alors incomplete_format fmt sinon
        filtre fmt.[j] avec
        | '#' | '0' | '-' | ' ' | '+' -> scan_flags i (j + 1)
        | _ -> scan_width i j
      et scan_width i j = scan_width_or_prec_value scan_precision i j
      et scan_decimal_string scan i j =
        si j >= len alors incomplete_format fmt sinon
        filtre fmt.[j] avec
        | '0' .. '9' -> scan_decimal_string scan i (j + 1)
        | _ -> scan i j
      et scan_width_or_prec_value scan i j =
        si j >= len alors incomplete_format fmt sinon
        filtre fmt.[j] avec
        | '*' ->
          soit ty_uresult, ty_result = scan i (j + 1) dans
          ty_uresult, ty_arrow Predef.type_int ty_result
        | '-' | '+' -> scan_decimal_string scan i (j + 1)
        | _ -> scan_decimal_string scan i j
      et scan_precision i j =
        si j >= len alors incomplete_format fmt sinon
        filtre fmt.[j] avec
        | '.' -> scan_width_or_prec_value scan_conversion i (j + 1)
        | _ -> scan_conversion i j
      et scan_indication j =
        si j >= len alors j - 1 sinon
        filtre fmt.[j] avec
        | '@' ->
          soit k = j + 1 dans
          si k >= len alors j - 1 sinon
          début filtre fmt.[k] avec
          | '%' ->
            soit k = k + 1 dans
            si k >= len alors j - 1 sinon
            début filtre fmt.[k] avec
            | '%' | '@' -> k
            | _c -> j - 1
            fin
          | _c -> k
          fin
        | _c -> j - 1
      et scan_range j =
        soit rec scan_closing j =
          si j >= len alors incomplete_format fmt sinon
          filtre fmt.[j] avec
          | ']' -> j
          | '%' ->
            soit j = j + 1 dans
            si j >= len alors incomplete_format fmt sinon
            début filtre fmt.[j] avec
            | '%' | '@' -> scan_closing (j + 1)
            | c -> bad_conversion fmt j c
            fin
          | c -> scan_closing (j + 1) dans
        soit scan_first_pos j =
          si j >= len alors incomplete_format fmt sinon
          filtre fmt.[j] avec
          | ']' -> scan_closing (j + 1)
          | c -> scan_closing j dans
        soit scan_first_neg j =
          si j >= len alors incomplete_format fmt sinon
          filtre fmt.[j] avec
          | '^' -> scan_first_pos (j + 1)
          | c -> scan_first_pos j dans

        scan_first_neg j

      et conversion j ty_arg =
        soit ty_uresult, ty_result = scan_format (j + 1) dans
        ty_uresult,
        si skip alors ty_result sinon ty_arrow ty_arg ty_result

      et conversion_a j ty_e ty_arg =
        soit ty_uresult, ty_result = conversion j ty_arg dans
        soit ty_a = ty_arrow ty_input (ty_arrow ty_e ty_aresult) dans
        ty_uresult, ty_arrow ty_a ty_result

      et conversion_r j ty_e ty_arg =
        soit ty_uresult, ty_result = conversion j ty_arg dans
        soit ty_r = ty_arrow ty_input ty_e dans
        ty_arrow ty_r ty_uresult, ty_result

      et scan_conversion i j =
        si j >= len alors incomplete_format fmt sinon
        filtre fmt.[j] avec
        | '%' | '@' | '!' | ',' -> scan_format (j + 1)
        | 's' | 'S' ->
          soit j = scan_indication (j + 1) dans
          conversion j Predef.type_string
        | '[' ->
          soit j = scan_range (j + 1) dans
          soit j = scan_indication (j + 1) dans
          conversion j Predef.type_string
        | 'c' | 'C' -> conversion j Predef.type_char
        | 'd' | 'i' | 'o' | 'u' | 'x' | 'X' | 'N' ->
          conversion j Predef.type_int
        | 'f' | 'e' | 'E' | 'g' | 'G' | 'F' -> conversion j Predef.type_float
        | 'B' | 'b' -> conversion j Predef.type_bool
        | 'a' | 'r' tel conv ->
          soit conversion =
            si conv = 'a' alors conversion_a sinon conversion_r dans
          soit ty_e = newvar () dans
          soit j = j + 1 dans
          si j >= len alors conversion (j - 1) ty_e ty_e sinon début
            filtre fmt.[j] avec
(*            | 'a' | 'A' -> conversion j ty_e (Predef.type_array ty_e)
            | 'l' | 'L' -> conversion j ty_e (Predef.type_list ty_e)
            | 'o' | 'O' -> conversion j ty_e (Predef.type_option ty_e)*)
            | _ -> conversion (j - 1) ty_e ty_e fin
(*        | 'r' ->
          let ty_e = newvar () in
          let j = j + 1 in
          if j >= len then conversion_r (j - 1) ty_e ty_e else begin
            match fmt.[j] with
            | 'a' | 'A' -> conversion_r j ty_e (Pref.type_array ty_e)
            | 'l' | 'L' -> conversion_r j ty_e (Pref.type_list ty_e)
            | 'o' | 'O' -> conversion_r j ty_e (Pref.type_option ty_e)
            | _ -> conversion_r (j - 1) ty_e ty_e end *)
        | 't' -> conversion j (ty_arrow ty_input ty_aresult)
        | 'l' | 'n' | 'L' tel c ->
          soit j = j + 1 dans
          si j >= len alors conversion (j - 1) Predef.type_int sinon début
            filtre fmt.[j] avec
            | 'd' | 'i' | 'o' | 'u' | 'x' | 'X' ->
              soit ty_arg =
                filtre c avec
                | 'l' -> Predef.type_int32
                | 'n' -> Predef.type_nativeint
                | _ -> Predef.type_int64 dans
              conversion j ty_arg
            | c -> conversion (j - 1) Predef.type_int
          fin
        | '{' | '(' tel c ->
          soit j = j + 1 dans
          si j >= len alors incomplete_format fmt sinon
          soit sj =
            Printf.CamlinternalPr.Tformat.sub_format
              (fonc fmt -> incomplete_format (format_to_string fmt))
              (fonc fmt -> bad_conversion (format_to_string fmt))
              c (string_to_format fmt) j dans
          soit sfmt = String.sub fmt j (sj - 2 - j) dans
          soit ty_sfmt = type_in_format sfmt dans
          début filtre c avec
          | '{' -> conversion (sj - 1) ty_sfmt
          | _ -> incr meta; conversion (j - 1) ty_sfmt fin
        | ')' quand !meta > 0 -> decr meta; scan_format (j + 1)
        | c -> bad_conversion fmt i c dans
      scan_flags i j dans

    soit ty_ureader, ty_args = scan_format 0 dans
    newty
      (Tconstr
        (Predef.path_format6,
         [ ty_args; ty_input; ty_aresult;
           ty_ureader; ty_uresult; ty_result; ],
         ref Mnil)) dans

  type_in_format fmt

(* Approximate the type of an expression, for better recursion *)

soit rec approx_type env sty =
  filtre sty.ptyp_desc avec
    Ptyp_arrow (p, _, sty) ->
      soit ty1 = si is_optional p alors type_option (newvar ()) sinon newvar () dans
      newty (Tarrow (p, ty1, approx_type env sty, Cok))
  | Ptyp_tuple args ->
      newty (Ttuple (List.map (approx_type env) args))
  | Ptyp_constr (lid, ctl) ->
      début essaie
        soit (path, decl) = Env.lookup_type lid.txt env dans
        si List.length ctl <> decl.type_arity alors raise Not_found;
        soit tyl = List.map (approx_type env) ctl dans
        newconstr path tyl
      avec Not_found -> newvar ()
      fin
  | Ptyp_poly (_, sty) ->
      approx_type env sty
  | _ -> newvar ()

soit rec type_approx env sexp =
  filtre sexp.pexp_desc avec
    Pexp_let (_, _, e) -> type_approx env e
  | Pexp_fun (p, _, _, e) quand is_optional p ->
       newty (Tarrow(p, type_option (newvar ()), type_approx env e, Cok))
  | Pexp_fun (p,_,_, e) ->
       newty (Tarrow(p, newvar (), type_approx env e, Cok))
  | Pexp_function ({pc_rhs=e}::_) ->
       newty (Tarrow("", newvar (), type_approx env e, Cok))
  | Pexp_match (_, {pc_rhs=e}::_) -> type_approx env e
  | Pexp_try (e, _) -> type_approx env e
  | Pexp_tuple l -> newty (Ttuple(List.map (type_approx env) l))
  | Pexp_ifthenelse (_,e,_) -> type_approx env e
  | Pexp_sequence (_,e) -> type_approx env e
  | Pexp_constraint (e, sty) ->
      soit ty = type_approx env e dans
      soit ty1 = approx_type env sty dans
      début essaie unify env ty ty1 avec Unify trace ->
        raise(Error(sexp.pexp_loc, env, Expr_type_clash trace))
      fin;
      ty1
  | Pexp_coerce (e, sty1, sty2) ->
      soit approx_ty_opt = fonction
        | None -> newvar ()
        | Some sty -> approx_type env sty
      dans
      soit ty = type_approx env e
      et ty1 = approx_ty_opt sty1
      et ty2 = approx_type env sty2 dans
      début essaie unify env ty ty1 avec Unify trace ->
        raise(Error(sexp.pexp_loc, env, Expr_type_clash trace))
      fin;
      ty2
  | _ -> newvar ()

(* List labels in a function type, and whether return type is a variable *)
soit rec list_labels_aux env visited ls ty_fun =
  soit ty = expand_head env ty_fun dans
  si List.memq ty visited alors
    List.rev ls, faux
  sinon filtre ty.desc avec
    Tarrow (l, _, ty_res, _) ->
      list_labels_aux env (ty::visited) (l::ls) ty_res
  | _ ->
      List.rev ls, is_Tvar ty

soit list_labels env ty =
  wrap_trace_gadt_instances env (list_labels_aux env [] []) ty

(* Check that all univars are safe in a type *)
soit check_univars env expans kind exp ty_expected vars =
  si expans && not (is_nonexpansive exp) alors
    generalize_expansive env exp.exp_type;
  (* need to expand twice? cf. Ctype.unify2 *)
  soit vars = List.map (expand_head env) vars dans
  soit vars = List.map (expand_head env) vars dans
  soit vars' =
    List.filter
      (fonc t ->
        soit t = repr t dans
        generalize t;
        filtre t.desc avec
          Tvar name quand t.level = generic_level ->
            log_type t; t.desc <- Tunivar name; vrai
        | _ -> faux)
      vars dans
  si List.length vars = List.length vars' alors () sinon
  soit ty = newgenty (Tpoly(repr exp.exp_type, vars'))
  et ty_expected = repr ty_expected dans
  raise (Error (exp.exp_loc, env,
                Less_general(kind, [ty, ty; ty_expected, ty_expected])))

(* Check that a type is not a function *)
soit check_application_result env statement exp =
  soit loc = exp.exp_loc dans
  filtre (expand_head env exp.exp_type).desc avec
  | Tarrow _ ->
      Location.prerr_warning exp.exp_loc Warnings.Partial_application
  | Tvar _ -> ()
  | Tconstr (p, _, _) quand Path.same p Predef.path_unit -> ()
  | _ ->
      si statement alors
        Location.prerr_warning loc Warnings.Statement_type

(* Check that a type is generalizable at some level *)
soit generalizable level ty =
  soit rec check ty =
    soit ty = repr ty dans
    si ty.level < lowest_level alors () sinon
    si ty.level <= level alors raise Exit sinon
    (mark_type_node ty; iter_type_expr check ty)
  dans
  essaie check ty; unmark_type ty; vrai
  avec Exit -> unmark_type ty; faux

(* Hack to allow coercion of self. Will clean-up later. *)
soit self_coercion = ref ([] : (Path.t * Location.t list ref) list)

(* Helpers for packaged modules. *)
soit create_package_type loc env (p, l) =
  soit s = !Typetexp.transl_modtype_longident loc env p dans
  soit fields = List.map (fonc (name, ct) ->
                           name, Typetexp.transl_simple_type env faux ct) l dans
  soit ty = newty (Tpackage (s,
                    List.map fst l,
                   List.map (fonc (_, cty) -> cty.ctyp_type) fields))
  dans
   (s, fields, ty)

 soit wrap_unpacks sexp unpacks =
   soit ouvre Ast_helper dans
   List.fold_left
     (fonc sexp (name, loc) ->
       Exp.letmodule ~loc:sexp.pexp_loc
         name
         (Mod.unpack ~loc
            (Exp.ident ~loc:name.loc (mkloc (Longident.Lident name.txt) name.loc)))
         sexp
     )
    sexp unpacks

(* Helpers for type_cases *)

soit contains_variant_either ty =
  soit rec loop ty =
    soit ty = repr ty dans
    si ty.level >= lowest_level alors début
      mark_type_node ty;
      filtre ty.desc avec
        Tvariant row ->
          soit row = row_repr row dans
          si not row.row_fixed alors
            List.iter
              (fonc (_,f) ->
                filtre row_field_repr f avec Reither _ -> raise Exit | _ -> ())
              row.row_fields;
          iter_row loop row
      | _ ->
          iter_type_expr loop ty
    fin
  dans
  essaie loop ty; unmark_type ty; faux
  avec Exit -> unmark_type ty; vrai

soit iter_ppat f p =
  filtre p.ppat_desc avec
  | Ppat_any | Ppat_var _ | Ppat_constant _ | Ppat_interval _
  | Ppat_extension _
  | Ppat_type _ | Ppat_unpack _ -> ()
  | Ppat_array pats -> List.iter f pats
  | Ppat_or (p1,p2) -> f p1; f p2
  | Ppat_variant (_, arg) | Ppat_construct (_, arg) -> may f arg
  | Ppat_tuple lst ->  List.iter f lst
  | Ppat_alias (p,_) | Ppat_constraint (p,_) | Ppat_lazy p -> f p
  | Ppat_record (args, flag) -> List.iter (fonc (_,p) -> f p) args

soit contains_polymorphic_variant p =
  soit rec loop p =
    filtre p.ppat_desc avec
      Ppat_variant _ | Ppat_type _ -> raise Exit
    | _ -> iter_ppat loop p
  dans
  essaie loop p; faux avec Exit -> vrai

soit contains_gadt env p =
  soit rec loop p =
    filtre p.ppat_desc avec
      Ppat_construct (lid, _) ->
        début essaie
          soit cstrs = Env.lookup_all_constructors lid.txt env dans
          List.iter (fonc (cstr,_) -> si cstr.cstr_generalized alors raise Exit)
            cstrs
        avec Not_found -> ()
        fin; iter_ppat loop p
    | _ -> iter_ppat loop p
  dans
  essaie loop p; faux avec Exit -> vrai

soit check_absent_variant env =
  iter_pattern
    (fonction {pat_desc = Tpat_variant (s, arg, row)} tel pat ->
      soit row = row_repr !row dans
      si List.exists (fonc (s',fi) -> s = s' && row_field_repr fi <> Rabsent)
          row.row_fields
      || not row.row_fixed && not (static_row row)  (* same as Ctype.poly *)
      alors () sinon
      soit ty_arg =
        filtre arg avec None -> [] | Some p -> [correct_levels p.pat_type] dans
      soit row' = {row_fields = [s, Reither(arg=None,ty_arg,vrai,ref None)];
                  row_more = newvar (); row_bound = ();
                  row_closed = faux; row_fixed = faux; row_name = None} dans
      (* Should fail *)
      unify_pat env {pat avec pat_type = newty (Tvariant row')}
                    (correct_levels pat.pat_type)
      | _ -> ())

(* Duplicate types of values in the environment *)
(* XXX Should we do something about global type variables too? *)

soit duplicate_ident_types loc caselist env =
  soit caselist =
    List.filter (fonc {pc_lhs} -> contains_gadt env pc_lhs) caselist dans
  soit idents = all_idents_cases caselist dans
  List.fold_left
    (fonc env s ->
      essaie
        (* XXX This will mark the value as being used;
           I don't think this is what we want *)
        soit (path, desc) = Env.lookup_value (Longident.Lident s) env dans
        filtre path avec
          Path.Pident id ->
            soit desc = {desc avec val_type = correct_levels desc.val_type} dans
            Env.add_value id desc env
        | _ -> env
      avec Not_found -> env)
    env idents

(* Typing of expressions *)

soit unify_exp env exp expected_ty =
  (* Format.eprintf "@[%a@ %a@]@." Printtyp.raw_type_expr exp.exp_type
    Printtyp.raw_type_expr expected_ty; *)
    unify_exp_types exp.exp_loc env exp.exp_type expected_ty

soit rec type_exp env sexp =
  (* We now delegate everything to type_expect *)
  type_expect env sexp (newvar ())

(* Typing of an expression with an expected type.
   This provide better error messages, and allows controlled
   propagation of return type information.
   In the principal case, [type_expected'] may be at generic_level.
 *)

et type_expect ?in_function env sexp ty_expected =
  soit previous_saved_types = Cmt_format.get_saved_types () dans
  soit prev_warnings = Typetexp.warning_attribute sexp.pexp_attributes dans
  soit exp = type_expect_ ?in_function env sexp ty_expected dans
  début filtre prev_warnings avec Some x -> Warnings.restore x | None -> () fin;
  Cmt_format.set_saved_types (Cmt_format.Partial_expression exp :: previous_saved_types);
  exp

et type_expect_ ?in_function env sexp ty_expected =
  soit loc = sexp.pexp_loc dans
  (* Record the expression type before unifying it with the expected type *)
  soit rue exp =
    unify_exp env (re exp) (instance env ty_expected);
    exp
  dans
  filtre sexp.pexp_desc avec
  | Pexp_ident lid ->
      début
        soit (path, desc) = Typetexp.find_value env loc lid.txt dans
        si !Clflags.annotations alors début
          soit dloc = desc.Types.val_loc dans
          soit annot =
            si dloc.Location.loc_ghost alors Annot.Iref_external
            sinon Annot.Iref_internal dloc
          dans
          soit name = Path.name ~paren:Oprint.parenthesized_ident path dans
          Stypes.record (Stypes.An_ident (loc, name, annot))
        fin;
        rue {
          exp_desc =
            début filtre desc.val_kind avec
              Val_ivar (_, cl_num) ->
                soit (self_path, _) =
                  Env.lookup_value (Longident.Lident ("self-" ^ cl_num)) env
                dans
                Texp_instvar(self_path, path,
                             filtre lid.txt avec
                                 Longident.Lident txt -> { txt; loc = lid.loc }
                               | _ -> affirme faux)
            | Val_self (_, _, cl_num, _) ->
                soit (path, _) =
                  Env.lookup_value (Longident.Lident ("self-" ^ cl_num)) env
                dans
                Texp_ident(path, lid, desc)
            | Val_unbound ->
                raise(Error(loc, env, Masked_instance_variable lid.txt))
            (*| Val_prim _ ->
                let p = Env.normalize_path (Some loc) env path in
                Env.add_required_global (Path.head p);
                Texp_ident(path, lid, desc)*)
            | _ ->
                Texp_ident(path, lid, desc)
          fin;
          exp_loc = loc; exp_extra = [];
          exp_type = instance env desc.val_type;
          exp_attributes = sexp.pexp_attributes;
          exp_env = env }
      fin
  | Pexp_constant(Const_string (s, _) tel cst) ->
      rue {
        exp_desc = Texp_constant cst;
        exp_loc = loc; exp_extra = [];
        exp_type =
        (* Terrible hack for format strings *)
           début filtre (repr (expand_head env ty_expected)).desc avec
             Tconstr(path, _, _) quand Path.same path Predef.path_format6 ->
               type_format loc s
           | _ -> instance_def Predef.type_string
           fin;
        exp_attributes = sexp.pexp_attributes;
        exp_env = env }
  | Pexp_constant cst ->
      rue {
        exp_desc = Texp_constant cst;
        exp_loc = loc; exp_extra = [];
        exp_type = type_constant cst;
        exp_attributes = sexp.pexp_attributes;
        exp_env = env }
  | Pexp_let(Nonrecursive,
             [{pvb_pat=spat; pvb_expr=sval; pvb_attributes=[]}], sbody)
    quand contains_gadt env spat ->
    (* TODO: allow non-empty attributes? *)
      type_expect ?in_function env
        {sexp avec
         pexp_desc = Pexp_match (sval, [Ast_helper.Exp.case spat sbody])}
        ty_expected
  | Pexp_let(rec_flag, spat_sexp_list, sbody) ->
      soit scp =
        filtre sexp.pexp_attributes, rec_flag avec
        | [{txt="#default"},_], _ -> None
        | _, Recursive -> Some (Annot.Idef loc)
        | _, Nonrecursive -> Some (Annot.Idef sbody.pexp_loc)
      dans
      soit (pat_exp_list, new_env, unpacks) =
        type_let env rec_flag spat_sexp_list scp vrai dans
      soit body =
        type_expect new_env (wrap_unpacks sbody unpacks) ty_expected dans
      re {
        exp_desc = Texp_let(rec_flag, pat_exp_list, body);
        exp_loc = loc; exp_extra = [];
        exp_type = body.exp_type;
        exp_attributes = sexp.pexp_attributes;
        exp_env = env }
  | Pexp_fun (l, Some default, spat, sexp) ->
      affirme(is_optional l); (* default allowed only with optional argument *)
      soit ouvre Ast_helper dans
      soit default_loc = default.pexp_loc dans
      soit scases = [
        Exp.case
          (Pat.construct ~loc:default_loc
             (mknoloc (Longident.(Ldot (Lident "*predef*", "Some"))))
             (Some (Pat.var ~loc:default_loc (mknoloc "*sth*"))))
          (Exp.ident ~loc:default_loc (mknoloc (Longident.Lident "*sth*")));

        Exp.case
          (Pat.construct ~loc:default_loc
             (mknoloc (Longident.(Ldot (Lident "*predef*", "None"))))
             None)
          default;
       ]
      dans
      soit smatch =
        Exp.match_ ~loc (Exp.ident ~loc (mknoloc (Longident.Lident "*opt*")))
          scases
      dans
      soit sfun =
        Exp.fun_ ~loc
          l None
          (Pat.var ~loc (mknoloc "*opt*"))
          (Exp.let_ ~loc Nonrecursive ~attrs:[mknoloc "#default",PStr []]
             [Vb.mk spat smatch] sexp)
      dans
      type_expect ?in_function env sfun ty_expected
        (* TODO: keep attributes, call type_function directly *)
  | Pexp_fun (l, None, spat, sexp) ->
      type_function ?in_function loc sexp.pexp_attributes env ty_expected
        l [{pc_lhs=spat; pc_guard=None; pc_rhs=sexp}]
  | Pexp_function caselist ->
      type_function ?in_function
        loc sexp.pexp_attributes env ty_expected "" caselist
  | Pexp_apply(sfunct, sargs) ->
      begin_def (); (* one more level for non-returning functions *)
      si !Clflags.principal alors begin_def ();
      soit funct = type_exp env sfunct dans
      si !Clflags.principal alors début
          end_def ();
          generalize_structure funct.exp_type
        fin;
      soit rec lower_args seen ty_fun =
        soit ty = expand_head env ty_fun dans
        si List.memq ty seen alors () sinon
        filtre ty.desc avec
          Tarrow (l, ty_arg, ty_fun, com) ->
            (essaie unify_var env (newvar()) ty_arg avec Unify _ -> affirme faux);
            lower_args (ty::seen) ty_fun
        | _ -> ()
      dans
      soit ty = instance env funct.exp_type dans
      end_def ();
      wrap_trace_gadt_instances env (lower_args []) ty;
      begin_def ();
      soit (args, ty_res) = type_application env funct sargs dans
      end_def ();
      unify_var env (newvar()) funct.exp_type;
      rue {
        exp_desc = Texp_apply(funct, args);
        exp_loc = loc; exp_extra = [];
        exp_type = ty_res;
        exp_attributes = sexp.pexp_attributes;
        exp_env = env }
  | Pexp_match(sarg, caselist) ->
      begin_def ();
      soit arg = type_exp env sarg dans
      end_def ();
      si is_nonexpansive arg alors generalize arg.exp_type
      sinon generalize_expansive env arg.exp_type;
      soit cases, partial =
        type_cases env arg.exp_type ty_expected vrai loc caselist
      dans
      re {
        exp_desc = Texp_match(arg, cases, partial);
        exp_loc = loc; exp_extra = [];
        exp_type = instance env ty_expected;
        exp_attributes = sexp.pexp_attributes;
        exp_env = env }
  | Pexp_try(sbody, caselist) ->
      soit body = type_expect env sbody ty_expected dans
      soit cases, _ =
        type_cases env Predef.type_exn ty_expected faux loc caselist dans
      re {
        exp_desc = Texp_try(body, cases);
        exp_loc = loc; exp_extra = [];
        exp_type = body.exp_type;
        exp_attributes = sexp.pexp_attributes;
        exp_env = env }
  | Pexp_tuple sexpl ->
      soit subtypes = List.map (fonc _ -> newgenvar ()) sexpl dans
      soit to_unify = newgenty (Ttuple subtypes) dans
      unify_exp_types loc env to_unify ty_expected;
      soit expl =
        List.map2 (fonc body ty -> type_expect env body ty) sexpl subtypes
      dans
      re {
        exp_desc = Texp_tuple expl;
        exp_loc = loc; exp_extra = [];
        (* Keep sharing *)
        exp_type = newty (Ttuple (List.map (fonc e -> e.exp_type) expl));
        exp_attributes = sexp.pexp_attributes;
        exp_env = env }
  | Pexp_construct(lid, sarg) ->
      type_construct env loc lid sarg ty_expected sexp.pexp_attributes
  | Pexp_variant(l, sarg) ->
      (* Keep sharing *)
      soit ty_expected0 = instance env ty_expected dans
      début essaie filtre
        sarg, expand_head env ty_expected, expand_head env ty_expected0 avec
      | Some sarg, {desc = Tvariant row}, {desc = Tvariant row0} ->
          soit row = row_repr row dans
          début filtre row_field_repr (List.assoc l row.row_fields),
          row_field_repr (List.assoc l row0.row_fields) avec
            Rpresent (Some ty), Rpresent (Some ty0) ->
              soit arg = type_argument env sarg ty ty0 dans
              re { exp_desc = Texp_variant(l, Some arg);
                   exp_loc = loc; exp_extra = [];
                   exp_type = ty_expected0;
                   exp_attributes = sexp.pexp_attributes;
                   exp_env = env }
          | _ -> raise Not_found
          fin
      | _ -> raise Not_found
      avec Not_found ->
        soit arg = may_map (type_exp env) sarg dans
        soit arg_type = may_map (fonc arg -> arg.exp_type) arg dans
        rue {
          exp_desc = Texp_variant(l, arg);
          exp_loc = loc; exp_extra = [];
          exp_type= newty (Tvariant{row_fields = [l, Rpresent arg_type];
                                    row_more = newvar ();
                                    row_bound = ();
                                    row_closed = faux;
                                    row_fixed = faux;
                                    row_name = None});
          exp_attributes = sexp.pexp_attributes;
          exp_env = env }
      fin
  | Pexp_record(lid_sexp_list, opt_sexp) ->
      soit opt_exp =
        filtre opt_sexp avec
          None -> None
        | Some sexp ->
            si !Clflags.principal alors begin_def ();
            soit exp = type_exp env sexp dans
            si !Clflags.principal alors début
              end_def ();
              generalize_structure exp.exp_type
            fin;
            Some exp
      dans
      soit ty_record, opath =
        soit get_path ty =
          essaie
            soit (p0, p,_) = extract_concrete_record env ty dans
            (* XXX level may be wrong *)
            Some (p0, p, ty.level = generic_level || not !Clflags.principal)
          avec Not_found -> None
        dans
        filtre get_path ty_expected avec
          None ->
            début filtre opt_exp avec
              None -> newvar (), None
            | Some exp ->
                filtre get_path exp.exp_type avec
                  None -> newvar (), None
                | Some (_, p', _) tel op ->
                    soit decl = Env.find_type p' env dans
                    begin_def ();
                    soit ty =
                      newconstr p' (instance_list env decl.type_params) dans
                    end_def ();
                    generalize_structure ty;
                    ty, op
            fin
        | op -> ty_expected, op
      dans
      soit closed = (opt_sexp = None) dans
      soit lbl_exp_list =
        wrap_disambiguate "Cette expression d'enregistrement doit avoir" ty_record
          (type_label_a_list loc closed env
             (type_label_exp vrai env loc ty_record)
             opath)
          lid_sexp_list
      dans
      unify_exp_types loc env ty_record (instance env ty_expected);

      (* type_label_a_list returns a list of labels sorted by lbl_pos *)
      (* note: check_duplicates would better be implemented in
         type_label_a_list directly *)
      soit rec check_duplicates = fonction
        | (_, lbl1, _) :: (_, lbl2, _) :: _ quand lbl1.lbl_pos = lbl2.lbl_pos ->
          raise(Error(loc, env, Label_multiply_defined lbl1.lbl_name))
        | _ :: rem ->
            check_duplicates rem
        | [] -> ()
      dans
      check_duplicates lbl_exp_list;
      soit opt_exp =
        filtre opt_exp, lbl_exp_list avec
          None, _ -> None
        | Some exp, (lid, lbl, lbl_exp) :: _ ->
            soit ty_exp = instance env exp.exp_type dans
            soit unify_kept lbl =
              (* do not connect overridden labels *)
              si List.for_all
                  (fonc (_, lbl',_) -> lbl'.lbl_pos <> lbl.lbl_pos)
                  lbl_exp_list
              alors début
                soit _, ty_arg1, ty_res1 = instance_label faux lbl
                et _, ty_arg2, ty_res2 = instance_label faux lbl dans
                unify env ty_arg1 ty_arg2;
                unify env (instance env ty_expected) ty_res2;
                unify_exp_types exp.exp_loc env ty_exp ty_res1;
              fin dans
            Array.iter unify_kept lbl.lbl_all;
            Some {exp avec exp_type = ty_exp}
        | _ -> affirme faux
      dans
      soit num_fields =
        filtre lbl_exp_list avec [] -> affirme faux
        | (_, lbl,_)::_ -> Array.length lbl.lbl_all dans
      si opt_sexp = None && List.length lid_sexp_list <> num_fields alors début
        soit present_indices =
          List.map (fonc (_, lbl, _) -> lbl.lbl_pos) lbl_exp_list dans
        soit label_names = extract_label_names sexp env ty_expected dans
        soit rec missing_labels n = fonction
            [] -> []
          | lbl :: rem ->
              si List.mem n present_indices alors missing_labels (n + 1) rem
              sinon lbl :: missing_labels (n + 1) rem
        dans
        soit missing = missing_labels 0 label_names dans
        raise(Error(loc, env, Label_missing missing))
      fin
      sinon si opt_sexp <> None && List.length lid_sexp_list = num_fields alors
        Location.prerr_warning loc Warnings.Useless_record_with;
      re {
        exp_desc = Texp_record(lbl_exp_list, opt_exp);
        exp_loc = loc; exp_extra = [];
        exp_type = instance env ty_expected;
        exp_attributes = sexp.pexp_attributes;
        exp_env = env }
  | Pexp_field(srecord, lid) ->
      soit (record, label, _) = type_label_access env loc srecord lid dans
      soit (_, ty_arg, ty_res) = instance_label faux label dans
      unify_exp env record ty_res;
      rue {
        exp_desc = Texp_field(record, lid, label);
        exp_loc = loc; exp_extra = [];
        exp_type = ty_arg;
        exp_attributes = sexp.pexp_attributes;
        exp_env = env }
  | Pexp_setfield(srecord, lid, snewval) ->
      soit (record, label, opath) = type_label_access env loc srecord lid dans
      soit ty_record = si opath = None alors newvar () sinon record.exp_type dans
      soit (label_loc, label, newval) =
        type_label_exp faux env loc ty_record (lid, label, snewval) dans
      unify_exp env record ty_record;
      si label.lbl_mut = Immutable alors
        raise(Error(loc, env, Label_not_mutable lid.txt));
      rue {
        exp_desc = Texp_setfield(record, label_loc, label, newval);
        exp_loc = loc; exp_extra = [];
        exp_type = instance_def Predef.type_unit;
        exp_attributes = sexp.pexp_attributes;
        exp_env = env }
  | Pexp_array(sargl) ->
      soit ty = newgenvar() dans
      soit to_unify = Predef.type_array ty dans
      unify_exp_types loc env to_unify ty_expected;
      soit argl = List.map (fonc sarg -> type_expect env sarg ty) sargl dans
      re {
        exp_desc = Texp_array argl;
        exp_loc = loc; exp_extra = [];
        exp_type = instance env ty_expected;
        exp_attributes = sexp.pexp_attributes;
        exp_env = env }
  | Pexp_ifthenelse(scond, sifso, sifnot) ->
      soit cond = type_expect env scond Predef.type_bool dans
      début filtre sifnot avec
        None ->
          soit ifso = type_expect env sifso Predef.type_unit dans
          rue {
            exp_desc = Texp_ifthenelse(cond, ifso, None);
            exp_loc = loc; exp_extra = [];
            exp_type = ifso.exp_type;
            exp_attributes = sexp.pexp_attributes;
            exp_env = env }
      | Some sifnot ->
          soit ifso = type_expect env sifso ty_expected dans
          soit ifnot = type_expect env sifnot ty_expected dans
          (* Keep sharing *)
          unify_exp env ifnot ifso.exp_type;
          re {
            exp_desc = Texp_ifthenelse(cond, ifso, Some ifnot);
            exp_loc = loc; exp_extra = [];
            exp_type = ifso.exp_type;
            exp_attributes = sexp.pexp_attributes;
            exp_env = env }
      fin
  | Pexp_sequence(sexp1, sexp2) ->
      soit exp1 = type_statement env sexp1 dans
      soit exp2 = type_expect env sexp2 ty_expected dans
      re {
        exp_desc = Texp_sequence(exp1, exp2);
        exp_loc = loc; exp_extra = [];
        exp_type = exp2.exp_type;
        exp_attributes = sexp.pexp_attributes;
        exp_env = env }
  | Pexp_while(scond, sbody) ->
      soit cond = type_expect env scond Predef.type_bool dans
      soit body = type_statement env sbody dans
      rue {
        exp_desc = Texp_while(cond, body);
        exp_loc = loc; exp_extra = [];
        exp_type = instance_def Predef.type_unit;
        exp_attributes = sexp.pexp_attributes;
        exp_env = env }
  | Pexp_for(param, slow, shigh, dir, sbody) ->
      soit low = type_expect env slow Predef.type_int dans
      soit high = type_expect env shigh Predef.type_int dans
      soit id, new_env =
        filtre param.ppat_desc avec
        | Ppat_any -> Ident.create "_for", env
        | Ppat_var {txt} ->
            Env.enter_value txt {val_type = instance_def Predef.type_int;
                                 val_attributes = [];
                                 val_kind = Val_reg; Types.val_loc = loc; } env
              ~check:(fonc s -> Warnings.Unused_for_index s)
        | _ ->
            raise (Error (param.ppat_loc, env, Invalid_for_loop_index))
      dans
      soit body = type_statement new_env sbody dans
      rue {
        exp_desc = Texp_for(id, param, low, high, dir, body);
        exp_loc = loc; exp_extra = [];
        exp_type = instance_def Predef.type_unit;
        exp_attributes = sexp.pexp_attributes;
        exp_env = env }
  | Pexp_constraint (sarg, sty) ->
      soit separate = vrai dans (* always separate, 1% slowdown for lablgtk *)
      si separate alors begin_def ();
      soit cty = Typetexp.transl_simple_type env faux sty dans
      soit ty = cty.ctyp_type dans
      soit (arg, ty') =
        si separate alors début
          end_def ();
          generalize_structure ty;
          (type_argument env sarg ty (instance env ty), instance env ty)
        fin sinon
          (type_argument env sarg ty ty, ty)
      dans
      rue {
        exp_desc = arg.exp_desc;
        exp_loc = arg.exp_loc;
        exp_type = ty';
        exp_attributes = arg.exp_attributes;
        exp_env = env;
        exp_extra =
          (Texp_constraint cty, loc, sexp.pexp_attributes) :: arg.exp_extra;
      }
  | Pexp_coerce(sarg, sty, sty') ->
      soit separate = vrai (* always separate, 1% slowdown for lablgtk *)
        (* !Clflags.principal || Env.has_local_constraints env *) dans
      soit (arg, ty',cty,cty') =
        filtre sty avec
        | None ->
            soit (cty', force) =
              Typetexp.transl_simple_type_delayed env sty'
            dans
            soit ty' = cty'.ctyp_type dans
            si separate alors begin_def ();
            soit arg = type_exp env sarg dans
            soit gen =
              si separate alors début
                end_def ();
                soit tv = newvar () dans
                soit gen = generalizable tv.level arg.exp_type dans
                unify_var env tv arg.exp_type;
                gen
              fin sinon vrai
            dans
            début filtre arg.exp_desc, !self_coercion, (repr ty').desc avec
              Texp_ident(_, _, {val_kind=Val_self _}), (path,r) :: _,
              Tconstr(path',_,_) quand Path.same path path' ->
                (* prerr_endline "self coercion"; *)
                r := loc :: !r;
                force ()
            | _ quand free_variables ~env arg.exp_type = []
                  && free_variables ~env ty' = [] ->
                si not gen && (* first try a single coercion *)
                  soit snap = snapshot () dans
                  soit ty, b = enlarge_type env ty' dans
                  essaie
                    force (); Ctype.unify env arg.exp_type ty; vrai
                  avec Unify _ ->
                    backtrack snap; faux
                alors ()
                sinon début essaie
                  soit force' = subtype env arg.exp_type ty' dans
                  force (); force' ();
                  si not gen alors
                    Location.prerr_warning loc
                      (Warnings.Not_principal "cette coercion de base");
                avec Subtype (tr1, tr2) ->
                  (* prerr_endline "coercion failed"; *)
                  raise(Error(loc, env, Not_subtype(tr1, tr2)))
                fin;
            | _ ->
                soit ty, b = enlarge_type env ty' dans
                force ();
                début essaie Ctype.unify env arg.exp_type ty avec Unify trace ->
                  raise(Error(sarg.pexp_loc, env,
                        Coercion_failure(ty', full_expand env ty', trace, b)))
                fin
            fin;
            (arg, ty', None, cty')
        | Some sty ->
            si separate alors begin_def ();
            soit (cty, force) =
              Typetexp.transl_simple_type_delayed env sty
            et (cty', force') =
              Typetexp.transl_simple_type_delayed env sty'
            dans
            soit ty = cty.ctyp_type dans
            soit ty' = cty'.ctyp_type dans
            début essaie
              soit force'' = subtype env ty ty' dans
              force (); force' (); force'' ()
            avec Subtype (tr1, tr2) ->
              raise(Error(loc, env, Not_subtype(tr1, tr2)))
            fin;
            si separate alors début
              end_def ();
              generalize_structure ty;
              generalize_structure ty';
              (type_argument env sarg ty (instance env ty),
               instance env ty', Some cty, cty')
            fin sinon
              (type_argument env sarg ty ty, ty', Some cty, cty')
      dans
      rue {
        exp_desc = arg.exp_desc;
        exp_loc = arg.exp_loc;
        exp_type = ty';
        exp_attributes = arg.exp_attributes;
        exp_env = env;
        exp_extra = (Texp_coerce (cty, cty'), loc, sexp.pexp_attributes) ::
                       arg.exp_extra;
      }
  | Pexp_send (e, met) ->
      si !Clflags.principal alors begin_def ();
      soit obj = type_exp env e dans
      début essaie
        soit (meth, exp, typ) =
          filtre obj.exp_desc avec
            Texp_ident(path, _, {val_kind = Val_self (meths, _, _, privty)}) ->
              soit (id, typ) =
                filter_self_method env met Private meths privty
              dans
              si is_Tvar (repr typ) alors
                Location.prerr_warning loc
                  (Warnings.Undeclared_virtual_method met);
              (Tmeth_val id, None, typ)
          | Texp_ident(path, lid, {val_kind = Val_anc (methods, cl_num)}) ->
              soit method_id =
                début essaie List.assoc met methods avec Not_found ->
                  raise(Error(e.pexp_loc, env, Undefined_inherited_method met))
                fin
              dans
              début filtre
                Env.lookup_value (Longident.Lident ("selfpat-" ^ cl_num)) env,
                Env.lookup_value (Longident.Lident ("self-" ^cl_num)) env
              avec
                (_, ({val_kind = Val_self (meths, _, _, privty)} tel desc)),
                (path, _) ->
                  soit (_, typ) =
                    filter_self_method env met Private meths privty
                  dans
                  soit method_type = newvar () dans
                  soit (obj_ty, res_ty) = filter_arrow env method_type "" dans
                  unify env obj_ty desc.val_type;
                  unify env res_ty (instance env typ);
                  soit exp =
                    Texp_apply({exp_desc =
                                Texp_ident(Path.Pident method_id, lid,
                                           {val_type = method_type;
                                            val_kind = Val_reg;
                                            val_attributes = [];
                                            Types.val_loc = Location.none});
                                exp_loc = loc; exp_extra = [];
                                exp_type = method_type;
                                exp_attributes = []; (* check *)
                                exp_env = env},
                          ["",
                            Some {exp_desc = Texp_ident(path, lid, desc);
                                  exp_loc = obj.exp_loc; exp_extra = [];
                                  exp_type = desc.val_type;
                                  exp_attributes = []; (* check *)
                                  exp_env = env},
                               Required])
                  dans
                  (Tmeth_name met, Some (re {exp_desc = exp;
                                             exp_loc = loc; exp_extra = [];
                                             exp_type = typ;
                                             exp_attributes = []; (* check *)
                                             exp_env = env}), typ)
              |  _ ->
                  affirme faux
              fin
          | _ ->
              (Tmeth_name met, None,
               filter_method env met Public obj.exp_type)
        dans
        si !Clflags.principal alors début
          end_def ();
          generalize_structure typ;
        fin;
        soit typ =
          filtre repr typ avec
            {desc = Tpoly (ty, [])} ->
              instance env ty
          | {desc = Tpoly (ty, tl); level = l} ->
              si !Clflags.principal && l <> generic_level alors
                Location.prerr_warning loc
                  (Warnings.Not_principal "cette utilisation de méthode polymorphe");
              snd (instance_poly faux tl ty)
          | {desc = Tvar _} tel ty ->
              soit ty' = newvar () dans
              unify env (instance_def ty) (newty(Tpoly(ty',[])));
              (* if not !Clflags.nolabels then
                 Location.prerr_warning loc (Warnings.Unknown_method met); *)
              ty'
          | _ ->
              affirme faux
        dans
        rue {
          exp_desc = Texp_send(obj, meth, exp);
          exp_loc = loc; exp_extra = [];
          exp_type = typ;
          exp_attributes = sexp.pexp_attributes;
          exp_env = env }
      avec Unify _ ->
        raise(Error(e.pexp_loc, env, Undefined_method (obj.exp_type, met)))
      fin
  | Pexp_new cl ->
      soit (cl_path, cl_decl) = Typetexp.find_class env loc cl.txt dans
      début filtre cl_decl.cty_new avec
          None ->
            raise(Error(loc, env, Virtual_class cl.txt))
        | Some ty ->
            rue {
              exp_desc = Texp_new (cl_path, cl, cl_decl);
              exp_loc = loc; exp_extra = [];
              exp_type = instance_def ty;
              exp_attributes = sexp.pexp_attributes;
              exp_env = env }
        fin
  | Pexp_setinstvar (lab, snewval) ->
      début essaie
        soit (path, desc) = Env.lookup_value (Longident.Lident lab.txt) env dans
        filtre desc.val_kind avec
          Val_ivar (Mutable, cl_num) ->
            soit newval =
              type_expect env snewval (instance env desc.val_type) dans
            soit (path_self, _) =
              Env.lookup_value (Longident.Lident ("self-" ^ cl_num)) env
            dans
            rue {
              exp_desc = Texp_setinstvar(path_self, path, lab, newval);
              exp_loc = loc; exp_extra = [];
              exp_type = instance_def Predef.type_unit;
              exp_attributes = sexp.pexp_attributes;
              exp_env = env }
        | Val_ivar _ ->
            raise(Error(loc, env, Instance_variable_not_mutable(vrai,lab.txt)))
        | _ ->
            raise(Error(loc, env, Instance_variable_not_mutable(faux,lab.txt)))
      avec
        Not_found ->
          raise(Error(loc, env, Unbound_instance_variable lab.txt))
      fin
  | Pexp_override lst ->
      soit _ =
       List.fold_right
        (fonc (lab, _) l ->
           si List.exists (fonc l -> l.txt = lab.txt) l alors
             raise(Error(loc, env,
                         Value_multiply_overridden lab.txt));
           lab::l)
        lst
        [] dans
      début filtre
        essaie
          Env.lookup_value (Longident.Lident "selfpat-*") env,
          Env.lookup_value (Longident.Lident "self-*") env
        avec Not_found ->
          raise(Error(loc, env, Outside_class))
      avec
        (_, {val_type = self_ty; val_kind = Val_self (_, vars, _, _)}),
        (path_self, _) ->
          soit type_override (lab, snewval) =
            début essaie
              soit (id, _, _, ty) = Vars.find lab.txt !vars dans
              (Path.Pident id, lab, type_expect env snewval (instance env ty))
            avec
              Not_found ->
                raise(Error(loc, env, Unbound_instance_variable lab.txt))
            fin
          dans
          soit modifs = List.map type_override lst dans
          rue {
            exp_desc = Texp_override(path_self, modifs);
            exp_loc = loc; exp_extra = [];
            exp_type = self_ty;
            exp_attributes = sexp.pexp_attributes;
            exp_env = env }
      | _ ->
          affirme faux
      fin
  | Pexp_letmodule(name, smodl, sbody) ->
      soit ty = newvar() dans
      (* remember original level *)
      begin_def ();
      Ident.set_current_time ty.level;
      soit context = Typetexp.narrow () dans
      soit modl = !type_module env smodl dans
      soit (id, new_env) = Env.enter_module name.txt modl.mod_type env dans
      Ctype.init_def(Ident.current_time());
      Typetexp.widen context;
      soit body = type_expect new_env sbody ty_expected dans
      (* go back to original level *)
      end_def ();
      (* Unification of body.exp_type with the fresh variable ty
         fails if and only if the prefix condition is violated,
         i.e. if generative types rooted at id show up in the
         type body.exp_type.  Thus, this unification enforces the
         scoping condition on "let module". *)
      début essaie
        Ctype.unify_var new_env ty body.exp_type
      avec Unify _ ->
        raise(Error(loc, env, Scoping_let_module(name.txt, body.exp_type)))
      fin;
      re {
        exp_desc = Texp_letmodule(id, name, modl, body);
        exp_loc = loc; exp_extra = [];
        exp_type = ty;
        exp_attributes = sexp.pexp_attributes;
        exp_env = env }
  | Pexp_assert (e) ->
      soit cond = type_expect env e Predef.type_bool dans
      soit exp_type =
        filtre cond.exp_desc avec
        | Texp_construct(_, {cstr_name="false"}, _) ->
            instance env ty_expected
        | _ ->
            instance_def Predef.type_unit
      dans
      rue {
        exp_desc = Texp_assert cond;
        exp_loc = loc; exp_extra = [];
        exp_type;
        exp_attributes = sexp.pexp_attributes;
        exp_env = env;
      }
  | Pexp_lazy e ->
      soit ty = newgenvar () dans
      soit to_unify = Predef.type_lazy_t ty dans
      unify_exp_types loc env to_unify ty_expected;
      soit arg = type_expect env e ty dans
      re {
        exp_desc = Texp_lazy arg;
        exp_loc = loc; exp_extra = [];
        exp_type = instance env ty_expected;
        exp_attributes = sexp.pexp_attributes;
        exp_env = env;
      }
  | Pexp_object s ->
      soit desc, sign, meths = !type_object env loc s dans
      rue {
        exp_desc = Texp_object (desc, (*sign,*) meths);
        exp_loc = loc; exp_extra = [];
        exp_type = sign.csig_self;
        exp_attributes = sexp.pexp_attributes;
        exp_env = env;
      }
  | Pexp_poly(sbody, sty) ->
      si !Clflags.principal alors begin_def ();
      soit ty, cty =
        filtre sty avec None -> repr ty_expected, None
        | Some sty ->
            soit sty = Ast_helper.Typ.force_poly sty dans
            soit cty = Typetexp.transl_simple_type env faux sty dans
            repr cty.ctyp_type, Some cty
      dans
      si !Clflags.principal alors début
        end_def ();
        generalize_structure ty
      fin;
      si sty <> None alors
        unify_exp_types loc env (instance env ty) (instance env ty_expected);
      soit exp =
        filtre (expand_head env ty).desc avec
          Tpoly (ty', []) ->
            soit exp = type_expect env sbody ty' dans
            { exp avec exp_type = instance env ty }
        | Tpoly (ty', tl) ->
            (* One more level to generalize locally *)
            begin_def ();
            si !Clflags.principal alors begin_def ();
            soit vars, ty'' = instance_poly vrai tl ty' dans
            si !Clflags.principal alors début
              end_def ();
              generalize_structure ty''
            fin;
            soit exp = type_expect env sbody ty'' dans
            end_def ();
            check_univars env faux "méthode" exp ty_expected vars;
            { exp avec exp_type = instance env ty }
        | Tvar _ ->
            soit exp = type_exp env sbody dans
            soit exp = {exp avec exp_type = newty (Tpoly (exp.exp_type, []))} dans
            unify_exp env exp ty;
            exp
        | _ -> affirme faux
      dans
      re { exp avec exp_extra =
             (Texp_poly cty, loc, sexp.pexp_attributes) :: exp.exp_extra }
  | Pexp_newtype(name, sbody) ->
      soit ty = newvar () dans
      (* remember original level *)
      begin_def ();
      (* Create a fake abstract type declaration for name. *)
      soit level = get_current_level () dans
      soit decl = {
        type_params = [];
        type_arity = 0;
        type_kind = Type_abstract;
        type_private = Public;
        type_manifest = None;
        type_variance = [];
        type_newtype_level = Some (level, level);
        type_loc = loc;
        type_attributes = [];
      }
      dans
      Ident.set_current_time ty.level;
      soit (id, new_env) = Env.enter_type name decl env dans
      Ctype.init_def(Ident.current_time());

      soit body = type_exp new_env sbody dans
      (* Replace every instance of this type constructor in the resulting
         type. *)
      soit seen = Hashtbl.create 8 dans
      soit rec replace t =
        si Hashtbl.mem seen t.id alors ()
        sinon début
          Hashtbl.add seen t.id ();
          filtre t.desc avec
          | Tconstr (Path.Pident id', _, _) quand id == id' -> link_type t ty
          | _ -> Btype.iter_type_expr replace t
        fin
      dans
      soit ety = Subst.type_expr Subst.identity body.exp_type dans
      replace ety;
      (* back to original level *)
      end_def ();
      (* lower the levels of the result type *)
      (* unify_var env ty ety; *)

      (* non-expansive if the body is non-expansive, so we don't introduce
         any new extra node in the typed AST. *)
      rue { body avec exp_loc = loc; exp_type = ety;
            exp_extra =
            (Texp_newtype name, loc, sexp.pexp_attributes) :: body.exp_extra }
  | Pexp_pack m ->
      soit (p, nl, tl) =
        filtre Ctype.expand_head env (instance env ty_expected) avec
          {desc = Tpackage (p, nl, tl)} ->
            si !Clflags.principal &&
              (Ctype.expand_head env ty_expected).level < Btype.generic_level
            alors
              Location.prerr_warning loc
                (Warnings.Not_principal "cet paquetage de module");
            (p, nl, tl)
        | {desc = Tvar _} ->
            raise (Error (loc, env, Cannot_infer_signature))
        | _ ->
            raise (Error (loc, env, Not_a_packed_module ty_expected))
      dans
      soit (modl, tl') = !type_package env m p nl tl dans
      rue {
        exp_desc = Texp_pack modl;
        exp_loc = loc; exp_extra = [];
        exp_type = newty (Tpackage (p, nl, tl'));
        exp_attributes = sexp.pexp_attributes;
        exp_env = env }
  | Pexp_open (ovf, lid, e) ->
      soit (path, newenv) = !type_open ovf env sexp.pexp_loc lid dans
      soit exp = type_expect newenv e ty_expected dans
      { exp avec
        exp_extra = (Texp_open (ovf, path, lid, newenv), loc,
                     sexp.pexp_attributes) ::
                      exp.exp_extra;
      }
  | Pexp_extension (s, _arg) ->
      raise (Error (s.loc, env, Extension s.txt))

et type_function ?in_function loc attrs env ty_expected l caselist =
  soit (loc_fun, ty_fun) =
    filtre in_function avec Some p -> p
    | None -> (loc, instance env ty_expected)
  dans
  soit separate = !Clflags.principal || Env.has_local_constraints env dans
  si separate alors begin_def ();
  soit (ty_arg, ty_res) =
    essaie filter_arrow env (instance env ty_expected) l
    avec Unify _ ->
      filtre expand_head env ty_expected avec
        {desc = Tarrow _} tel ty ->
          raise(Error(loc, env, Abstract_wrong_label(l, ty)))
      | _ ->
          raise(Error(loc_fun, env,
                      Too_many_arguments (in_function <> None, ty_fun)))
  dans
  soit ty_arg =
    si is_optional l alors
      soit tv = newvar() dans
      début
        essaie unify env ty_arg (type_option tv)
        avec Unify _ -> affirme faux
      fin;
      type_option tv
    sinon ty_arg
  dans
  si separate alors début
    end_def ();
    generalize_structure ty_arg;
    generalize_structure ty_res
  fin;
  soit cases, partial =
    type_cases ~in_function:(loc_fun,ty_fun) env ty_arg ty_res
      vrai loc caselist dans
  soit not_function ty =
    soit ls, tvar = list_labels env ty dans
    ls = [] && not tvar
  dans
  si is_optional l && not_function ty_res alors
    Location.prerr_warning (List.hd cases).c_lhs.pat_loc
      Warnings.Unerasable_optional_argument;
  re {
  exp_desc = Texp_function(l,cases, partial);
    exp_loc = loc; exp_extra = [];
    exp_type = instance env (newgenty (Tarrow(l, ty_arg, ty_res, Cok)));
    exp_attributes = attrs;
    exp_env = env }


et type_label_access env loc srecord lid =
  si !Clflags.principal alors begin_def ();
  soit record = type_exp env srecord dans
  si !Clflags.principal alors début
    end_def ();
    generalize_structure record.exp_type
  fin;
  soit ty_exp = record.exp_type dans
  soit opath =
    essaie
      soit (p0, p,_) = extract_concrete_record env ty_exp dans
      Some(p0, p, ty_exp.level = generic_level || not !Clflags.principal)
    avec Not_found -> None
  dans
  soit labels = Typetexp.find_all_labels env lid.loc lid.txt dans
  soit label =
    wrap_disambiguate "Cette expression a" ty_exp
      (Label.disambiguate lid env opath) labels dans
  (record, label, opath)

et type_label_exp create env loc ty_expected
          (lid, label, sarg) =
  (* Here also ty_expected may be at generic_level *)
  begin_def ();
  soit separate = !Clflags.principal || Env.has_local_constraints env dans
  si separate alors (begin_def (); begin_def ());
  soit (vars, ty_arg, ty_res) = instance_label vrai label dans
  si separate alors début
    end_def ();
    (* Generalize label information *)
    generalize_structure ty_arg;
    generalize_structure ty_res
  fin;
  début essaie
    unify env (instance_def ty_res) (instance env ty_expected)
  avec Unify trace ->
    raise (Error(lid.loc, env, Label_mismatch(lid.txt, trace)))
  fin;
  (* Instantiate so that we can generalize internal nodes *)
  soit ty_arg = instance_def ty_arg dans
  si separate alors début
    end_def ();
    (* Generalize information merged from ty_expected *)
    generalize_structure ty_arg
  fin;
  si label.lbl_private = Private alors
    si create alors
      raise (Error(loc, env, Private_type ty_expected))
    sinon
      raise (Error(lid.loc, env, Private_label(lid.txt, ty_expected)));
  soit arg =
    soit snap = si vars = [] alors None sinon Some (Btype.snapshot ()) dans
    soit arg = type_argument env sarg ty_arg (instance env ty_arg) dans
    end_def ();
    essaie
      check_univars env (vars <> []) "valeur du champ" arg label.lbl_arg vars;
      arg
    avec exn quand not (is_nonexpansive arg) -> essaie
      (* Try to retype without propagating ty_arg, cf PR#4862 *)
      may Btype.backtrack snap;
      begin_def ();
      soit arg = type_exp env sarg dans
      end_def ();
      generalize_expansive env arg.exp_type;
      unify_exp env arg ty_arg;
      check_univars env faux "valeur du champ" arg label.lbl_arg vars;
      arg
    avec Error (_, _, Less_general _) tel e -> raise e
    | _ -> raise exn    (* In case of failure return the first error *)
  dans
  (lid, label, {arg avec exp_type = instance env arg.exp_type})

et type_argument env sarg ty_expected' ty_expected =
  (* ty_expected' may be generic *)
  soit no_labels ty =
    soit ls, tvar = list_labels env ty dans
    not tvar && List.for_all ((=) "") ls
  dans
  soit rec is_inferred sexp =
    filtre sexp.pexp_desc avec
      Pexp_ident _ | Pexp_apply _ | Pexp_send _ | Pexp_field _ -> vrai
    | Pexp_open (_, _, e) -> is_inferred e
    | _ -> faux
  dans
  filtre expand_head env ty_expected' avec
    {desc = Tarrow("",ty_arg,ty_res,_); level = lv} quand is_inferred sarg ->
      (* apply optional arguments when expected type is "" *)
      (* we must be very careful about not breaking the semantics *)
      si !Clflags.principal alors begin_def ();
      soit texp = type_exp env sarg dans
      si !Clflags.principal alors début
        end_def ();
        generalize_structure texp.exp_type
      fin;
      soit rec make_args args ty_fun =
        filtre (expand_head env ty_fun).desc avec
        | Tarrow (l,ty_arg,ty_fun,_) quand is_optional l ->
            soit ty = option_none (instance env ty_arg) sarg.pexp_loc dans
            make_args ((l, Some ty, Optional) :: args) ty_fun
        | Tarrow (l,_,ty_res',_) quand l = "" || !Clflags.classic ->
            List.rev args, ty_fun, no_labels ty_res'
        | Tvar _ ->  List.rev args, ty_fun, faux
        |  _ -> [], texp.exp_type, faux
      dans
      soit args, ty_fun', simple_res = make_args [] texp.exp_type dans
      soit warn = !Clflags.principal &&
        (lv <> generic_level || (repr ty_fun').level <> generic_level)
      et texp = {texp avec exp_type = instance env texp.exp_type}
      et ty_fun = instance env ty_fun' dans
      si not (simple_res || no_labels ty_res) alors début
        unify_exp env texp ty_expected;
        texp
      fin sinon début
      unify_exp env {texp avec exp_type = ty_fun} ty_expected;
      si args = [] alors texp sinon
      (* eta-expand to avoid side effects *)
      soit var_pair name ty =
        soit id = Ident.create name dans
        {pat_desc = Tpat_var (id, mknoloc name); pat_type = ty;pat_extra=[];
         pat_attributes = [];
         pat_loc = Location.none; pat_env = env},
        {exp_type = ty; exp_loc = Location.none; exp_env = env;
         exp_extra = []; exp_attributes = [];
         exp_desc =
         Texp_ident(Path.Pident id, mknoloc (Longident.Lident name),
                    {val_type = ty; val_kind = Val_reg;
                     val_attributes = [];
                     Types.val_loc = Location.none})}
      dans
      soit eta_pat, eta_var = var_pair "eta" ty_arg dans
      soit func texp =
        soit e =
          {texp avec exp_type = ty_res; exp_desc =
           Texp_apply
             (texp,
              args @ ["", Some eta_var, Required])}
        dans
        { texp avec exp_type = ty_fun; exp_desc =
          Texp_function("", [case eta_pat e], Total) }
      dans
      Location.prerr_warning texp.exp_loc
        (Warnings.Eliminated_optional_arguments (List.map (fonc (l, _, _) -> l) args));
      si warn alors Location.prerr_warning texp.exp_loc
          (Warnings.Without_principality "argument implicite éliminé");
      si is_nonexpansive texp alors func texp sinon
      (* let-expand to have side effects *)
      soit let_pat, let_var = var_pair "arg" texp.exp_type dans
      re { texp avec exp_type = ty_fun; exp_desc =
           Texp_let (Nonrecursive,
                     [{vb_pat=let_pat; vb_expr=texp; vb_attributes=[]}],
                     func let_var) }
      fin
  | _ ->
      soit texp = type_expect env sarg ty_expected' dans
      unify_exp env texp ty_expected;
      texp

et type_application env funct sargs =
  (* funct.exp_type may be generic *)
  soit result_type omitted ty_fun =
    List.fold_left
      (fonc ty_fun (l,ty,lv) -> newty2 lv (Tarrow(l,ty,ty_fun,Cok)))
      ty_fun omitted
  dans
  soit has_label l ty_fun =
    soit ls, tvar = list_labels env ty_fun dans
    tvar || List.mem l ls
  dans
  soit ignored = ref [] dans
  soit rec type_unknown_args
      (args :
      (Asttypes.label * (unit -> Typedtree.expression) option *
         Typedtree.optional) list)
    omitted ty_fun = fonction
      [] ->
        (List.map
            (fonction l, None, x -> l, None, x
                | l, Some f, x -> l, Some (f ()), x)
           (List.rev args),
         instance env (result_type omitted ty_fun))
    | (l1, sarg1) :: sargl ->
        soit (ty1, ty2) =
          soit ty_fun = expand_head env ty_fun dans
          filtre ty_fun.desc avec
            Tvar _ ->
              soit t1 = newvar () et t2 = newvar () dans
              soit not_identity = fonction
                  Texp_ident(_,_,{val_kind=Val_prim
                                  {Primitive.prim_name="%identity"}}) ->
                    faux
                | _ -> vrai
              dans
              si ty_fun.level >= t1.level && not_identity funct.exp_desc alors
                Location.prerr_warning sarg1.pexp_loc Warnings.Unused_argument;
              unify env ty_fun (newty (Tarrow(l1,t1,t2,Clink(ref Cunknown))));
              (t1, t2)
          | Tarrow (l,t1,t2,_) quand l = l1
            || !Clflags.classic && l1 = "" && not (is_optional l) ->
              (t1, t2)
          | td ->
              soit ty_fun =
                filtre td avec Tarrow _ -> newty td | _ -> ty_fun dans
              soit ty_res = result_type (omitted @ !ignored) ty_fun dans
              filtre ty_res.desc avec
                Tarrow _ ->
                  si (!Clflags.classic || not (has_label l1 ty_fun)) alors
                    raise (Error(sarg1.pexp_loc, env,
                                 Apply_wrong_label(l1, ty_res)))
                  sinon
                    raise (Error(funct.exp_loc, env, Incoherent_label_order))
              | _ ->
                  raise(Error(funct.exp_loc, env, Apply_non_function
                                (expand_head env funct.exp_type)))
        dans
        soit optional = si is_optional l1 alors Optional sinon Required dans
        soit arg1 () =
          soit arg1 = type_expect env sarg1 ty1 dans
          si optional = Optional alors
            unify_exp env arg1 (type_option(newvar()));
          arg1
        dans
        type_unknown_args ((l1, Some arg1, optional) :: args) omitted ty2 sargl
  dans
  soit ignore_labels =
    !Clflags.classic ||
    début
      soit ls, tvar = list_labels env funct.exp_type dans
      not tvar &&
      soit labels = List.filter (fonc l -> not (is_optional l)) ls dans
      List.length labels = List.length sargs &&
      List.for_all (fonc (l,_) -> l = "") sargs &&
      List.exists (fonc l -> l <> "") labels &&
      (Location.prerr_warning funct.exp_loc Warnings.Labels_omitted;
       vrai)
    fin
  dans
  soit warned = ref faux dans
  soit rec type_args args omitted ty_fun ty_fun0 ty_old sargs more_sargs =
    filtre expand_head env ty_fun, expand_head env ty_fun0 avec
      {desc=Tarrow (l, ty, ty_fun, com); level=lv} tel ty_fun',
      {desc=Tarrow (_, ty0, ty_fun0, _)}
      quand (sargs <> [] || more_sargs <> []) && commu_repr com = Cok ->
        soit may_warn loc w =
          si not !warned && !Clflags.principal && lv <> generic_level
          alors début
            warned := vrai;
            Location.prerr_warning loc w
          fin
        dans
        soit name = label_name l
        et optional = si is_optional l alors Optional sinon Required dans
        soit sargs, more_sargs, arg =
          si ignore_labels && not (is_optional l) alors début
            (* In classic mode, omitted = [] *)
            filtre sargs, more_sargs avec
              (l', sarg0) :: _, _ ->
                raise(Error(sarg0.pexp_loc, env,
                            Apply_wrong_label(l', ty_old)))
            | _, (l', sarg0) :: more_sargs ->
                si l <> l' && l' <> "" alors
                  raise(Error(sarg0.pexp_loc, env,
                              Apply_wrong_label(l', ty_fun')))
                sinon
                  ([], more_sargs,
                   Some (fonc () -> type_argument env sarg0 ty ty0))
            | _ ->
                affirme faux
          fin sinon essaie
            soit (l', sarg0, sargs, more_sargs) =
              essaie
                soit (l', sarg0, sargs1, sargs2) = extract_label name sargs dans
                si sargs1 <> [] alors
                  may_warn sarg0.pexp_loc
                    (Warnings.Not_principal "commuter cet argument");
                (l', sarg0, sargs1 @ sargs2, more_sargs)
              avec Not_found ->
                soit (l', sarg0, sargs1, sargs2) =
                  extract_label name more_sargs dans
                si sargs1 <> [] || sargs <> [] alors
                  may_warn sarg0.pexp_loc
                    (Warnings.Not_principal "commuter this argument");
                (l', sarg0, sargs @ sargs1, sargs2)
            dans
            si optional = Required && is_optional l' alors
              Location.prerr_warning sarg0.pexp_loc
                (Warnings.Nonoptional_label l);
            sargs, more_sargs,
            si optional = Required || is_optional l' alors
              Some (fonc () -> type_argument env sarg0 ty ty0)
            sinon début
              may_warn sarg0.pexp_loc
                (Warnings.Not_principal "utiliser un argument optionnel ici");
              Some (fonc () -> option_some (type_argument env sarg0
                                             (extract_option_type env ty)
                                             (extract_option_type env ty0)))
            fin
          avec Not_found ->
            sargs, more_sargs,
            si optional = Optional &&
              (List.mem_assoc "" sargs || List.mem_assoc "" more_sargs)
            alors début
              may_warn funct.exp_loc
                (Warnings.Without_principality "argument optionnel éliminé");
              ignored := (l,ty,lv) :: !ignored;
              Some (fonc () -> option_none (instance env ty) Location.none)
            fin sinon début
              may_warn funct.exp_loc
                (Warnings.Without_principality "argument commuté");
              None
            fin
        dans
        soit omitted =
          si arg = None alors (l,ty,lv) :: omitted sinon omitted dans
        soit ty_old = si sargs = [] alors ty_fun sinon ty_old dans
        type_args ((l,arg,optional)::args) omitted ty_fun ty_fun0
          ty_old sargs more_sargs
    | _ ->
        filtre sargs avec
          (l, sarg0) :: _ quand ignore_labels ->
            raise(Error(sarg0.pexp_loc, env,
                        Apply_wrong_label(l, ty_old)))
        | _ ->
            type_unknown_args args omitted ty_fun0
              (sargs @ more_sargs)
  dans
  filtre funct.exp_desc, sargs avec
    (* Special case for ignore: avoid discarding warning *)
    Texp_ident (_, _, {val_kind=Val_prim{Primitive.prim_name="%ignore"}}),
    ["", sarg] ->
      soit ty_arg, ty_res = filter_arrow env (instance env funct.exp_type) "" dans
      soit exp = type_expect env sarg ty_arg dans
      début filtre (expand_head env exp.exp_type).desc avec
      | Tarrow _ ->
          Location.prerr_warning exp.exp_loc Warnings.Partial_application
      | Tvar _ ->
          add_delayed_check (fonc () -> check_application_result env faux exp)
      | _ -> ()
      fin;
      (["", Some exp, Required], ty_res)
  | _ ->
      soit ty = funct.exp_type dans
      si ignore_labels alors
        type_args [] [] ty (instance env ty) ty [] sargs
      sinon
        type_args [] [] ty (instance env ty) ty sargs []

et type_construct env loc lid sarg ty_expected attrs =
  soit opath =
    essaie
      soit (p0, p,_) = extract_concrete_variant env ty_expected dans
      Some(p0, p, ty_expected.level = generic_level || not !Clflags.principal)
    avec Not_found -> None
  dans
  soit constrs = Typetexp.find_all_constructors env lid.loc lid.txt dans
  soit constr =
    wrap_disambiguate "Cette expression de type somme doit avoir" ty_expected
      (Constructor.disambiguate lid env opath) constrs dans
  Env.mark_constructor Env.Positive env (Longident.last lid.txt) constr;
  Typetexp.check_deprecated loc constr.cstr_attributes constr.cstr_name;
  soit sargs =
    filtre sarg avec
      None -> []
    | Some {pexp_desc = Pexp_tuple sel} quand constr.cstr_arity > 1 -> sel
    | Some se -> [se] dans
  si List.length sargs <> constr.cstr_arity alors
    raise(Error(loc, env, Constructor_arity_mismatch
                  (lid.txt, constr.cstr_arity, List.length sargs)));
  soit separate = !Clflags.principal || Env.has_local_constraints env dans
  si separate alors (begin_def (); begin_def ());
  soit (ty_args, ty_res) = instance_constructor constr dans
  soit texp =
    re {
      exp_desc = Texp_construct(lid, constr, []);
      exp_loc = loc; exp_extra = [];
      exp_type = ty_res;
      exp_attributes = attrs;
      exp_env = env } dans
  si separate alors début
    end_def ();
    generalize_structure ty_res;
    unify_exp env {texp avec exp_type = instance_def ty_res}
                  (instance env ty_expected);
    end_def ();
    List.iter generalize_structure ty_args;
    generalize_structure ty_res;
  fin;
  soit ty_args0, ty_res =
    filtre instance_list env (ty_res :: ty_args) avec
      t :: tl -> tl, t
    | _ -> affirme faux
  dans
  soit texp = {texp avec exp_type = ty_res} dans
  si not separate alors unify_exp env texp (instance env ty_expected);
  soit args = List.map2 (fonc e (t,t0) -> type_argument env e t t0) sargs
      (List.combine ty_args ty_args0) dans
  si constr.cstr_private = Private alors
    raise(Error(loc, env, Private_type ty_res));
  (* NOTE: shouldn't we call "re" on this final expression? -- AF *)
  { texp avec
    exp_desc = Texp_construct(lid, constr, args) }

(* Typing of statements (expressions whose values are discarded) *)

et type_statement env sexp =
  soit loc = (final_subexpression sexp).pexp_loc dans
  begin_def();
  soit exp = type_exp env sexp dans
  end_def();
  si !Clflags.strict_sequence alors
    soit expected_ty = instance_def Predef.type_unit dans
    unify_exp env exp expected_ty;
    exp sinon
  soit ty = expand_head env exp.exp_type et tv = newvar() dans
  début filtre ty.desc avec
  | Tarrow _ ->
      Location.prerr_warning loc Warnings.Partial_application
  | Tconstr (p, _, _) quand Path.same p Predef.path_unit -> ()
  | Tvar _ quand ty.level > tv.level ->
      Location.prerr_warning loc Warnings.Nonreturning_statement
  | Tvar _ ->
      add_delayed_check (fonc () -> check_application_result env vrai exp)
  | _ ->
      Location.prerr_warning loc Warnings.Statement_type
  fin;
  unify_var env tv ty;
  exp

(* Typing of match cases *)

et type_cases ?in_function env ty_arg ty_res partial_flag loc caselist =
  (* ty_arg is _fully_ generalized *)
  soit patterns = List.map (fonc {pc_lhs=p} -> p) caselist dans
  soit erase_either =
    List.exists contains_polymorphic_variant patterns
    && contains_variant_either ty_arg
  et has_gadts = List.exists (contains_gadt env) patterns dans
(*  prerr_endline ( if has_gadts then "contains gadt" else "no gadt"); *)
  soit ty_arg =
    si (has_gadts || erase_either) && not !Clflags.principal
    alors correct_levels ty_arg sinon ty_arg
  et ty_res, env =
    si has_gadts && not !Clflags.principal alors
      correct_levels ty_res, duplicate_ident_types loc caselist env
    sinon ty_res, env
  dans
  soit lev, env =
    si has_gadts alors début
      (* raise level for existentials *)
      begin_def ();
      Ident.set_current_time (get_current_level ());
      soit lev = Ident.current_time () dans
      Ctype.init_def (lev+1000);                 (* up to 1000 existentials *)
      (lev, Env.add_gadt_instance_level lev env)
    fin sinon (get_current_level (), env)
  dans
(*  if has_gadts then
    Format.printf "lev = %d@.%a@." lev Printtyp.raw_type_expr ty_res; *)
  begin_def (); (* propagation of the argument *)
  soit ty_arg' = newvar () dans
  soit pattern_force = ref [] dans
(*  Format.printf "@[%i %i@ %a@]@." lev (get_current_level())
    Printtyp.raw_type_expr ty_arg; *)
  soit pat_env_list =
    List.map
      (fonc {pc_lhs; pc_guard; pc_rhs} ->
        soit loc =
          soit ouvre Location dans
          filtre pc_guard avec
          | None -> pc_rhs.pexp_loc
          | Some g -> {pc_rhs.pexp_loc avec loc_start=g.pexp_loc.loc_start}
        dans
        si !Clflags.principal alors begin_def (); (* propagation of pattern *)
        soit scope = Some (Annot.Idef loc) dans
        soit (pat, ext_env, force, unpacks) =
          soit partial =
            si !Clflags.principal || erase_either
            alors Some faux sinon None dans
          soit ty_arg = instance ?partial env ty_arg dans
          type_pattern ~lev env pc_lhs scope ty_arg
        dans
        pattern_force := force @ !pattern_force;
        soit pat =
          si !Clflags.principal alors début
            end_def ();
            iter_pattern (fonc {pat_type=t} -> generalize_structure t) pat;
            { pat avec pat_type = instance env pat.pat_type }
          fin sinon pat
        dans
        (pat, (ext_env, unpacks)))
      caselist dans
  (* Unify cases (delayed to keep it order-free) *)
  soit patl = List.map fst pat_env_list dans
  List.iter (fonc pat -> unify_pat env pat ty_arg') patl;
  (* Check for polymorphic variants to close *)
  si List.exists has_variants patl alors début
    Parmatch.pressure_variants env patl;
    List.iter (iter_pattern finalize_variant) patl
  fin;
  (* `Contaminating' unifications start here *)
  List.iter (fonc f -> f()) !pattern_force;
  (* Post-processing and generalization *)
  List.iter (iter_pattern (fonc {pat_type=t} -> unify_var env t (newvar())))
    patl;
  List.iter (fonc pat -> unify_pat env pat (instance env ty_arg)) patl;
  end_def ();
  List.iter (iter_pattern (fonc {pat_type=t} -> generalize t)) patl;
  (* type bodies *)
  soit in_function = si List.length caselist = 1 alors in_function sinon None dans
  soit cases =
    List.map2
      (fonc (pat, (ext_env, unpacks)) {pc_lhs; pc_guard; pc_rhs} ->
        soit sexp = wrap_unpacks pc_rhs unpacks dans
        soit ty_res' =
          si !Clflags.principal alors début
            begin_def ();
            soit ty = instance ~partial:vrai env ty_res dans
            end_def ();
            generalize_structure ty; ty
          fin
          sinon si contains_gadt env pc_lhs alors correct_levels ty_res
          sinon ty_res dans
(*        Format.printf "@[%i %i, ty_res' =@ %a@]@." lev (get_current_level())
          Printtyp.raw_type_expr ty_res'; *)
        soit guard =
          filtre pc_guard avec
          | None -> None
          | Some scond ->
              Some
                (type_expect ext_env (wrap_unpacks scond unpacks)
                   Predef.type_bool)
        dans
        soit exp = type_expect ?in_function ext_env sexp ty_res' dans
        {
         c_lhs = pat;
         c_guard = guard;
         c_rhs = {exp avec exp_type = instance env ty_res'}
        }
      )
      pat_env_list caselist
  dans
  si !Clflags.principal || has_gadts alors début
    soit ty_res' = instance env ty_res dans
    List.iter (fonc c -> unify_exp env c.c_rhs ty_res') cases
  fin;
  soit partial =
    si partial_flag alors
      Parmatch.check_partial_gadt (partial_pred ~lev env ty_arg) loc cases
    sinon
      Partial
  dans
  add_delayed_check
    (fonc () ->
      List.iter (fonc (pat, (env, _)) -> check_absent_variant env pat)
        pat_env_list;
      Parmatch.check_unused env cases);
  si has_gadts alors début
    end_def ();
    (* Ensure that existential types do not escape *)
    unify_exp_types loc env (instance env ty_res) (newvar ()) ;
  fin;
  cases, partial

(* Typing of let bindings *)

et type_let ?(check = fonc s -> Warnings.Unused_var s)
             ?(check_strict = fonc s -> Warnings.Unused_var_strict s)
    env rec_flag spat_sexp_list scope allow =
  soit ouvre Ast_helper dans
  begin_def();
  si !Clflags.principal alors begin_def ();

  soit is_fake_let =
    filtre spat_sexp_list avec
    | [{pvb_expr={pexp_desc=Pexp_match(
           {pexp_desc=Pexp_ident({ txt = Longident.Lident "*opt*"})},_)}}] ->
        vrai (* the fake let-declaration introduced by fun ?(x = e) -> ... *)
    | _ ->
        faux
  dans
  soit check = si is_fake_let alors check_strict sinon check dans

  soit spatl =
    List.map
      (fonc {pvb_pat=spat; pvb_expr=sexp; pvb_attributes=_} ->
        filtre spat.ppat_desc, sexp.pexp_desc avec
          (Ppat_any | Ppat_constraint _), _ -> spat
        | _, Pexp_coerce (_, _, sty)
        | _, Pexp_constraint (_, sty) quand !Clflags.principal ->
            (* propagate type annotation to pattern,
               to allow it to be generalized in -principal mode *)
            Pat.constraint_
              ~loc:{spat.ppat_loc avec Location.loc_ghost=vrai}
              spat
              sty
        | _ -> spat)
      spat_sexp_list dans
  soit nvs = List.map (fonc _ -> newvar ()) spatl dans
  soit (pat_list, new_env, force, unpacks) =
    type_pattern_list env spatl scope nvs allow dans
  soit is_recursive = (rec_flag = Recursive) dans
  (* If recursive, first unify with an approximation of the expression *)
  si is_recursive alors
    List.iter2
      (fonc pat binding ->
        soit pat =
          filtre pat.pat_type.desc avec
          | Tpoly (ty, tl) ->
              {pat avec pat_type =
               snd (instance_poly ~keep_names:vrai faux tl ty)}
          | _ -> pat
        dans unify_pat env pat (type_approx env binding.pvb_expr))
      pat_list spat_sexp_list;
  (* Polymorphic variant processing *)
  List.iter
    (fonc pat ->
      si has_variants pat alors début
        Parmatch.pressure_variants env [pat];
        iter_pattern finalize_variant pat
      fin)
    pat_list;
  (* Generalize the structure *)
  soit pat_list =
    si !Clflags.principal alors début
      end_def ();
      List.map
        (fonc pat ->
          iter_pattern (fonc pat -> generalize_structure pat.pat_type) pat;
          {pat avec pat_type = instance env pat.pat_type})
        pat_list
    fin sinon pat_list dans
  (* Only bind pattern variables after generalizing *)
  List.iter (fonc f -> f()) force;
  soit exp_env =
    si is_recursive alors new_env sinon env dans

  soit current_slot = ref None dans
  soit rec_needed = ref faux dans
  soit warn_unused =
    Warnings.is_active (check "") || Warnings.is_active (check_strict "") ||
    (is_recursive && (Warnings.is_active Warnings.Unused_rec_flag))
  dans
  soit pat_slot_list =
    (* Algorithm to detect unused declarations in recursive bindings:
       - During type checking of the definitions, we capture the 'value_used'
         events on the bound identifiers and record them in a slot corresponding
         to the current definition (!current_slot).
         In effect, this creates a dependency graph between definitions.

       - After type checking the definition (!current_slot = None),
         when one of the bound identifier is effectively used, we trigger
         again all the events recorded in the corresponding slot.
         The effect is to traverse the transitive closure of the graph created
         in the first step.

       We also keep track of whether *all* variables in a given pattern
       are unused. If this is the case, for local declarations, the issued
       warning is 26, not 27.
     *)
    List.map
      (fonc pat ->
        si not warn_unused alors pat, None
        sinon
          soit some_used = ref faux dans
            (* has one of the identifier of this pattern been used? *)
          soit slot = ref [] dans
          List.iter
            (fonc (id,_) ->
              soit vd = Env.find_value (Path.Pident id) new_env dans
              (* note: Env.find_value does not trigger the value_used event *)
              soit name = Ident.name id dans
              soit used = ref faux dans
              si not (name = "" || name.[0] = '_' || name.[0] = '#') alors
                add_delayed_check
                  (fonc () ->
                    si not !used alors
                      Location.prerr_warning vd.Types.val_loc
                        ((si !some_used alors check_strict sinon check) name)
                  );
              Env.set_value_used_callback
                name vd
                (fonc () ->
                  filtre !current_slot avec
                  | Some slot ->
                      slot := (name, vd) :: !slot; rec_needed := vrai
                  | None ->
                      List.iter
                        (fonc (name, vd) -> Env.mark_value_used name vd)
                        (get_ref slot);
                      used := vrai;
                      some_used := vrai
                )
            )
            (Typedtree.pat_bound_idents pat);
          pat, Some slot
        )
      pat_list
  dans
  soit exp_list =
    List.map2
      (fonc {pvb_expr=sexp; _} (pat, slot) ->
        soit sexp =
          si rec_flag = Recursive alors wrap_unpacks sexp unpacks sinon sexp dans
        si is_recursive alors current_slot := slot;
        filtre pat.pat_type.desc avec
        | Tpoly (ty, tl) ->
            begin_def ();
            si !Clflags.principal alors begin_def ();
            soit vars, ty' = instance_poly ~keep_names:vrai vrai tl ty dans
            si !Clflags.principal alors début
              end_def ();
              generalize_structure ty'
            fin;
            soit exp = type_expect exp_env sexp ty' dans
            end_def ();
            check_univars env vrai "définition" exp pat.pat_type vars;
            {exp avec exp_type = instance env exp.exp_type}
        | _ -> type_expect exp_env sexp pat.pat_type)
      spat_sexp_list pat_slot_list dans
  current_slot := None;
  si is_recursive && not !rec_needed
  && Warnings.is_active Warnings.Unused_rec_flag alors
    Location.prerr_warning (List.hd spat_sexp_list).pvb_pat.ppat_loc
      Warnings.Unused_rec_flag;
  List.iter2
    (fonc pat exp -> ignore(Parmatch.check_partial pat.pat_loc [case pat exp]))
    pat_list exp_list;
  end_def();
  List.iter2
    (fonc pat exp ->
       si not (is_nonexpansive exp) alors
         iter_pattern (fonc pat -> generalize_expansive env pat.pat_type) pat)
    pat_list exp_list;
  List.iter
    (fonc pat -> iter_pattern (fonc pat -> generalize pat.pat_type) pat)
    pat_list;
  soit l = List.combine pat_list exp_list dans
  soit l =
    List.map2
      (fonc (p, e) pvb ->
        {vb_pat=p; vb_expr=e; vb_attributes=pvb.pvb_attributes})
      l spat_sexp_list
  dans
  (l, new_env, unpacks)

(* Typing of toplevel bindings *)

soit type_binding env rec_flag spat_sexp_list scope =
  Typetexp.reset_type_variables();
  soit (pat_exp_list, new_env, unpacks) =
    type_let
      ~check:(fonc s -> Warnings.Unused_value_declaration s)
      ~check_strict:(fonc s -> Warnings.Unused_value_declaration s)
      env rec_flag spat_sexp_list scope faux
  dans
  (pat_exp_list, new_env)

soit type_let env rec_flag spat_sexp_list scope =
  soit (pat_exp_list, new_env, unpacks) =
    type_let env rec_flag spat_sexp_list scope faux dans
  (pat_exp_list, new_env)

(* Typing of toplevel expressions *)

soit type_expression env sexp =
  Typetexp.reset_type_variables();
  begin_def();
  soit exp = type_exp env sexp dans
  end_def();
  si is_nonexpansive exp alors generalize exp.exp_type
  sinon generalize_expansive env exp.exp_type;
  filtre sexp.pexp_desc avec
    Pexp_ident lid ->
      (* Special case for keeping type variables when looking-up a variable *)
      soit (path, desc) = Env.lookup_value lid.txt env dans
      {exp avec exp_type = desc.val_type}
  | _ -> exp

(* Error report *)

ouvre Format
ouvre Printtyp

soit report_error env ppf = fonction
  | Polymorphic_label lid ->
      fprintf ppf "@[Le champs d'enregistrement %a est polymophe.@ %s@]"
        longident lid "Vous ne pouvez pas l'instancier dans un motif."
  | Constructor_arity_mismatch(lid, expected, provided) ->
      fprintf ppf
       "@[Le constructeur %a@ attend %i argument(s),@ \
        mais est appliqué ici à %i argument(s)@]"
       longident lid expected provided
  | Label_mismatch(lid, trace) ->
      report_unification_error ppf env trace
        (fonction ppf ->
           fprintf ppf "Le champ %a@ appartient au type"
                   longident lid)
        (fonction ppf ->
           fprintf ppf "mais est mélangé ici avec des champs du type")
  | Pattern_type_clash trace ->
      report_unification_error ppf env trace
        (fonction ppf ->
          fprintf ppf "Ce motif filtre des valeurs de type")
        (fonction ppf ->
          fprintf ppf "mais il était attendu un motif filtrant des valeurs de type")
  | Or_pattern_type_clash (id, trace) ->
      report_unification_error ppf env trace
        (fonction ppf ->
          fprintf ppf "La variable %s du membre gauche de ce motif | a le type" (Ident.name id))
        (fonction ppf ->
          fprintf ppf "mais son membre droit a le type")
  | Multiply_bound_variable name ->
      fprintf ppf "La variable %s est liée plusieurs fois dans ce motif" name
  | Orpat_vars id ->
      fprintf ppf "La variable %s doit apparaître des deux côtés de ce motif |"
        (Ident.name id)
  | Expr_type_clash trace ->
      report_unification_error ppf env trace
        (fonction ppf ->
           fprintf ppf "Cette expression a le type")
        (fonction ppf ->
           fprintf ppf "mais son type attendu est")
  | Apply_non_function typ ->
      reset_and_mark_loops typ;
      début filtre (repr typ).desc avec
        Tarrow _ ->
          fprintf ppf "@[<v>@[<2>Cette fonction a le type@ %a@]"
            type_expr typ;
          fprintf ppf "@ @[Elle est appliquée a trop d'arguments;@ %s@]@]"
                      "peut-être avez-vous oublié un `;'."
      | _ ->
          fprintf ppf "@[<v>@[<2>Cette expression a le type@ %a@]@ %s@]"
            type_expr typ
            "Ce n'est pas une fonction ; elle ne peut pas être appliquée."
      fin
  | Apply_wrong_label (l, ty) ->
      soit print_label ppf = fonction
        | "" -> fprintf ppf "sans label"
        | l ->
            fprintf ppf "avec le label %s%s" (si is_optional l alors "" sinon "~") l
      dans
      reset_and_mark_loops ty;
      fprintf ppf
        "@[<v>@[<2>La fonction appliquée à cete argument a le type@ %a@]@.\
          Cet arguement ne peut pas être appliqué %a@]"
        type_expr ty print_label l
  | Label_multiply_defined s ->
      fprintf ppf "Le champ d'enregistrement %s est défini plusieurs fois" s
  | Label_missing labels ->
      soit print_labels ppf =
        List.iter (fonc lbl -> fprintf ppf "@ %s" (Ident.name lbl)) dans
      fprintf ppf "@[<hov>Des champs d'enregistrements ne sont pas définis :%a@]"
        print_labels labels
  | Label_not_mutable lid ->
      fprintf ppf "Le champ d'enregistrement %a n'est pas mutable" longident lid
  | Wrong_name (eorp, ty, kind, p, lid) ->
      reset_and_mark_loops ty;
      fprintf ppf "@[@[<2>%s le type@ %a@]@ "
        eorp type_expr ty;
      fprintf ppf "%s %a n'appartient pas au type %a@]"
        (si kind = "enregistrement" alors "Le champ" sinon "Le constructeur")
        longident lid (*kind*) path p;
      si kind = "enregistrement" alors Label.spellcheck ppf env p lid
                                   sinon Constructor.spellcheck ppf env p lid
  | Name_type_mismatch (kind, lid, tp, tpl) ->
      soit name = si kind = "enregistrement" alors "champ" sinon "constructeur" dans
      report_ambiguous_type_error ppf env tp tpl
        (fonction ppf ->
           fprintf ppf "Le %s %a@ appartient au type %s"
             name longident lid kind)
        (fonction ppf ->
           fprintf ppf "Le %s %a@ appartient à l'un des types de %s suivants :"
             name longident lid kind)
        (fonction ppf ->
           fprintf ppf "mais un %s devait appartenir au type %s"
             name kind)
  | Incomplete_format s ->
      fprintf ppf "Fin de chaîne de format prématurée ``%S''" s
  | Bad_conversion (fmt, i, c) ->
      fprintf ppf
        "Mauvaise conversion %%%c, au caractère numéro %d \
         dans la chaîne de format ``%s''" c i fmt
  | Undefined_method (ty, me) ->
      reset_and_mark_loops ty;
      fprintf ppf
        "@[<v>@[Cette expression a le type@;<1 2>%a@]@,\
         Il n'a pas de méthode %s@]" type_expr ty me
  | Undefined_inherited_method me ->
      fprintf ppf "Cette expression n'a pas de méthode %s" me
  | Virtual_class cl ->
      fprintf ppf "Impossible d'instancier la classe virtuelle %a"
        longident cl
  | Unbound_instance_variable v ->
      fprintf ppf "Variable d'instance non liée %s" v
  | Instance_variable_not_mutable (b, v) ->
      si b alors
        fprintf ppf "La variable d'instance %s n'est pas mutable" v
      sinon
        fprintf ppf "La valeur %s n'est pas une variable d'instance" v
  | Not_subtype(tr1, tr2) ->
      report_subtyping_error ppf env tr1 "n'est pas un sous-type de" tr2
  | Outside_class ->
      fprintf ppf "Cette duplication d'objet apparaît en dehors d'une définition de méthode"
  | Value_multiply_overridden v ->
      fprintf ppf "La variable d'instance %s est redéfinie plusieurs fois" v
  | Coercion_failure (ty, ty', trace, b) ->
      report_unification_error ppf env trace
        (fonction ppf ->
           soit ty, ty' = prepare_expansion (ty, ty') dans
           fprintf ppf
             "Cette expression ne peut pas être coercée au type@;<1 2>%a;@ elle a le type"
           (type_expansion ty) ty')
        (fonction ppf ->
           fprintf ppf "mais elle est utilisée avec le type");
      si b alors
        fprintf ppf ".@.@[<hov>%s@ %s@]"
          "Cette coercion simple n'est pas complètement générale."
          "Considérez l'utilisation d'une double coercion."
  | Too_many_arguments (in_function, ty) ->
      reset_and_mark_loops ty;
      si in_function alors début
        fprintf ppf "Cette fonction attend trop d'arguments,@ ";
        fprintf ppf "elle devrait avoir le type@ %a"
          type_expr ty
      fin sinon début
        fprintf ppf "Cette expression ne devrait pas être une fonction,@ ";
        fprintf ppf "Son type attendu est@ %a"
          type_expr ty
      fin
  | Abstract_wrong_label (l, ty) ->
      soit label_mark = fonction
        | "" -> "mais son premier argument n'a pas de label"
        |  l -> sprintf "mais son premier argument a le label ~%s" l dans
      reset_and_mark_loops ty;
      fprintf ppf "@[<v>@[<2>Cette fonction devrait avoir le type@ %a@]@,%s@]"
      type_expr ty (label_mark l)
  | Scoping_let_module(id, ty) ->
      reset_and_mark_loops ty;
      fprintf ppf
       "Cette expression `soit module' a le type@ %a@ " type_expr ty;
      fprintf ppf
       "Dans ce type, le nom de module %s lié localement s'échappe de sa portée" id
  | Masked_instance_variable lid ->
      fprintf ppf
        "La variable d'instance %a@ \
         ne peut pas être accédée depuis la définition d'une autre variable d'instance"
        longident lid
  | Private_type ty ->
      fprintf ppf "Impossible de créer des valeurs du type privé %a" type_expr ty
  | Private_label (lid, ty) ->
      fprintf ppf "Impossible de muter le champ %a du type privé %a"
        longident lid type_expr ty
  | Not_a_variant_type lid ->
      fprintf ppf "Le type %a@ n'est pas untype somme" longident lid
  | Incoherent_label_order ->
      fprintf ppf "Cette fonction est appliquée aux arguements@ ";
      fprintf ppf "dans un ordre différent des autres appels.@ ";
      fprintf ppf "Ceci est autorisé que lorsque le type réel est connu."
  | Less_general (kind, trace) ->
      report_unification_error ppf env trace
        (fonc ppf -> fprintf ppf "Ce %s a le type" kind)
        (fonc ppf -> fprintf ppf "ce qui est moins général que")
  | Modules_not_allowed ->
      fprintf ppf "Les modules ne sont pas autorisés dans ce motif."
  | Cannot_infer_signature ->
      fprintf ppf
        "La signature pour ce module empaqueté ne peut pas être inféré."
  | Not_a_packed_module ty ->
      fprintf ppf
        "Cette expression est un module empaqueté, mais son type attendu est@ %a"
        type_expr ty
  | Recursive_local_constraint trace ->
      report_unification_error ppf env trace
        (fonction ppf ->
           fprintf ppf "Contrainte locale récursive en unifiant")
        (fonction ppf ->
           fprintf ppf "avec")
  | Unexpected_existential ->
      fprintf ppf
        "existentielle inattendue"
  | Unqualified_gadt_pattern (tpath, name) ->
      fprintf ppf "@[Le constructeur de TDAG %s de type %a@ %s.@]"
        name path tpath
        "doit être qualifié dans ce motif"
  | Invalid_interval ->
      fprintf ppf "@[Seuls des intervales de caractères sont supportés dans les motifs.@]"
  | Invalid_for_loop_index ->
      fprintf ppf
        "@[Indice de boucle for invalide : seuls des variables et _ sont autorisés.@]"
  | Extension s ->
      fprintf ppf "Extension non interprétée '%s'." s

soit report_error env ppf err =
  wrap_printing_env env (fonc () -> report_error env ppf err)

soit () =
  Location.register_error_of_exn
    (fonction
      | Error (loc, env, err) ->
        Some (Location.error_of_printer loc (report_error env) err)
      | _ ->
        None
    )

soit () =
  Env.add_delayed_check_forward := add_delayed_check
