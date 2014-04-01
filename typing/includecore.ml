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

(* Inclusion checks for the core language *)

ouvre Asttypes
ouvre Path
ouvre Types
ouvre Typedtree

(* Inclusion between value descriptions *)

exception Dont_match

soit value_descriptions env vd1 vd2 =
  si Ctype.moregeneral env vrai vd1.val_type vd2.val_type alors début
    filtre (vd1.val_kind, vd2.val_kind) avec
        (Val_prim p1, Val_prim p2) ->
          si p1 = p2 alors Tcoerce_none sinon raise Dont_match
      | (Val_prim p, _) -> Tcoerce_primitive p
      | (_, Val_prim p) -> raise Dont_match
      | (_, _) -> Tcoerce_none
  fin sinon
    raise Dont_match

(* Inclusion between "private" annotations *)

soit private_flags decl1 decl2 =
  filtre decl1.type_private, decl2.type_private avec
  | Private, Public ->
      decl2.type_kind = Type_abstract &&
      (decl2.type_manifest = None || decl1.type_kind <> Type_abstract)
  | _, _ -> vrai

(* Inclusion between manifest types (particularly for private row types) *)

soit is_absrow env ty =
  filtre ty.desc avec
    Tconstr(Pident id, _, _) ->
      début filtre Ctype.expand_head env ty avec
        {desc=Tobject _|Tvariant _} -> vrai
      | _ -> faux
      fin
  | _ -> faux

soit type_manifest env ty1 params1 ty2 params2 priv2 =
  soit ty1' = Ctype.expand_head env ty1 et ty2' = Ctype.expand_head env ty2 dans
  filtre ty1'.desc, ty2'.desc avec
    Tvariant row1, Tvariant row2 quand is_absrow env (Btype.row_more row2) ->
      soit row1 = Btype.row_repr row1 et row2 = Btype.row_repr row2 dans
      Ctype.equal env vrai (ty1::params1) (row2.row_more::params2) &&
      début filtre row1.row_more avec
        {desc=Tvar _|Tconstr _|Tnil} -> vrai
      | _ -> faux
      fin &&
      soit r1, r2, pairs =
        Ctype.merge_row_fields row1.row_fields row2.row_fields dans
      (not row2.row_closed ||
       row1.row_closed && Ctype.filter_row_fields faux r1 = []) &&
      List.for_all
        (fonc (_,f) -> filtre Btype.row_field_repr f avec
          Rabsent | Reither _ -> vrai | Rpresent _ -> faux)
        r2 &&
      soit to_equal = ref (List.combine params1 params2) dans
      List.for_all
        (fonc (_, f1, f2) ->
          filtre Btype.row_field_repr f1, Btype.row_field_repr f2 avec
            Rpresent(Some t1),
            (Rpresent(Some t2) | Reither(faux, [t2], _, _)) ->
              to_equal := (t1,t2) :: !to_equal; vrai
          | Rpresent None, (Rpresent None | Reither(vrai, [], _, _)) -> vrai
          | Reither(c1,tl1,_,_), Reither(c2,tl2,_,_)
            quand List.length tl1 = List.length tl2 && c1 = c2 ->
              to_equal := List.combine tl1 tl2 @ !to_equal; vrai
          | Rabsent, (Reither _ | Rabsent) -> vrai
          | _ -> faux)
        pairs &&
      soit tl1, tl2 = List.split !to_equal dans
      Ctype.equal env vrai tl1 tl2
  | Tobject (fi1, _), Tobject (fi2, _)
    quand is_absrow env (snd(Ctype.flatten_fields fi2)) ->
      soit (fields2,rest2) = Ctype.flatten_fields fi2 dans
      Ctype.equal env vrai (ty1::params1) (rest2::params2) &&
      soit (fields1,rest1) = Ctype.flatten_fields fi1 dans
      (filtre rest1 avec {desc=Tnil|Tvar _|Tconstr _} -> vrai | _ -> faux) &&
      soit pairs, miss1, miss2 = Ctype.associate_fields fields1 fields2 dans
      miss2 = [] &&
      soit tl1, tl2 =
        List.split (List.map (fonc (_,_,t1,_,t2) -> t1, t2) pairs) dans
      Ctype.equal env vrai (params1 @ tl1) (params2 @ tl2)
  | _ ->
      soit rec check_super ty1 =
        Ctype.equal env vrai (ty1 :: params1) (ty2 :: params2) ||
        priv2 = Private &&
        essaie check_super
              (Ctype.try_expand_once_opt env (Ctype.expand_head env ty1))
        avec Ctype.Cannot_expand -> faux
      dans check_super ty1

(* Inclusion between type declarations *)

type type_mismatch =
    Arity
  | Privacy
  | Kind
  | Constraint
  | Manifest
  | Variance
  | Field_type de Ident.t
  | Field_mutable de Ident.t
  | Field_arity de Ident.t
  | Field_names de int * Ident.t * Ident.t
  | Field_missing de bool * Ident.t
  | Record_representation de bool

soit report_type_mismatch0 first second ppf err =
  soit pr fmt = Format.fprintf ppf fmt dans
  filtre err avec
    Arity -> pr "Ils ont des arités différentes"
  | Privacy -> pr "Un type privé devrait être révélé"
  | Kind -> pr "Leurs sortes diffèrent"
  | Constraint -> pr "Leurs contraintes diffèrent"
  | Manifest -> ()
  | Variance -> pr "Leur variances ne correspondent pas"
  | Field_type s ->
      pr "Les types pour le champ %s ne sont pas égaux" (Ident.name s)
  | Field_mutable s ->
      pr "La mutabilité du champ %s est différente" (Ident.name s)
  | Field_arity s ->
      pr "Les arités pour le champ %s diffèrent" (Ident.name s)
  | Field_names (n, name1, name2) ->
      pr "Les champs numéro %i ont des noms différents, %s and %s"
        n (Ident.name name1) (Ident.name name2)
  | Field_missing (b, s) ->
      pr "Le champ %s est seulement présent dans %s"
        (Ident.name s) (si b alors second sinon first)
  | Record_representation b ->
      pr "Leurs représentations internes diffèrent :@ %s %s"
        (si b alors second sinon first)
        "utilise une représentation déballée des nombres flottants"

soit report_type_mismatch first second ppf =
  List.iter
    (fonc err ->
      si err = Manifest alors () sinon
      Format.fprintf ppf "@ %a." (report_type_mismatch0 first second) err)

soit rec compare_variants env decl1 decl2 n cstrs1 cstrs2 =
  filtre cstrs1, cstrs2 avec
    [], []           -> []
  | [], c::_ -> [Field_missing (vrai, c.Types.cd_id)]
  | c::_, [] -> [Field_missing (faux, c.Types.cd_id)]
  | {Types.cd_id=cstr1; cd_args=arg1; cd_res=ret1}::rem1,
    {Types.cd_id=cstr2; cd_args=arg2; cd_res=ret2}::rem2 ->
      si Ident.name cstr1 <> Ident.name cstr2 alors
        [Field_names (n, cstr1, cstr2)]
      sinon si List.length arg1 <> List.length arg2 alors
        [Field_arity cstr1]
      sinon filtre ret1, ret2 avec
      | Some r1, Some r2 quand not (Ctype.equal env vrai [r1] [r2]) ->
          [Field_type cstr1]
      | Some _, None | None, Some _ ->
          [Field_type cstr1]
      | _ ->
          si Misc.for_all2
              (fonc ty1 ty2 ->
                Ctype.equal env vrai (ty1::decl1.type_params)
                  (ty2::decl2.type_params))
              (arg1) (arg2)
          alors
            compare_variants env decl1 decl2 (n+1) rem1 rem2
          sinon [Field_type cstr1]


soit rec compare_records env decl1 decl2 n labels1 labels2 =
  filtre labels1, labels2 avec
    [], []           -> []
  | [], l::_ -> [Field_missing (vrai, l.ld_id)]
  | l::_, [] -> [Field_missing (faux, l.ld_id)]
  | {Types.ld_id=lab1; ld_mutable=mut1; ld_type=arg1}::rem1,
    {Types.ld_id=lab2; ld_mutable=mut2; ld_type=arg2}::rem2 ->
      si Ident.name lab1 <> Ident.name lab2
      alors [Field_names (n, lab1, lab2)]
      sinon si mut1 <> mut2 alors [Field_mutable lab1] sinon
      si Ctype.equal env vrai (arg1::decl1.type_params)
                              (arg2::decl2.type_params)
      alors compare_records env decl1 decl2 (n+1) rem1 rem2
      sinon [Field_type lab1]

soit type_declarations ?(equality = faux) env name decl1 id decl2 =
  si decl1.type_arity <> decl2.type_arity alors [Arity] sinon
  si not (private_flags decl1 decl2) alors [Privacy] sinon
  soit err = filtre (decl1.type_kind, decl2.type_kind) avec
      (_, Type_abstract) -> []
    | (Type_variant cstrs1, Type_variant cstrs2) ->
        soit mark cstrs usage name decl =
          List.iter
            (fonc c ->
              Env.mark_constructor_used usage name decl (Ident.name c.Types.cd_id))
            cstrs
        dans
        soit usage =
          si decl1.type_private = Private || decl2.type_private = Public
          alors Env.Positive sinon Env.Privatize
        dans
        mark cstrs1 usage name decl1;
        si equality alors mark cstrs2 Env.Positive (Ident.name id) decl2;
        compare_variants env decl1 decl2 1 cstrs1 cstrs2
    | (Type_record(labels1,rep1), Type_record(labels2,rep2)) ->
        soit err = compare_records env decl1 decl2 1 labels1 labels2 dans
        si err <> [] || rep1 = rep2 alors err sinon
        [Record_representation (rep2 = Record_float)]
    | (_, _) -> [Kind]
  dans
  si err <> [] alors err sinon
  soit err = filtre (decl1.type_manifest, decl2.type_manifest) avec
      (_, None) ->
        si Ctype.equal env vrai decl1.type_params decl2.type_params
        alors [] sinon [Constraint]
    | (Some ty1, Some ty2) ->
        si type_manifest env ty1 decl1.type_params ty2 decl2.type_params
            decl2.type_private
        alors [] sinon [Manifest]
    | (None, Some ty2) ->
        soit ty1 =
          Btype.newgenty (Tconstr(Pident id, decl2.type_params, ref Mnil))
        dans
        si Ctype.equal env vrai decl1.type_params decl2.type_params alors
          si Ctype.equal env faux [ty1] [ty2] alors []
          sinon [Manifest]
        sinon [Constraint]
  dans
  si err <> [] alors err sinon
  soit abstr =
    decl2.type_private = Private ||
    decl2.type_kind = Type_abstract && decl2.type_manifest = None dans
  si List.for_all2
      (fonc ty (v1,v2) ->
        soit ouvre Variance dans
        soit imp a b = not a || b dans
        soit (co1,cn1) = get_upper v1 et (co2,cn2) = get_upper v2 dans
        imp abstr (imp co1 co2 && imp cn1 cn2) &&
        (abstr || Btype.(is_Tvar (repr ty)) || co1 = co2 && cn1 = cn2) &&
        soit (p1,n1,i1,j1) = get_lower v1 et (p2,n2,i2,j2) = get_lower v2 dans
        imp abstr (imp p2 p1 && imp n2 n1 && imp i2 i1 && imp j2 j1))
      decl2.type_params (List.combine decl1.type_variance decl2.type_variance)
  alors [] sinon [Variance]

(* Inclusion between exception declarations *)

soit exception_declarations env ed1 ed2 =
  Misc.for_all2 (fonc ty1 ty2 -> Ctype.equal env faux [ty1] [ty2])
    ed1.exn_args ed2.exn_args

(* Inclusion between class types *)
soit encode_val (mut, ty) rem =
  début filtre mut avec
    Asttypes.Mutable   -> Predef.type_unit
  | Asttypes.Immutable -> Btype.newgenvar ()
  fin
  ::ty::rem

soit meths meths1 meths2 =
  Meths.fold
    (fonc nam t2 (ml1, ml2) ->
       (début essaie
          Meths.find nam meths1 :: ml1
        avec Not_found ->
          ml1
        fin,
        t2 :: ml2))
    meths2 ([], [])

soit vars vars1 vars2 =
  Vars.fold
    (fonc lab v2 (vl1, vl2) ->
       (début essaie
          encode_val (Vars.find lab vars1) vl1
        avec Not_found ->
          vl1
        fin,
        encode_val v2 vl2))
    vars2 ([], [])
