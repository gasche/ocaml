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

ouvre Typedtree

module type MapArgument = sig
  val enter_structure : structure -> structure
  val enter_value_description : value_description -> value_description
  val enter_type_declaration : type_declaration -> type_declaration
  val enter_pattern : pattern -> pattern
  val enter_expression : expression -> expression
  val enter_package_type : package_type -> package_type
  val enter_signature : signature -> signature
  val enter_signature_item : signature_item -> signature_item
  val enter_module_type_declaration : module_type_declaration -> module_type_declaration
  val enter_module_type : module_type -> module_type
  val enter_module_expr : module_expr -> module_expr
  val enter_with_constraint : with_constraint -> with_constraint
  val enter_class_expr : class_expr -> class_expr
  val enter_class_signature : class_signature -> class_signature
  val enter_class_description : class_description -> class_description
  val enter_class_type_declaration :
    class_type_declaration -> class_type_declaration
  val enter_class_infos : 'a class_infos -> 'a class_infos
  val enter_class_type : class_type -> class_type
  val enter_class_type_field : class_type_field -> class_type_field
  val enter_core_type : core_type -> core_type
  val enter_class_structure : class_structure -> class_structure
  val enter_class_field : class_field -> class_field
  val enter_structure_item : structure_item -> structure_item

  val leave_structure : structure -> structure
  val leave_value_description : value_description -> value_description
  val leave_type_declaration : type_declaration -> type_declaration
  val leave_pattern : pattern -> pattern
  val leave_expression : expression -> expression
  val leave_package_type : package_type -> package_type
  val leave_signature : signature -> signature
  val leave_signature_item : signature_item -> signature_item
  val leave_module_type_declaration : module_type_declaration -> module_type_declaration
  val leave_module_type : module_type -> module_type
  val leave_module_expr : module_expr -> module_expr
  val leave_with_constraint : with_constraint -> with_constraint
  val leave_class_expr : class_expr -> class_expr
  val leave_class_signature : class_signature -> class_signature
  val leave_class_description : class_description -> class_description
  val leave_class_type_declaration :
    class_type_declaration -> class_type_declaration
  val leave_class_infos : 'a class_infos -> 'a class_infos
  val leave_class_type : class_type -> class_type
  val leave_class_type_field : class_type_field -> class_type_field
  val leave_core_type : core_type -> core_type
  val leave_class_structure : class_structure -> class_structure
  val leave_class_field : class_field -> class_field
  val leave_structure_item : structure_item -> structure_item

fin


module MakeMap(Map : MapArgument) = struct

  soit may_map f v =
    filtre v avec
        None -> v
      | Some x -> Some (f x)


  ouvre Misc

  soit rec map_structure str =
    soit str = Map.enter_structure str dans
    soit str_items = List.map map_structure_item str.str_items dans
    Map.leave_structure { str avec str_items = str_items }

  et map_binding vb =
    {
      vb_pat = map_pattern vb.vb_pat;
      vb_expr = map_expression vb.vb_expr;
      vb_attributes = vb.vb_attributes;
    }

  et map_bindings rec_flag list =
    List.map map_binding list

  et map_case {c_lhs; c_guard; c_rhs} =
    {
     c_lhs = map_pattern c_lhs;
     c_guard = may_map map_expression c_guard;
     c_rhs = map_expression c_rhs;
    }

  et map_cases list =
    List.map map_case list

  et map_structure_item item =
    soit item = Map.enter_structure_item item dans
    soit str_desc =
      filtre item.str_desc avec
          Tstr_eval (exp, attrs) -> Tstr_eval (map_expression exp, attrs)
        | Tstr_value (rec_flag, list) ->
          Tstr_value (rec_flag, map_bindings rec_flag list)
        | Tstr_primitive vd ->
          Tstr_primitive (map_value_description vd)
        | Tstr_type list ->
          Tstr_type (List.map map_type_declaration list)
        | Tstr_exception cd ->
          Tstr_exception (map_constructor_declaration cd)
        | Tstr_exn_rebind (id, name, path, lid, attrs) ->
          Tstr_exn_rebind (id, name, path, lid, attrs)
        | Tstr_module x ->
          Tstr_module (map_module_binding x)
        | Tstr_recmodule list ->
          soit list = List.map map_module_binding list dans
          Tstr_recmodule list
        | Tstr_modtype mtd ->
          Tstr_modtype (map_module_type_declaration mtd)
        | Tstr_open (ovf, path, lid, attrs) -> Tstr_open (ovf, path, lid, attrs)
        | Tstr_class list ->
          soit list =
            List.map (fonc (ci, string_list, virtual_flag) ->
              soit ci = Map.enter_class_infos ci dans
              soit ci_expr = map_class_expr ci.ci_expr dans
              (Map.leave_class_infos { ci avec ci_expr = ci_expr},
               string_list, virtual_flag)
            ) list
          dans
          Tstr_class list
        | Tstr_class_type list ->
          soit list = List.map (fonc (id, name, ct) ->
            soit ct = Map.enter_class_infos ct dans
            soit ci_expr = map_class_type ct.ci_expr dans
            (id, name, Map.leave_class_infos { ct avec ci_expr = ci_expr})
          ) list dans
          Tstr_class_type list
        | Tstr_include (mexpr, sg, attrs) ->
          Tstr_include (map_module_expr mexpr, sg, attrs)
        | Tstr_attribute x -> Tstr_attribute x
    dans
    Map.leave_structure_item { item avec str_desc = str_desc}

  et map_module_binding x =
    {x avec mb_expr = map_module_expr x.mb_expr}

  et map_value_description v =
    soit v = Map.enter_value_description v dans
    soit val_desc = map_core_type v.val_desc dans
    Map.leave_value_description { v avec val_desc = val_desc }

  et map_type_declaration decl =
    soit decl = Map.enter_type_declaration decl dans
    soit typ_cstrs = List.map (fonc (ct1, ct2, loc) ->
      (map_core_type ct1,
       map_core_type ct2,
       loc)
    ) decl.typ_cstrs dans
    soit typ_kind = filtre decl.typ_kind avec
        Ttype_abstract -> Ttype_abstract
      | Ttype_variant list ->
          soit list = List.map map_constructor_declaration list dans
          Ttype_variant list
      | Ttype_record list ->
        soit list =
          List.map
            (fonc ld ->
              {ld avec ld_type = map_core_type ld.ld_type}
            ) list
        dans
        Ttype_record list
    dans
    soit typ_manifest =
      filtre decl.typ_manifest avec
          None -> None
        | Some ct -> Some (map_core_type ct)
    dans
    Map.leave_type_declaration { decl avec typ_cstrs = typ_cstrs;
      typ_kind = typ_kind; typ_manifest = typ_manifest }

  et map_constructor_declaration cd =
    {cd avec cd_args = List.map map_core_type cd.cd_args;
     cd_res = may_map map_core_type cd.cd_res
    }

  et map_pattern pat =
    soit pat = Map.enter_pattern pat dans
    soit pat_desc =
      filtre pat.pat_desc avec
        | Tpat_alias (pat1, p, text) ->
          soit pat1 = map_pattern pat1 dans
          Tpat_alias (pat1, p, text)
        | Tpat_tuple list -> Tpat_tuple (List.map map_pattern list)
        | Tpat_construct (lid, cstr_decl, args) ->
          Tpat_construct (lid, cstr_decl,
                          List.map map_pattern args)
        | Tpat_variant (label, pato, rowo) ->
          soit pato = filtre pato avec
              None -> pato
            | Some pat -> Some (map_pattern pat)
          dans
          Tpat_variant (label, pato, rowo)
        | Tpat_record (list, closed) ->
          Tpat_record (List.map (fonc (lid, lab_desc, pat) ->
            (lid, lab_desc, map_pattern pat) ) list, closed)
        | Tpat_array list -> Tpat_array (List.map map_pattern list)
        | Tpat_or (p1, p2, rowo) ->
          Tpat_or (map_pattern p1, map_pattern p2, rowo)
        | Tpat_lazy p -> Tpat_lazy (map_pattern p)
        | Tpat_constant _
        | Tpat_any
        | Tpat_var _ -> pat.pat_desc

    dans
    soit pat_extra = List.map map_pat_extra pat.pat_extra dans
    Map.leave_pattern { pat avec pat_desc = pat_desc; pat_extra = pat_extra }

  et map_pat_extra pat_extra =
    filtre pat_extra avec
      | Tpat_constraint ct, loc, attrs -> (Tpat_constraint (map_core_type  ct), loc, attrs)
      | (Tpat_type _ | Tpat_unpack), _, _ -> pat_extra

  et map_expression exp =
    soit exp = Map.enter_expression exp dans
    soit exp_desc =
      filtre exp.exp_desc avec
          Texp_ident (_, _, _)
        | Texp_constant _ -> exp.exp_desc
        | Texp_let (rec_flag, list, exp) ->
          Texp_let (rec_flag,
                    map_bindings rec_flag list,
                    map_expression exp)
        | Texp_function (label, cases, partial) ->
          Texp_function (label, map_cases cases, partial)
        | Texp_apply (exp, list) ->
          Texp_apply (map_expression exp,
                      List.map (fonc (label, expo, optional) ->
                        soit expo =
                          filtre expo avec
                              None -> expo
                            | Some exp -> Some (map_expression exp)
                        dans
                        (label, expo, optional)
                      ) list )
        | Texp_match (exp, list, partial) ->
          Texp_match (
            map_expression exp,
            map_cases list,
            partial
          )
        | Texp_try (exp, list) ->
          Texp_try (
            map_expression exp,
            map_cases list
          )
        | Texp_tuple list ->
          Texp_tuple (List.map map_expression list)
        | Texp_construct (lid, cstr_desc, args) ->
          Texp_construct (lid, cstr_desc,
                          List.map map_expression args )
        | Texp_variant (label, expo) ->
          soit expo =filtre expo avec
              None -> expo
            | Some exp -> Some (map_expression exp)
          dans
          Texp_variant (label, expo)
        | Texp_record (list, expo) ->
          soit list =
            List.map (fonc (lid, lab_desc, exp) ->
              (lid, lab_desc, map_expression exp)
            ) list dans
          soit expo = filtre expo avec
              None -> expo
            | Some exp -> Some (map_expression exp)
          dans
          Texp_record (list, expo)
        | Texp_field (exp, lid, label) ->
          Texp_field (map_expression exp, lid, label)
        | Texp_setfield (exp1, lid, label, exp2) ->
          Texp_setfield (
            map_expression exp1,
            lid,
            label,
            map_expression exp2)
        | Texp_array list ->
          Texp_array (List.map map_expression list)
        | Texp_ifthenelse (exp1, exp2, expo) ->
          Texp_ifthenelse (
            map_expression exp1,
            map_expression exp2,
            filtre expo avec
                None -> expo
              | Some exp -> Some (map_expression exp)
          )
        | Texp_sequence (exp1, exp2) ->
          Texp_sequence (
            map_expression exp1,
            map_expression exp2
          )
        | Texp_while (exp1, exp2) ->
          Texp_while (
            map_expression exp1,
            map_expression exp2
          )
        | Texp_for (id, name, exp1, exp2, dir, exp3) ->
          Texp_for (
            id, name,
            map_expression exp1,
            map_expression exp2,
            dir,
            map_expression exp3
          )
        | Texp_send (exp, meth, expo) ->
          Texp_send (map_expression exp, meth, may_map map_expression expo)
        | Texp_new (path, lid, cl_decl) -> exp.exp_desc
        | Texp_instvar (_, path, _) -> exp.exp_desc
        | Texp_setinstvar (path, lid, path2, exp) ->
          Texp_setinstvar (path, lid, path2, map_expression exp)
        | Texp_override (path, list) ->
          Texp_override (
            path,
            List.map (fonc (path, lid, exp) ->
              (path, lid, map_expression exp)
            ) list
          )
        | Texp_letmodule (id, name, mexpr, exp) ->
          Texp_letmodule (
            id, name,
            map_module_expr mexpr,
            map_expression exp
          )
        | Texp_assert exp -> Texp_assert (map_expression exp)
        | Texp_lazy exp -> Texp_lazy (map_expression exp)
        | Texp_object (cl, string_list) ->
          Texp_object (map_class_structure cl, string_list)
        | Texp_pack (mexpr) ->
          Texp_pack (map_module_expr mexpr)
    dans
    soit exp_extra = List.map map_exp_extra exp.exp_extra dans
    Map.leave_expression {
      exp avec
        exp_desc = exp_desc;
        exp_extra = exp_extra; }

  et map_exp_extra ((desc, loc, attrs) tel exp_extra) =
    filtre desc avec
      | Texp_constraint ct ->
        Texp_constraint (map_core_type ct), loc, attrs
      | Texp_coerce (None, ct) ->
        Texp_coerce (None, map_core_type ct), loc, attrs
      | Texp_coerce (Some ct1, ct2) ->
        Texp_coerce (Some (map_core_type ct1),
                         map_core_type ct2), loc, attrs
      | Texp_poly (Some ct) ->
        Texp_poly (Some ( map_core_type ct )), loc, attrs
      | Texp_newtype _
      | Texp_open _
      | Texp_poly None -> exp_extra


  et map_package_type pack =
    soit pack = Map.enter_package_type pack dans
    soit pack_fields = List.map (
      fonc (s, ct) -> (s, map_core_type ct) ) pack.pack_fields dans
    Map.leave_package_type { pack avec pack_fields = pack_fields }

  et map_signature sg =
    soit sg = Map.enter_signature sg dans
    soit sig_items = List.map map_signature_item sg.sig_items dans
    Map.leave_signature { sg avec sig_items = sig_items }

  et map_signature_item item =
    soit item = Map.enter_signature_item item dans
    soit sig_desc =
      filtre item.sig_desc avec
          Tsig_value vd ->
            Tsig_value (map_value_description vd)
        | Tsig_type list -> Tsig_type (List.map map_type_declaration list)
        | Tsig_exception cd ->
          Tsig_exception (map_constructor_declaration cd)
        | Tsig_module md ->
          Tsig_module {md avec md_type = map_module_type md.md_type}
        | Tsig_recmodule list ->
          Tsig_recmodule
              (List.map
                 (fonc md -> {md avec md_type = map_module_type md.md_type})
                 list
              )
        | Tsig_modtype mtd ->
          Tsig_modtype (map_module_type_declaration mtd)
        | Tsig_open _ -> item.sig_desc
        | Tsig_include (mty, sg, attrs) -> Tsig_include (map_module_type mty, sg, attrs)
        | Tsig_class list -> Tsig_class (List.map map_class_description list)
        | Tsig_class_type list ->
          Tsig_class_type (List.map map_class_type_declaration list)
        | Tsig_attribute _ tel x -> x
    dans
    Map.leave_signature_item { item avec sig_desc = sig_desc }

  et map_module_type_declaration mtd =
    soit mtd = Map.enter_module_type_declaration mtd dans
    soit mtd = {mtd avec mtd_type = may_map map_module_type mtd.mtd_type} dans
    Map.leave_module_type_declaration mtd


  et map_class_description cd =
    soit cd = Map.enter_class_description cd dans
    soit ci_expr = map_class_type cd.ci_expr dans
    Map.leave_class_description { cd avec ci_expr = ci_expr}

  et map_class_type_declaration cd =
    soit cd = Map.enter_class_type_declaration cd dans
    soit ci_expr = map_class_type cd.ci_expr dans
    Map.leave_class_type_declaration { cd avec ci_expr = ci_expr }

  et map_module_type mty =
    soit mty = Map.enter_module_type mty dans
    soit mty_desc =
      filtre mty.mty_desc avec
          Tmty_ident _ -> mty.mty_desc
        | Tmty_alias _ -> mty.mty_desc
        | Tmty_signature sg -> Tmty_signature (map_signature sg)
        | Tmty_functor (id, name, mtype1, mtype2) ->
          Tmty_functor (id, name, Misc.may_map map_module_type mtype1,
                        map_module_type mtype2)
        | Tmty_with (mtype, list) ->
          Tmty_with (map_module_type mtype,
                     List.map (fonc (path, lid, withc) ->
                       (path, lid, map_with_constraint withc)
                     ) list)
        | Tmty_typeof mexpr ->
          Tmty_typeof (map_module_expr mexpr)
    dans
    Map.leave_module_type { mty avec mty_desc = mty_desc}

  et map_with_constraint cstr =
    soit cstr = Map.enter_with_constraint cstr dans
    soit cstr =
      filtre cstr avec
          Twith_type decl -> Twith_type (map_type_declaration decl)
        | Twith_typesubst decl -> Twith_typesubst (map_type_declaration decl)
        | Twith_module (path, lid) -> cstr
        | Twith_modsubst (path, lid) -> cstr
    dans
    Map.leave_with_constraint cstr

  et map_module_expr mexpr =
    soit mexpr = Map.enter_module_expr mexpr dans
    soit mod_desc =
      filtre mexpr.mod_desc avec
          Tmod_ident (p, lid) -> mexpr.mod_desc
        | Tmod_structure st -> Tmod_structure (map_structure st)
        | Tmod_functor (id, name, mtype, mexpr) ->
          Tmod_functor (id, name, Misc.may_map map_module_type mtype,
                        map_module_expr mexpr)
        | Tmod_apply (mexp1, mexp2, coercion) ->
          Tmod_apply (map_module_expr mexp1, map_module_expr mexp2, coercion)
        | Tmod_constraint (mexpr, mod_type, Tmodtype_implicit, coercion ) ->
          Tmod_constraint (map_module_expr mexpr, mod_type,
                           Tmodtype_implicit, coercion)
        | Tmod_constraint (mexpr, mod_type,
                           Tmodtype_explicit mtype, coercion) ->
          Tmod_constraint (map_module_expr mexpr, mod_type,
                           Tmodtype_explicit (map_module_type mtype),
                           coercion)
        | Tmod_unpack (exp, mod_type) ->
          Tmod_unpack (map_expression exp, mod_type)
    dans
    Map.leave_module_expr { mexpr avec mod_desc = mod_desc }

  et map_class_expr cexpr =
    soit cexpr = Map.enter_class_expr cexpr dans
    soit cl_desc =
      filtre cexpr.cl_desc avec
        | Tcl_constraint (cl, None, string_list1, string_list2, concr ) ->
          Tcl_constraint (map_class_expr cl, None, string_list1,
                          string_list2, concr)
        | Tcl_structure clstr -> Tcl_structure (map_class_structure clstr)
        | Tcl_fun (label, pat, priv, cl, partial) ->
          Tcl_fun (label, map_pattern pat,
                   List.map (fonc (id, name, exp) ->
                     (id, name, map_expression exp)) priv,
                   map_class_expr cl, partial)

        | Tcl_apply (cl, args) ->
          Tcl_apply (map_class_expr cl,
                     List.map (fonc (label, expo, optional) ->
                       (label, may_map map_expression expo,
                        optional)
                     ) args)
        | Tcl_let (rec_flat, bindings, ivars, cl) ->
          Tcl_let (rec_flat, map_bindings rec_flat bindings,
                   List.map (fonc (id, name, exp) ->
                     (id, name, map_expression exp)) ivars,
                   map_class_expr cl)

        | Tcl_constraint (cl, Some clty, vals, meths, concrs) ->
          Tcl_constraint ( map_class_expr cl,
                           Some (map_class_type clty), vals, meths, concrs)

        | Tcl_ident (id, name, tyl) ->
          Tcl_ident (id, name, List.map map_core_type tyl)
    dans
    Map.leave_class_expr { cexpr avec cl_desc = cl_desc }

  et map_class_type ct =
    soit ct = Map.enter_class_type ct dans
    soit cltyp_desc =
      filtre ct.cltyp_desc avec
          Tcty_signature csg -> Tcty_signature (map_class_signature csg)
        | Tcty_constr (path, lid, list) ->
          Tcty_constr (path, lid, List.map map_core_type list)
        | Tcty_arrow (label, ct, cl) ->
          Tcty_arrow (label, map_core_type ct, map_class_type cl)
    dans
    Map.leave_class_type { ct avec cltyp_desc = cltyp_desc }

  et map_class_signature cs =
    soit cs = Map.enter_class_signature cs dans
    soit csig_self = map_core_type cs.csig_self dans
    soit csig_fields = List.map map_class_type_field cs.csig_fields dans
    Map.leave_class_signature { cs avec
      csig_self = csig_self; csig_fields = csig_fields }


  et map_class_type_field ctf =
    soit ctf = Map.enter_class_type_field ctf dans
    soit ctf_desc =
      filtre ctf.ctf_desc avec
          Tctf_inherit ct -> Tctf_inherit (map_class_type ct)
        | Tctf_val (s, mut, virt, ct) ->
          Tctf_val (s, mut, virt, map_core_type ct)
        | Tctf_method (s, priv, virt, ct) ->
          Tctf_method (s, priv, virt, map_core_type ct)
        | Tctf_constraint (ct1, ct2) ->
          Tctf_constraint (map_core_type ct1, map_core_type ct2)
    dans
    Map.leave_class_type_field { ctf avec ctf_desc = ctf_desc }

  et map_core_type ct =
    soit ct = Map.enter_core_type ct dans
    soit ctyp_desc =
      filtre ct.ctyp_desc avec
          Ttyp_any
        | Ttyp_var _ -> ct.ctyp_desc
        | Ttyp_arrow (label, ct1, ct2) ->
          Ttyp_arrow (label, map_core_type ct1, map_core_type ct2)
        | Ttyp_tuple list -> Ttyp_tuple (List.map map_core_type list)
        | Ttyp_constr (path, lid, list) ->
          Ttyp_constr (path, lid, List.map map_core_type list)
        | Ttyp_object (list, o) ->
          Ttyp_object (List.map (fonc (s, t) -> (s, map_core_type t)) list, o)
        | Ttyp_class (path, lid, list) ->
          Ttyp_class (path, lid, List.map map_core_type list)
        | Ttyp_alias (ct, s) -> Ttyp_alias (map_core_type ct, s)
        | Ttyp_variant (list, bool, labels) ->
          Ttyp_variant (List.map map_row_field list, bool, labels)
        | Ttyp_poly (list, ct) -> Ttyp_poly (list, map_core_type ct)
        | Ttyp_package pack -> Ttyp_package (map_package_type pack)
    dans
    Map.leave_core_type { ct avec ctyp_desc = ctyp_desc }

  et map_class_structure cs =
    soit cs = Map.enter_class_structure cs dans
    soit cstr_self = map_pattern cs.cstr_self dans
    soit cstr_fields = List.map map_class_field cs.cstr_fields dans
    Map.leave_class_structure { cs avec cstr_self; cstr_fields }

  et map_row_field rf =
    filtre rf avec
        Ttag (label, bool, list) ->
          Ttag (label, bool, List.map map_core_type list)
      | Tinherit ct -> Tinherit (map_core_type ct)

  et map_class_field cf =
    soit cf = Map.enter_class_field cf dans
    soit cf_desc =
      filtre cf.cf_desc avec
          Tcf_inherit (ovf, cl, super, vals, meths) ->
            Tcf_inherit (ovf, map_class_expr cl, super, vals, meths)
        | Tcf_constraint (cty, cty') ->
          Tcf_constraint (map_core_type cty, map_core_type cty')
        | Tcf_val (lab, mut, ident, Tcfk_virtual cty, b) ->
          Tcf_val (lab, mut, ident, Tcfk_virtual (map_core_type cty), b)
        | Tcf_val (lab, mut, ident, Tcfk_concrete (o, exp), b) ->
          Tcf_val (lab, mut, ident, Tcfk_concrete (o, map_expression exp), b)
        | Tcf_method (lab, priv, Tcfk_virtual cty) ->
          Tcf_method (lab, priv, Tcfk_virtual (map_core_type cty))
        | Tcf_method (lab, priv, Tcfk_concrete (o, exp)) ->
          Tcf_method (lab, priv, Tcfk_concrete (o, map_expression exp))
        | Tcf_initializer exp -> Tcf_initializer (map_expression exp)
    dans
    Map.leave_class_field { cf avec cf_desc = cf_desc }
fin


module DefaultMapArgument = struct

  soit enter_structure t = t
  soit enter_value_description t = t
  soit enter_type_declaration t = t
  soit enter_exception_declaration t = t
  soit enter_pattern t = t
  soit enter_expression t = t
  soit enter_package_type t = t
  soit enter_signature t = t
  soit enter_signature_item t = t
  soit enter_module_type_declaration t = t
  soit enter_module_type t = t
  soit enter_module_expr t = t
  soit enter_with_constraint t = t
  soit enter_class_expr t = t
  soit enter_class_signature t = t
  soit enter_class_description t = t
  soit enter_class_type_declaration t = t
  soit enter_class_infos t = t
  soit enter_class_type t = t
  soit enter_class_type_field t = t
  soit enter_core_type t = t
  soit enter_class_structure t = t
  soit enter_class_field t = t
  soit enter_structure_item t = t


  soit leave_structure t = t
  soit leave_value_description t = t
  soit leave_type_declaration t = t
  soit leave_exception_declaration t = t
  soit leave_pattern t = t
  soit leave_expression t = t
  soit leave_package_type t = t
  soit leave_signature t = t
  soit leave_signature_item t = t
  soit leave_module_type_declaration t = t
  soit leave_module_type t = t
  soit leave_module_expr t = t
  soit leave_with_constraint t = t
  soit leave_class_expr t = t
  soit leave_class_signature t = t
  soit leave_class_description t = t
  soit leave_class_type_declaration t = t
  soit leave_class_infos t = t
  soit leave_class_type t = t
  soit leave_class_type_field t = t
  soit leave_core_type t = t
  soit leave_class_structure t = t
  soit leave_class_field t = t
  soit leave_structure_item t = t

fin
