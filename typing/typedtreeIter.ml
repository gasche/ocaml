(**************************************************************************)
(*                                                                        *)
(*                                OCaml                                   *)
(*                                                                        *)
(*    Thomas Gazagnaire (OCamlPro), Fabrice Le Fessant (INRIA Saclay)     *)
(*                                                                        *)
(*   Copyright 2007 Institut National de Recherche en Informatique et     *)
(*   en Automatique.  All rights reserved.  This file is distributed      *)
(*   under the terms of the Q Public License version 1.0.                 *)
(*                                                                        *)
(**************************************************************************)

(*
TODO:
 - 2012/05/10: Follow camlp4 way of building map and iter using classes
     and inheritance ?
*)

ouvre Asttypes
ouvre Typedtree

module type IteratorArgument = sig

    val enter_structure : structure -> unit
    val enter_value_description : value_description -> unit
    val enter_type_declaration : type_declaration -> unit
    val enter_pattern : pattern -> unit
    val enter_expression : expression -> unit
    val enter_package_type : package_type -> unit
    val enter_signature : signature -> unit
    val enter_signature_item : signature_item -> unit
    val enter_module_type_declaration : module_type_declaration -> unit
    val enter_module_type : module_type -> unit
    val enter_module_expr : module_expr -> unit
    val enter_with_constraint : with_constraint -> unit
    val enter_class_expr : class_expr -> unit
    val enter_class_signature : class_signature -> unit
    val enter_class_declaration : class_declaration -> unit
    val enter_class_description : class_description -> unit
    val enter_class_type_declaration : class_type_declaration -> unit
    val enter_class_type : class_type -> unit
    val enter_class_type_field : class_type_field -> unit
    val enter_core_type : core_type -> unit
    val enter_class_structure : class_structure -> unit
    val enter_class_field : class_field -> unit
    val enter_structure_item : structure_item -> unit


    val leave_structure : structure -> unit
    val leave_value_description : value_description -> unit
    val leave_type_declaration : type_declaration -> unit
    val leave_pattern : pattern -> unit
    val leave_expression : expression -> unit
    val leave_package_type : package_type -> unit
    val leave_signature : signature -> unit
    val leave_signature_item : signature_item -> unit
    val leave_module_type_declaration : module_type_declaration -> unit
    val leave_module_type : module_type -> unit
    val leave_module_expr : module_expr -> unit
    val leave_with_constraint : with_constraint -> unit
    val leave_class_expr : class_expr -> unit
    val leave_class_signature : class_signature -> unit
    val leave_class_declaration : class_declaration -> unit
    val leave_class_description : class_description -> unit
    val leave_class_type_declaration : class_type_declaration -> unit
    val leave_class_type : class_type -> unit
    val leave_class_type_field : class_type_field -> unit
    val leave_core_type : core_type -> unit
    val leave_class_structure : class_structure -> unit
    val leave_class_field : class_field -> unit
    val leave_structure_item : structure_item -> unit

    val enter_bindings : rec_flag -> unit
    val enter_binding : value_binding -> unit
    val leave_binding : value_binding -> unit
    val leave_bindings : rec_flag -> unit

      fin

module MakeIterator(Iter : IteratorArgument) : sig

    val iter_structure : structure -> unit
    val iter_signature : signature -> unit
    val iter_structure_item : structure_item -> unit
    val iter_signature_item : signature_item -> unit
    val iter_expression : expression -> unit
    val iter_module_type : module_type -> unit
    val iter_pattern : pattern -> unit
    val iter_class_expr : class_expr -> unit

  fin = struct

    soit may_iter f v =
      filtre v avec
        None -> ()
      | Some x -> f x


    soit rec iter_structure str =
      Iter.enter_structure str;
      List.iter iter_structure_item str.str_items;
      Iter.leave_structure str


    et iter_binding vb =
      Iter.enter_binding vb;
      iter_pattern vb.vb_pat;
      iter_expression vb.vb_expr;
      Iter.leave_binding vb

    et iter_bindings rec_flag list =
      Iter.enter_bindings rec_flag;
      List.iter iter_binding list;
      Iter.leave_bindings rec_flag

    et iter_case {c_lhs; c_guard; c_rhs} =
      iter_pattern c_lhs;
      may_iter iter_expression c_guard;
      iter_expression c_rhs

    et iter_cases cases =
      List.iter iter_case cases

    et iter_structure_item item =
      Iter.enter_structure_item item;
      début
        filtre item.str_desc avec
          Tstr_eval (exp, _attrs) -> iter_expression exp
        | Tstr_value (rec_flag, list) ->
            iter_bindings rec_flag list
        | Tstr_primitive vd -> iter_value_description vd
        | Tstr_type list -> List.iter iter_type_declaration list
        | Tstr_exception cd -> iter_constructor_declaration cd
        | Tstr_exn_rebind _ -> ()
        | Tstr_module x -> iter_module_binding x
        | Tstr_recmodule list -> List.iter iter_module_binding list
        | Tstr_modtype mtd -> iter_module_type_declaration mtd
        | Tstr_open _ -> ()
        | Tstr_class list ->
            List.iter (fonc (ci, _, _) ->
                Iter.enter_class_declaration ci;
                iter_class_expr ci.ci_expr;
                Iter.leave_class_declaration ci;
            ) list
        | Tstr_class_type list ->
            List.iter (fonc (id, _, ct) ->
                Iter.enter_class_type_declaration ct;
                iter_class_type ct.ci_expr;
                Iter.leave_class_type_declaration ct;
            ) list
        | Tstr_include (mexpr, _, _attrs) ->
            iter_module_expr mexpr
        | Tstr_attribute _ ->
            ()
      fin;
      Iter.leave_structure_item item

    et iter_module_binding x =
      iter_module_expr x.mb_expr

    et iter_value_description v =
      Iter.enter_value_description v;
      iter_core_type v.val_desc;
      Iter.leave_value_description v

    et iter_constructor_declaration cd =
      List.iter iter_core_type cd.cd_args;
      option iter_core_type cd.cd_res;

    et iter_type_declaration decl =
      Iter.enter_type_declaration decl;
      List.iter (fonc (ct1, ct2, loc) ->
          iter_core_type ct1;
          iter_core_type ct2
      ) decl.typ_cstrs;
      début filtre decl.typ_kind avec
          Ttype_abstract -> ()
        | Ttype_variant list ->
            List.iter iter_constructor_declaration list
        | Ttype_record list ->
            List.iter
              (fonc ld ->
                iter_core_type ld.ld_type
            ) list
      fin;
      début filtre decl.typ_manifest avec
          None -> ()
        | Some ct -> iter_core_type ct
      fin;
      Iter.leave_type_declaration decl

    et iter_pattern pat =
      Iter.enter_pattern pat;
      List.iter (fonc (cstr, _, _attrs) -> filtre cstr avec
              | Tpat_type _ -> ()
              | Tpat_unpack -> ()
              | Tpat_constraint ct -> iter_core_type ct) pat.pat_extra;
      début
        filtre pat.pat_desc avec
          Tpat_any -> ()
        | Tpat_var (id, _) -> ()
        | Tpat_alias (pat1, _, _) -> iter_pattern pat1
        | Tpat_constant cst -> ()
        | Tpat_tuple list ->
            List.iter iter_pattern list
        | Tpat_construct (_, _, args) ->
            List.iter iter_pattern args
        | Tpat_variant (label, pato, _) ->
            début filtre pato avec
                None -> ()
              | Some pat -> iter_pattern pat
            fin
        | Tpat_record (list, closed) ->
            List.iter (fonc (_, _, pat) -> iter_pattern pat) list
        | Tpat_array list -> List.iter iter_pattern list
        | Tpat_or (p1, p2, _) -> iter_pattern p1; iter_pattern p2
        | Tpat_lazy p -> iter_pattern p
      fin;
      Iter.leave_pattern pat

    et option f x = filtre x avec None -> () | Some e -> f e

    et iter_expression exp =
      Iter.enter_expression exp;
      List.iter (fonction (cstr, _, _attrs) ->
        filtre cstr avec
          Texp_constraint ct ->
            iter_core_type ct
        | Texp_coerce (cty1, cty2) ->
            option iter_core_type cty1; iter_core_type cty2
        | Texp_open (_, path, _, _) -> ()
        | Texp_poly cto -> option iter_core_type cto
        | Texp_newtype s -> ())
        exp.exp_extra;
      début
        filtre exp.exp_desc avec
          Texp_ident (path, _, _) -> ()
        | Texp_constant cst -> ()
        | Texp_let (rec_flag, list, exp) ->
            iter_bindings rec_flag list;
            iter_expression exp
        | Texp_function (label, cases, _) ->
            iter_cases cases
        | Texp_apply (exp, list) ->
            iter_expression exp;
            List.iter (fonc (label, expo, _) ->
                filtre expo avec
                  None -> ()
                | Some exp -> iter_expression exp
            ) list
        | Texp_match (exp, list, _) ->
            iter_expression exp;
            iter_cases list
        | Texp_try (exp, list) ->
            iter_expression exp;
            iter_cases list
        | Texp_tuple list ->
            List.iter iter_expression list
        | Texp_construct (_, _, args) ->
            List.iter iter_expression args
        | Texp_variant (label, expo) ->
            début filtre expo avec
                None -> ()
              | Some exp -> iter_expression exp
            fin
        | Texp_record (list, expo) ->
            List.iter (fonc (_, _, exp) -> iter_expression exp) list;
            début filtre expo avec
                None -> ()
              | Some exp -> iter_expression exp
            fin
        | Texp_field (exp, _, label) ->
            iter_expression exp
        | Texp_setfield (exp1, _, label, exp2) ->
            iter_expression exp1;
            iter_expression exp2
        | Texp_array list ->
            List.iter iter_expression list
        | Texp_ifthenelse (exp1, exp2, expo) ->
            iter_expression exp1;
            iter_expression exp2;
            début filtre expo avec
                None -> ()
              | Some exp -> iter_expression exp
            fin
        | Texp_sequence (exp1, exp2) ->
            iter_expression exp1;
            iter_expression exp2
        | Texp_while (exp1, exp2) ->
            iter_expression exp1;
            iter_expression exp2
        | Texp_for (id, _, exp1, exp2, dir, exp3) ->
            iter_expression exp1;
            iter_expression exp2;
            iter_expression exp3
        | Texp_send (exp, meth, expo) ->
            iter_expression exp;
          début
            filtre expo avec
                None -> ()
              | Some exp -> iter_expression exp
          fin
        | Texp_new (path, _, _) -> ()
        | Texp_instvar (_, path, _) -> ()
        | Texp_setinstvar (_, _, _, exp) ->
            iter_expression exp
        | Texp_override (_, list) ->
            List.iter (fonc (path, _, exp) ->
                iter_expression exp
            ) list
        | Texp_letmodule (id, _, mexpr, exp) ->
            iter_module_expr mexpr;
            iter_expression exp
        | Texp_assert exp -> iter_expression exp
        | Texp_lazy exp -> iter_expression exp
        | Texp_object (cl, _) ->
            iter_class_structure cl
        | Texp_pack (mexpr) ->
            iter_module_expr mexpr
      fin;
      Iter.leave_expression exp;

    et iter_package_type pack =
      Iter.enter_package_type pack;
      List.iter (fonc (s, ct) -> iter_core_type ct) pack.pack_fields;
      Iter.leave_package_type pack;

    et iter_signature sg =
      Iter.enter_signature sg;
      List.iter iter_signature_item sg.sig_items;
      Iter.leave_signature sg;

    et iter_signature_item item =
      Iter.enter_signature_item item;
      début
        filtre item.sig_desc avec
          Tsig_value vd ->
            iter_value_description vd
        | Tsig_type list ->
            List.iter iter_type_declaration list
        | Tsig_exception cd ->
            iter_constructor_declaration cd
        | Tsig_module md ->
            iter_module_type md.md_type
        | Tsig_recmodule list ->
            List.iter (fonc md -> iter_module_type md.md_type) list
        | Tsig_modtype mtd ->
            iter_module_type_declaration mtd
        | Tsig_open _ -> ()
        | Tsig_include (mty, _, _attrs) -> iter_module_type mty
        | Tsig_class list ->
            List.iter iter_class_description list
        | Tsig_class_type list ->
            List.iter iter_class_type_declaration list
        | Tsig_attribute _ -> ()
      fin;
      Iter.leave_signature_item item;

    et iter_module_type_declaration mtd =
      Iter.enter_module_type_declaration mtd;
      début
        filtre mtd.mtd_type avec
        | None -> ()
        | Some mtype -> iter_module_type mtype
      fin;
      Iter.leave_module_type_declaration mtd


    et iter_class_description cd =
      Iter.enter_class_description cd;
      iter_class_type cd.ci_expr;
      Iter.leave_class_description cd;

    et iter_class_type_declaration cd =
      Iter.enter_class_type_declaration cd;
      iter_class_type cd.ci_expr;
        Iter.leave_class_type_declaration cd;

    et iter_module_type mty =
      Iter.enter_module_type mty;
      début
        filtre mty.mty_desc avec
          Tmty_ident (path, _) -> ()
        | Tmty_alias (path, _) -> ()
        | Tmty_signature sg -> iter_signature sg
        | Tmty_functor (id, _, mtype1, mtype2) ->
            Misc.may iter_module_type mtype1; iter_module_type mtype2
        | Tmty_with (mtype, list) ->
            iter_module_type mtype;
            List.iter (fonc (path, _, withc) ->
                iter_with_constraint withc
            ) list
        | Tmty_typeof mexpr ->
            iter_module_expr mexpr
      fin;
      Iter.leave_module_type mty;

    et iter_with_constraint cstr =
      Iter.enter_with_constraint cstr;
      début
        filtre cstr avec
          Twith_type decl -> iter_type_declaration decl
        | Twith_module _ -> ()
        | Twith_typesubst decl -> iter_type_declaration decl
        | Twith_modsubst _ -> ()
      fin;
      Iter.leave_with_constraint cstr;

    et iter_module_expr mexpr =
      Iter.enter_module_expr mexpr;
      début
        filtre mexpr.mod_desc avec
          Tmod_ident (p, _) -> ()
        | Tmod_structure st -> iter_structure st
        | Tmod_functor (id, _, mtype, mexpr) ->
            Misc.may iter_module_type mtype;
            iter_module_expr mexpr
        | Tmod_apply (mexp1, mexp2, _) ->
            iter_module_expr mexp1;
            iter_module_expr mexp2
        | Tmod_constraint (mexpr, _, Tmodtype_implicit, _ ) ->
            iter_module_expr mexpr
        | Tmod_constraint (mexpr, _, Tmodtype_explicit mtype, _) ->
            iter_module_expr mexpr;
            iter_module_type mtype
        | Tmod_unpack (exp, mty) ->
            iter_expression exp
(*          iter_module_type mty *)
      fin;
      Iter.leave_module_expr mexpr;

    et iter_class_expr cexpr =
      Iter.enter_class_expr cexpr;
      début
        filtre cexpr.cl_desc avec
        | Tcl_constraint (cl, None, _, _, _ ) ->
            iter_class_expr cl;
        | Tcl_structure clstr -> iter_class_structure clstr
        | Tcl_fun (label, pat, priv, cl, partial) ->
          iter_pattern pat;
          List.iter (fonc (id, _, exp) -> iter_expression exp) priv;
          iter_class_expr cl

        | Tcl_apply (cl, args) ->
            iter_class_expr cl;
            List.iter (fonc (label, expo, _) ->
                filtre expo avec
                  None -> ()
                | Some exp -> iter_expression exp
            ) args

        | Tcl_let (rec_flat, bindings, ivars, cl) ->
          iter_bindings rec_flat bindings;
          List.iter (fonc (id, _, exp) -> iter_expression exp) ivars;
            iter_class_expr cl

        | Tcl_constraint (cl, Some clty, vals, meths, concrs) ->
            iter_class_expr cl;
            iter_class_type clty

        | Tcl_ident (_, _, tyl) ->
            List.iter iter_core_type tyl
      fin;
      Iter.leave_class_expr cexpr;

    et iter_class_type ct =
      Iter.enter_class_type ct;
      début
        filtre ct.cltyp_desc avec
          Tcty_signature csg -> iter_class_signature csg
        | Tcty_constr (path, _, list) ->
            List.iter iter_core_type list
        | Tcty_arrow (label, ct, cl) ->
            iter_core_type ct;
            iter_class_type cl
      fin;
      Iter.leave_class_type ct;

    et iter_class_signature cs =
      Iter.enter_class_signature cs;
      iter_core_type cs.csig_self;
      List.iter iter_class_type_field cs.csig_fields;
      Iter.leave_class_signature cs


    et iter_class_type_field ctf =
      Iter.enter_class_type_field ctf;
      début
        filtre ctf.ctf_desc avec
          Tctf_inherit ct -> iter_class_type ct
        | Tctf_val (s, _mut, _virt, ct) ->
            iter_core_type ct
        | Tctf_method (s, _priv, _virt, ct) ->
            iter_core_type ct
        | Tctf_constraint  (ct1, ct2) ->
            iter_core_type ct1;
            iter_core_type ct2
      fin;
      Iter.leave_class_type_field ctf

    et iter_core_type ct =
      Iter.enter_core_type ct;
      début
        filtre ct.ctyp_desc avec
          Ttyp_any -> ()
        | Ttyp_var s -> ()
        | Ttyp_arrow (label, ct1, ct2) ->
            iter_core_type ct1;
            iter_core_type ct2
        | Ttyp_tuple list -> List.iter iter_core_type list
        | Ttyp_constr (path, _, list) ->
            List.iter iter_core_type list
        | Ttyp_object (list, o) ->
            List.iter (fonc (_, t) -> iter_core_type t) list
        | Ttyp_class (path, _, list) ->
            List.iter iter_core_type list
        | Ttyp_alias (ct, s) ->
            iter_core_type ct
        | Ttyp_variant (list, bool, labels) ->
            List.iter iter_row_field list
        | Ttyp_poly (list, ct) -> iter_core_type ct
        | Ttyp_package pack -> iter_package_type pack
      fin;
      Iter.leave_core_type ct

    et iter_class_structure cs =
      Iter.enter_class_structure cs;
      iter_pattern cs.cstr_self;
      List.iter iter_class_field cs.cstr_fields;
      Iter.leave_class_structure cs;


    et iter_row_field rf =
      filtre rf avec
        Ttag (label, bool, list) ->
          List.iter iter_core_type list
      | Tinherit ct -> iter_core_type ct

    et iter_class_field cf =
      Iter.enter_class_field cf;
      début
        filtre cf.cf_desc avec
          Tcf_inherit (ovf, cl, super, _vals, _meths) ->
          iter_class_expr cl
      | Tcf_constraint (cty, cty') ->
          iter_core_type cty;
          iter_core_type cty'
      | Tcf_val (lab, _, _, Tcfk_virtual cty, _) ->
          iter_core_type cty
      | Tcf_val (lab, _, _, Tcfk_concrete (_, exp), _) ->
          iter_expression exp
      | Tcf_method (lab, _, Tcfk_virtual cty) ->
          iter_core_type cty
      | Tcf_method (lab, _, Tcfk_concrete (_, exp)) ->
          iter_expression exp
      | Tcf_initializer exp ->
          iter_expression exp
      fin;
      Iter.leave_class_field cf;
  fin

module DefaultIteratorArgument = struct

      soit enter_structure _ = ()
      soit enter_value_description _ = ()
      soit enter_type_declaration _ = ()
      soit enter_exception_declaration _ = ()
      soit enter_pattern _ = ()
      soit enter_expression _ = ()
      soit enter_package_type _ = ()
      soit enter_signature _ = ()
      soit enter_signature_item _ = ()
      soit enter_module_type_declaration _ = ()
      soit enter_module_type _ = ()
      soit enter_module_expr _ = ()
      soit enter_with_constraint _ = ()
      soit enter_class_expr _ = ()
      soit enter_class_signature _ = ()
      soit enter_class_declaration _ = ()
      soit enter_class_description _ = ()
      soit enter_class_type_declaration _ = ()
      soit enter_class_type _ = ()
      soit enter_class_type_field _ = ()
      soit enter_core_type _ = ()
      soit enter_core_field_type _ = ()
      soit enter_class_structure _ = ()
    soit enter_class_field _ = ()
    soit enter_structure_item _ = ()


      soit leave_structure _ = ()
      soit leave_value_description _ = ()
      soit leave_type_declaration _ = ()
      soit leave_exception_declaration _ = ()
      soit leave_pattern _ = ()
      soit leave_expression _ = ()
      soit leave_package_type _ = ()
      soit leave_signature _ = ()
      soit leave_signature_item _ = ()
      soit leave_module_type_declaration _ = ()
      soit leave_module_type _ = ()
      soit leave_module_expr _ = ()
      soit leave_with_constraint _ = ()
      soit leave_class_expr _ = ()
      soit leave_class_signature _ = ()
      soit leave_class_declaration _ = ()
      soit leave_class_description _ = ()
      soit leave_class_type_declaration _ = ()
      soit leave_class_type _ = ()
      soit leave_class_type_field _ = ()
      soit leave_core_type _ = ()
      soit leave_core_field_type _ = ()
      soit leave_class_structure _ = ()
    soit leave_class_field _ = ()
    soit leave_structure_item _ = ()

    soit enter_binding _ = ()
    soit leave_binding _ = ()

    soit enter_bindings _ = ()
    soit leave_bindings _ = ()

  fin
