(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*                        Alain Frisch, LexiFi                         *)
(*                                                                     *)
(*  Copyright 2012 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

ouvre Typedtree

soit opt f = fonction None -> () | Some x -> f x

soit structure sub str =
  List.iter (sub # structure_item) str.str_items

soit constructor_decl sub cd =
  List.iter (sub # core_type) cd.cd_args;
  opt (sub # core_type) cd.cd_res

soit structure_item sub x =
  filtre x.str_desc avec
  | Tstr_eval (exp, _attrs) -> sub # expression exp
  | Tstr_value (rec_flag, list) -> sub # bindings (rec_flag, list)
  | Tstr_primitive v -> sub # value_description v
  | Tstr_type list -> List.iter (sub # type_declaration) list
  | Tstr_exception decl -> constructor_decl sub decl
  | Tstr_exn_rebind (_id, _, _p, _, _) -> ()
  | Tstr_module mb -> sub # module_binding mb
  | Tstr_recmodule list -> List.iter (sub # module_binding) list
  | Tstr_modtype mtd -> opt (sub # module_type) mtd.mtd_type
  | Tstr_open _ -> ()
  | Tstr_class list ->
      List.iter (fonc (ci, _, _) -> sub # class_expr ci.ci_expr) list
  | Tstr_class_type list ->
      List.iter (fonc (_id, _, ct) -> sub # class_type ct.ci_expr) list
  | Tstr_include (mexpr, _, _) -> sub # module_expr mexpr
  | Tstr_attribute _ -> ()

soit value_description sub x =
  sub # core_type x.val_desc

soit type_declaration sub decl =
  List.iter
    (fonc (ct1, ct2, _loc) -> sub # core_type ct1; sub # core_type ct2)
    decl.typ_cstrs;
  début filtre decl.typ_kind avec
  | Ttype_abstract -> ()
  | Ttype_variant list ->
      List.iter (constructor_decl sub) list
  | Ttype_record list ->
      List.iter (fonc ld -> sub # core_type ld.ld_type) list
  fin;
  opt (sub # core_type) decl.typ_manifest

soit pattern sub pat =
  soit extra = fonction
    | Tpat_type _
    | Tpat_unpack -> ()
    | Tpat_constraint ct -> sub # core_type ct
  dans
  List.iter (fonc (c, _, _) -> extra c) pat.pat_extra;
  filtre pat.pat_desc avec
  | Tpat_any
  | Tpat_var _
  | Tpat_constant _ -> ()
  | Tpat_tuple l
  | Tpat_construct (_, _, l) -> List.iter (sub # pattern) l
  | Tpat_variant (_, po, _) -> opt (sub # pattern) po
  | Tpat_record (l, _) -> List.iter (fonc (_, _, pat) -> sub # pattern pat) l
  | Tpat_array l -> List.iter (sub # pattern) l
  | Tpat_or (p1, p2, _) -> sub # pattern p1; sub # pattern p2
  | Tpat_alias (p, _, _)
  | Tpat_lazy p -> sub # pattern p

soit expression sub exp =
  soit extra = fonction
    | Texp_constraint cty ->
        sub # core_type cty
    | Texp_coerce (cty1, cty2) ->
        opt (sub # core_type) cty1; sub # core_type cty2
    | Texp_open _
    | Texp_newtype _ -> ()
    | Texp_poly cto -> opt (sub # core_type) cto
  dans
  List.iter (fonc (c, _, _) -> extra c) exp.exp_extra;
  filtre exp.exp_desc avec
  | Texp_ident _
  | Texp_constant _ -> ()
  | Texp_let (rec_flag, list, exp) ->
      sub # bindings (rec_flag, list);
      sub # expression exp
  | Texp_function (_, cases, _) ->
      sub # cases cases
  | Texp_apply (exp, list) ->
      sub # expression exp;
      List.iter (fonc (_, expo, _) -> opt (sub # expression) expo) list
  | Texp_match (exp, cases, _) ->
      sub # expression exp;
      sub # cases cases
  | Texp_try (exp, cases) ->
      sub # expression exp;
      sub # cases cases
  | Texp_tuple list ->
      List.iter (sub # expression) list
  | Texp_construct (_, _, args) ->
      List.iter (sub # expression) args
  | Texp_variant (_, expo) ->
      opt (sub # expression) expo
  | Texp_record (list, expo) ->
      List.iter (fonc (_, _, exp) -> sub # expression exp) list;
      opt (sub # expression) expo
  | Texp_field (exp, _, _label) ->
      sub # expression exp
  | Texp_setfield (exp1, _, _label, exp2) ->
      sub # expression exp1;
      sub # expression exp2
  | Texp_array list ->
      List.iter (sub # expression) list
  | Texp_ifthenelse (exp1, exp2, expo) ->
      sub # expression exp1;
      sub # expression exp2;
      opt (sub # expression) expo
  | Texp_sequence (exp1, exp2) ->
      sub # expression exp1;
      sub # expression exp2
  | Texp_while (exp1, exp2) ->
      sub # expression exp1;
      sub # expression exp2
  | Texp_for (_id, _, exp1, exp2, _dir, exp3) ->
      sub # expression exp1;
      sub # expression exp2;
      sub # expression exp3
  | Texp_send (exp, _meth, expo) ->
      sub # expression exp;
      opt (sub # expression) expo
  | Texp_new (_path, _, _) -> ()
  | Texp_instvar (_, _path, _) -> ()
  | Texp_setinstvar (_, _, _, exp) ->
      sub # expression exp
  | Texp_override (_, list) ->
      List.iter (fonc (_path, _, exp) -> sub # expression exp) list
  | Texp_letmodule (_id, _, mexpr, exp) ->
      sub # module_expr mexpr;
      sub # expression exp
  | Texp_assert exp -> sub # expression exp
  | Texp_lazy exp -> sub # expression exp
  | Texp_object (cl, _) ->
      sub # class_structure cl
  | Texp_pack (mexpr) ->
      sub # module_expr mexpr


soit package_type sub pack =
  List.iter (fonc (_s, ct) -> sub # core_type ct) pack.pack_fields

soit signature sub sg =
  List.iter (sub # signature_item) sg.sig_items

soit signature_item sub item =
  filtre item.sig_desc avec
  | Tsig_value v ->
      sub # value_description v
  | Tsig_type list ->
      List.iter (sub # type_declaration) list
  | Tsig_exception decl ->
      constructor_decl sub decl
  | Tsig_module md ->
      sub # module_type md.md_type
  | Tsig_recmodule list ->
      List.iter (fonc md -> sub # module_type md.md_type) list
  | Tsig_modtype mtd ->
      opt (sub # module_type) mtd.mtd_type
  | Tsig_open _ -> ()
  | Tsig_include (mty,_,_) -> sub # module_type mty
  | Tsig_class list ->
      List.iter (sub # class_description) list
  | Tsig_class_type list ->
      List.iter (sub # class_type_declaration) list
  | Tsig_attribute _ -> ()

soit class_description sub cd =
  sub # class_type cd.ci_expr

soit class_type_declaration sub cd =
  sub # class_type cd.ci_expr

soit module_type sub mty =
  filtre mty.mty_desc avec
  | Tmty_ident (_path, _) -> ()
  | Tmty_alias (_path, _) -> ()
  | Tmty_signature sg -> sub # signature sg
  | Tmty_functor (_id, _, mtype1, mtype2) ->
      Misc.may (sub # module_type) mtype1; sub # module_type mtype2
  | Tmty_with (mtype, list) ->
      sub # module_type mtype;
      List.iter (fonc (_, _, withc) -> sub # with_constraint withc) list
  | Tmty_typeof mexpr ->
      sub # module_expr mexpr

soit with_constraint sub cstr =
  filtre cstr avec
  | Twith_type decl -> sub # type_declaration decl
  | Twith_module _ -> ()
  | Twith_typesubst decl -> sub # type_declaration decl
  | Twith_modsubst _ -> ()

soit module_expr sub mexpr =
  filtre mexpr.mod_desc avec
  | Tmod_ident (_p, _) -> ()
  | Tmod_structure st -> sub # structure st
  | Tmod_functor (_id, _, mtype, mexpr) ->
      Misc.may (sub # module_type) mtype;
      sub # module_expr mexpr
  | Tmod_apply (mexp1, mexp2, _) ->
      sub # module_expr mexp1;
      sub # module_expr mexp2
  | Tmod_constraint (mexpr, _, Tmodtype_implicit, _ ) ->
      sub # module_expr mexpr
  | Tmod_constraint (mexpr, _, Tmodtype_explicit mtype, _) ->
      sub # module_expr mexpr;
      sub # module_type mtype
  | Tmod_unpack (exp, _mty) ->
      sub # expression exp
(*          sub # module_type mty *)

soit module_binding sub mb =
  module_expr sub mb.mb_expr

soit class_expr sub cexpr =
  filtre cexpr.cl_desc avec
  | Tcl_constraint (cl, None, _, _, _ ) ->
      sub # class_expr cl;
  | Tcl_structure clstr -> sub # class_structure clstr
  | Tcl_fun (_label, pat, priv, cl, _partial) ->
      sub # pattern pat;
      List.iter (fonc (_id, _, exp) -> sub # expression exp) priv;
      sub # class_expr cl
  | Tcl_apply (cl, args) ->
      sub # class_expr cl;
      List.iter (fonc (_label, expo, _) -> opt (sub # expression) expo) args
  | Tcl_let (rec_flat, bindings, ivars, cl) ->
      sub # bindings (rec_flat, bindings);
      List.iter (fonc (_id, _, exp) -> sub # expression exp) ivars;
      sub # class_expr cl
  | Tcl_constraint (cl, Some clty, _vals, _meths, _concrs) ->
      sub # class_expr cl;
      sub # class_type clty
  | Tcl_ident (_, _, tyl) ->
      List.iter (sub # core_type) tyl

soit class_type sub ct =
  filtre ct.cltyp_desc avec
  | Tcty_signature csg -> sub # class_signature csg
  | Tcty_constr (_path, _, list) -> List.iter (sub # core_type) list
  | Tcty_arrow (_label, ct, cl) ->
      sub # core_type ct;
      sub # class_type cl

soit class_signature sub cs =
  sub # core_type cs.csig_self;
  List.iter (sub # class_type_field) cs.csig_fields

soit class_type_field sub ctf =
  filtre ctf.ctf_desc avec
  | Tctf_inherit ct -> sub # class_type ct
  | Tctf_val (_s, _mut, _virt, ct) ->
      sub # core_type ct
  | Tctf_method (_s, _priv, _virt, ct) ->
      sub # core_type ct
  | Tctf_constraint  (ct1, ct2) ->
      sub # core_type ct1;
      sub # core_type ct2

soit core_type sub ct =
  filtre ct.ctyp_desc avec
  | Ttyp_any -> ()
  | Ttyp_var _s -> ()
  | Ttyp_arrow (_label, ct1, ct2) ->
      sub # core_type ct1;
      sub # core_type ct2
  | Ttyp_tuple list -> List.iter (sub # core_type) list
  | Ttyp_constr (_path, _, list) ->
      List.iter (sub # core_type) list
  | Ttyp_object (list, _o) ->
      List.iter (fonc (_, t) -> sub # core_type t) list
  | Ttyp_class (_path, _, list) ->
      List.iter (sub # core_type) list
  | Ttyp_alias (ct, _s) ->
      sub # core_type ct
  | Ttyp_variant (list, _bool, _labels) ->
      List.iter (sub # row_field) list
  | Ttyp_poly (_list, ct) -> sub # core_type ct
  | Ttyp_package pack -> sub # package_type pack

soit class_structure sub cs =
  sub # pattern cs.cstr_self;
  List.iter (sub # class_field) cs.cstr_fields

soit row_field sub rf =
  filtre rf avec
  | Ttag (_label, _bool, list) -> List.iter (sub # core_type) list
  | Tinherit ct -> sub # core_type ct

soit class_field sub cf =
  filtre cf.cf_desc avec
  | Tcf_inherit (_ovf, cl, _super, _vals, _meths) ->
      sub # class_expr cl
  | Tcf_constraint (cty, cty') ->
      sub # core_type cty;
      sub # core_type cty'
  | Tcf_val (_, _, _mut, Tcfk_virtual cty, _override) ->
      sub # core_type cty
  | Tcf_val (_, _, _mut, Tcfk_concrete (_, exp), _override) ->
      sub # expression exp
  | Tcf_method (_, _priv, Tcfk_virtual cty) ->
      sub # core_type cty
  | Tcf_method (_, _priv, Tcfk_concrete (_, exp)) ->
      sub # expression exp
  | Tcf_initializer exp ->
      sub # expression exp

soit bindings sub (_rec_flag, list) =
  List.iter (sub # binding) list

soit cases sub l =
  List.iter (sub # case) l

soit case sub {c_lhs; c_guard; c_rhs} =
  sub # pattern c_lhs;
  opt (sub # expression) c_guard;
  sub # expression c_rhs

soit binding sub vb =
  sub # pattern vb.vb_pat;
  sub # expression vb.vb_expr

classe iter = objet(this)
  méthode binding = binding this
  méthode bindings = bindings this
  méthode case = case this
  méthode cases = cases this
  méthode class_description = class_description this
  méthode class_expr = class_expr this
  méthode class_field = class_field this
  méthode class_signature = class_signature this
  méthode class_structure = class_structure this
  méthode class_type = class_type this
  méthode class_type_declaration = class_type_declaration this
  méthode class_type_field = class_type_field this
  méthode core_type = core_type this
  méthode expression = expression this
  méthode module_binding = module_binding this
  méthode module_expr = module_expr this
  méthode module_type = module_type this
  méthode package_type = package_type this
  méthode pattern = pattern this
  méthode row_field = row_field this
  méthode signature = signature this
  méthode signature_item = signature_item this
  méthode structure = structure this
  méthode structure_item = structure_item this
  méthode type_declaration = type_declaration this
  méthode value_description = value_description this
  méthode with_constraint = with_constraint this
fin
