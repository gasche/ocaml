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

(* Abstract syntax tree after typing *)

ouvre Asttypes
ouvre Types

(* Value expressions for the core language *)

type partial = Partial | Total
type optional = Required | Optional

type attribute = Parsetree.attribute
type attributes = attribute list

type pattern =
  { pat_desc: pattern_desc;
    pat_loc: Location.t;
    pat_extra : (pat_extra * Location.t * attributes) list;
    pat_type: type_expr;
    modifiable pat_env: Env.t;
    pat_attributes: attributes;
   }

et pat_extra =
  | Tpat_constraint de core_type
  | Tpat_type de Path.t * Longident.t loc
  | Tpat_unpack

et pattern_desc =
    Tpat_any
  | Tpat_var de Ident.t * string loc
  | Tpat_alias de pattern * Ident.t * string loc
  | Tpat_constant de constant
  | Tpat_tuple de pattern list
  | Tpat_construct de
      Longident.t loc * constructor_description * pattern list
  | Tpat_variant de label * pattern option * row_desc ref
  | Tpat_record de
      (Longident.t loc * label_description * pattern) list *
        closed_flag
  | Tpat_array de pattern list
  | Tpat_or de pattern * pattern * row_desc option
  | Tpat_lazy de pattern

et expression =
  { exp_desc: expression_desc;
    exp_loc: Location.t;
    exp_extra: (exp_extra * Location.t * attributes) list;
    exp_type: type_expr;
    exp_env: Env.t;
    exp_attributes: attributes;
   }

et exp_extra =
  | Texp_constraint de core_type
  | Texp_coerce de core_type option * core_type
  | Texp_open de override_flag * Path.t * Longident.t loc * Env.t
  | Texp_poly de core_type option
  | Texp_newtype de string

et expression_desc =
    Texp_ident de Path.t * Longident.t loc * Types.value_description
  | Texp_constant de constant
  | Texp_let de rec_flag * value_binding list * expression
  | Texp_function de label * case list * partial
  | Texp_apply de expression * (label * expression option * optional) list
  | Texp_match de expression * case list * partial
  | Texp_try de expression * case list
  | Texp_tuple de expression list
  | Texp_construct de
      Longident.t loc * constructor_description * expression list
  | Texp_variant de label * expression option
  | Texp_record de
      (Longident.t loc * label_description * expression) list *
        expression option
  | Texp_field de expression * Longident.t loc * label_description
  | Texp_setfield de
      expression * Longident.t loc * label_description * expression
  | Texp_array de expression list
  | Texp_ifthenelse de expression * expression * expression option
  | Texp_sequence de expression * expression
  | Texp_while de expression * expression
  | Texp_for de
      Ident.t * Parsetree.pattern * expression * expression * direction_flag *
        expression
  | Texp_send de expression * meth * expression option
  | Texp_new de Path.t * Longident.t loc * Types.class_declaration
  | Texp_instvar de Path.t * Path.t * string loc
  | Texp_setinstvar de Path.t * Path.t * string loc * expression
  | Texp_override de Path.t * (Path.t * string loc * expression) list
  | Texp_letmodule de Ident.t * string loc * module_expr * expression
  | Texp_assert de expression
  | Texp_lazy de expression
  | Texp_object de class_structure * string list
  | Texp_pack de module_expr

et meth =
    Tmeth_name de string
  | Tmeth_val de Ident.t

et case =
    {
     c_lhs: pattern;
     c_guard: expression option;
     c_rhs: expression;
    }

(* Value expressions for the class language *)

et class_expr =
    {
     cl_desc: class_expr_desc;
     cl_loc: Location.t;
     cl_type: Types.class_type;
     cl_env: Env.t;
     cl_attributes: attributes;
    }

et class_expr_desc =
    Tcl_ident de Path.t * Longident.t loc * core_type list
  | Tcl_structure de class_structure
  | Tcl_fun de
      label * pattern * (Ident.t * string loc * expression) list * class_expr *
        partial
  | Tcl_apply de class_expr * (label * expression option * optional) list
  | Tcl_let de rec_flag * value_binding list *
                  (Ident.t * string loc * expression) list * class_expr
  | Tcl_constraint de
      class_expr * class_type option * string list * string list * Concr.t
    (* Visible instance variables, methods and concretes methods *)

et class_structure =
  {
   cstr_self: pattern;
   cstr_fields: class_field list;
   cstr_type: Types.class_signature;
   cstr_meths: Ident.t Meths.t;
  }

et class_field =
   {
    cf_desc: class_field_desc;
    cf_loc: Location.t;
    cf_attributes: attributes;
  }

et class_field_kind =
  | Tcfk_virtual de core_type
  | Tcfk_concrete de override_flag * expression

et class_field_desc =
    Tcf_inherit de
      override_flag * class_expr * string option * (string * Ident.t) list *
        (string * Ident.t) list
    (* Inherited instance variables and concrete methods *)
  | Tcf_val de string loc * mutable_flag * Ident.t * class_field_kind * bool
  | Tcf_method de string loc * private_flag * class_field_kind
  | Tcf_constraint de core_type * core_type
  | Tcf_initializer de expression

(* Value expressions for the module language *)

et module_expr =
  { mod_desc: module_expr_desc;
    mod_loc: Location.t;
    mod_type: Types.module_type;
    mod_env: Env.t;
    mod_attributes: attributes;
   }

et module_type_constraint =
  Tmodtype_implicit
| Tmodtype_explicit de module_type

et module_expr_desc =
    Tmod_ident de Path.t * Longident.t loc
  | Tmod_structure de structure
  | Tmod_functor de Ident.t * string loc * module_type option * module_expr
  | Tmod_apply de module_expr * module_expr * module_coercion
  | Tmod_constraint de
      module_expr * Types.module_type * module_type_constraint * module_coercion
  | Tmod_unpack de expression * Types.module_type

et structure = {
  str_items : structure_item list;
  str_type : Types.signature;
  str_final_env : Env.t;
}

et structure_item =
  { str_desc : structure_item_desc;
    str_loc : Location.t;
    str_env : Env.t
  }

et structure_item_desc =
    Tstr_eval de expression * attributes
  | Tstr_value de rec_flag * value_binding list
  | Tstr_primitive de value_description
  | Tstr_type de type_declaration list
  | Tstr_exception de constructor_declaration
  | Tstr_exn_rebind de Ident.t * string loc * Path.t * Longident.t loc * attributes
  | Tstr_module de module_binding
  | Tstr_recmodule de module_binding list
  | Tstr_modtype de module_type_declaration
  | Tstr_open de override_flag * Path.t * Longident.t loc * attributes
  | Tstr_class de (class_declaration * string list * virtual_flag) list
  | Tstr_class_type de (Ident.t * string loc * class_type_declaration) list
  | Tstr_include de module_expr * Types.signature * attributes
  | Tstr_attribute de attribute

et module_binding =
    {
     mb_id: Ident.t;
     mb_name: string loc;
     mb_expr: module_expr;
     mb_attributes: attributes;
     mb_loc: Location.t;
    }

et value_binding =
  {
    vb_pat: pattern;
    vb_expr: expression;
    vb_attributes: attributes;
  }

et module_coercion =
    Tcoerce_none
  | Tcoerce_structure de (int * module_coercion) list *
                         (Ident.t * int * module_coercion) list
  | Tcoerce_functor de module_coercion * module_coercion
  | Tcoerce_primitive de Primitive.description
  | Tcoerce_alias de Path.t * module_coercion

et module_type =
  { mty_desc: module_type_desc;
    mty_type : Types.module_type;
    mty_env : Env.t;
    mty_loc: Location.t;
    mty_attributes: attributes;
   }

et module_type_desc =
    Tmty_ident de Path.t * Longident.t loc
  | Tmty_signature de signature
  | Tmty_functor de Ident.t * string loc * module_type option * module_type
  | Tmty_with de module_type * (Path.t * Longident.t loc * with_constraint) list
  | Tmty_typeof de module_expr
  | Tmty_alias de Path.t * Longident.t loc

et signature = {
  sig_items : signature_item list;
  sig_type : Types.signature;
  sig_final_env : Env.t;
}

et signature_item =
  { sig_desc: signature_item_desc;
    sig_env : Env.t; (* BINANNOT ADDED *)
    sig_loc: Location.t }

et signature_item_desc =
    Tsig_value de value_description
  | Tsig_type de type_declaration list
  | Tsig_exception de constructor_declaration
  | Tsig_module de module_declaration
  | Tsig_recmodule de module_declaration list
  | Tsig_modtype de module_type_declaration
  | Tsig_open de override_flag * Path.t * Longident.t loc * attributes
  | Tsig_include de module_type * Types.signature * attributes
  | Tsig_class de class_description list
  | Tsig_class_type de class_type_declaration list
  | Tsig_attribute de attribute

et module_declaration =
    {
     md_id: Ident.t;
     md_name: string loc;
     md_type: module_type;
     md_attributes: attributes;
     md_loc: Location.t;
    }

et module_type_declaration =
    {
     mtd_id: Ident.t;
     mtd_name: string loc;
     mtd_type: module_type option;
     mtd_attributes: attributes;
     mtd_loc: Location.t;
    }

et with_constraint =
    Twith_type de type_declaration
  | Twith_module de Path.t * Longident.t loc
  | Twith_typesubst de type_declaration
  | Twith_modsubst de Path.t * Longident.t loc

et core_type =
(* mutable because of [Typeclass.declare_method] *)
  { modifiable ctyp_desc : core_type_desc;
    modifiable ctyp_type : type_expr;
    ctyp_env : Env.t; (* BINANNOT ADDED *)
    ctyp_loc : Location.t;
    ctyp_attributes: attributes;
   }

et core_type_desc =
    Ttyp_any
  | Ttyp_var de string
  | Ttyp_arrow de label * core_type * core_type
  | Ttyp_tuple de core_type list
  | Ttyp_constr de Path.t * Longident.t loc * core_type list
  | Ttyp_object de (string * core_type) list * closed_flag
  | Ttyp_class de Path.t * Longident.t loc * core_type list
  | Ttyp_alias de core_type * string
  | Ttyp_variant de row_field list * closed_flag * label list option
  | Ttyp_poly de string list * core_type
  | Ttyp_package de package_type

et package_type = {
  pack_name : Path.t;
  pack_fields : (Longident.t loc * core_type) list;
  pack_type : Types.module_type;
  pack_txt : Longident.t loc;
}

et row_field =
    Ttag de label * bool * core_type list
  | Tinherit de core_type

et value_description =
  { val_id: Ident.t;
    val_name: string loc;
    val_desc: core_type;
    val_val: Types.value_description;
    val_prim: string list;
    val_loc: Location.t;
    val_attributes: attributes;
    }

et type_declaration =
  {
    typ_id: Ident.t;
    typ_name: string loc;
    typ_params: (string loc option * variance) list;
    typ_type: Types.type_declaration;
    typ_cstrs: (core_type * core_type * Location.t) list;
    typ_kind: type_kind;
    typ_private: private_flag;
    typ_manifest: core_type option;
    typ_loc: Location.t;
    typ_attributes: attributes;
   }

et type_kind =
    Ttype_abstract
  | Ttype_variant de constructor_declaration list
  | Ttype_record de label_declaration list

et label_declaration =
    {
     ld_id: Ident.t;
     ld_name: string loc;
     ld_mutable: mutable_flag;
     ld_type: core_type;
     ld_loc: Location.t;
     ld_attributes: attributes;
    }

et constructor_declaration =
    {
     cd_id: Ident.t;
     cd_name: string loc;
     cd_args: core_type list;
     cd_res: core_type option;
     cd_loc: Location.t;
     cd_attributes: attributes;
    }

et class_type =
    {
     cltyp_desc: class_type_desc;
     cltyp_type: Types.class_type;
     cltyp_env: Env.t;
     cltyp_loc: Location.t;
     cltyp_attributes: attributes;
    }

et class_type_desc =
    Tcty_constr de Path.t * Longident.t loc * core_type list
  | Tcty_signature de class_signature
  | Tcty_arrow de label * core_type * class_type

et class_signature = {
    csig_self : core_type;
    csig_fields : class_type_field list;
    csig_type : Types.class_signature;
  }

et class_type_field = {
    ctf_desc: class_type_field_desc;
    ctf_loc: Location.t;
    ctf_attributes: attributes;
  }

et class_type_field_desc =
  | Tctf_inherit de class_type
  | Tctf_val de (string * mutable_flag * virtual_flag * core_type)
  | Tctf_method de (string * private_flag * virtual_flag * core_type)
  | Tctf_constraint de (core_type * core_type)

et class_declaration =
  class_expr class_infos

et class_description =
  class_type class_infos

et class_type_declaration =
  class_type class_infos

et 'a class_infos =
  { ci_virt: virtual_flag;
    ci_params: (string loc * variance) list;
    ci_id_name : string loc;
    ci_id_class: Ident.t;
    ci_id_class_type : Ident.t;
    ci_id_object : Ident.t;
    ci_id_typesharp : Ident.t;
    ci_expr: 'a;
    ci_decl: Types.class_declaration;
    ci_type_decl : Types.class_type_declaration;
    ci_loc: Location.t;
    ci_attributes: attributes;
   }

(* Auxiliary functions over the a.s.t. *)

val iter_pattern_desc: (pattern -> unit) -> pattern_desc -> unit
val map_pattern_desc: (pattern -> pattern) -> pattern_desc -> pattern_desc

val let_bound_idents: value_binding list -> Ident.t list
val rev_let_bound_idents: value_binding list -> Ident.t list

val let_bound_idents_with_loc:
    value_binding list -> (Ident.t * string loc) list

(* Alpha conversion of patterns *)
val alpha_pat: (Ident.t * Ident.t) list -> pattern -> pattern

val mknoloc: 'a -> 'a Asttypes.loc
val mkloc: 'a -> Location.t -> 'a Asttypes.loc

val pat_bound_idents: pattern -> (Ident.t * string Asttypes.loc) list
