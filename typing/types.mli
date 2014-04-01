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

(* Representation of types and declarations *)

ouvre Asttypes

(* Type expressions for the core language *)

type type_expr =
  { modifiable desc: type_desc;
    modifiable level: int;
    modifiable id: int }

et type_desc =
    Tvar de string option
  | Tarrow de label * type_expr * type_expr * commutable
  | Ttuple de type_expr list
  | Tconstr de Path.t * type_expr list * abbrev_memo ref
  | Tobject de type_expr * (Path.t * type_expr list) option ref
  | Tfield de string * field_kind * type_expr * type_expr
  | Tnil
  | Tlink de type_expr
  | Tsubst de type_expr         (* for copying *)
  | Tvariant de row_desc
  | Tunivar de string option
  | Tpoly de type_expr * type_expr list
  | Tpackage de Path.t * Longident.t list * type_expr list

et row_desc =
    { row_fields: (label * row_field) list;
      row_more: type_expr;
      row_bound: unit; (* kept for compatibility *)
      row_closed: bool;
      row_fixed: bool;
      row_name: (Path.t * type_expr list) option }

et row_field =
    Rpresent de type_expr option
  | Reither de bool * type_expr list * bool * row_field option ref
        (* 1st true denotes a constant constructor *)
        (* 2nd true denotes a tag in a pattern matching, and
           is erased later *)
  | Rabsent

et abbrev_memo =
    Mnil
  | Mcons de private_flag * Path.t * type_expr * type_expr * abbrev_memo
  | Mlink de abbrev_memo ref

et field_kind =
    Fvar de field_kind option ref
  | Fpresent
  | Fabsent

et commutable =
    Cok
  | Cunknown
  | Clink de commutable ref

module TypeOps : sig
  type t = type_expr
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int
fin

(* Maps of methods and instance variables *)

module Meths : Map.S avec type key = string
module Vars  : Map.S avec type key = string

(* Value descriptions *)

type value_description =
  { val_type: type_expr;                (* Type of the value *)
    val_kind: value_kind;
    val_loc: Location.t;
    val_attributes: Parsetree.attributes;
   }

et value_kind =
    Val_reg                             (* Regular value *)
  | Val_prim de Primitive.description   (* Primitive *)
  | Val_ivar de mutable_flag * string   (* Instance variable (mutable ?) *)
  | Val_self de (Ident.t * type_expr) Meths.t ref *
                (Ident.t * mutable_flag * virtual_flag * type_expr) Vars.t ref *
                string * type_expr
                                        (* Self *)
  | Val_anc de (string * Ident.t) list * string
                                        (* Ancestor *)
  | Val_unbound                         (* Unbound variable *)

(* Constructor descriptions *)

type constructor_description =
  { cstr_name: string;                  (* Constructor name *)
    cstr_res: type_expr;                (* Type of the result *)
    cstr_existentials: type_expr list;  (* list of existentials *)
    cstr_args: type_expr list;          (* Type of the arguments *)
    cstr_arity: int;                    (* Number of arguments *)
    cstr_tag: constructor_tag;          (* Tag for heap blocks *)
    cstr_consts: int;                   (* Number of constant constructors *)
    cstr_nonconsts: int;                (* Number of non-const constructors *)
    cstr_normal: int;                   (* Number of non generalized constrs *)
    cstr_generalized: bool;             (* Constrained return type? *)
    cstr_private: private_flag;         (* Read-only constructor? *)
    cstr_loc: Location.t;
    cstr_attributes: Parsetree.attributes;
   }

et constructor_tag =
    Cstr_constant de int                (* Constant constructor (an int) *)
  | Cstr_block de int                   (* Regular constructor (a block) *)
  | Cstr_exception de Path.t * Location.t (* Exception constructor *)

(* Record label descriptions *)

type label_description =
  { lbl_name: string;                   (* Short name *)
    lbl_res: type_expr;                 (* Type of the result *)
    lbl_arg: type_expr;                 (* Type of the argument *)
    lbl_mut: mutable_flag;              (* Is this a mutable field? *)
    lbl_pos: int;                       (* Position in block *)
    lbl_all: label_description array;   (* All the labels in this type *)
    lbl_repres: record_representation;  (* Representation for this record *)
    lbl_private: private_flag;          (* Read-only field? *)
    lbl_loc: Location.t;
    lbl_attributes: Parsetree.attributes;
  }

et record_representation =
    Record_regular                      (* All fields are boxed / tagged *)
  | Record_float                        (* All fields are floats *)

(* Variance *)

module Variance : sig
  type t
  type f = May_pos | May_neg | May_weak | Inj | Pos | Neg | Inv
  val null : t                          (* no occurence *)
  val full : t                          (* strictly invariant *)
  val covariant : t                     (* strictly covariant *)
  val may_inv : t                       (* maybe invariant *)
  val union  : t -> t -> t
  val inter  : t -> t -> t
  val subset : t -> t -> bool
  val set : f -> bool -> t -> t
  val mem : f -> t -> bool
  val conjugate : t -> t                (* exchange positive and negative *)
  val get_upper : t -> bool * bool                  (* may_pos, may_neg   *)
  val get_lower : t -> bool * bool * bool * bool    (* pos, neg, inv, inj *)
fin

(* Type definitions *)

type type_declaration =
  { type_params: type_expr list;
    type_arity: int;
    type_kind: type_kind;
    type_private: private_flag;
    type_manifest: type_expr option;
    type_variance: Variance.t list;
    (* covariant, contravariant, weakly contravariant, injective *)
    type_newtype_level: (int * int) option;
    (* definition level * expansion level *)
    type_loc: Location.t;
    type_attributes: Parsetree.attributes;
  }

et type_kind =
    Type_abstract
  | Type_record de label_declaration list  * record_representation
  | Type_variant de constructor_declaration list

et label_declaration =
  {
    ld_id: Ident.t;
    ld_mutable: mutable_flag;
    ld_type: type_expr;
    ld_loc: Location.t;
    ld_attributes: Parsetree.attributes;
  }

et constructor_declaration =
  {
    cd_id: Ident.t;
    cd_args: type_expr list;
    cd_res: type_expr option;
    cd_loc: Location.t;
    cd_attributes: Parsetree.attributes;
  }

et type_transparence =
    Type_public      (* unrestricted expansion *)
  | Type_new         (* "new" type *)
  | Type_private     (* private type *)

type exception_declaration =
    { exn_args: type_expr list;
      exn_loc: Location.t;
      exn_attributes: Parsetree.attributes;
    }

(* Type expressions for the class language *)

module Concr : Set.S avec type elt = string

type class_type =
    Cty_constr de Path.t * type_expr list * class_type
  | Cty_signature de class_signature
  | Cty_arrow de label * type_expr * class_type

et class_signature =
  { csig_self: type_expr;
    csig_vars:
      (Asttypes.mutable_flag * Asttypes.virtual_flag * type_expr) Vars.t;
    csig_concr: Concr.t;
    csig_inher: (Path.t * type_expr list) list }

type class_declaration =
  { cty_params: type_expr list;
    modifiable cty_type: class_type;
    cty_path: Path.t;
    cty_new: type_expr option;
    cty_variance: Variance.t list;
    cty_loc: Location.t;
    cty_attributes: Parsetree.attributes;
  }

type class_type_declaration =
  { clty_params: type_expr list;
    clty_type: class_type;
    clty_path: Path.t;
    clty_variance: Variance.t list;
    clty_loc: Location.t;
    clty_attributes: Parsetree.attributes;
  }

(* Type expressions for the module language *)

type module_type =
    Mty_ident de Path.t
  | Mty_signature de signature
  | Mty_functor de Ident.t * module_type option * module_type
  | Mty_alias de Path.t

et signature = signature_item list

et signature_item =
    Sig_value de Ident.t * value_description
  | Sig_type de Ident.t * type_declaration * rec_status
  | Sig_exception de Ident.t * exception_declaration
  | Sig_module de Ident.t * module_declaration * rec_status
  | Sig_modtype de Ident.t * modtype_declaration
  | Sig_class de Ident.t * class_declaration * rec_status
  | Sig_class_type de Ident.t * class_type_declaration * rec_status

et module_declaration =
  {
    md_type: module_type;
    md_attributes: Parsetree.attributes;
    md_loc: Location.t;
  }

et modtype_declaration =
  {
    mtd_type: module_type option;  (* None: abstract *)
    mtd_attributes: Parsetree.attributes;
    mtd_loc: Location.t;
  }

et rec_status =
    Trec_not                            (* not recursive *)
  | Trec_first                          (* first in a recursive group *)
  | Trec_next                           (* not first in a recursive group *)
