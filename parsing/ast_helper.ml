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

(** Helpers to produce Parsetree fragments *)

ouvre Asttypes
ouvre Parsetree

type lid = Longident.t loc
type str = string loc
type loc = Location.t
type attrs = attribute list

soit default_loc = ref Location.none

soit with_default_loc l f =
  soit old = !default_loc dans
  default_loc := l;
  essaie soit r = f () dans default_loc := old; r
  avec exn -> default_loc := old; raise exn

module Typ = struct
  soit mk ?(loc = !default_loc) ?(attrs = []) d = {ptyp_desc = d; ptyp_loc = loc; ptyp_attributes = attrs}
  soit attr d a = {d avec ptyp_attributes = d.ptyp_attributes @ [a]}

  soit any ?loc ?attrs () = mk ?loc ?attrs Ptyp_any
  soit var ?loc ?attrs a = mk ?loc ?attrs (Ptyp_var a)
  soit arrow ?loc ?attrs a b c = mk ?loc ?attrs (Ptyp_arrow (a, b, c))
  soit tuple ?loc ?attrs a = mk ?loc ?attrs (Ptyp_tuple a)
  soit constr ?loc ?attrs a b = mk ?loc ?attrs (Ptyp_constr (a, b))
  soit object_ ?loc ?attrs a b = mk ?loc ?attrs (Ptyp_object (a, b))
  soit class_ ?loc ?attrs a b = mk ?loc ?attrs (Ptyp_class (a, b))
  soit alias ?loc ?attrs a b = mk ?loc ?attrs (Ptyp_alias (a, b))
  soit variant ?loc ?attrs a b c = mk ?loc ?attrs (Ptyp_variant (a, b, c))
  soit poly ?loc ?attrs a b = mk ?loc ?attrs (Ptyp_poly (a, b))
  soit package ?loc ?attrs a b = mk ?loc ?attrs (Ptyp_package (a, b))
  soit extension ?loc ?attrs a = mk ?loc ?attrs (Ptyp_extension a)

  soit force_poly t =
    filtre t.ptyp_desc avec
    | Ptyp_poly _ -> t
    | _ -> poly ~loc:t.ptyp_loc [] t (* -> ghost? *)
fin

module Pat = struct
  soit mk ?(loc = !default_loc) ?(attrs = []) d = {ppat_desc = d; ppat_loc = loc; ppat_attributes = attrs}
  soit attr d a = {d avec ppat_attributes = d.ppat_attributes @ [a]}

  soit any ?loc ?attrs () = mk ?loc ?attrs Ppat_any
  soit var ?loc ?attrs a = mk ?loc ?attrs (Ppat_var a)
  soit alias ?loc ?attrs a b = mk ?loc ?attrs (Ppat_alias (a, b))
  soit constant ?loc ?attrs a = mk ?loc ?attrs (Ppat_constant a)
  soit interval ?loc ?attrs a b = mk ?loc ?attrs (Ppat_interval (a, b))
  soit tuple ?loc ?attrs a = mk ?loc ?attrs (Ppat_tuple a)
  soit construct ?loc ?attrs a b = mk ?loc ?attrs (Ppat_construct (a, b))
  soit variant ?loc ?attrs a b = mk ?loc ?attrs (Ppat_variant (a, b))
  soit record ?loc ?attrs a b = mk ?loc ?attrs (Ppat_record (a, b))
  soit array ?loc ?attrs a = mk ?loc ?attrs (Ppat_array a)
  soit or_ ?loc ?attrs a b = mk ?loc ?attrs (Ppat_or (a, b))
  soit constraint_ ?loc ?attrs a b = mk ?loc ?attrs (Ppat_constraint (a, b))
  soit type_ ?loc ?attrs a = mk ?loc ?attrs (Ppat_type a)
  soit lazy_ ?loc ?attrs a = mk ?loc ?attrs (Ppat_lazy a)
  soit unpack ?loc ?attrs a = mk ?loc ?attrs (Ppat_unpack a)
  soit extension ?loc ?attrs a = mk ?loc ?attrs (Ppat_extension a)
fin

module Exp = struct
  soit mk ?(loc = !default_loc) ?(attrs = []) d = {pexp_desc = d; pexp_loc = loc; pexp_attributes = attrs}
  soit attr d a = {d avec pexp_attributes = d.pexp_attributes @ [a]}

  soit ident ?loc ?attrs a = mk ?loc ?attrs (Pexp_ident a)
  soit constant ?loc ?attrs a = mk ?loc ?attrs (Pexp_constant a)
  soit let_ ?loc ?attrs a b c = mk ?loc ?attrs (Pexp_let (a, b, c))
  soit fun_ ?loc ?attrs a b c d = mk ?loc ?attrs (Pexp_fun (a, b, c, d))
  soit function_ ?loc ?attrs a = mk ?loc ?attrs (Pexp_function a)
  soit apply ?loc ?attrs a b = mk ?loc ?attrs (Pexp_apply (a, b))
  soit match_ ?loc ?attrs a b = mk ?loc ?attrs (Pexp_match (a, b))
  soit try_ ?loc ?attrs a b = mk ?loc ?attrs (Pexp_try (a, b))
  soit tuple ?loc ?attrs a = mk ?loc ?attrs (Pexp_tuple a)
  soit construct ?loc ?attrs a b = mk ?loc ?attrs (Pexp_construct (a, b))
  soit variant ?loc ?attrs a b = mk ?loc ?attrs (Pexp_variant (a, b))
  soit record ?loc ?attrs a b = mk ?loc ?attrs (Pexp_record (a, b))
  soit field ?loc ?attrs a b = mk ?loc ?attrs (Pexp_field (a, b))
  soit setfield ?loc ?attrs a b c = mk ?loc ?attrs (Pexp_setfield (a, b, c))
  soit array ?loc ?attrs a = mk ?loc ?attrs (Pexp_array a)
  soit ifthenelse ?loc ?attrs a b c = mk ?loc ?attrs (Pexp_ifthenelse (a, b, c))
  soit sequence ?loc ?attrs a b = mk ?loc ?attrs (Pexp_sequence (a, b))
  soit while_ ?loc ?attrs a b = mk ?loc ?attrs (Pexp_while (a, b))
  soit for_ ?loc ?attrs a b c d e = mk ?loc ?attrs (Pexp_for (a, b, c, d, e))
  soit constraint_ ?loc ?attrs a b = mk ?loc ?attrs (Pexp_constraint (a, b))
  soit coerce ?loc ?attrs a b c = mk ?loc ?attrs (Pexp_coerce (a, b, c))
  soit send ?loc ?attrs a b = mk ?loc ?attrs (Pexp_send (a, b))
  soit new_ ?loc ?attrs a = mk ?loc ?attrs (Pexp_new a)
  soit setinstvar ?loc ?attrs a b = mk ?loc ?attrs (Pexp_setinstvar (a, b))
  soit override ?loc ?attrs a = mk ?loc ?attrs (Pexp_override a)
  soit letmodule ?loc ?attrs a b c= mk ?loc ?attrs (Pexp_letmodule (a, b, c))
  soit assert_ ?loc ?attrs a = mk ?loc ?attrs (Pexp_assert a)
  soit lazy_ ?loc ?attrs a = mk ?loc ?attrs (Pexp_lazy a)
  soit poly ?loc ?attrs a b = mk ?loc ?attrs (Pexp_poly (a, b))
  soit object_ ?loc ?attrs a = mk ?loc ?attrs (Pexp_object a)
  soit newtype ?loc ?attrs a b = mk ?loc ?attrs (Pexp_newtype (a, b))
  soit pack ?loc ?attrs a = mk ?loc ?attrs (Pexp_pack a)
  soit open_ ?loc ?attrs a b c = mk ?loc ?attrs (Pexp_open (a, b, c))
  soit extension ?loc ?attrs a = mk ?loc ?attrs (Pexp_extension a)

  soit case lhs ?guard rhs =
    {
     pc_lhs = lhs;
     pc_guard = guard;
     pc_rhs = rhs;
    }
fin

module Mty = struct
  soit mk ?(loc = !default_loc) ?(attrs = []) d = {pmty_desc = d; pmty_loc = loc; pmty_attributes = attrs}
  soit attr d a = {d avec pmty_attributes = d.pmty_attributes @ [a]}

  soit ident ?loc ?attrs a = mk ?loc ?attrs (Pmty_ident a)
  soit alias ?loc ?attrs a = mk ?loc ?attrs (Pmty_alias a)
  soit signature ?loc ?attrs a = mk ?loc ?attrs (Pmty_signature a)
  soit functor_ ?loc ?attrs a b c = mk ?loc ?attrs (Pmty_functor (a, b, c))
  soit with_ ?loc ?attrs a b = mk ?loc ?attrs (Pmty_with (a, b))
  soit typeof_ ?loc ?attrs a = mk ?loc ?attrs (Pmty_typeof a)
  soit extension ?loc ?attrs a = mk ?loc ?attrs (Pmty_extension a)
fin

module Mod = struct
soit mk ?(loc = !default_loc) ?(attrs = []) d = {pmod_desc = d; pmod_loc = loc; pmod_attributes = attrs}
  soit attr d a = {d avec pmod_attributes = d.pmod_attributes @ [a]}

  soit ident ?loc ?attrs x = mk ?loc ?attrs (Pmod_ident x)
  soit structure ?loc ?attrs x = mk ?loc ?attrs (Pmod_structure x)
  soit functor_ ?loc ?attrs arg arg_ty body = mk ?loc ?attrs (Pmod_functor (arg, arg_ty, body))
  soit apply ?loc ?attrs m1 m2 = mk ?loc ?attrs (Pmod_apply (m1, m2))
  soit constraint_ ?loc ?attrs m mty = mk ?loc ?attrs (Pmod_constraint (m, mty))
  soit unpack ?loc ?attrs e = mk ?loc ?attrs (Pmod_unpack e)
  soit extension ?loc ?attrs a = mk ?loc ?attrs (Pmod_extension a)
fin

module Sig = struct
  soit mk ?(loc = !default_loc) d = {psig_desc = d; psig_loc = loc}

  soit value ?loc a = mk ?loc (Psig_value a)
  soit type_ ?loc a = mk ?loc (Psig_type a)
  soit exception_ ?loc a = mk ?loc (Psig_exception a)
  soit module_ ?loc a = mk ?loc (Psig_module a)
  soit rec_module ?loc a = mk ?loc (Psig_recmodule a)
  soit modtype ?loc a = mk ?loc (Psig_modtype a)
  soit open_ ?loc ?(attrs = []) a b = mk ?loc (Psig_open (a, b, attrs))
  soit include_ ?loc ?(attrs = []) a = mk ?loc (Psig_include (a, attrs))
  soit class_ ?loc a = mk ?loc (Psig_class a)
  soit class_type ?loc a = mk ?loc (Psig_class_type a)
  soit extension ?loc ?(attrs = []) a = mk ?loc (Psig_extension (a, attrs))
  soit attribute ?loc a = mk ?loc (Psig_attribute a)
fin

module Str = struct
  soit mk ?(loc = !default_loc) d = {pstr_desc = d; pstr_loc = loc}

  soit eval ?loc ?(attrs = []) a = mk ?loc (Pstr_eval (a, attrs))
  soit value ?loc a b = mk ?loc (Pstr_value (a, b))
  soit primitive ?loc a = mk ?loc (Pstr_primitive a)
  soit type_ ?loc a = mk ?loc (Pstr_type a)
  soit exception_ ?loc a = mk ?loc (Pstr_exception a)
  soit exn_rebind ?loc ?(attrs = []) a b = mk ?loc (Pstr_exn_rebind (a, b, attrs))
  soit module_ ?loc a = mk ?loc (Pstr_module a)
  soit rec_module ?loc a = mk ?loc (Pstr_recmodule a)
  soit modtype ?loc a = mk ?loc (Pstr_modtype a)
  soit open_ ?loc ?(attrs = []) a b = mk ?loc (Pstr_open (a, b, attrs))
  soit class_ ?loc a = mk ?loc (Pstr_class a)
  soit class_type ?loc a = mk ?loc (Pstr_class_type a)
  soit include_ ?loc ?(attrs = []) a = mk ?loc (Pstr_include (a, attrs))
  soit extension ?loc ?(attrs = []) a = mk ?loc (Pstr_extension (a, attrs))
  soit attribute ?loc a = mk ?loc (Pstr_attribute a)
fin

module Cl = struct
  soit mk ?(loc = !default_loc) ?(attrs = []) d =
    {
     pcl_desc = d;
     pcl_loc = loc;
     pcl_attributes = attrs;
    }
  soit attr d a = {d avec pcl_attributes = d.pcl_attributes @ [a]}

  soit constr ?loc ?attrs a b = mk ?loc ?attrs (Pcl_constr (a, b))
  soit structure ?loc ?attrs a = mk ?loc ?attrs (Pcl_structure a)
  soit fun_ ?loc ?attrs a b c d = mk ?loc ?attrs (Pcl_fun (a, b, c, d))
  soit apply ?loc ?attrs a b = mk ?loc ?attrs (Pcl_apply (a, b))
  soit let_ ?loc ?attrs a b c = mk ?loc ?attrs (Pcl_let (a, b, c))
  soit constraint_ ?loc ?attrs a b = mk ?loc ?attrs (Pcl_constraint (a, b))
  soit extension ?loc ?attrs a = mk ?loc ?attrs (Pcl_extension a)
fin

module Cty = struct
  soit mk ?(loc = !default_loc) ?(attrs = []) d =
    {
     pcty_desc = d;
     pcty_loc = loc;
     pcty_attributes = attrs;
    }
  soit attr d a = {d avec pcty_attributes = d.pcty_attributes @ [a]}

  soit constr ?loc ?attrs a b = mk ?loc ?attrs (Pcty_constr (a, b))
  soit signature ?loc ?attrs a = mk ?loc ?attrs (Pcty_signature a)
  soit arrow ?loc ?attrs a b c = mk ?loc ?attrs (Pcty_arrow (a, b, c))
  soit extension ?loc ?attrs a = mk ?loc ?attrs (Pcty_extension a)
fin

module Ctf = struct
  soit mk ?(loc = !default_loc) ?(attrs = []) d =
    {
     pctf_desc = d;
     pctf_loc = loc;
     pctf_attributes = attrs;
    }
  soit attr d a = {d avec pctf_attributes = d.pctf_attributes @ [a]}

  soit inherit_ ?loc ?attrs a = mk ?loc ?attrs (Pctf_inherit a)
  soit val_ ?loc ?attrs a b c d = mk ?loc ?attrs (Pctf_val (a, b, c, d))
  soit method_ ?loc ?attrs a b c d = mk ?loc ?attrs (Pctf_method (a, b, c, d))
  soit constraint_ ?loc ?attrs a b = mk ?loc ?attrs (Pctf_constraint (a, b))
  soit extension ?loc ?attrs a = mk ?loc ?attrs (Pctf_extension a)
fin

module Cf = struct
  soit mk ?(loc = !default_loc) ?(attrs = []) d =
    {
     pcf_desc = d;
     pcf_loc = loc;
     pcf_attributes = attrs;
    }
  soit attr d a = {d avec pcf_attributes = d.pcf_attributes @ [a]}

  soit inherit_ ?loc ?attrs a b c = mk ?loc ?attrs (Pcf_inherit (a, b, c))
  soit val_ ?loc ?attrs a b c = mk ?loc ?attrs (Pcf_val (a, b, c))
  soit method_ ?loc ?attrs a b c = mk ?loc ?attrs (Pcf_method (a, b, c))
  soit constraint_ ?loc ?attrs a b = mk ?loc ?attrs (Pcf_constraint (a, b))
  soit initializer_ ?loc ?attrs a = mk ?loc ?attrs (Pcf_initializer a)
  soit extension ?loc ?attrs a = mk ?loc ?attrs (Pcf_extension a)

  soit virtual_ ct = Cfk_virtual ct
  soit concrete o e = Cfk_concrete (o, e)
fin

module Val = struct
  soit mk ?(loc = !default_loc) ?(attrs = []) ?(prim = []) name typ =
    {
     pval_name = name;
     pval_type = typ;
     pval_attributes = attrs;
     pval_loc = loc;
     pval_prim = prim;
    }
fin

module Md = struct
  soit mk ?(loc = !default_loc) ?(attrs = []) name typ =
    {
     pmd_name = name;
     pmd_type = typ;
     pmd_attributes = attrs;
     pmd_loc = loc;
    }
fin

module Mtd = struct
  soit mk ?(loc = !default_loc) ?(attrs = []) ?typ name =
    {
     pmtd_name = name;
     pmtd_type = typ;
     pmtd_attributes = attrs;
     pmtd_loc = loc;
    }
fin

module Mb = struct
  soit mk ?(loc = !default_loc) ?(attrs = []) name expr =
    {
     pmb_name = name;
     pmb_expr = expr;
     pmb_attributes = attrs;
     pmb_loc = loc;
    }
fin

module Vb = struct
  soit mk ?(attrs = []) pat expr =
    {
     pvb_pat = pat;
     pvb_expr = expr;
     pvb_attributes = attrs;
    }
fin

module Ci = struct
  soit mk ?(loc = !default_loc) ?(attrs = []) ?(virt = Concrete) ?(params = []) name expr =
    {
     pci_virt = virt;
     pci_params = params;
     pci_name = name;
     pci_expr = expr;
     pci_attributes = attrs;
     pci_loc = loc;
    }
fin

module Type = struct
  soit mk ?(loc = !default_loc) ?(attrs = [])
      ?(params = [])
      ?(cstrs = [])
      ?(kind = Ptype_abstract)
      ?(priv = Public)
      ?manifest
      name =
    {
     ptype_name = name;
     ptype_params = params;
     ptype_cstrs = cstrs;
     ptype_kind = kind;
     ptype_private = priv;
     ptype_manifest = manifest;
     ptype_attributes = attrs;
     ptype_loc = loc;
    }

  soit constructor ?(loc = !default_loc) ?(attrs = []) ?(args = []) ?res name =
    {
     pcd_name = name;
     pcd_args = args;
     pcd_res = res;
     pcd_loc = loc;
     pcd_attributes = attrs;
    }

  soit field ?(loc = !default_loc) ?(attrs = []) ?(mut = Immutable) name typ =
    {
     pld_name = name;
     pld_mutable = mut;
     pld_type = typ;
     pld_loc = loc;
     pld_attributes = attrs;
    }
fin

module Csig = struct
  soit mk self fields =
    {
     pcsig_self = self;
     pcsig_fields = fields;
    }
fin

module Cstr = struct
  soit mk self fields =
    {
     pcstr_self = self;
     pcstr_fields = fields;
    }
fin

module Convenience = struct
  ouvre Location

  soit may_tuple tup = fonction
    | [] -> None
    | [x] -> Some x
    | l -> Some (tup ?loc:None ?attrs:None l)

  soit lid s = mkloc (Longident.parse s) !default_loc
  soit tuple l = Exp.tuple l
  soit constr s args = Exp.construct (lid s) (may_tuple Exp.tuple args)
  soit nil () = constr "[]" []
  soit unit () = constr "()" []
  soit cons hd tl = constr "::" [hd; tl]
  soit list l = List.fold_right cons l (nil ())
  soit str s = Exp.constant (Const_string (s, None))
  soit int x = Exp.constant (Const_int x)
  soit char x = Exp.constant (Const_char x)
  soit float x = Exp.constant (Const_float (string_of_float x))
  soit record ?over l =
    Exp.record (List.map (fonc (s, e) -> (lid s, e)) l) over
  soit func l = Exp.function_ (List.map (fonc (p, e) -> Exp.case p e) l)
  soit lam ?(label = "") ?default pat exp = Exp.fun_ label default pat exp
  soit app f l = Exp.apply f (List.map (fonc a -> "", a) l)
  soit evar s = Exp.ident (lid s)
  soit let_in ?(recursive = faux) b body =
    Exp.let_ (si recursive alors Recursive sinon Nonrecursive) b body

  soit pvar s = Pat.var (mkloc s !default_loc)
  soit pconstr s args = Pat.construct (lid s) (may_tuple Pat.tuple args)
  soit precord ?(closed = Open) l = Pat.record (List.map (fonc (s, e) -> (lid s, e)) l) closed
  soit pnil () = pconstr "[]" []
  soit pcons hd tl = pconstr "::" [hd; tl]
  soit punit () = pconstr "()" []
  soit plist l = List.fold_right pcons l (pnil ())
  soit ptuple l = Pat.tuple l

  soit pstr s = Pat.constant (Const_string (s, None))
  soit pint x = Pat.constant (Const_int x)
  soit pchar x = Pat.constant (Const_char x)
  soit pfloat x = Pat.constant (Const_float (string_of_float x))

  soit tconstr c l = Typ.constr (lid c) l

  soit get_str = fonction
    | {pexp_desc=Pexp_constant (Const_string (s, _)); _} -> Some s
    | e -> None

  soit get_lid = fonction
    | {pexp_desc=Pexp_ident{txt=id;_};_} ->
        Some (String.concat "." (Longident.flatten id))
    | _ -> None

  soit find_attr s attrs =
    essaie Some (snd (List.find (fonc (x, _) -> x.txt = s) attrs))
    avec Not_found -> None

  soit expr_of_payload = fonction
    | PStr [{pstr_desc=Pstr_eval(e, _)}] -> Some e
    | _ -> None

  soit find_attr_expr s attrs =
    filtre find_attr s attrs avec
    | Some e -> expr_of_payload e
    | None -> None

  soit has_attr s attrs =
    find_attr s attrs <> None
fin
