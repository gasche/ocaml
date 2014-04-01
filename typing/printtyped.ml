2(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*                  Fabrice Le Fessant, INRIA Saclay                   *)
(*                                                                     *)
(*  Copyright 1999 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Tublic License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

ouvre Asttypes;;
ouvre Format;;
ouvre Lexing;;
ouvre Location;;
ouvre Typedtree;;

soit fmt_position f l =
  si l.pos_lnum = -1
  alors fprintf f "%s[%d]" l.pos_fname l.pos_cnum
  sinon fprintf f "%s[%d,%d+%d]" l.pos_fname l.pos_lnum l.pos_bol
               (l.pos_cnum - l.pos_bol)
;;

soit fmt_location f loc =
  fprintf f "(%a..%a)" fmt_position loc.loc_start fmt_position loc.loc_end;
  si loc.loc_ghost alors fprintf f " ghost";
;;

soit rec fmt_longident_aux f x =
  filtre x avec
  | Longident.Lident (s) -> fprintf f "%s" s;
  | Longident.Ldot (y, s) -> fprintf f "%a.%s" fmt_longident_aux y s;
  | Longident.Lapply (y, z) ->
      fprintf f "%a(%a)" fmt_longident_aux y fmt_longident_aux z;
;;

soit fmt_longident_noloc f x = fprintf f "\"%a\"" fmt_longident_aux x;;
soit fmt_longident f x = fprintf f "\"%a\"" fmt_longident_aux x.txt;;

soit fmt_ident = Ident.print

soit rec fmt_path_aux f x =
  filtre x avec
  | Path.Pident (s) -> fprintf f "%a" fmt_ident s;
  | Path.Pdot (y, s, _pos) -> fprintf f "%a.%s" fmt_path_aux y s;
  | Path.Papply (y, z) ->
      fprintf f "%a(%a)" fmt_path_aux y fmt_path_aux z;
;;

soit fmt_path f x = fprintf f "\"%a\"" fmt_path_aux x;;
soit fmt_path_loc f x = fprintf f "\"%a\"" fmt_path_aux x.txt;;

soit fmt_constant f x =
  filtre x avec
  | Const_int (i) -> fprintf f "Const_int %d" i;
  | Const_char (c) -> fprintf f "Const_char %02x" (Char.code c);
  | Const_string (s, None) -> fprintf f "Const_string(%S,None)" s;
  | Const_string (s, Some delim) ->
      fprintf f "Const_string (%S,Some %S)" s delim;
  | Const_float (s) -> fprintf f "Const_float %s" s;
  | Const_int32 (i) -> fprintf f "Const_int32 %ld" i;
  | Const_int64 (i) -> fprintf f "Const_int64 %Ld" i;
  | Const_nativeint (i) -> fprintf f "Const_nativeint %nd" i;
;;

soit fmt_mutable_flag f x =
  filtre x avec
  | Immutable -> fprintf f "Immutable";
  | Mutable -> fprintf f "Mutable";
;;

soit fmt_virtual_flag f x =
  filtre x avec
  | Virtual -> fprintf f "Virtual";
  | Concrete -> fprintf f "Concrete";
;;

soit fmt_override_flag f x =
  filtre x avec
  | Override -> fprintf f "Override";
  | Fresh -> fprintf f "Fresh";
;;

soit fmt_closed_flag f x =
  filtre x avec
  | Closed -> fprintf f "Closed"
  | Open -> fprintf f "Open"

soit fmt_rec_flag f x =
  filtre x avec
  | Nonrecursive -> fprintf f "Nonrec";
  | Recursive -> fprintf f "Rec";
;;

soit fmt_direction_flag f x =
  filtre x avec
  | Upto -> fprintf f "Up";
  | Downto -> fprintf f "Down";
;;

soit fmt_private_flag f x =
  filtre x avec
  | Public -> fprintf f "Public";
  | Private -> fprintf f "Private";
;;

soit line i f s (*...*) =
  fprintf f "%s" (String.make (2*i) ' ');
  fprintf f s (*...*)
;;

soit list i f ppf l =
  filtre l avec
  | [] -> line i ppf "[]\n";
  | _ :: _ ->
     line i ppf "[\n";
     List.iter (f (i+1) ppf) l;
     line i ppf "]\n";
;;

soit option i f ppf x =
  filtre x avec
  | None -> line i ppf "None\n";
  | Some x ->
      line i ppf "Some\n";
      f (i+1) ppf x;
;;

soit longident i ppf li = line i ppf "%a\n" fmt_longident li;;
soit path i ppf li = line i ppf "%a\n" fmt_path li;;
soit ident i ppf li = line i ppf "%a\n" fmt_ident li;;
soit string i ppf s = line i ppf "\"%s\"\n" s;;
soit string_loc i ppf s = line i ppf "\"%s\"\n" s.txt;;
soit bool i ppf x = line i ppf "%s\n" (string_of_bool x);;
soit label i ppf x = line i ppf "label=\"%s\"\n" x;;

soit attributes i ppf l =
  soit i = i + 1 dans
  List.iter
    (fonc (s, arg) ->
      line i ppf "attribute \"%s\"\n" s.txt;
      Printast.payload (i + 1) ppf arg;
    )
    l

soit rec core_type i ppf x =
  line i ppf "core_type %a\n" fmt_location x.ctyp_loc;
  attributes i ppf x.ctyp_attributes;
  soit i = i+1 dans
  filtre x.ctyp_desc avec
  | Ttyp_any -> line i ppf "Ptyp_any\n";
  | Ttyp_var (s) -> line i ppf "Ptyp_var %s\n" s;
  | Ttyp_arrow (l, ct1, ct2) ->
      line i ppf "Ptyp_arrow\n";
      string i ppf l;
      core_type i ppf ct1;
      core_type i ppf ct2;
  | Ttyp_tuple l ->
      line i ppf "Ptyp_tuple\n";
      list i core_type ppf l;
  | Ttyp_constr (li, _, l) ->
      line i ppf "Ptyp_constr %a\n" fmt_path li;
      list i core_type ppf l;
  | Ttyp_variant (l, closed, low) ->
      line i ppf "Ptyp_variant closed=%a\n" fmt_closed_flag closed;
      list i label_x_bool_x_core_type_list ppf l;
      option i (fonc i -> list i string) ppf low
  | Ttyp_object (l, c) ->
      line i ppf "Ptyp_object %a\n" fmt_closed_flag c;
      soit i = i + 1 dans
      List.iter
        (fonc (s, t) ->
          line i ppf "method %s" s;
          core_type (i + 1) ppf t
        )
        l
  | Ttyp_class (li, _, l) ->
      line i ppf "Ptyp_class %a\n" fmt_path li;
      list i core_type ppf l;
  | Ttyp_alias (ct, s) ->
      line i ppf "Ptyp_alias \"%s\"\n" s;
      core_type i ppf ct;
  | Ttyp_poly (sl, ct) ->
      line i ppf "Ptyp_poly%a\n"
        (fonc ppf -> List.iter (fonc x -> fprintf ppf " '%s" x)) sl;
      core_type i ppf ct;
  | Ttyp_package { pack_name = s; pack_fields = l } ->
      line i ppf "Ptyp_package %a\n" fmt_path s;
      list i package_with ppf l;

et package_with i ppf (s, t) =
  line i ppf "with type %a\n" fmt_longident s;
  core_type i ppf t

et pattern i ppf x =
  line i ppf "pattern %a\n" fmt_location x.pat_loc;
  attributes i ppf x.pat_attributes;
  soit i = i+1 dans
  filtre x.pat_extra avec
    | (Tpat_unpack, _, attrs) :: rem ->
        line i ppf "Tpat_unpack\n";
        attributes i ppf attrs;
        pattern i ppf { x avec pat_extra = rem }
    | (Tpat_constraint cty, _, attrs) :: rem ->
        line i ppf "Tpat_constraint\n";
        attributes i ppf attrs;
        core_type i ppf cty;
        pattern i ppf { x avec pat_extra = rem }
    | (Tpat_type (id, _), _, attrs) :: rem ->
        line i ppf "Tpat_type %a\n" fmt_path id;
        attributes i ppf attrs;
        pattern i ppf { x avec pat_extra = rem }
    | [] ->
  filtre x.pat_desc avec
  | Tpat_any -> line i ppf "Ppat_any\n";
  | Tpat_var (s,_) -> line i ppf "Ppat_var \"%a\"\n" fmt_ident s;
  | Tpat_alias (p, s,_) ->
      line i ppf "Ppat_alias \"%a\"\n" fmt_ident s;
      pattern i ppf p;
  | Tpat_constant (c) -> line i ppf "Ppat_constant %a\n" fmt_constant c;
  | Tpat_tuple (l) ->
      line i ppf "Ppat_tuple\n";
      list i pattern ppf l;
  | Tpat_construct (li, _, po) ->
      line i ppf "Ppat_construct %a\n" fmt_longident li;
      list i pattern ppf po;
  | Tpat_variant (l, po, _) ->
      line i ppf "Ppat_variant \"%s\"\n" l;
      option i pattern ppf po;
  | Tpat_record (l, c) ->
      line i ppf "Ppat_record\n";
      list i longident_x_pattern ppf l;
  | Tpat_array (l) ->
      line i ppf "Ppat_array\n";
      list i pattern ppf l;
  | Tpat_or (p1, p2, _) ->
      line i ppf "Ppat_or\n";
      pattern i ppf p1;
      pattern i ppf p2;
  | Tpat_lazy p ->
      line i ppf "Ppat_lazy\n";
      pattern i ppf p;

et expression_extra i ppf x attrs =
  filtre x avec
  | Texp_constraint ct ->
      line i ppf "Pexp_constraint\n";
      attributes i ppf attrs;
      core_type i ppf ct;
  | Texp_coerce (cto1, cto2) ->
      line i ppf "Pexp_constraint\n";
      attributes i ppf attrs;
      option i core_type ppf cto1;
      core_type i ppf cto2;
  | Texp_open (ovf, m, _, _) ->
      line i ppf "Pexp_open %a \"%a\"\n" fmt_override_flag ovf fmt_path m;
      attributes i ppf attrs;
  | Texp_poly cto ->
      line i ppf "Pexp_poly\n";
      attributes i ppf attrs;
      option i core_type ppf cto;
  | Texp_newtype s ->
      line i ppf "Pexp_newtype \"%s\"\n" s;
      attributes i ppf attrs;

et expression i ppf x =
  line i ppf "expression %a\n" fmt_location x.exp_loc;
  attributes i ppf x.exp_attributes;
  soit i =
    List.fold_left (fonc i (extra,_,attrs) -> expression_extra i ppf extra attrs; i+1)
      (i+1) x.exp_extra
  dans
  filtre x.exp_desc avec
  | Texp_ident (li,_,_) -> line i ppf "Pexp_ident %a\n" fmt_path li;
  | Texp_instvar (_, li,_) -> line i ppf "Pexp_instvar %a\n" fmt_path li;
  | Texp_constant (c) -> line i ppf "Pexp_constant %a\n" fmt_constant c;
  | Texp_let (rf, l, e) ->
      line i ppf "Pexp_let %a\n" fmt_rec_flag rf;
      list i value_binding ppf l;
      expression i ppf e;
  | Texp_function (p, l, _partial) ->
      line i ppf "Pexp_function \"%s\"\n" p;
(*      option i expression ppf eo; *)
      list i case ppf l;
  | Texp_apply (e, l) ->
      line i ppf "Pexp_apply\n";
      expression i ppf e;
      list i label_x_expression ppf l;
  | Texp_match (e, l, partial) ->
      line i ppf "Pexp_match\n";
      expression i ppf e;
      list i case ppf l;
  | Texp_try (e, l) ->
      line i ppf "Pexp_try\n";
      expression i ppf e;
      list i case ppf l;
  | Texp_tuple (l) ->
      line i ppf "Pexp_tuple\n";
      list i expression ppf l;
  | Texp_construct (li, _, eo) ->
      line i ppf "Pexp_construct %a\n" fmt_longident li;
      list i expression ppf eo;
  | Texp_variant (l, eo) ->
      line i ppf "Pexp_variant \"%s\"\n" l;
      option i expression ppf eo;
  | Texp_record (l, eo) ->
      line i ppf "Pexp_record\n";
      list i longident_x_expression ppf l;
      option i expression ppf eo;
  | Texp_field (e, li, _) ->
      line i ppf "Pexp_field\n";
      expression i ppf e;
      longident i ppf li;
  | Texp_setfield (e1, li, _, e2) ->
      line i ppf "Pexp_setfield\n";
      expression i ppf e1;
      longident i ppf li;
      expression i ppf e2;
  | Texp_array (l) ->
      line i ppf "Pexp_array\n";
      list i expression ppf l;
  | Texp_ifthenelse (e1, e2, eo) ->
      line i ppf "Pexp_ifthenelse\n";
      expression i ppf e1;
      expression i ppf e2;
      option i expression ppf eo;
  | Texp_sequence (e1, e2) ->
      line i ppf "Pexp_sequence\n";
      expression i ppf e1;
      expression i ppf e2;
  | Texp_while (e1, e2) ->
      line i ppf "Pexp_while\n";
      expression i ppf e1;
      expression i ppf e2;
  | Texp_for (s, _, e1, e2, df, e3) ->
      line i ppf "Pexp_for \"%a\" %a\n" fmt_ident s fmt_direction_flag df;
      expression i ppf e1;
      expression i ppf e2;
      expression i ppf e3;
  | Texp_send (e, Tmeth_name s, eo) ->
      line i ppf "Pexp_send \"%s\"\n" s;
      expression i ppf e;
      option i expression ppf eo
  | Texp_send (e, Tmeth_val s, eo) ->
      line i ppf "Pexp_send \"%a\"\n" fmt_ident s;
      expression i ppf e;
      option i expression ppf eo
  | Texp_new (li, _, _) -> line i ppf "Pexp_new %a\n" fmt_path li;
  | Texp_setinstvar (_, s, _, e) ->
      line i ppf "Pexp_setinstvar \"%a\"\n" fmt_path s;
      expression i ppf e;
  | Texp_override (_, l) ->
      line i ppf "Pexp_override\n";
      list i string_x_expression ppf l;
  | Texp_letmodule (s, _, me, e) ->
      line i ppf "Pexp_letmodule \"%a\"\n" fmt_ident s;
      module_expr i ppf me;
      expression i ppf e;
  | Texp_assert (e) ->
      line i ppf "Pexp_assert";
      expression i ppf e;
  | Texp_lazy (e) ->
      line i ppf "Pexp_lazy";
      expression i ppf e;
  | Texp_object (s, _) ->
      line i ppf "Pexp_object";
      class_structure i ppf s
  | Texp_pack me ->
      line i ppf "Pexp_pack";
      module_expr i ppf me

et value_description i ppf x =
  line i ppf "value_description %a %a\n" fmt_ident x.val_id fmt_location x.val_loc;
  attributes i ppf x.val_attributes;
  core_type (i+1) ppf x.val_desc;
  list (i+1) string ppf x.val_prim;

et type_parameter i ppf (x, _variance) =
  filtre x avec
  | Some x ->
      string i ppf x.txt
  | None ->
      string i ppf "_"

et type_declaration i ppf x =
  line i ppf "type_declaration %a %a\n" fmt_ident x.typ_id fmt_location x.typ_loc;
  attributes i ppf x.typ_attributes;
  soit i = i+1 dans
  line i ppf "ptype_params =\n";
  list (i+1) type_parameter ppf x.typ_params;
  line i ppf "ptype_cstrs =\n";
  list (i+1) core_type_x_core_type_x_location ppf x.typ_cstrs;
  line i ppf "ptype_kind =\n";
  type_kind (i+1) ppf x.typ_kind;
  line i ppf "ptype_private = %a\n" fmt_private_flag x.typ_private;
  line i ppf "ptype_manifest =\n";
  option (i+1) core_type ppf x.typ_manifest;

et type_kind i ppf x =
  filtre x avec
  | Ttype_abstract ->
      line i ppf "Ptype_abstract\n"
  | Ttype_variant l ->
      line i ppf "Ptype_variant\n";
      list (i+1) constructor_decl ppf l;
  | Ttype_record l ->
      line i ppf "Ptype_record\n";
      list (i+1) label_decl ppf l;

et class_type i ppf x =
  line i ppf "class_type %a\n" fmt_location x.cltyp_loc;
  attributes i ppf x.cltyp_attributes;
  soit i = i+1 dans
  filtre x.cltyp_desc avec
  | Tcty_constr (li, _, l) ->
      line i ppf "Pcty_constr %a\n" fmt_path li;
      list i core_type ppf l;
  | Tcty_signature (cs) ->
      line i ppf "Pcty_signature\n";
      class_signature i ppf cs;
  | Tcty_arrow (l, co, cl) ->
      line i ppf "Pcty_arrow \"%s\"\n" l;
      core_type i ppf co;
      class_type i ppf cl;

et class_signature i ppf { csig_self = ct; csig_fields = l } =
  line i ppf "class_signature\n";
  core_type (i+1) ppf ct;
  list (i+1) class_type_field ppf l;

et class_type_field i ppf x =
  line i ppf "class_type_field %a\n" fmt_location x.ctf_loc;
  soit i = i+1 dans
  attributes i ppf x.ctf_attributes;
  filtre x.ctf_desc avec
  | Tctf_inherit (ct) ->
      line i ppf "Pctf_inherit\n";
      class_type i ppf ct;
  | Tctf_val (s, mf, vf, ct) ->
      line i ppf "Pctf_val \"%s\" %a %a\n" s fmt_mutable_flag mf
           fmt_virtual_flag vf;
      core_type (i+1) ppf ct;
  | Tctf_method (s, pf, vf, ct) ->
      line i ppf "Pctf_method \"%s\" %a %a\n" s fmt_private_flag pf fmt_virtual_flag vf;
      core_type (i+1) ppf ct;
  | Tctf_constraint (ct1, ct2) ->
      line i ppf "Pctf_constraint\n";
      core_type (i+1) ppf ct1;
      core_type (i+1) ppf ct2;

et class_description i ppf x =
  line i ppf "class_description %a\n" fmt_location x.ci_loc;
  attributes i ppf x.ci_attributes;
  soit i = i+1 dans
  line i ppf "pci_virt = %a\n" fmt_virtual_flag x.ci_virt;
  line i ppf "pci_params =\n";
  cl_type_parameters (i+1) ppf x.ci_params;
  line i ppf "pci_name = \"%s\"\n" x.ci_id_name.txt;
  line i ppf "pci_expr =\n";
  class_type (i+1) ppf x.ci_expr;

et class_type_declaration i ppf x =
  line i ppf "class_type_declaration %a\n" fmt_location x.ci_loc;
  soit i = i+1 dans
  line i ppf "pci_virt = %a\n" fmt_virtual_flag x.ci_virt;
  line i ppf "pci_params =\n";
  cl_type_parameters (i+1) ppf x.ci_params;
  line i ppf "pci_name = \"%s\"\n" x.ci_id_name.txt;
  line i ppf "pci_expr =\n";
  class_type (i+1) ppf x.ci_expr;

et class_expr i ppf x =
  line i ppf "class_expr %a\n" fmt_location x.cl_loc;
  attributes i ppf x.cl_attributes;
  soit i = i+1 dans
  filtre x.cl_desc avec
  | Tcl_ident (li, _, l) ->
      line i ppf "Pcl_constr %a\n" fmt_path li;
      list i core_type ppf l;
  | Tcl_structure (cs) ->
      line i ppf "Pcl_structure\n";
      class_structure i ppf cs;
  | Tcl_fun (l, eo, p, e, _) -> affirme faux (* TODO *)
(*      line i ppf "Pcl_fun\n";
      label i ppf l;
      option i expression ppf eo;
      pattern i ppf p;
      class_expr i ppf e; *)
  | Tcl_apply (ce, l) ->
      line i ppf "Pcl_apply\n";
      class_expr i ppf ce;
      list i label_x_expression ppf l;
  | Tcl_let (rf, l1, l2, ce) ->
      line i ppf "Pcl_let %a\n" fmt_rec_flag rf;
      list i value_binding ppf l1;
      list i ident_x_loc_x_expression_def ppf l2;
      class_expr i ppf ce;
  | Tcl_constraint (ce, Some ct, _, _, _) ->
      line i ppf "Pcl_constraint\n";
      class_expr i ppf ce;
      class_type i ppf ct;
  | Tcl_constraint (_, None, _, _, _) -> affirme faux
        (* TODO : is it possible ? see parsetree *)

et class_structure i ppf { cstr_self = p; cstr_fields = l } =
  line i ppf "class_structure\n";
  pattern (i+1) ppf p;
  list (i+1) class_field ppf l;

et class_field i ppf x = affirme faux (* TODO *)
(*  let loc = x.cf_loc in
  match x.cf_desc with
  | Tcf_inher (ovf, ce, so) ->
      line i ppf "Pcf_inher %a\n" fmt_override_flag ovf;
      class_expr (i+1) ppf ce;
      option (i+1) string ppf so;
  | Tcf_valvirt (s, mf, ct) ->
      line i ppf "Pcf_valvirt \"%s\" %a %a\n"
        s.txt fmt_mutable_flag mf fmt_location loc;
      core_type (i+1) ppf ct;
  | Tcf_val (s, mf, ovf, e) ->
      line i ppf "Pcf_val \"%s\" %a %a %a\n"
        s.txt fmt_mutable_flag mf fmt_override_flag ovf fmt_location loc;
      expression (i+1) ppf e;
  | Tcf_virt (s, pf, ct) ->
      line i ppf "Pcf_virt \"%s\" %a %a\n"
        s.txt fmt_private_flag pf fmt_location loc;
      core_type (i+1) ppf ct;
  | Tcf_meth (s, pf, ovf, e) ->
      line i ppf "Pcf_meth \"%s\" %a %a %a\n"
        s.txt fmt_private_flag pf fmt_override_flag ovf fmt_location loc;
      expression (i+1) ppf e;
  | Tcf_constr (ct1, ct2) ->
      line i ppf "Pcf_constr %a\n" fmt_location loc;
      core_type (i+1) ppf ct1;
      core_type (i+1) ppf ct2;
  | Tcf_init (e) ->
      line i ppf "Pcf_init\n";
      expression (i+1) ppf e;
*)

et class_declaration i ppf x =
  line i ppf "class_declaration %a\n" fmt_location x.ci_loc;
  soit i = i+1 dans
  line i ppf "pci_virt = %a\n" fmt_virtual_flag x.ci_virt;
  line i ppf "pci_params =\n";
  cl_type_parameters (i+1) ppf x.ci_params;
  line i ppf "pci_name = \"%s\"\n" x.ci_id_name.txt;
  line i ppf "pci_expr =\n";
  class_expr (i+1) ppf x.ci_expr;

et module_type i ppf x =
  line i ppf "module_type %a\n" fmt_location x.mty_loc;
  attributes i ppf x.mty_attributes;
  soit i = i+1 dans
  filtre x.mty_desc avec
  | Tmty_ident (li,_) -> line i ppf "Pmty_ident %a\n" fmt_path li;
  | Tmty_alias (li,_) -> line i ppf "Pmty_alias %a\n" fmt_path li;
  | Tmty_signature (s) ->
      line i ppf "Pmty_signature\n";
      signature i ppf s;
  | Tmty_functor (s, _, mt1, mt2) ->
      line i ppf "Pmty_functor \"%a\"\n" fmt_ident s;
      Misc.may (module_type i ppf) mt1;
      module_type i ppf mt2;
  | Tmty_with (mt, l) ->
      line i ppf "Pmty_with\n";
      module_type i ppf mt;
      list i longident_x_with_constraint ppf l;
  | Tmty_typeof m ->
      line i ppf "Pmty_typeof\n";
      module_expr i ppf m;

et signature i ppf x = list i signature_item ppf x.sig_items

et signature_item i ppf x =
  line i ppf "signature_item %a\n" fmt_location x.sig_loc;
  soit i = i+1 dans
  filtre x.sig_desc avec
  | Tsig_value vd ->
      line i ppf "Psig_value\n";
      value_description i ppf vd;
  | Tsig_type l ->
      line i ppf "Psig_type\n";
      list i type_declaration ppf l;
  | Tsig_exception cd ->
      line i ppf "Psig_exception\n";
      constructor_decl i ppf cd
  | Tsig_module md ->
      line i ppf "Psig_module \"%a\"\n" fmt_ident md.md_id;
      attributes i ppf md.md_attributes;
      module_type i ppf md.md_type
  | Tsig_recmodule decls ->
      line i ppf "Psig_recmodule\n";
      list i module_declaration ppf decls;
  | Tsig_modtype x ->
      line i ppf "Psig_modtype \"%a\"\n" fmt_ident x.mtd_id;
      attributes i ppf x.mtd_attributes;
      modtype_declaration i ppf x.mtd_type
  | Tsig_open (ovf, li,_,attrs) ->
      line i ppf "Psig_open %a %a\n" fmt_override_flag ovf  fmt_path li;
      attributes i ppf attrs
  | Tsig_include (mt, _, attrs) ->
      line i ppf "Psig_include\n";
      attributes i ppf attrs;
      module_type i ppf mt
  | Tsig_class (l) ->
      line i ppf "Psig_class\n";
      list i class_description ppf l;
  | Tsig_class_type (l) ->
      line i ppf "Psig_class_type\n";
      list i class_type_declaration ppf l;
  | Tsig_attribute (s, arg) ->
      line i ppf "Psig_attribute \"%s\"\n" s.txt;
      Printast.payload i ppf arg

et module_declaration i ppf md =
  line i ppf "%a" fmt_ident md.md_id;
  attributes i ppf md.md_attributes;
  module_type (i+1) ppf md.md_type;

et module_binding i ppf x =
  line i ppf "%a\n" fmt_ident x.mb_id;
  attributes i ppf x.mb_attributes;
  module_expr (i+1) ppf x.mb_expr

et modtype_declaration i ppf = fonction
  | None -> line i ppf "#abstract"
  | Some mt -> module_type (i + 1) ppf mt

et with_constraint i ppf x =
  filtre x avec
  | Twith_type (td) ->
      line i ppf "Pwith_type\n";
      type_declaration (i+1) ppf td;
  | Twith_typesubst (td) ->
      line i ppf "Pwith_typesubst\n";
      type_declaration (i+1) ppf td;
  | Twith_module (li,_) -> line i ppf "Pwith_module %a\n" fmt_path li;
  | Twith_modsubst (li,_) -> line i ppf "Pwith_modsubst %a\n" fmt_path li;

et module_expr i ppf x =
  line i ppf "module_expr %a\n" fmt_location x.mod_loc;
  attributes i ppf x.mod_attributes;
  soit i = i+1 dans
  filtre x.mod_desc avec
  | Tmod_ident (li,_) -> line i ppf "Pmod_ident %a\n" fmt_path li;
  | Tmod_structure (s) ->
      line i ppf "Pmod_structure\n";
      structure i ppf s;
  | Tmod_functor (s, _, mt, me) ->
      line i ppf "Pmod_functor \"%a\"\n" fmt_ident s;
      Misc.may (module_type i ppf) mt;
      module_expr i ppf me;
  | Tmod_apply (me1, me2, _) ->
      line i ppf "Pmod_apply\n";
      module_expr i ppf me1;
      module_expr i ppf me2;
  | Tmod_constraint (me, _, Tmodtype_explicit mt, _) ->
      line i ppf "Pmod_constraint\n";
      module_expr i ppf me;
      module_type i ppf mt;
  | Tmod_constraint (me, _, Tmodtype_implicit, _) -> affirme faux (* TODO *)
(*      line i ppf "Pmod_constraint\n";
      module_expr i ppf me;
      module_type i ppf mt; *)
  | Tmod_unpack (e, _) ->
      line i ppf "Pmod_unpack\n";
      expression i ppf e;

et structure i ppf x = list i structure_item ppf x.str_items

et structure_item i ppf x =
  line i ppf "structure_item %a\n" fmt_location x.str_loc;
  soit i = i+1 dans
  filtre x.str_desc avec
  | Tstr_eval (e, attrs) ->
      line i ppf "Pstr_eval\n";
      attributes i ppf attrs;
      expression i ppf e;
  | Tstr_value (rf, l) ->
      line i ppf "Pstr_value %a\n" fmt_rec_flag rf;
      list i value_binding ppf l;
  | Tstr_primitive vd ->
      line i ppf "Pstr_primitive\n";
      value_description i ppf vd;
  | Tstr_type l ->
      line i ppf "Pstr_type\n";
      list i type_declaration ppf l;
  | Tstr_exception cd ->
      line i ppf "Pstr_exception\n";
      constructor_decl i ppf cd;
  | Tstr_exn_rebind (s, _, li, _, attrs) ->
      line i ppf "Pstr_exn_rebind \"%a\" %a\n" fmt_ident s fmt_path li;
      attributes i ppf attrs
  | Tstr_module x ->
      line i ppf "Pstr_module\n";
      module_binding i ppf x
  | Tstr_recmodule bindings ->
      line i ppf "Pstr_recmodule\n";
      list i module_binding ppf bindings
  | Tstr_modtype x ->
      line i ppf "Pstr_modtype \"%a\"\n" fmt_ident x.mtd_id;
      attributes i ppf x.mtd_attributes;
      modtype_declaration i ppf x.mtd_type
  | Tstr_open (ovf, li, _, attrs) ->
      line i ppf "Pstr_open %a %a\n" fmt_override_flag ovf fmt_path li;
      attributes i ppf attrs
  | Tstr_class (l) ->
      line i ppf "Pstr_class\n";
      list i class_declaration ppf (List.map (fonc (cl, _,_) -> cl) l);
  | Tstr_class_type (l) ->
      line i ppf "Pstr_class_type\n";
      list i class_type_declaration ppf (List.map (fonc (_, _, cl) -> cl) l);
  | Tstr_include (me, _, attrs) ->
      line i ppf "Pstr_include";
      attributes i ppf attrs;
      module_expr i ppf me;
  | Tstr_attribute (s, arg) ->
      line i ppf "Pstr_attribute \"%s\"\n" s.txt;
      Printast.payload i ppf arg

et string_x_module_type i ppf (s, _, mty) =
  ident i ppf s;
  module_type (i+1) ppf mty;

et string_x_modtype_x_module i ppf (s, _, mty, modl) =
  ident i ppf s;
  module_type (i+1) ppf mty;
  module_expr (i+1) ppf modl;

et longident_x_with_constraint i ppf (li, _, wc) =
  line i ppf "%a\n" fmt_path li;
  with_constraint (i+1) ppf wc;

et core_type_x_core_type_x_location i ppf (ct1, ct2, l) =
  line i ppf "<constraint> %a\n" fmt_location l;
  core_type (i+1) ppf ct1;
  core_type (i+1) ppf ct2;

et constructor_decl i ppf {cd_id; cd_name = _; cd_args; cd_res; cd_loc; cd_attributes} =
  line i ppf "%a\n" fmt_location cd_loc;
  attributes i ppf cd_attributes;
  line (i+1) ppf "%a\n" fmt_ident cd_id;
  list (i+1) core_type ppf cd_args;
  option (i+1) core_type ppf cd_res

et label_decl i ppf {ld_id; ld_name = _; ld_mutable; ld_type; ld_loc; ld_attributes} =
  line i ppf "%a\n" fmt_location ld_loc;
  attributes i ppf ld_attributes;
  line (i+1) ppf "%a\n" fmt_mutable_flag ld_mutable;
  line (i+1) ppf "%a" fmt_ident ld_id;
  core_type (i+1) ppf ld_type

et cl_type_parameters i ppf l =
  line i ppf "<params>\n";
  list (i+1) cl_type_parameter ppf l;

et cl_type_parameter i ppf (x, _variance) =
  string_loc i ppf x

et longident_x_pattern i ppf (li, _, p) =
  line i ppf "%a\n" fmt_longident li;
  pattern (i+1) ppf p;

et case i ppf {c_lhs; c_guard; c_rhs} =
  line i ppf "<case>\n";
  pattern (i+1) ppf c_lhs;
  début filtre c_guard avec
  | None -> ()
  | Some g -> line (i+1) ppf "<when>\n"; expression (i + 2) ppf g
  fin;
  expression (i+1) ppf c_rhs;

et value_binding i ppf x =
  line i ppf "<def>\n";
  attributes (i+1) ppf x.vb_attributes;
  pattern (i+1) ppf x.vb_pat;
  expression (i+1) ppf x.vb_expr

et string_x_expression i ppf (s, _, e) =
  line i ppf "<override> \"%a\"\n" fmt_path s;
  expression (i+1) ppf e;

et longident_x_expression i ppf (li, _, e) =
  line i ppf "%a\n" fmt_longident li;
  expression (i+1) ppf e;

et label_x_expression i ppf (l, e, _) =
  line i ppf "<label> \"%s\"\n" l;
  (filtre e avec None -> () | Some e -> expression (i+1) ppf e)

et ident_x_loc_x_expression_def i ppf (l,_, e) =
  line i ppf "<def> \"%a\"\n" fmt_ident l;
  expression (i+1) ppf e;

et label_x_bool_x_core_type_list i ppf x =
  filtre x avec
    Ttag (l, b, ctl) ->
      line i ppf "Rtag \"%s\" %s\n" l (string_of_bool b);
      list (i+1) core_type ppf ctl
  | Tinherit (ct) ->
      line i ppf "Rinherit\n";
      core_type (i+1) ppf ct
;;

soit interface ppf x = list 0 signature_item ppf x.sig_items;;

soit implementation ppf x = list 0 structure_item ppf x.str_items;;

soit implementation_with_coercion ppf (x, _) = implementation ppf x
