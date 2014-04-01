(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*             Damien Doligez, projet Para, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1999 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

ouvre Asttypes;;
ouvre Format;;
ouvre Lexing;;
ouvre Location;;
ouvre Parsetree;;

soit fmt_position with_name f l =
  soit fname = si with_name alors l.pos_fname sinon "" dans
  si l.pos_lnum = -1
  alors fprintf f "%s[%d]" fname l.pos_cnum
  sinon fprintf f "%s[%d,%d+%d]" fname l.pos_lnum l.pos_bol
               (l.pos_cnum - l.pos_bol)
;;

soit fmt_location f loc =
  soit p_2nd_name = loc.loc_start.pos_fname <> loc.loc_end.pos_fname dans
  fprintf f "(%a..%a)" (fmt_position vrai) loc.loc_start
                       (fmt_position p_2nd_name) loc.loc_end;
  si loc.loc_ghost alors fprintf f " ghost";
;;

soit rec fmt_longident_aux f x =
  filtre x avec
  | Longident.Lident (s) -> fprintf f "%s" s;
  | Longident.Ldot (y, s) -> fprintf f "%a.%s" fmt_longident_aux y s;
  | Longident.Lapply (y, z) ->
      fprintf f "%a(%a)" fmt_longident_aux y fmt_longident_aux z;
;;

soit fmt_longident f x = fprintf f "\"%a\"" fmt_longident_aux x;;

soit fmt_longident_loc f x =
  fprintf f "\"%a\" %a" fmt_longident_aux x.txt fmt_location x.loc;
;;

soit fmt_string_loc f x =
  fprintf f "\"%s\" %a" x.txt fmt_location x.loc;
;;

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
  fprintf f "%s" (String.make ((2*i) mod 72) ' ');
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

soit longident_loc i ppf li = line i ppf "%a\n" fmt_longident_loc li;;
soit string i ppf s = line i ppf "\"%s\"\n" s;;
soit string_loc i ppf s = line i ppf "%a\n" fmt_string_loc s;;
soit bool i ppf x = line i ppf "%s\n" (string_of_bool x);;
soit label i ppf x = line i ppf "label=\"%s\"\n" x;;

soit rec core_type i ppf x =
  line i ppf "core_type %a\n" fmt_location x.ptyp_loc;
  attributes i ppf x.ptyp_attributes;
  soit i = i+1 dans
  filtre x.ptyp_desc avec
  | Ptyp_any -> line i ppf "Ptyp_any\n";
  | Ptyp_var (s) -> line i ppf "Ptyp_var %s\n" s;
  | Ptyp_arrow (l, ct1, ct2) ->
      line i ppf "Ptyp_arrow\n";
      string i ppf l;
      core_type i ppf ct1;
      core_type i ppf ct2;
  | Ptyp_tuple l ->
      line i ppf "Ptyp_tuple\n";
      list i core_type ppf l;
  | Ptyp_constr (li, l) ->
      line i ppf "Ptyp_constr %a\n" fmt_longident_loc li;
      list i core_type ppf l;
  | Ptyp_variant (l, closed, low) ->
      line i ppf "Ptyp_variant closed=%a\n" fmt_closed_flag closed;
      list i label_x_bool_x_core_type_list ppf l;
      option i (fonc i -> list i string) ppf low
  | Ptyp_object (l, c) ->
      line i ppf "Ptyp_object %a\n" fmt_closed_flag c;
      soit i = i + 1 dans
      List.iter
        (fonc (s, t) ->
          line i ppf "method %s" s;
          core_type (i + 1) ppf t
        )
        l
  | Ptyp_class (li, l) ->
      line i ppf "Ptyp_class %a\n" fmt_longident_loc li;
      list i core_type ppf l
  | Ptyp_alias (ct, s) ->
      line i ppf "Ptyp_alias \"%s\"\n" s;
      core_type i ppf ct;
  | Ptyp_poly (sl, ct) ->
      line i ppf "Ptyp_poly%a\n"
        (fonc ppf -> List.iter (fonc x -> fprintf ppf " '%s" x)) sl;
      core_type i ppf ct;
  | Ptyp_package (s, l) ->
      line i ppf "Ptyp_package %a\n" fmt_longident_loc s;
      list i package_with ppf l;
  | Ptyp_extension (s, arg) ->
      line i ppf "Ptyp_extension \"%s\"\n" s.txt;
      payload i ppf arg

et package_with i ppf (s, t) =
  line i ppf "with type %a\n" fmt_longident_loc s;
  core_type i ppf t

et pattern i ppf x =
  line i ppf "pattern %a\n" fmt_location x.ppat_loc;
  attributes i ppf x.ppat_attributes;
  soit i = i+1 dans
  filtre x.ppat_desc avec
  | Ppat_any -> line i ppf "Ppat_any\n";
  | Ppat_var (s) -> line i ppf "Ppat_var %a\n" fmt_string_loc s;
  | Ppat_alias (p, s) ->
      line i ppf "Ppat_alias %a\n" fmt_string_loc s;
      pattern i ppf p;
  | Ppat_constant (c) -> line i ppf "Ppat_constant %a\n" fmt_constant c;
  | Ppat_interval (c1, c2) -> line i ppf "Ppat_interval %a..%a\n" fmt_constant c1 fmt_constant c2;
  | Ppat_tuple (l) ->
      line i ppf "Ppat_tuple\n";
      list i pattern ppf l;
  | Ppat_construct (li, po) ->
      line i ppf "Ppat_construct %a\n" fmt_longident_loc li;
      option i pattern ppf po;
  | Ppat_variant (l, po) ->
      line i ppf "Ppat_variant \"%s\"\n" l;
      option i pattern ppf po;
  | Ppat_record (l, c) ->
      line i ppf "Ppat_record %a\n" fmt_closed_flag c;
      list i longident_x_pattern ppf l;
  | Ppat_array (l) ->
      line i ppf "Ppat_array\n";
      list i pattern ppf l;
  | Ppat_or (p1, p2) ->
      line i ppf "Ppat_or\n";
      pattern i ppf p1;
      pattern i ppf p2;
  | Ppat_lazy p ->
      line i ppf "Ppat_lazy\n";
      pattern i ppf p;
  | Ppat_constraint (p, ct) ->
      line i ppf "Ppat_constraint\n";
      pattern i ppf p;
      core_type i ppf ct;
  | Ppat_type (li) ->
      line i ppf "Ppat_type\n";
      longident_loc i ppf li
  | Ppat_unpack s ->
      line i ppf "Ppat_unpack %a\n" fmt_string_loc s;
  | Ppat_extension (s, arg) ->
      line i ppf "Ppat_extension \"%s\"\n" s.txt;
      payload i ppf arg

et expression i ppf x =
  line i ppf "expression %a\n" fmt_location x.pexp_loc;
  attributes i ppf x.pexp_attributes;
  soit i = i+1 dans
  filtre x.pexp_desc avec
  | Pexp_ident (li) -> line i ppf "Pexp_ident %a\n" fmt_longident_loc li;
  | Pexp_constant (c) -> line i ppf "Pexp_constant %a\n" fmt_constant c;
  | Pexp_let (rf, l, e) ->
      line i ppf "Pexp_let %a\n" fmt_rec_flag rf;
      list i value_binding ppf l;
      expression i ppf e;
  | Pexp_function l ->
      line i ppf "Pexp_function\n";
      list i case ppf l;
  | Pexp_fun (l, eo, p, e) ->
      line i ppf "Pexp_fun \"%s\"\n" l;
      option i expression ppf eo;
      pattern i ppf p;
      expression i ppf e;
  | Pexp_apply (e, l) ->
      line i ppf "Pexp_apply\n";
      expression i ppf e;
      list i label_x_expression ppf l;
  | Pexp_match (e, l) ->
      line i ppf "Pexp_match\n";
      expression i ppf e;
      list i case ppf l;
  | Pexp_try (e, l) ->
      line i ppf "Pexp_try\n";
      expression i ppf e;
      list i case ppf l;
  | Pexp_tuple (l) ->
      line i ppf "Pexp_tuple\n";
      list i expression ppf l;
  | Pexp_construct (li, eo) ->
      line i ppf "Pexp_construct %a\n" fmt_longident_loc li;
      option i expression ppf eo;
  | Pexp_variant (l, eo) ->
      line i ppf "Pexp_variant \"%s\"\n" l;
      option i expression ppf eo;
  | Pexp_record (l, eo) ->
      line i ppf "Pexp_record\n";
      list i longident_x_expression ppf l;
      option i expression ppf eo;
  | Pexp_field (e, li) ->
      line i ppf "Pexp_field\n";
      expression i ppf e;
      longident_loc i ppf li;
  | Pexp_setfield (e1, li, e2) ->
      line i ppf "Pexp_setfield\n";
      expression i ppf e1;
      longident_loc i ppf li;
      expression i ppf e2;
  | Pexp_array (l) ->
      line i ppf "Pexp_array\n";
      list i expression ppf l;
  | Pexp_ifthenelse (e1, e2, eo) ->
      line i ppf "Pexp_ifthenelse\n";
      expression i ppf e1;
      expression i ppf e2;
      option i expression ppf eo;
  | Pexp_sequence (e1, e2) ->
      line i ppf "Pexp_sequence\n";
      expression i ppf e1;
      expression i ppf e2;
  | Pexp_while (e1, e2) ->
      line i ppf "Pexp_while\n";
      expression i ppf e1;
      expression i ppf e2;
  | Pexp_for (p, e1, e2, df, e3) ->
      line i ppf "Pexp_for %a\n" fmt_direction_flag df;
      pattern i ppf p;
      expression i ppf e1;
      expression i ppf e2;
      expression i ppf e3;
  | Pexp_constraint (e, ct) ->
      line i ppf "Pexp_constraint\n";
      expression i ppf e;
      core_type i ppf ct;
  | Pexp_coerce (e, cto1, cto2) ->
      line i ppf "Pexp_coerce\n";
      expression i ppf e;
      option i core_type ppf cto1;
      core_type i ppf cto2;
  | Pexp_send (e, s) ->
      line i ppf "Pexp_send \"%s\"\n" s;
      expression i ppf e;
  | Pexp_new (li) -> line i ppf "Pexp_new %a\n" fmt_longident_loc li;
  | Pexp_setinstvar (s, e) ->
      line i ppf "Pexp_setinstvar %a\n" fmt_string_loc s;
      expression i ppf e;
  | Pexp_override (l) ->
      line i ppf "Pexp_override\n";
      list i string_x_expression ppf l;
  | Pexp_letmodule (s, me, e) ->
      line i ppf "Pexp_letmodule %a\n" fmt_string_loc s;
      module_expr i ppf me;
      expression i ppf e;
  | Pexp_assert (e) ->
      line i ppf "Pexp_assert\n";
      expression i ppf e;
  | Pexp_lazy (e) ->
      line i ppf "Pexp_lazy\n";
      expression i ppf e;
  | Pexp_poly (e, cto) ->
      line i ppf "Pexp_poly\n";
      expression i ppf e;
      option i core_type ppf cto;
  | Pexp_object s ->
      line i ppf "Pexp_object\n";
      class_structure i ppf s
  | Pexp_newtype (s, e) ->
      line i ppf "Pexp_newtype \"%s\"\n" s;
      expression i ppf e
  | Pexp_pack me ->
      line i ppf "Pexp_pack\n";
      module_expr i ppf me
  | Pexp_open (ovf, m, e) ->
      line i ppf "Pexp_open %a \"%a\"\n" fmt_override_flag ovf
        fmt_longident_loc m;
      expression i ppf e
  | Pexp_extension (s, arg) ->
      line i ppf "Pexp_extension \"%s\"\n" s.txt;
      payload i ppf arg

et value_description i ppf x =
  line i ppf "value_description %a %a\n" fmt_string_loc x.pval_name fmt_location x.pval_loc;
  attributes i ppf x.pval_attributes;
  core_type (i+1) ppf x.pval_type;
  list (i+1) string ppf x.pval_prim

et type_parameter i ppf (x, _variance) =
  filtre x avec
  | Some x ->
      string_loc i ppf x
  | None ->
      string i ppf "_"

et type_declaration i ppf x =
  line i ppf "type_declaration %a %a\n" fmt_string_loc x.ptype_name fmt_location x.ptype_loc;
  attributes i ppf x.ptype_attributes;
  soit i = i+1 dans
  line i ppf "ptype_params =\n";
  list (i+1) type_parameter ppf x.ptype_params;
  line i ppf "ptype_cstrs =\n";
  list (i+1) core_type_x_core_type_x_location ppf x.ptype_cstrs;
  line i ppf "ptype_kind =\n";
  type_kind (i+1) ppf x.ptype_kind;
  line i ppf "ptype_private = %a\n" fmt_private_flag x.ptype_private;
  line i ppf "ptype_manifest =\n";
  option (i+1) core_type ppf x.ptype_manifest

et attributes i ppf l =
  soit i = i + 1 dans
  List.iter
    (fonc (s, arg) ->
      line i ppf "attribute \"%s\"\n" s.txt;
      payload (i + 1) ppf arg;
    )
    l

et payload i ppf = fonction
  | PStr x -> structure i ppf x
  | PTyp x -> core_type i ppf x
  | PPat (x, None) -> pattern i ppf x
  | PPat (x, Some g) ->
    pattern i ppf x;
    line i ppf "<when>\n";
    expression (i + 1) ppf g


et type_kind i ppf x =
  filtre x avec
  | Ptype_abstract ->
      line i ppf "Ptype_abstract\n"
  | Ptype_variant l ->
      line i ppf "Ptype_variant\n";
      list (i+1) constructor_decl ppf l;
  | Ptype_record l ->
      line i ppf "Ptype_record\n";
      list (i+1) label_decl ppf l;

et class_type i ppf x =
  line i ppf "class_type %a\n" fmt_location x.pcty_loc;
  attributes i ppf x.pcty_attributes;
  soit i = i+1 dans
  filtre x.pcty_desc avec
  | Pcty_constr (li, l) ->
      line i ppf "Pcty_constr %a\n" fmt_longident_loc li;
      list i core_type ppf l;
  | Pcty_signature (cs) ->
      line i ppf "Pcty_signature\n";
      class_signature i ppf cs;
  | Pcty_arrow (l, co, cl) ->
      line i ppf "Pcty_arrow \"%s\"\n" l;
      core_type i ppf co;
      class_type i ppf cl;
  | Pcty_extension (s, arg) ->
      line i ppf "Pcty_extension \"%s\"\n" s.txt;
      payload i ppf arg

et class_signature i ppf cs =
  line i ppf "class_signature\n";
  core_type (i+1) ppf cs.pcsig_self;
  list (i+1) class_type_field ppf cs.pcsig_fields;

et class_type_field i ppf x =
  line i ppf "class_type_field %a\n" fmt_location x.pctf_loc;
  soit i = i+1 dans
  attributes i ppf x.pctf_attributes;
  filtre x.pctf_desc avec
  | Pctf_inherit (ct) ->
      line i ppf "Pctf_inherit\n";
      class_type i ppf ct;
  | Pctf_val (s, mf, vf, ct) ->
      line i ppf "Pctf_val \"%s\" %a %a\n" s fmt_mutable_flag mf
           fmt_virtual_flag vf;
      core_type (i+1) ppf ct;
  | Pctf_method (s, pf, vf, ct) ->
      line i ppf "Pctf_method \"%s\" %a %a\n" s fmt_private_flag pf fmt_virtual_flag vf;
      core_type (i+1) ppf ct;
  | Pctf_constraint (ct1, ct2) ->
      line i ppf "Pctf_constraint\n";
      core_type (i+1) ppf ct1;
      core_type (i+1) ppf ct2;
  | Pctf_extension (s, arg) ->
      line i ppf "Pctf_extension \"%s\"\n" s.txt;
     payload i ppf arg

et class_description i ppf x =
  line i ppf "class_description %a\n" fmt_location x.pci_loc;
  attributes i ppf x.pci_attributes;
  soit i = i+1 dans
  line i ppf "pci_virt = %a\n" fmt_virtual_flag x.pci_virt;
  line i ppf "pci_params =\n";
  cl_type_parameters (i+1) ppf x.pci_params;
  line i ppf "pci_name = %a\n" fmt_string_loc x.pci_name;
  line i ppf "pci_expr =\n";
  class_type (i+1) ppf x.pci_expr;

et class_type_declaration i ppf x =
  line i ppf "class_type_declaration %a\n" fmt_location x.pci_loc;
  attributes i ppf x.pci_attributes;
  soit i = i+1 dans
  line i ppf "pci_virt = %a\n" fmt_virtual_flag x.pci_virt;
  line i ppf "pci_params =\n";
  cl_type_parameters (i+1) ppf x.pci_params;
  line i ppf "pci_name = %a\n" fmt_string_loc x.pci_name;
  line i ppf "pci_expr =\n";
  class_type (i+1) ppf x.pci_expr;

et class_expr i ppf x =
  line i ppf "class_expr %a\n" fmt_location x.pcl_loc;
  attributes i ppf x.pcl_attributes;
  soit i = i+1 dans
  filtre x.pcl_desc avec
  | Pcl_constr (li, l) ->
      line i ppf "Pcl_constr %a\n" fmt_longident_loc li;
      list i core_type ppf l;
  | Pcl_structure (cs) ->
      line i ppf "Pcl_structure\n";
      class_structure i ppf cs;
  | Pcl_fun (l, eo, p, e) ->
      line i ppf "Pcl_fun\n";
      label i ppf l;
      option i expression ppf eo;
      pattern i ppf p;
      class_expr i ppf e;
  | Pcl_apply (ce, l) ->
      line i ppf "Pcl_apply\n";
      class_expr i ppf ce;
      list i label_x_expression ppf l;
  | Pcl_let (rf, l, ce) ->
      line i ppf "Pcl_let %a\n" fmt_rec_flag rf;
      list i value_binding ppf l;
      class_expr i ppf ce;
  | Pcl_constraint (ce, ct) ->
      line i ppf "Pcl_constraint\n";
      class_expr i ppf ce;
      class_type i ppf ct;
  | Pcl_extension (s, arg) ->
      line i ppf "Pcl_extension \"%s\"\n" s.txt;
      payload i ppf arg

et class_structure i ppf { pcstr_self = p; pcstr_fields = l } =
  line i ppf "class_structure\n";
  pattern (i+1) ppf p;
  list (i+1) class_field ppf l;

et class_field i ppf x =
  line i ppf "class_field %a\n" fmt_location x.pcf_loc;
  soit i = i + 1 dans
  attributes i ppf x.pcf_attributes;
  filtre x.pcf_desc avec
  | Pcf_inherit (ovf, ce, so) ->
      line i ppf "Pcf_inherit %a\n" fmt_override_flag ovf;
      class_expr (i+1) ppf ce;
      option (i+1) string ppf so;
  | Pcf_val (s, mf, k) ->
      line i ppf "Pcf_val %a\n" fmt_mutable_flag mf;
      line (i+1) ppf "%a\n" fmt_string_loc s;
      class_field_kind (i+1) ppf k
  | Pcf_method (s, pf, k) ->
      line i ppf "Pcf_method %a\n" fmt_private_flag pf;
      line (i+1) ppf "%a\n" fmt_string_loc s;
      class_field_kind (i+1) ppf k
  | Pcf_constraint (ct1, ct2) ->
      line i ppf "Pcf_constraint\n";
      core_type (i+1) ppf ct1;
      core_type (i+1) ppf ct2;
  | Pcf_initializer (e) ->
      line i ppf "Pcf_initializer\n";
      expression (i+1) ppf e;
  | Pcf_extension (s, arg) ->
      line i ppf "Pcf_extension \"%s\"\n" s.txt;
      payload i ppf arg

et class_field_kind i ppf = fonction
  | Cfk_concrete (o, e) ->
      line i ppf "Concrete %a\n" fmt_override_flag o;
      expression i ppf e
  | Cfk_virtual t ->
      line i ppf "Virtual\n";
      core_type i ppf t

et class_declaration i ppf x =
  line i ppf "class_declaration %a\n" fmt_location x.pci_loc;
  attributes i ppf x.pci_attributes;
  soit i = i+1 dans
  line i ppf "pci_virt = %a\n" fmt_virtual_flag x.pci_virt;
  line i ppf "pci_params =\n";
  cl_type_parameters (i+1) ppf x.pci_params;
  line i ppf "pci_name = %a\n" fmt_string_loc x.pci_name;
  line i ppf "pci_expr =\n";
  class_expr (i+1) ppf x.pci_expr;

et module_type i ppf x =
  line i ppf "module_type %a\n" fmt_location x.pmty_loc;
  attributes i ppf x.pmty_attributes;
  soit i = i+1 dans
  filtre x.pmty_desc avec
  | Pmty_ident li -> line i ppf "Pmty_ident %a\n" fmt_longident_loc li;
  | Pmty_alias li -> line i ppf "Pmty_alias %a\n" fmt_longident_loc li;
  | Pmty_signature (s) ->
      line i ppf "Pmty_signature\n";
      signature i ppf s;
  | Pmty_functor (s, mt1, mt2) ->
      line i ppf "Pmty_functor %a\n" fmt_string_loc s;
      Misc.may (module_type i ppf) mt1;
      module_type i ppf mt2;
  | Pmty_with (mt, l) ->
      line i ppf "Pmty_with\n";
      module_type i ppf mt;
      list i with_constraint ppf l;
  | Pmty_typeof m ->
      line i ppf "Pmty_typeof\n";
      module_expr i ppf m;
  | Pmty_extension (s, arg) ->
      line i ppf "Pmod_extension \"%s\"\n" s.txt;
      payload i ppf arg

et signature i ppf x = list i signature_item ppf x

et signature_item i ppf x =
  line i ppf "signature_item %a\n" fmt_location x.psig_loc;
  soit i = i+1 dans
  filtre x.psig_desc avec
  | Psig_value vd ->
      line i ppf "Psig_value\n";
      value_description i ppf vd;
  | Psig_type (l) ->
      line i ppf "Psig_type\n";
      list i type_declaration ppf l;
  | Psig_exception cd ->
      line i ppf "Psig_exception\n";
      constructor_decl i ppf cd;
  | Psig_module pmd ->
      line i ppf "Psig_module %a\n" fmt_string_loc pmd.pmd_name;
      attributes i ppf pmd.pmd_attributes;
      module_type i ppf pmd.pmd_type
  | Psig_recmodule decls ->
      line i ppf "Psig_recmodule\n";
      list i module_declaration ppf decls;
  | Psig_modtype x ->
      line i ppf "Psig_modtype %a\n" fmt_string_loc x.pmtd_name;
      attributes i ppf x.pmtd_attributes;
      modtype_declaration i ppf x.pmtd_type
  | Psig_open (ovf, li, attrs) ->
      line i ppf "Psig_open %a %a\n"
        fmt_override_flag ovf
        fmt_longident_loc li;
      attributes i ppf attrs
  | Psig_include (mt, attrs) ->
      line i ppf "Psig_include\n";
      module_type i ppf mt;
      attributes i ppf attrs
  | Psig_class (l) ->
      line i ppf "Psig_class\n";
      list i class_description ppf l;
  | Psig_class_type (l) ->
      line i ppf "Psig_class_type\n";
      list i class_type_declaration ppf l;
  | Psig_extension ((s, arg), attrs) ->
      line i ppf "Psig_extension \"%s\"\n" s.txt;
      attributes i ppf attrs;
      payload i ppf arg
  | Psig_attribute (s, arg) ->
      line i ppf "Psig_attribute \"%s\"\n" s.txt;
      payload i ppf arg

et modtype_declaration i ppf = fonction
  | None -> line i ppf "#abstract"
  | Some mt -> module_type (i+1) ppf mt

et with_constraint i ppf x =
  filtre x avec
  | Pwith_type (lid, td) ->
      line i ppf "Pwith_type %a\n" fmt_longident_loc lid;
      type_declaration (i+1) ppf td;
  | Pwith_typesubst (td) ->
      line i ppf "Pwith_typesubst\n";
      type_declaration (i+1) ppf td;
  | Pwith_module (lid1, lid2) ->
      line i ppf "Pwith_module %a = %a\n"
        fmt_longident_loc lid1
        fmt_longident_loc lid2;
  | Pwith_modsubst (s, li) ->
      line i ppf "Pwith_modsubst %a = %a\n"
        fmt_string_loc s
        fmt_longident_loc li;

et module_expr i ppf x =
  line i ppf "module_expr %a\n" fmt_location x.pmod_loc;
  attributes i ppf x.pmod_attributes;
  soit i = i+1 dans
  filtre x.pmod_desc avec
  | Pmod_ident (li) -> line i ppf "Pmod_ident %a\n" fmt_longident_loc li;
  | Pmod_structure (s) ->
      line i ppf "Pmod_structure\n";
      structure i ppf s;
  | Pmod_functor (s, mt, me) ->
      line i ppf "Pmod_functor %a\n" fmt_string_loc s;
      Misc.may (module_type i ppf) mt;
      module_expr i ppf me;
  | Pmod_apply (me1, me2) ->
      line i ppf "Pmod_apply\n";
      module_expr i ppf me1;
      module_expr i ppf me2;
  | Pmod_constraint (me, mt) ->
      line i ppf "Pmod_constraint\n";
      module_expr i ppf me;
      module_type i ppf mt;
  | Pmod_unpack (e) ->
      line i ppf "Pmod_unpack\n";
      expression i ppf e;
  | Pmod_extension (s, arg) ->
      line i ppf "Pmod_extension \"%s\"\n" s.txt;
      payload i ppf arg

et structure i ppf x = list i structure_item ppf x

et structure_item i ppf x =
  line i ppf "structure_item %a\n" fmt_location x.pstr_loc;
  soit i = i+1 dans
  filtre x.pstr_desc avec
  | Pstr_eval (e, attrs) ->
      line i ppf "Pstr_eval\n";
      attributes i ppf attrs;
      expression i ppf e;
  | Pstr_value (rf, l) ->
      line i ppf "Pstr_value %a\n" fmt_rec_flag rf;
      list i value_binding ppf l;
  | Pstr_primitive vd ->
      line i ppf "Pstr_primitive\n";
      value_description i ppf vd;
  | Pstr_type l ->
      line i ppf "Pstr_type\n";
      list i type_declaration ppf l;
  | Pstr_exception cd ->
      line i ppf "Pstr_exception\n";
      constructor_decl i ppf cd;
  | Pstr_exn_rebind (s, li, attrs) ->
      line i ppf "Pstr_exn_rebind\n";
      attributes i ppf attrs;
      line (i+1) ppf "%a\n" fmt_string_loc s;
      line (i+1) ppf "%a\n" fmt_longident_loc li
  | Pstr_module x ->
      line i ppf "Pstr_module\n";
      module_binding i ppf x
  | Pstr_recmodule bindings ->
      line i ppf "Pstr_recmodule\n";
      list i module_binding ppf bindings;
  | Pstr_modtype x ->
      line i ppf "Pstr_modtype %a\n" fmt_string_loc x.pmtd_name;
      attributes i ppf x.pmtd_attributes;
      modtype_declaration i ppf x.pmtd_type
  | Pstr_open (ovf, li, attrs) ->
      line i ppf "Pstr_open %a %a\n"
        fmt_override_flag ovf
        fmt_longident_loc li;
      attributes i ppf attrs
  | Pstr_class (l) ->
      line i ppf "Pstr_class\n";
      list i class_declaration ppf l;
  | Pstr_class_type (l) ->
      line i ppf "Pstr_class_type\n";
      list i class_type_declaration ppf l;
  | Pstr_include (me, attrs) ->
      line i ppf "Pstr_include";
      attributes i ppf attrs;
      module_expr i ppf me
  | Pstr_extension ((s, arg), attrs) ->
      line i ppf "Pstr_extension \"%s\"\n" s.txt;
      attributes i ppf attrs;
      payload i ppf arg
  | Pstr_attribute (s, arg) ->
      line i ppf "Pstr_attribute \"%s\"\n" s.txt;
      payload i ppf arg

et module_declaration i ppf pmd =
  string_loc i ppf pmd.pmd_name;
  attributes i ppf pmd.pmd_attributes;
  module_type (i+1) ppf pmd.pmd_type;

et module_binding i ppf x =
  string_loc i ppf x.pmb_name;
  attributes i ppf x.pmb_attributes;
  module_expr (i+1) ppf x.pmb_expr

et core_type_x_core_type_x_location i ppf (ct1, ct2, l) =
  line i ppf "<constraint> %a\n" fmt_location l;
  core_type (i+1) ppf ct1;
  core_type (i+1) ppf ct2;

et constructor_decl i ppf {pcd_name; pcd_args; pcd_res; pcd_loc; pcd_attributes} =
  line i ppf "%a\n" fmt_location pcd_loc;
  attributes i ppf pcd_attributes;
  line (i+1) ppf "%a\n" fmt_string_loc pcd_name;
  list (i+1) core_type ppf pcd_args;
  option (i+1) core_type ppf pcd_res

et label_decl i ppf {pld_name; pld_mutable; pld_type; pld_loc; pld_attributes} =
  line i ppf "%a\n" fmt_location pld_loc;
  attributes i ppf pld_attributes;
  line (i+1) ppf "%a\n" fmt_mutable_flag pld_mutable;
  line (i+1) ppf "%a" fmt_string_loc pld_name;
  core_type (i+1) ppf pld_type

et cl_type_parameters i ppf l =
  line i ppf "<params>\n";
  list (i+1) cl_type_parameter ppf l;

et cl_type_parameter i ppf (x, _variance) =
  string_loc i ppf x

et longident_x_pattern i ppf (li, p) =
  line i ppf "%a\n" fmt_longident_loc li;
  pattern (i+1) ppf p;

et case i ppf {pc_lhs; pc_guard; pc_rhs} =
  line i ppf "<case>\n";
  pattern (i+1) ppf pc_lhs;
  début filtre pc_guard avec
  | None -> ()
  | Some g -> line (i+1) ppf "<when>\n"; expression (i + 2) ppf g
  fin;
  expression (i+1) ppf pc_rhs;

et value_binding i ppf x =
  line i ppf "<def>\n";
  attributes (i+1) ppf x.pvb_attributes;
  pattern (i+1) ppf x.pvb_pat;
  expression (i+1) ppf x.pvb_expr

et string_x_expression i ppf (s, e) =
  line i ppf "<override> %a\n" fmt_string_loc s;
  expression (i+1) ppf e;

et longident_x_expression i ppf (li, e) =
  line i ppf "%a\n" fmt_longident_loc li;
  expression (i+1) ppf e;

et label_x_expression i ppf (l,e) =
  line i ppf "<label> \"%s\"\n" l;
  expression (i+1) ppf e;

et label_x_bool_x_core_type_list i ppf x =
  filtre x avec
    Rtag (l, b, ctl) ->
      line i ppf "Rtag \"%s\" %s\n" l (string_of_bool b);
      list (i+1) core_type ppf ctl
  | Rinherit (ct) ->
      line i ppf "Rinherit\n";
      core_type (i+1) ppf ct
;;

soit rec toplevel_phrase i ppf x =
  filtre x avec
  | Ptop_def (s) ->
      line i ppf "Ptop_def\n";
      structure (i+1) ppf s;
  | Ptop_dir (s, da) ->
      line i ppf "Ptop_dir \"%s\"\n" s;
      directive_argument i ppf da;

et directive_argument i ppf x =
  filtre x avec
  | Pdir_none -> line i ppf "Pdir_none\n"
  | Pdir_string (s) -> line i ppf "Pdir_string \"%s\"\n" s;
  | Pdir_int (i) -> line i ppf "Pdir_int %d\n" i;
  | Pdir_ident (li) -> line i ppf "Pdir_ident %a\n" fmt_longident li;
  | Pdir_bool (b) -> line i ppf "Pdir_bool %s\n" (string_of_bool b);
;;

soit interface ppf x = list 0 signature_item ppf x;;

soit implementation ppf x = list 0 structure_item ppf x;;

soit top_phrase ppf x = toplevel_phrase 0 ppf x;;
