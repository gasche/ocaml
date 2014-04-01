(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*                  Projet Cristal, INRIA Rocquencourt                 *)
(*                                                                     *)
(*  Copyright 2002 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

ouvre Format
ouvre Outcometree

exception Ellipsis

soit cautious f ppf arg =
  essaie f ppf arg avec
    Ellipsis -> fprintf ppf "..."

soit rec print_ident ppf =
  fonction
    Oide_ident s -> pp_print_string ppf s
  | Oide_dot (id, s) ->
      print_ident ppf id; pp_print_char ppf '.'; pp_print_string ppf s
  | Oide_apply (id1, id2) ->
      fprintf ppf "%a(%a)" print_ident id1 print_ident id2

soit parenthesized_ident name =
  (List.mem name ["or"; "mod"; "land"; "lor"; "lxor"; "lsl"; "lsr"; "asr"])
  ||
  (filtre name.[0] avec
      'a'..'z' | 'A'..'Z' | '\223'..'\246' | '\248'..'\255' | '_' ->
        faux
    | _ -> vrai)

soit value_ident ppf name =
  si parenthesized_ident name alors
    fprintf ppf "( %s )" name
  sinon
    pp_print_string ppf name

(* Values *)

soit valid_float_lexeme s =
  soit l = String.length s dans
  soit rec loop i =
    si i >= l alors s ^ "." sinon
    filtre s.[i] avec
    | '0' .. '9' | '-' -> loop (i+1)
    | _ -> s
  dans loop 0

soit float_repres f =
  filtre classify_float f avec
    FP_nan -> "nan"
  | FP_infinite ->
      si f < 0.0 alors "neg_infinity" sinon "infinity"
  | _ ->
      soit float_val =
        soit s1 = Printf.sprintf "%.12g" f dans
        si f = float_of_string s1 alors s1 sinon
        soit s2 = Printf.sprintf "%.15g" f dans
        si f = float_of_string s2 alors s2 sinon
        Printf.sprintf "%.18g" f
      dans valid_float_lexeme float_val

soit parenthesize_if_neg ppf fmt v isneg =
  si isneg alors pp_print_char ppf '(';
  fprintf ppf fmt v;
  si isneg alors pp_print_char ppf ')'

soit print_out_value ppf tree =
  soit rec print_tree_1 ppf =
    fonction
    | Oval_constr (name, [param]) ->
        fprintf ppf "@[<1>%a@ %a@]" print_ident name print_constr_param param
    | Oval_constr (name, (_ :: _ tel params)) ->
        fprintf ppf "@[<1>%a@ (%a)@]" print_ident name
          (print_tree_list print_tree_1 ",") params
    | Oval_variant (name, Some param) ->
        fprintf ppf "@[<2>`%s@ %a@]" name print_constr_param param
    | tree -> print_simple_tree ppf tree
  et print_constr_param ppf = fonction
    | Oval_int i -> parenthesize_if_neg ppf "%i" i (i < 0)
    | Oval_int32 i -> parenthesize_if_neg ppf "%lil" i (i < 0l)
    | Oval_int64 i -> parenthesize_if_neg ppf "%LiL" i (i < 0L)
    | Oval_nativeint i -> parenthesize_if_neg ppf "%nin" i (i < 0n)
    | Oval_float f -> parenthesize_if_neg ppf "%s" (float_repres f) (f < 0.0)
    | tree -> print_simple_tree ppf tree
  et print_simple_tree ppf =
    fonction
      Oval_int i -> fprintf ppf "%i" i
    | Oval_int32 i -> fprintf ppf "%lil" i
    | Oval_int64 i -> fprintf ppf "%LiL" i
    | Oval_nativeint i -> fprintf ppf "%nin" i
    | Oval_float f -> pp_print_string ppf (float_repres f)
    | Oval_char c -> fprintf ppf "%C" c
    | Oval_string s ->
        début essaie fprintf ppf "%S" s avec
          Invalid_argument "String.create" -> fprintf ppf "<huge string>"
        fin
    | Oval_list tl ->
        fprintf ppf "@[<1>[%a]@]" (print_tree_list print_tree_1 ";") tl
    | Oval_array tl ->
        fprintf ppf "@[<2>[|%a|]@]" (print_tree_list print_tree_1 ";") tl
    | Oval_constr (name, []) -> print_ident ppf name
    | Oval_variant (name, None) -> fprintf ppf "`%s" name
    | Oval_stuff s -> pp_print_string ppf s
    | Oval_record fel ->
        fprintf ppf "@[<1>{%a}@]" (cautious (print_fields vrai)) fel
    | Oval_ellipsis -> raise Ellipsis
    | Oval_printer f -> f ppf
    | Oval_tuple tree_list ->
        fprintf ppf "@[<1>(%a)@]" (print_tree_list print_tree_1 ",") tree_list
    | tree -> fprintf ppf "@[<1>(%a)@]" (cautious print_tree_1) tree
  et print_fields first ppf =
    fonction
      [] -> ()
    | (name, tree) :: fields ->
        si not first alors fprintf ppf ";@ ";
        fprintf ppf "@[<1>%a@ =@ %a@]" print_ident name (cautious print_tree_1)
          tree;
        print_fields faux ppf fields
  et print_tree_list print_item sep ppf tree_list =
    soit rec print_list first ppf =
      fonction
        [] -> ()
      | tree :: tree_list ->
          si not first alors fprintf ppf "%s@ " sep;
          print_item ppf tree;
          print_list faux ppf tree_list
    dans
    cautious (print_list vrai) ppf tree_list
  dans
  cautious print_tree_1 ppf tree

soit out_value = ref print_out_value

(* Types *)

soit rec print_list_init pr sep ppf =
  fonction
    [] -> ()
  | a :: l -> sep ppf; pr ppf a; print_list_init pr sep ppf l

soit rec print_list pr sep ppf =
  fonction
    [] -> ()
  | [a] -> pr ppf a
  | a :: l -> pr ppf a; sep ppf; print_list pr sep ppf l

soit pr_present =
  print_list (fonc ppf s -> fprintf ppf "`%s" s) (fonc ppf -> fprintf ppf "@ ")

soit pr_vars =
  print_list (fonc ppf s -> fprintf ppf "'%s" s) (fonc ppf -> fprintf ppf "@ ")

soit rec print_out_type ppf =
  fonction
  | Otyp_alias (ty, s) ->
      fprintf ppf "@[%a@ as '%s@]" print_out_type ty s
  | Otyp_poly (sl, ty) ->
      fprintf ppf "@[<hov 2>%a.@ %a@]"
        pr_vars sl
        print_out_type ty
  | ty ->
      print_out_type_1 ppf ty

et print_out_type_1 ppf =
  fonction
    Otyp_arrow (lab, ty1, ty2) ->
      pp_open_box ppf 0;
      si lab <> "" alors (pp_print_string ppf lab; pp_print_char ppf ':');
      print_out_type_2 ppf ty1;
      pp_print_string ppf " ->";
      pp_print_space ppf ();
      print_out_type_1 ppf ty2;
      pp_close_box ppf ()
  | ty -> print_out_type_2 ppf ty
et print_out_type_2 ppf =
  fonction
    Otyp_tuple tyl ->
      fprintf ppf "@[<0>%a@]" (print_typlist print_simple_out_type " *") tyl
  | ty -> print_simple_out_type ppf ty
et print_simple_out_type ppf =
  fonction
    Otyp_class (ng, id, tyl) ->
      fprintf ppf "@[%a%s#%a@]" print_typargs tyl (si ng alors "_" sinon "")
        print_ident id
  | Otyp_constr (id, tyl) ->
      pp_open_box ppf 0;
      print_typargs ppf tyl;
      print_ident ppf id;
      pp_close_box ppf ()
  | Otyp_object (fields, rest) ->
      fprintf ppf "@[<2>< %a >@]" (print_fields rest) fields
  | Otyp_stuff s -> pp_print_string ppf s
  | Otyp_var (ng, s) -> fprintf ppf "'%s%s" (si ng alors "_" sinon "") s
  | Otyp_variant (non_gen, row_fields, closed, tags) ->
      soit print_present ppf =
        fonction
          None | Some [] -> ()
        | Some l -> fprintf ppf "@;<1 -2>> @[<hov>%a@]" pr_present l
      dans
      soit print_fields ppf =
        fonction
          Ovar_fields fields ->
            print_list print_row_field (fonc ppf -> fprintf ppf "@;<1 -2>| ")
              ppf fields
        | Ovar_name (id, tyl) ->
            fprintf ppf "@[%a%a@]" print_typargs tyl print_ident id
      dans
      fprintf ppf "%s[%s@[<hv>@[<hv>%a@]%a ]@]" (si non_gen alors "_" sinon "")
        (si closed alors si tags = None alors " " sinon "< "
         sinon si tags = None alors "> " sinon "? ")
        print_fields row_fields
        print_present tags
  | Otyp_alias _ | Otyp_poly _ | Otyp_arrow _ | Otyp_tuple _ tel ty ->
      pp_open_box ppf 1;
      pp_print_char ppf '(';
      print_out_type ppf ty;
      pp_print_char ppf ')';
      pp_close_box ppf ()
  | Otyp_abstract | Otyp_sum _ | Otyp_record _ | Otyp_manifest (_, _) -> ()
  | Otyp_module (p, n, tyl) ->
      fprintf ppf "@[<1>(module %s" p;
      soit first = ref vrai dans
      List.iter2
        (fonc s t ->
          soit sep = si !first alors (first := faux; "with") sinon "and" dans
          fprintf ppf " %s type %s = %a" sep s print_out_type t
        )
        n tyl;
      fprintf ppf ")@]"
et print_fields rest ppf =
  fonction
    [] ->
      début filtre rest avec
        Some non_gen -> fprintf ppf "%s.." (si non_gen alors "_" sinon "")
      | None -> ()
      fin
  | [s, t] ->
      fprintf ppf "%s : %a" s print_out_type t;
      début filtre rest avec
        Some _ -> fprintf ppf ";@ "
      | None -> ()
      fin;
      print_fields rest ppf []
  | (s, t) :: l ->
      fprintf ppf "%s : %a;@ %a" s print_out_type t (print_fields rest) l
et print_row_field ppf (l, opt_amp, tyl) =
  soit pr_of ppf =
    si opt_amp alors fprintf ppf " of@ &@ "
    sinon si tyl <> [] alors fprintf ppf " of@ "
    sinon fprintf ppf ""
  dans
  fprintf ppf "@[<hv 2>`%s%t%a@]" l pr_of (print_typlist print_out_type " &")
    tyl
et print_typlist print_elem sep ppf =
  fonction
    [] -> ()
  | [ty] -> print_elem ppf ty
  | ty :: tyl ->
      print_elem ppf ty;
      pp_print_string ppf sep;
      pp_print_space ppf ();
      print_typlist print_elem sep ppf tyl
et print_typargs ppf =
  fonction
    [] -> ()
  | [ty1] -> print_simple_out_type ppf ty1; pp_print_space ppf ()
  | tyl ->
      pp_open_box ppf 1;
      pp_print_char ppf '(';
      print_typlist print_out_type "," ppf tyl;
      pp_print_char ppf ')';
      pp_close_box ppf ();
      pp_print_space ppf ()

soit out_type = ref print_out_type

(* Class types *)

soit type_parameter ppf (ty, (co, cn)) =
  fprintf ppf "%s%s"
    (si not cn alors "+" sinon si not co alors "-" sinon "")
    (si ty = "_" alors ty sinon "'"^ty)

soit print_out_class_params ppf =
  fonction
    [] -> ()
  | tyl ->
      fprintf ppf "@[<1>[%a]@]@ "
        (print_list type_parameter (fonc ppf -> fprintf ppf ", "))
        tyl

soit rec print_out_class_type ppf =
  fonction
    Octy_constr (id, tyl) ->
      soit pr_tyl ppf =
        fonction
          [] -> ()
        | tyl ->
            fprintf ppf "@[<1>[%a]@]@ " (print_typlist !out_type ",") tyl
      dans
      fprintf ppf "@[%a%a@]" pr_tyl tyl print_ident id
  | Octy_arrow (lab, ty, cty) ->
      fprintf ppf "@[%s%a ->@ %a@]" (si lab <> "" alors lab ^ ":" sinon "")
        print_out_type_2 ty print_out_class_type cty
  | Octy_signature (self_ty, csil) ->
      soit pr_param ppf =
        fonction
          Some ty -> fprintf ppf "@ @[(%a)@]" !out_type ty
        | None -> ()
      dans
      fprintf ppf "@[<hv 2>@[<2>object%a@]@ %a@;<1 -2>end@]" pr_param self_ty
        (print_list print_out_class_sig_item (fonc ppf -> fprintf ppf "@ "))
        csil
et print_out_class_sig_item ppf =
  fonction
    Ocsg_constraint (ty1, ty2) ->
      fprintf ppf "@[<2>constraint %a =@ %a@]" !out_type ty1
        !out_type ty2
  | Ocsg_method (name, priv, virt, ty) ->
      fprintf ppf "@[<2>method %s%s%s :@ %a@]"
        (si priv alors "private " sinon "") (si virt alors "virtual " sinon "")
        name !out_type ty
  | Ocsg_value (name, mut, vr, ty) ->
      fprintf ppf "@[<2>val %s%s%s :@ %a@]"
        (si mut alors "mutable " sinon "")
        (si vr alors "virtual " sinon "")
        name !out_type ty

soit out_class_type = ref print_out_class_type

(* Signature *)

soit out_module_type = ref (fonc _ -> failwith "Oprint.out_module_type")
soit out_sig_item = ref (fonc _ -> failwith "Oprint.out_sig_item")
soit out_signature = ref (fonc _ -> failwith "Oprint.out_signature")

soit rec print_out_functor ppf =
  fonction
    Omty_functor (_, None, mty_res) ->
      fprintf ppf "() %a" print_out_functor mty_res
  | Omty_functor (name , Some mty_arg, mty_res) ->
      fprintf ppf "(%s : %a) %a" name
        print_out_module_type mty_arg print_out_functor mty_res
  | m -> fprintf ppf "->@ %a" print_out_module_type m
et print_out_module_type ppf =
  fonction
    Omty_abstract -> ()
  | Omty_functor _ tel t ->
      fprintf ppf "@[<2>functor@ %a@]" print_out_functor t
  | Omty_ident id -> fprintf ppf "%a" print_ident id
  | Omty_signature sg ->
      fprintf ppf "@[<hv 2>sig@ %a@;<1 -2>end@]" !out_signature sg
  | Omty_alias id -> fprintf ppf "(module %a)" print_ident id
et print_out_signature ppf =
  fonction
    [] -> ()
  | [item] -> !out_sig_item ppf item
  | item :: items ->
      fprintf ppf "%a@ %a" !out_sig_item item print_out_signature items
et print_out_sig_item ppf =
  fonction
    Osig_class (vir_flag, name, params, clt, rs) ->
      fprintf ppf "@[<2>%s%s@ %a%s@ :@ %a@]"
        (si rs = Orec_next alors "and" sinon "class")
        (si vir_flag alors " virtual" sinon "") print_out_class_params params
        name !out_class_type clt
  | Osig_class_type (vir_flag, name, params, clt, rs) ->
      fprintf ppf "@[<2>%s%s@ %a%s@ =@ %a@]"
        (si rs = Orec_next alors "and" sinon "class type")
        (si vir_flag alors " virtual" sinon "") print_out_class_params params
        name !out_class_type clt
  | Osig_exception (id, tyl) ->
      fprintf ppf "@[<2>exception %a@]" print_out_constr (id, tyl,None)
  | Osig_modtype (name, Omty_abstract) ->
      fprintf ppf "@[<2>module type %s@]" name
  | Osig_modtype (name, mty) ->
      fprintf ppf "@[<2>module type %s =@ %a@]" name !out_module_type mty
  | Osig_module (name, Omty_alias id, _) ->
      fprintf ppf "@[<2>module %s =@ %a@]" name print_ident id
  | Osig_module (name, mty, rs) ->
      fprintf ppf "@[<2>%s %s :@ %a@]"
        (filtre rs avec Orec_not -> "module"
                     | Orec_first -> "module rec"
                     | Orec_next -> "and")
        name !out_module_type mty
  | Osig_type(td, rs) ->
        print_out_type_decl
          (si rs = Orec_next alors "and" sinon "type")
          ppf td
  | Osig_value (name, ty, prims) ->
      soit kwd = si prims = [] alors "val" sinon "external" dans
      soit pr_prims ppf =
        fonction
          [] -> ()
        | s :: sl ->
            fprintf ppf "@ = \"%s\"" s;
            List.iter (fonc s -> fprintf ppf "@ \"%s\"" s) sl
      dans
      fprintf ppf "@[<2>%s %a :@ %a%a@]" kwd value_ident name !out_type
        ty pr_prims prims

et print_out_type_decl kwd ppf (name, args, ty, priv, constraints) =
  soit print_constraints ppf params =
    List.iter
      (fonc (ty1, ty2) ->
         fprintf ppf "@ @[<2>constraint %a =@ %a@]" !out_type ty1
           !out_type ty2)
      params
  dans
  soit type_defined ppf =
    filtre args avec
      [] -> pp_print_string ppf name
    | [arg] -> fprintf ppf "@[%a@ %s@]" type_parameter arg name
    | _ ->
        fprintf ppf "@[(@[%a)@]@ %s@]"
          (print_list type_parameter (fonc ppf -> fprintf ppf ",@ ")) args name
  dans
  soit print_manifest ppf =
    fonction
      Otyp_manifest (ty, _) -> fprintf ppf " =@ %a" !out_type ty
    | _ -> ()
  dans
  soit print_name_args ppf =
    fprintf ppf "%s %t%a" kwd type_defined print_manifest ty
  dans
  soit ty =
    filtre ty avec
      Otyp_manifest (_, ty) -> ty
    | _ -> ty
  dans
  soit print_private ppf = fonction
    Asttypes.Private -> fprintf ppf " private"
  | Asttypes.Public -> () dans
  soit print_out_tkind ppf = fonction
  | Otyp_abstract -> ()
  | Otyp_record lbls ->
      fprintf ppf " =%a {%a@;<1 -2>}"
        print_private priv
        (print_list_init print_out_label (fonc ppf -> fprintf ppf "@ ")) lbls
  | Otyp_sum constrs ->
      fprintf ppf " =%a@;<1 2>%a"
        print_private priv
        (print_list print_out_constr (fonc ppf -> fprintf ppf "@ | ")) constrs
  | ty ->
      fprintf ppf " =%a@;<1 2>%a"
        print_private priv
        !out_type ty
  dans
  fprintf ppf "@[<2>@[<hv 2>%t%a@]%a@]"
    print_name_args
    print_out_tkind ty
    print_constraints constraints
et print_out_constr ppf (name, tyl,ret_type_opt) =
  filtre ret_type_opt avec
  | None ->
      début filtre tyl avec
      | [] ->
          pp_print_string ppf name
      | _ ->
          fprintf ppf "@[<2>%s of@ %a@]" name
            (print_typlist print_simple_out_type " *") tyl
      fin
  | Some ret_type ->
      début filtre tyl avec
      | [] ->
          fprintf ppf "@[<2>%s :@ %a@]" name print_simple_out_type  ret_type
      | _ ->
          fprintf ppf "@[<2>%s :@ %a -> %a@]" name
            (print_typlist print_simple_out_type " *")
            tyl print_simple_out_type ret_type
      fin


et print_out_label ppf (name, mut, arg) =
  fprintf ppf "@[<2>%s%s :@ %a@];" (si mut alors "mutable " sinon "") name
    !out_type arg

soit _ = out_module_type := print_out_module_type
soit _ = out_signature := print_out_signature
soit _ = out_sig_item := print_out_sig_item

(* Phrases *)

soit print_out_exception ppf exn outv =
  filtre exn avec
    Sys.Break -> fprintf ppf "Interrupted.@."
  | Out_of_memory -> fprintf ppf "Out of memory during evaluation.@."
  | Stack_overflow ->
      fprintf ppf "Stack overflow during evaluation (looping recursion?).@."
  | _ -> fprintf ppf "@[Exception:@ %a.@]@." !out_value outv

soit rec print_items ppf =
  fonction
    [] -> ()
  | (tree, valopt) :: items ->
      début filtre valopt avec
        Some v ->
          fprintf ppf "@[<2>%a =@ %a@]" !out_sig_item tree
            !out_value v
      | None -> fprintf ppf "@[%a@]" !out_sig_item tree
      fin;
      si items <> [] alors fprintf ppf "@ %a" print_items items

soit print_out_phrase ppf =
  fonction
    Ophr_eval (outv, ty) ->
      fprintf ppf "@[- : %a@ =@ %a@]@." !out_type ty !out_value outv
  | Ophr_signature [] -> ()
  | Ophr_signature items -> fprintf ppf "@[<v>%a@]@." print_items items
  | Ophr_exception (exn, outv) -> print_out_exception ppf exn outv

soit out_phrase = ref print_out_phrase
