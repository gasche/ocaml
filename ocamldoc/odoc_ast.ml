(***********************************************************************)
(*                                                                     *)
(*                             OCamldoc                                *)
(*                                                                     *)
(*            Maxence Guesdon, projet Cristal, INRIA Rocquencourt      *)
(*                                                                     *)
(*  Copyright 2001 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(** Analysis of implementation files. *)
ouvre Misc
ouvre Asttypes
ouvre Types
ouvre Typedtree

soit print_DEBUG3 s = print_string s ; print_newline ();;
soit print_DEBUG s = print_string s ; print_newline ();;

type typedtree = (Typedtree.structure * Typedtree.module_coercion)

module Name = Odoc_name
ouvre Odoc_parameter
ouvre Odoc_value
ouvre Odoc_type
ouvre Odoc_exception
ouvre Odoc_class
ouvre Odoc_module
ouvre Odoc_types

(** This variable contains the regular expression representing a blank.*)
soit blank = "[ \010\013\009\012']"

(** This variable contains the regular expression representing a blank but not a '\n'.*)
soit simple_blank = "[ \013\009\012]"

(** This module is used to search for structure items by name in a Typedtree.structure.
   One function creates two hash tables, which can then be used to search for elements.
   Class elements do not use tables.
*)
module Typedtree_search =
  struct
    type ele =
      | M de string
      | MT de string
      | T de string
      | C de string
      | CT de string
      | E de string
      | ER de string
      | P de string
      | IM de string

    type tab = (ele, Typedtree.structure_item_desc) Hashtbl.t
    type tab_values = (Odoc_module.Name.t, Typedtree.pattern * Typedtree.expression) Hashtbl.t

    soit iter_val_pattern = fonction
      | Typedtree.Tpat_any -> None
      | Typedtree.Tpat_var (name, _) -> Some (Name.from_ident name)
      | Typedtree.Tpat_tuple _ -> None (* A VOIR quand on traitera les tuples *)
      | _ -> None

    soit add_to_hashes table table_values tt =
      filtre tt avec
      | Typedtree.Tstr_module mb ->
          Hashtbl.add table (M (Name.from_ident mb.mb_id)) tt
      | Typedtree.Tstr_recmodule mods ->
          List.iter
            (fonc mb ->
              Hashtbl.add table (M (Name.from_ident mb.mb_id))
                (Typedtree.Tstr_module mb)
            )
            mods
      | Typedtree.Tstr_modtype mtd ->
          Hashtbl.add table (MT (Name.from_ident mtd.mtd_id)) tt
      | Typedtree.Tstr_exception decl ->
          Hashtbl.add table (E (Name.from_ident decl.cd_id)) tt
      | Typedtree.Tstr_exn_rebind (ident, _, _, _, _) ->
          Hashtbl.add table (ER (Name.from_ident ident)) tt
      | Typedtree.Tstr_type ident_type_decl_list ->
          List.iter
            (fonc td ->
              Hashtbl.add table (T (Name.from_ident td.typ_id))
                (Typedtree.Tstr_type [td]))
            ident_type_decl_list
      | Typedtree.Tstr_class info_list ->
          List.iter
            (fonc (ci, m, s) ->
              Hashtbl.add table (C (Name.from_ident ci.ci_id_class))
                (Typedtree.Tstr_class [ci, m, s]))
            info_list
      | Typedtree.Tstr_class_type info_list ->
          List.iter
            (fonc ((id,id_loc,_) tel ci) ->
              Hashtbl.add table
                (CT (Name.from_ident id))
                (Typedtree.Tstr_class_type [ci]))
            info_list
      | Typedtree.Tstr_value (_, pat_exp_list) ->
          List.iter
            (fonc {vb_pat=pat; vb_expr=exp} ->
              filtre iter_val_pattern pat.Typedtree.pat_desc avec
                None -> ()
              | Some n -> Hashtbl.add table_values n (pat,exp)
            )
            pat_exp_list
      | Typedtree.Tstr_primitive vd ->
          Hashtbl.add table (P (Name.from_ident vd.val_id)) tt
      | Typedtree.Tstr_open _ -> ()
      | Typedtree.Tstr_include _ -> ()
      | Typedtree.Tstr_eval _ -> ()
      | Typedtree.Tstr_attribute _ -> ()

    soit tables typedtree =
      soit t = Hashtbl.create 13 dans
      soit t_values = Hashtbl.create 13 dans
      List.iter (fonc str -> add_to_hashes t t_values str.str_desc) typedtree;
      (t, t_values)

    soit search_module table name =
      filtre Hashtbl.find table (M name) avec
        (Typedtree.Tstr_module mb) -> mb.mb_expr
      | _ -> affirme faux

    soit search_module_type table name =
      filtre Hashtbl.find table (MT name) avec
      | (Typedtree.Tstr_modtype mtd) -> mtd
      | _ -> affirme faux

    soit search_exception table name =
      filtre Hashtbl.find table (E name) avec
      | (Typedtree.Tstr_exception decl) -> decl
      | _ -> affirme faux

    soit search_exception_rebind table name =
      filtre Hashtbl.find table (ER name) avec
      | (Typedtree.Tstr_exn_rebind (_, _, p, _, _)) -> p
      | _ -> affirme faux

    soit search_type_declaration table name =
      filtre Hashtbl.find table (T name) avec
      | (Typedtree.Tstr_type [td]) -> td
      | _ -> affirme faux

    soit search_class_exp table name =
      filtre Hashtbl.find table (C name) avec
      | (Typedtree.Tstr_class [(ci, _, _ )]) ->
          soit ce = ci.ci_expr dans
          (
           essaie
             soit type_decl = search_type_declaration table name dans
             (ce, type_decl.typ_type.Types.type_params)
           avec
             Not_found ->
               (ce, [])
          )
      | _ -> affirme faux

    soit search_class_type_declaration table name =
      filtre Hashtbl.find table (CT name) avec
      | (Typedtree.Tstr_class_type [(_,_,cltype_decl)]) -> cltype_decl
      | _ -> affirme faux

    soit search_value table name = Hashtbl.find table name

    soit search_primitive table name =
      filtre Hashtbl.find table (P name) avec
        Tstr_primitive vd -> vd.val_val.Types.val_type
      | _ -> affirme faux

    soit get_nth_inherit_class_expr cls n =
      soit rec iter cpt = fonction
        | [] ->
            raise Not_found
        | { cf_desc = Typedtree.Tcf_inherit (_, clexp, _, _, _) } :: q ->
            si n = cpt alors clexp sinon iter (cpt+1) q
        | _ :: q ->
            iter cpt q
      dans
      iter 0 cls.Typedtree.cstr_fields

    soit search_attribute_type cls name =
      soit rec iter = fonction
        | [] ->
            raise Not_found
        | { cf_desc = Typedtree.Tcf_val (_, _, ident, Tcfk_concrete (_, exp), _) } :: q
          quand Name.from_ident ident = name ->
            exp.Typedtree.exp_type
        | { cf_desc = Typedtree.Tcf_val (_, _, ident, Tcfk_virtual typ, _) } :: q
          quand Name.from_ident ident = name ->
            typ.Typedtree.ctyp_type
        | _ :: q ->
            iter q
      dans
      iter cls.Typedtree.cstr_fields

    soit class_sig_of_cltype_decl =
      soit rec iter = fonction
        Types.Cty_constr (_, _, cty) -> iter cty
      | Types.Cty_signature s -> s
      | Types.Cty_arrow (_,_, cty) -> iter cty
      dans
      fonc ct_decl -> iter ct_decl.Types.clty_type

   soit search_method_expression cls name =
      soit rec iter = fonction
        | [] ->
            raise Not_found
        | { cf_desc = Typedtree.Tcf_method (label, _, Tcfk_concrete (_, exp)) } :: q quand label.txt = name ->
            exp
        | _ :: q ->
            iter q
      dans
      iter cls.Typedtree.cstr_fields
  fin

module Analyser =
  foncteur (My_ir : Odoc_sig.Info_retriever) ->

  struct
    module Sig = Odoc_sig.Analyser (My_ir)

    (** This variable is used to load a file as a string and retrieve characters from it.*)
    soit file = Sig.file

    (** The name of the analysed file. *)
    soit file_name = Sig.file_name

    (** This function takes two indexes (start and end) and return the string
       corresponding to the indexes in the file global variable. The function
       prepare_file must have been called to fill the file global variable.*)
    soit get_string_of_file = Sig.get_string_of_file

    (** This function loads the given file in the file global variable.
       and sets file_name.*)
    soit prepare_file = Sig.prepare_file

    (** The function used to get the comments in a class. *)
    soit get_comments_in_class = Sig.get_comments_in_class

    (** The function used to get the comments in a module. *)
    soit get_comments_in_module = Sig.get_comments_in_module

    (** This function takes a parameter pattern and builds the
       corresponding [parameter] structure. The f_desc function
       is used to retrieve a parameter description, if any, from
       a parameter name.
    *)
    soit tt_param_info_from_pattern env f_desc pat =
      soit rec iter_pattern pat =
        filtre pat.pat_desc avec
          Typedtree.Tpat_var (ident, _) ->
            soit name = Name.from_ident ident dans
            Simple_name { sn_name = name ;
                          sn_text = f_desc name ;
                          sn_type = Odoc_env.subst_type env pat.pat_type
                        }

        | Typedtree.Tpat_alias (pat, _, _) ->
            iter_pattern pat

        | Typedtree.Tpat_tuple patlist ->
            Tuple
              (List.map iter_pattern patlist,
               Odoc_env.subst_type env pat.pat_type)

        | Typedtree.Tpat_construct (_, cons_desc, _) quand
            (* we give a name to the parameter only if it unit *)
            (filtre cons_desc.cstr_res.desc avec
              Tconstr (p, _, _) ->
                Path.same p Predef.path_unit
            | _ ->
                faux)
          ->
            (* a () argument, it never has description *)
            Simple_name { sn_name = "()" ;
                          sn_text = None ;
                          sn_type = Odoc_env.subst_type env pat.pat_type
                        }

        | _ ->
            (* implicit pattern matching -> anonymous parameter *)
            Simple_name { sn_name = "()" ;
                          sn_text = None ;
                          sn_type = Odoc_env.subst_type env pat.pat_type
                        }
      dans
      iter_pattern pat

    (** Analysis of the parameter of a function. Return a list of t_parameter created from
       the (pattern, expression) structures encountered. *)
    soit rec tt_analyse_function_parameters env current_comment_opt pat_exp_list =
      filtre pat_exp_list avec
        [] ->
          (* This case means we have a 'function' without pattern, that's impossible *)
          raise (Failure "tt_analyse_function_parameters: 'function' without pattern")

      | {c_lhs=pattern_param} :: second_ele :: q ->
          (* implicit pattern matching -> anonymous parameter and no more parameter *)
          (* A VOIR : le label ? *)
          soit parameter = Odoc_parameter.Tuple ([], Odoc_env.subst_type env pattern_param.pat_type) dans
          [ parameter ]

      | {c_lhs=pattern_param; c_rhs=func_body} :: [] ->
          soit parameter =
            tt_param_info_from_pattern
              env
              (Odoc_parameter.desc_from_info_opt current_comment_opt)
              pattern_param

          dans
         (* For optional parameters with a default value, a special treatment is required *)
         (* we look if the name of the parameter we just add is "*opt*", which means
            that there is a let param_name = ... in ... just right now *)
          soit (p, next_exp) =
            filtre parameter avec
              Simple_name { sn_name = "*opt*" } ->
                (
                 (
                  filtre func_body.exp_desc avec
                    Typedtree.Texp_let (_, {vb_pat={pat_desc = Typedtree.Tpat_var (id, _) };
                                            vb_expr=exp} :: _, func_body2) ->
                      soit name = Name.from_ident id dans
                      soit new_param = Simple_name
                          { sn_name = name ;
                            sn_text = Odoc_parameter.desc_from_info_opt current_comment_opt name ;
                            sn_type = Odoc_env.subst_type env exp.exp_type
                          }
                      dans
                      (new_param, func_body2)
                  | _ ->
                      print_DEBUG3 "Pas le bon filtre pour le parametre optionnel avec valeur par defaut.";
                      (parameter, func_body)
                 )
                )
            | _ ->
                (parameter, func_body)
          dans
         (* continue if the body is still a function *)
          filtre next_exp.exp_desc avec
            Texp_function (_, pat_exp_list, _) ->
              p :: (tt_analyse_function_parameters env current_comment_opt pat_exp_list)
          | _ ->
              (* something else ; no more parameter *)
              [ p ]

     (** Analysis of a Tstr_value from the typedtree. Create and return a list of [t_value].
        @raise Failure if an error occurs.*)
     soit tt_analyse_value env current_module_name comment_opt loc pat_exp rec_flag =
       soit (pat, exp) = pat_exp dans
       filtre (pat.pat_desc, exp.exp_desc) avec
         (Typedtree.Tpat_var (ident, _), Typedtree.Texp_function (_, pat_exp_list2, partial)) ->
           (* a new function is defined *)
           soit name_pre = Name.from_ident ident dans
           soit name = Name.parens_if_infix name_pre dans
           soit complete_name = Name.concat current_module_name name dans
           soit code =
              si !Odoc_global.keep_code alors
                Some (get_string_of_file loc.Location.loc_start.Lexing.pos_cnum
                      loc.Location.loc_end.Lexing.pos_cnum)
              sinon
                None
            dans
           (* create the value *)
           soit new_value = {
             val_name = complete_name ;
             val_info = comment_opt ;
             val_type = Odoc_env.subst_type env pat.Typedtree.pat_type ;
             val_recursive = rec_flag = Asttypes.Recursive ;
             val_parameters = tt_analyse_function_parameters env comment_opt pat_exp_list2 ;
             val_code = code ;
             val_loc = { loc_impl = Some loc ; loc_inter = None } ;
           }
           dans
           [ new_value ]

       | (Typedtree.Tpat_var (ident, _), _) ->
           (* a new value is defined *)
           soit name_pre = Name.from_ident ident dans
           soit name = Name.parens_if_infix name_pre dans
           soit complete_name = Name.concat current_module_name name dans
           soit code =
             si !Odoc_global.keep_code alors
                Some (get_string_of_file loc.Location.loc_start.Lexing.pos_cnum
                      loc.Location.loc_end.Lexing.pos_cnum)
             sinon
               None
            dans
           soit new_value = {
             val_name = complete_name ;
             val_info = comment_opt ;
             val_type = Odoc_env.subst_type env pat.Typedtree.pat_type ;
             val_recursive = rec_flag = Asttypes.Recursive ;
             val_parameters = [] ;
             val_code = code ;
             val_loc = { loc_impl = Some loc ; loc_inter = None } ;
           }
           dans
           [ new_value ]

       | (Typedtree.Tpat_tuple lpat, _) ->
           (* new identifiers are defined *)
           (* A VOIR : by now we don't accept to have global variables defined in tuples *)
           []

       | _ ->
           (* something else, we don't care ? A VOIR *)
           []

    (** This function takes a Typedtree.class_expr and returns a string which can stand for the class name.
       The name can be "object ... end" if the class expression is not an ident or a class constraint or a class apply. *)
    soit rec tt_name_of_class_expr clexp =
(*
      (
       match clexp.Typedtree.cl_desc with
         Tclass_ident _ -> prerr_endline "Tclass_ident"
       | Tclass_structure _ -> prerr_endline "Tclass_structure"
       | Tclass_fun _ -> prerr_endline "Tclass_fun"
       | Tclass_apply _ -> prerr_endline "Tclass_apply"
       | Tclass_let _ -> prerr_endline "Tclass_let"
       | Tclass_constraint _ -> prerr_endline "Tclass_constraint"
      );
*)
      filtre clexp.Typedtree.cl_desc avec
        Typedtree.Tcl_ident (p, _, _) -> Name.from_path p
      | Typedtree.Tcl_constraint (class_expr, _, _, _, _)
      | Typedtree.Tcl_apply (class_expr, _) -> tt_name_of_class_expr class_expr
(*
      | Typedtree.Tclass_fun (_, _, class_expr, _) -> tt_name_of_class_expr class_expr
      | Typedtree.Tclass_let (_,_,_, class_expr) -> tt_name_of_class_expr class_expr
*)
      |  _ -> Odoc_messages.object_end

    (** Analysis of a method expression to get the method parameters.
       @param first indicates if we're analysing the method for
       the first time ; in that case we must not keep the first parameter,
       which is "self-*", the object itself.
    *)
    soit rec tt_analyse_method_expression env current_method_name comment_opt ?(first=vrai) exp =
      filtre exp.Typedtree.exp_desc avec
        Typedtree.Texp_function (_, pat_exp_list, _) ->
          (
           filtre pat_exp_list avec
             [] ->
               (* it is not a function since there are no parameters *)
               (* we can't get here normally *)
               raise (Failure (Odoc_messages.bad_tree^" "^(Odoc_messages.method_without_param current_method_name)))
           | l ->
               filtre l avec
                 [] ->
                   (* cas impossible, on l'a filtre avant *)
                   affirme faux
               | {c_lhs=pattern_param} :: second_ele :: q ->
                   (* implicit pattern matching -> anonymous parameter *)
                   (* Note : We can't match this pattern if it is the first call to the function. *)
                   soit new_param = Simple_name
                       { sn_name = "??" ; sn_text =  None;
                         sn_type = Odoc_env.subst_type env pattern_param.Typedtree.pat_type }
                   dans
                   [ new_param ]

               | {c_lhs=pattern_param; c_rhs=body} :: [] ->
                   (* if this is the first call to the function, this is the first parameter and we skip it *)
                   si not first alors
                     (
                      soit parameter =
                        tt_param_info_from_pattern
                          env
                          (Odoc_parameter.desc_from_info_opt comment_opt)
                          pattern_param
                      dans
                      (* For optional parameters with a default value, a special treatment is required. *)
                      (* We look if the name of the parameter we just add is "*opt*", which means
                         that there is a let param_name = ... in ... just right now. *)
                      soit (current_param, next_exp) =
                        filtre parameter avec
                          Simple_name { sn_name = "*opt*"} ->
                            (
                             (
                              filtre body.exp_desc avec
                                Typedtree.Texp_let (_, {vb_pat={pat_desc = Typedtree.Tpat_var (id, _) };
                                                        vb_expr=exp} :: _, body2) ->
                                  soit name = Name.from_ident id dans
                                  soit new_param = Simple_name
                                      { sn_name = name ;
                                        sn_text = Odoc_parameter.desc_from_info_opt comment_opt name ;
                                        sn_type = Odoc_env.subst_type env exp.Typedtree.exp_type ;
                                      }
                                  dans
                                  (new_param, body2)
                              | _ ->
                                  print_DEBUG3 "Pas le bon filtre pour le parametre optionnel avec valeur par defaut.";
                                  (parameter, body)
                             )
                            )
                        | _ ->
                            (* no *opt* parameter, we add the parameter then continue *)
                            (parameter, body)
                      dans
                      current_param :: (tt_analyse_method_expression env current_method_name comment_opt ~first: faux next_exp)
                     )
                   sinon
                     tt_analyse_method_expression env current_method_name comment_opt ~first: faux body
          )
      | _ ->
          (* no more parameter *)
          []

    (** Analysis of a [Parsetree.class_struture] and a [Typedtree.class_structure] to get a couple
       (inherited classes, class elements). *)
    soit analyse_class_structure env current_class_name tt_class_sig last_pos pos_limit p_cls tt_cls table =
      soit rec iter acc_inher acc_fields last_pos = fonction
        | [] ->
            soit s = get_string_of_file last_pos pos_limit dans
            soit (_, ele_coms) = My_ir.all_special !file_name s dans
            soit ele_comments =
              List.fold_left
                (fonc acc -> fonc sc ->
                  filtre sc.Odoc_types.i_desc avec
                    None ->
                      acc
                  | Some t ->
                      acc @ [Class_comment t])
                []
                ele_coms
            dans
            (acc_inher, acc_fields @ ele_comments)
          | item :: q ->
              soit loc = item.Parsetree.pcf_loc dans
              filtre item.Parsetree.pcf_desc avec
        | (Parsetree.Pcf_inherit (_, p_clexp, _))  ->
            soit tt_clexp =
              soit n = List.length acc_inher dans
              essaie Typedtree_search.get_nth_inherit_class_expr tt_cls n
              avec Not_found ->
                raise (Failure (
                       Odoc_messages.inherit_classexp_not_found_in_typedtree n))
            dans
            soit (info_opt, ele_comments) =
              get_comments_in_class last_pos
                p_clexp.Parsetree.pcl_loc.Location.loc_start.Lexing.pos_cnum
            dans
            soit text_opt =
              filtre info_opt avec None -> None
              | Some i -> i.Odoc_types.i_desc dans
            soit name = tt_name_of_class_expr tt_clexp dans
            soit inher =
              {
                ic_name = Odoc_env.full_class_or_class_type_name env name ;
                ic_class = None ;
                ic_text = text_opt ;
              }
            dans
            iter (acc_inher @ [ inher ]) (acc_fields @ ele_comments)
              p_clexp.Parsetree.pcl_loc.Location.loc_end.Lexing.pos_cnum
              q

      | Parsetree.Pcf_val ({ txt = label }, mutable_flag, k) ->
            soit virt = filtre k avec Parsetree.Cfk_virtual _ -> vrai | Parsetree.Cfk_concrete _ -> faux dans
            soit complete_name = Name.concat current_class_name label dans
            soit (info_opt, ele_comments) = get_comments_in_class last_pos loc.Location.loc_start.Lexing.pos_cnum dans
            soit type_exp =
              essaie Typedtree_search.search_attribute_type tt_cls label
              avec Not_found ->
                raise (Failure (Odoc_messages.attribute_not_found_in_typedtree complete_name))
          dans
          soit code =
            si !Odoc_global.keep_code alors
              Some (get_string_of_file loc.Location.loc_start.Lexing.pos_cnum
                    loc.Location.loc_end.Lexing.pos_cnum)
            sinon
              None
          dans
          soit att =
            {
              att_value = { val_name = complete_name ;
                val_info = info_opt ;
                val_type = Odoc_env.subst_type env type_exp ;
                val_recursive = faux ;
                val_parameters = [] ;
                val_code = code ;
                val_loc = { loc_impl = Some loc ; loc_inter = None } ;
              } ;
              att_mutable = mutable_flag = Asttypes.Mutable ;
              att_virtual = virt ;
            }
          dans
          iter acc_inher (acc_fields @ ele_comments @ [ Class_attribute att ]) loc.Location.loc_end.Lexing.pos_cnum q

        | (Parsetree.Pcf_method  ({ txt = label }, private_flag, Parsetree.Cfk_virtual _)) ->
            soit complete_name = Name.concat current_class_name label dans
            soit (info_opt, ele_comments) = get_comments_in_class last_pos loc.Location.loc_start.Lexing.pos_cnum dans
            soit met_type =
              essaie Odoc_sig.Signature_search.search_method_type label tt_class_sig
              avec Not_found -> raise (Failure (Odoc_messages.method_type_not_found current_class_name label))
            dans
            soit real_type =
              filtre met_type.Types.desc avec
              Tarrow (_, _, t, _) ->
                t
            |  _ ->
                (* ?!? : not an arrow type ! return the original type *)
                met_type
          dans
          soit code =
            si !Odoc_global.keep_code alors
              Some (get_string_of_file loc.Location.loc_start.Lexing.pos_cnum
               loc.Location.loc_end.Lexing.pos_cnum)
            sinon
              None
          dans
          soit met =
            {
              met_value = {
                val_name = complete_name ;
                val_info = info_opt ;
                val_type = Odoc_env.subst_type env real_type ;
                val_recursive = faux ;
                val_parameters = [] ;
                val_code = code ;
                val_loc = { loc_impl = Some loc ; loc_inter = None } ;
              } ;
              met_private = private_flag = Asttypes.Private ;
              met_virtual = vrai ;
            }
          dans
          (* update the parameter description *)
          Odoc_value.update_value_parameters_text met.met_value;

          iter acc_inher (acc_fields @ ele_comments @ [ Class_method met ]) loc.Location.loc_end.Lexing.pos_cnum q

        | (Parsetree.Pcf_method ({ txt = label }, private_flag, Parsetree.Cfk_concrete _)) ->
            soit complete_name = Name.concat current_class_name label dans
            soit (info_opt, ele_comments) = get_comments_in_class last_pos loc.Location.loc_start.Lexing.pos_cnum dans
            soit exp =
              essaie Typedtree_search.search_method_expression tt_cls label
            avec Not_found -> raise (Failure (Odoc_messages.method_not_found_in_typedtree complete_name))
          dans
          soit real_type =
            filtre exp.exp_type.desc avec
              Tarrow (_, _, t,_) ->
                t
            |  _ ->
                (* ?!? : not an arrow type ! return the original type *)
                exp.Typedtree.exp_type
          dans
          soit code =
            si !Odoc_global.keep_code alors
                Some (get_string_of_file loc.Location.loc_start.Lexing.pos_cnum
               loc.Location.loc_end.Lexing.pos_cnum)
            sinon
              None
          dans
          soit met =
            {
              met_value = { val_name = complete_name ;
                val_info = info_opt ;
                val_type = Odoc_env.subst_type env real_type ;
                val_recursive = faux ;
                val_parameters = tt_analyse_method_expression env complete_name info_opt exp ;
                val_code = code ;
                val_loc = { loc_impl = Some loc ; loc_inter = None } ;
              } ;
              met_private = private_flag = Asttypes.Private ;
              met_virtual = faux ;
              }
          dans
          (* update the parameter description *)
          Odoc_value.update_value_parameters_text met.met_value;

          iter acc_inher (acc_fields @ ele_comments @ [ Class_method met ]) loc.Location.loc_end.Lexing.pos_cnum q

        | Parsetree.Pcf_constraint (_, _) ->
            (* don't give a $*%@ ! *)
            iter acc_inher acc_fields loc.Location.loc_end.Lexing.pos_cnum q

        | (Parsetree.Pcf_initializer exp) ->
            iter acc_inher acc_fields exp.Parsetree.pexp_loc.Location.loc_end.Lexing.pos_cnum q

        | Parsetree.Pcf_extension _ -> affirme faux
      dans
      iter [] [] last_pos (p_cls.Parsetree.pcstr_fields)

    (** Analysis of a [Parsetree.class_expr] and a [Typedtree.class_expr] to get a a couple (class parameters, class kind). *)
    soit rec analyse_class_kind env current_class_name comment_opt last_pos p_class_expr tt_class_exp table =
      filtre (p_class_expr.Parsetree.pcl_desc, tt_class_exp.Typedtree.cl_desc) avec
        (Parsetree.Pcl_constr (lid, _), tt_class_exp_desc ) ->
          soit name =
            filtre tt_class_exp_desc avec
              Typedtree.Tcl_ident (p,_,_) -> Name.from_path p
            | _ ->
                (* we try to get the name from the environment. *)
                (* A VOIR : dommage qu'on n'ait pas un Tclass_ident :-( meme quand on a class tutu = toto *)
                Name.from_longident lid.txt
          dans
          (* On n'a pas ici les parametres de type sous forme de Types.type_expr,
             par contre on peut les trouver dans le class_type *)
          soit params =
            filtre tt_class_exp.Typedtree.cl_type avec
              Types.Cty_constr (p2, type_exp_list, cltyp) ->
                (* cltyp is the class type for [type_exp_list] p *)
                type_exp_list
            | _ ->
                []
          dans
          ([],
           Class_constr
             {
               cco_name = Odoc_env.full_class_name env name ;
               cco_class = None ;
               cco_type_parameters = List.map (Odoc_env.subst_type env) params ;
             } )

      | (Parsetree.Pcl_structure p_class_structure, Typedtree.Tcl_structure tt_class_structure) ->
          (* we need the class signature to get the type of methods in analyse_class_structure *)
          soit tt_class_sig =
            filtre tt_class_exp.Typedtree.cl_type avec
              Types.Cty_signature class_sig -> class_sig
            | _ -> raise (Failure "analyse_class_kind: no class signature for a class structure.")
          dans
          soit (inherited_classes, class_elements) = analyse_class_structure
              env
              current_class_name
              tt_class_sig
              last_pos
              p_class_expr.Parsetree.pcl_loc.Location.loc_end.Lexing.pos_cnum
              p_class_structure
              tt_class_structure
              table
          dans
          ([],
           Class_structure (inherited_classes, class_elements) )

      | (Parsetree.Pcl_fun (label, expression_opt, pattern, p_class_expr2),
         Typedtree.Tcl_fun (_, pat, ident_exp_list, tt_class_expr2, partial)) ->
           (* we check that this is not an optional parameter with
              a default value. In this case, we look for the good parameter pattern *)
           soit (parameter, next_tt_class_exp) =
             filtre pat.Typedtree.pat_desc avec
               Typedtree.Tpat_var (ident, _) quand Name.from_ident ident = "*opt*" ->
                 (
                  (* there must be a Tcl_let just after *)
                  filtre tt_class_expr2.Typedtree.cl_desc avec
                    Typedtree.Tcl_let (_, {vb_pat={pat_desc = Typedtree.Tpat_var (id,_) };
                                           vb_expr=exp} :: _, _, tt_class_expr3) ->
                      soit name = Name.from_ident id dans
                      soit new_param = Simple_name
                          { sn_name = name ;
                            sn_text = Odoc_parameter.desc_from_info_opt comment_opt name ;
                            sn_type = Odoc_env.subst_type env exp.exp_type
                          }
                      dans
                      (new_param, tt_class_expr3)
                 | _ ->
                     (* strange case *)
                     (* we create the parameter and add it to the class *)
                     raise (Failure "analyse_class_kind: strange case")
                 )
             | _ ->
                 (* no optional parameter with default value, we create the parameter *)
                 soit new_param =
                   tt_param_info_from_pattern
                     env
                     (Odoc_parameter.desc_from_info_opt comment_opt)
                     pat
                 dans
                 (new_param, tt_class_expr2)
           dans
           soit (params, k) = analyse_class_kind
              env current_class_name comment_opt last_pos p_class_expr2
                next_tt_class_exp table
            dans
           (parameter :: params, k)

      | (Parsetree.Pcl_apply (p_class_expr2, _), Tcl_apply (tt_class_expr2, exp_opt_optional_list)) ->
          soit applied_name =
            (* we want an ident, or else the class applied will appear in the form object ... end,
               because if the class applied has no name, the code is kinda ugly, isn't it ? *)
            filtre tt_class_expr2.Typedtree.cl_desc avec
              Typedtree.Tcl_ident (p,_,_) -> Name.from_path p (* A VOIR : obtenir le nom complet *)
            | _ ->
                (* A VOIR : dommage qu'on n'ait pas un Tclass_ident :-( meme quand on a class tutu = toto *)
                filtre p_class_expr2.Parsetree.pcl_desc avec
                  Parsetree.Pcl_constr (lid, _) ->
                    (* we try to get the name from the environment. *)
                    Name.from_longident lid.txt
                |  _ ->
                    Odoc_messages.object_end
          dans
          soit param_exps = List.fold_left
              (fonc acc -> fonc (_, exp_opt, _) ->
                filtre exp_opt avec
                  None -> acc
                | Some e -> acc @ [e])
              []
              exp_opt_optional_list
          dans
          soit param_types = List.map (fonc e -> e.Typedtree.exp_type) param_exps dans
          soit params_code =
            List.map
              (fonc e -> get_string_of_file
                  e.exp_loc.Location.loc_start.Lexing.pos_cnum
                  e.exp_loc.Location.loc_end.Lexing.pos_cnum)
              param_exps
          dans
          ([],
           Class_apply
             { capp_name = Odoc_env.full_class_name env applied_name ;
               capp_class = None ;
               capp_params = param_types ;
               capp_params_code = params_code ;
             } )

      | (Parsetree.Pcl_let (_, _, p_class_expr2), Typedtree.Tcl_let (_, _, _, tt_class_expr2)) ->
          (* we don't care about these lets *)
          analyse_class_kind
              env current_class_name comment_opt last_pos p_class_expr2
              tt_class_expr2 table

      | (Parsetree.Pcl_constraint (p_class_expr2, p_class_type2),
         Typedtree.Tcl_constraint (tt_class_expr2, _, _, _, _)) ->
          soit (l, class_kind) = analyse_class_kind
              env current_class_name comment_opt last_pos p_class_expr2
                tt_class_expr2 table
            dans
            (* A VOIR : analyse du class type ? on n'a pas toutes les infos. cf. Odoc_sig.analyse_class_type_kind *)
          soit class_type_kind =
            (*Sig.analyse_class_type_kind
              env
              ""
              p_class_type2.Parsetree.pcty_loc.Location.loc_start.Lexing.pos_cnum
              p_class_type2
              tt_class_expr2.Typedtree.cl_type
            *)
            Class_type { cta_name = Odoc_messages.object_end ;
                         cta_class = None ; cta_type_parameters = [] }
          dans
          (l, Class_constraint (class_kind, class_type_kind))

      | _ ->
          raise (Failure "analyse_class_kind: Parsetree and typedtree don't match.")

    (** Analysis of a [Parsetree.class_declaration] and a [Typedtree.class_expr] to return a [t_class].*)
    soit analyse_class env current_module_name comment_opt p_class_decl tt_type_params tt_class_exp table =
      soit name = p_class_decl.Parsetree.pci_name dans
      soit complete_name = Name.concat current_module_name name.txt dans
      soit loc = p_class_decl.Parsetree.pci_expr.Parsetree.pcl_loc dans
      soit pos_start = loc.Location.loc_start.Lexing.pos_cnum dans
      soit type_parameters = tt_type_params dans
      soit virt = p_class_decl.Parsetree.pci_virt = Asttypes.Virtual dans
      soit cltype = Odoc_env.subst_class_type env tt_class_exp.Typedtree.cl_type dans
      soit (parameters, kind) = analyse_class_kind
          env
          complete_name
          comment_opt
          pos_start
          p_class_decl.Parsetree.pci_expr
          tt_class_exp
          table
      dans
      soit cl =
        {
          cl_name = complete_name ;
          cl_info = comment_opt ;
          cl_type = cltype ;
          cl_virtual = virt ;
          cl_type_parameters = type_parameters ;
          cl_kind = kind ;
          cl_parameters = parameters ;
          cl_loc = { loc_impl = Some loc ; loc_inter = None } ;
        }
      dans
      cl

    (** Get a name from a module expression, or "struct ... end" if the module expression
       is not an ident of a constraint on an ident. *)
    soit rec tt_name_from_module_expr mod_expr =
      filtre mod_expr.Typedtree.mod_desc avec
        Typedtree.Tmod_ident (p,_) -> Name.from_path p
      | Typedtree.Tmod_constraint (m_exp, _, _, _) -> tt_name_from_module_expr m_exp
      | Typedtree.Tmod_structure _
      | Typedtree.Tmod_functor _
      | Typedtree.Tmod_apply _
      | Typedtree.Tmod_unpack _ ->
          Odoc_messages.struct_end

    (** Get the list of included modules in a module structure of a typed tree. *)
    soit tt_get_included_module_list tt_structure =
      soit f acc item =
        filtre item.str_desc avec
          Typedtree.Tstr_include (mod_expr, _, _) ->
            acc @ [
                  { (* A VOIR : chercher dans les modules et les module types, avec quel env ? *)
                    im_name = tt_name_from_module_expr mod_expr ;
                    im_module = None ;
                    im_info = None ;
                  }
                ]
        | _ ->
            acc
      dans
      List.fold_left f [] tt_structure.str_items

    (** This function takes a [module element list] of a module and replaces the "dummy" included modules with
       the ones found in typed tree structure of the module. *)
    soit replace_dummy_included_modules module_elements included_modules =
      soit rec f = fonction
        | ([], _) ->
            []
        | ((Element_included_module im) :: q, (im_repl :: im_q)) ->
            (Element_included_module { im_repl avec im_info = im.im_info })
            :: (f (q, im_q))
        | ((Element_included_module im) :: q, []) ->
            (Element_included_module im) :: q
        | (ele :: q, l) ->
            ele :: (f (q, l))
      dans
      f (module_elements, included_modules)

    (** This function removes the elements of the module which does not
       belong to the given module type, if the module type is expanded
       and the module has a "structure" kind. *)
    soit rec filter_module_with_module_type_constraint m mt =
      filtre m.m_kind, mt avec
        Module_struct l, Types.Mty_signature lsig ->
          m.m_kind <- Module_struct (filter_module_elements_with_module_type_constraint l lsig);
          m.m_type <- mt;
      | _ -> ()

    (** This function removes the elements of the module type which does not
       belong to the given module type, if the module type is expanded
       and the module type has a "structure" kind. *)
    et filter_module_type_with_module_type_constraint mtyp mt =
      filtre mtyp.mt_kind, mt avec
        Some Module_type_struct l, Types.Mty_signature lsig ->
          mtyp.mt_kind <- Some (Module_type_struct (filter_module_elements_with_module_type_constraint l lsig));
          mtyp.mt_type <- Some mt;
      | _ -> ()

    et filter_module_elements_with_module_type_constraint l lsig =
      soit pred ele =
        soit f = filtre ele avec
          Element_module m ->
            (fonction
                Types.Sig_module (ident,md,_) ->
                  soit n1 = Name.simple m.m_name
                  et n2 = Ident.name ident dans
                  (
                   filtre n1 = n2 avec
                     vrai -> filter_module_with_module_type_constraint m md.md_type; vrai
                   | faux -> faux
                  )
              | _ -> faux)
        | Element_module_type mt ->
            (fonction
                Types.Sig_modtype (ident,{Types.mtd_type=Some t}) ->
                  soit n1 = Name.simple mt.mt_name
                  et n2 = Ident.name ident dans
                  (
                   filtre n1 = n2 avec
                     vrai -> filter_module_type_with_module_type_constraint mt t; vrai
                   | faux -> faux
                  )
              | _ -> faux)
        | Element_value v ->
            (fonction
                Types.Sig_value (ident,_) ->
                  soit n1 = Name.simple v.val_name
                  et n2 = Ident.name ident dans
                  n1 = n2
              | _ -> faux)
        | Element_type t ->
             (fonction
                Types.Sig_type (ident,_,_) ->
                  (* A VOIR: il est possible que le detail du type soit cache *)
                  soit n1 = Name.simple t.ty_name
                  et n2 = Ident.name ident dans
                  n1 = n2
               | _ -> faux)
        | Element_exception e ->
            (fonction
                Types.Sig_exception (ident,_) ->
                  soit n1 = Name.simple e.ex_name
                  et n2 = Ident.name ident dans
                  n1 = n2
              | _ -> faux)
        | Element_class c ->
            (fonction
                Types.Sig_class (ident,_,_) ->
                  soit n1 = Name.simple c.cl_name
                  et n2 = Ident.name ident dans
                  n1 = n2
              | _ -> faux)
        | Element_class_type ct ->
            (fonction
                Types.Sig_class_type (ident,_,_) ->
                  soit n1 = Name.simple ct.clt_name
                  et n2 = Ident.name ident dans
                  n1 = n2
              | _ -> faux)
        | Element_module_comment _ -> fonc _ -> vrai
        | Element_included_module _ -> fonc _ -> vrai
        dans
        List.exists f lsig
      dans
      List.filter pred l

    (** Analysis of a parse tree structure with a typed tree, to return module elements.*)
    soit rec analyse_structure env current_module_name last_pos pos_limit parsetree typedtree =
      print_DEBUG "Odoc_ast:analyse_struture";
      soit (table, table_values) = Typedtree_search.tables typedtree.str_items dans
      soit rec iter env last_pos = fonction
          [] ->
            soit s = get_string_of_file last_pos pos_limit dans
            soit (_, ele_coms) = My_ir.all_special !file_name s dans
            soit ele_comments =
              List.fold_left
                (fonc acc -> fonc sc ->
                  filtre sc.Odoc_types.i_desc avec
                    None ->
                      acc
                  | Some t ->
                      acc @ [Element_module_comment t])
                []
                ele_coms
            dans
            ele_comments
        | item :: q ->
            soit (comment_opt, ele_comments) =
              get_comments_in_module last_pos item.Parsetree.pstr_loc.Location.loc_start.Lexing.pos_cnum
            dans
            soit pos_limit2 =
              filtre q avec
                [] -> pos_limit
              | item2 :: _ -> item2.Parsetree.pstr_loc.Location.loc_start.Lexing.pos_cnum
            dans
            soit (maybe_more, new_env, elements) = analyse_structure_item
                env
                current_module_name
                item.Parsetree.pstr_loc
                pos_limit2
                comment_opt
                item.Parsetree.pstr_desc
                typedtree
                table
                table_values
            dans
            ele_comments @ elements @ (iter new_env (item.Parsetree.pstr_loc.Location.loc_end.Lexing.pos_cnum + maybe_more) q)
      dans
      iter env last_pos parsetree

   (** Analysis of a parse tree structure item to obtain a new environment and a list of elements.*)
   et analyse_structure_item env current_module_name loc pos_limit comment_opt parsetree_item_desc typedtree
        table table_values =
      print_DEBUG "Odoc_ast:analyse_struture_item";
      filtre parsetree_item_desc avec
        Parsetree.Pstr_eval _ ->
          (* don't care *)
          (0, env, [])
      | Parsetree.Pstr_attribute _
      | Parsetree.Pstr_extension _ ->
          (0, env, [])
      | Parsetree.Pstr_value (rec_flag, pat_exp_list) ->
          (* of rec_flag * (pattern * expression) list *)
          (* For each value, look for the value name, then look in the
             typedtree for the corresponding information,
             at last analyse this information to build the value *)
          soit rec iter_pat = fonction
            | Parsetree.Ppat_any -> None
            | Parsetree.Ppat_var name -> Some name
            | Parsetree.Ppat_tuple _ -> None (* A VOIR quand on traitera les tuples *)
            | Parsetree.Ppat_constraint (pat, _) -> iter_pat pat.Parsetree.ppat_desc
            | _ -> None
          dans
          soit rec iter ?(first=faux) last_pos acc_env acc p_e_list =
            filtre p_e_list avec
              [] ->
                (acc_env, acc)
            | {Parsetree.pvb_pat=pat; pvb_expr=exp} :: q ->
                soit value_name_opt = iter_pat pat.Parsetree.ppat_desc dans
                soit new_last_pos = exp.Parsetree.pexp_loc.Location.loc_end.Lexing.pos_cnum dans
                filtre value_name_opt avec
                  None ->
                    iter new_last_pos acc_env acc q
                | Some name ->
                    essaie
                      soit pat_exp = Typedtree_search.search_value table_values name.txt dans
                      soit (info_opt, ele_comments) =
                        (* we already have the optional comment for the first value. *)
                        si first alors
                          (comment_opt, [])
                        sinon
                          get_comments_in_module
                            last_pos
                            pat.Parsetree.ppat_loc.Location.loc_start.Lexing.pos_cnum
                      dans
                      soit l_values = tt_analyse_value
                          env
                          current_module_name
                          info_opt
                          loc
                          pat_exp
                          rec_flag
                      dans
                      soit new_env = List.fold_left
                          (fonc e -> fonc v ->
                            Odoc_env.add_value e v.val_name
                          )
                          acc_env
                          l_values
                      dans
                      soit l_ele = List.map (fonc v -> Element_value v) l_values dans
                      iter
                        new_last_pos
                        new_env
                        (acc @ ele_comments @ l_ele)
                        q
                    avec
                      Not_found ->
                        iter new_last_pos acc_env acc q
          dans
          soit (new_env, l_ele) = iter ~first: vrai loc.Location.loc_start.Lexing.pos_cnum env [] pat_exp_list dans
          (0, new_env, l_ele)

      | Parsetree.Pstr_primitive val_desc ->
            soit name_pre = val_desc.Parsetree.pval_name.txt dans
            (* of string * value_description *)
            print_DEBUG ("Parsetree.Pstr_primitive ("^name_pre^", ["^(String.concat ", " val_desc.Parsetree.pval_prim)^"]");
            soit typ = Typedtree_search.search_primitive table name_pre dans
            soit name = Name.parens_if_infix name_pre dans
            soit complete_name = Name.concat current_module_name name dans
            soit code =
              si !Odoc_global.keep_code alors
                Some (get_string_of_file loc.Location.loc_start.Lexing.pos_cnum
                      loc.Location.loc_end.Lexing.pos_cnum)
              sinon
                None
            dans
            soit new_value = {
                val_name = complete_name ;
                val_info = comment_opt ;
                val_type = Odoc_env.subst_type env typ ;
                val_recursive = faux ;
                val_parameters = [] ;
                val_code = code ;
                val_loc = { loc_impl = Some loc ; loc_inter = None } ;
              }
            dans
            soit new_env = Odoc_env.add_value env new_value.val_name dans
            (0, new_env, [Element_value new_value])

      | Parsetree.Pstr_type name_typedecl_list ->
          (* of (string * type_declaration) list *)
          (* we start by extending the environment *)
          soit new_env =
            List.fold_left
              (fonc acc_env {Parsetree.ptype_name = { txt = name }} ->
                soit complete_name = Name.concat current_module_name name dans
                Odoc_env.add_type acc_env complete_name
              )
              env
              name_typedecl_list
          dans
          soit rec f ?(first=faux) maybe_more_acc last_pos name_type_decl_list =
            filtre name_type_decl_list avec
              [] -> (maybe_more_acc, [])
            | type_decl :: q ->
                soit name = type_decl.Parsetree.ptype_name.txt dans
                soit complete_name = Name.concat current_module_name name dans
                soit loc = type_decl.Parsetree.ptype_loc dans
                soit loc_start = loc.Location.loc_start.Lexing.pos_cnum dans
                soit loc_end =  loc.Location.loc_end.Lexing.pos_cnum dans
                soit pos_limit2 =
                  filtre q avec
                      [] -> pos_limit
                    | td :: _ -> td.Parsetree.ptype_loc.Location.loc_start.Lexing.pos_cnum
                  dans
                  soit (maybe_more, name_comment_list) =
                    Sig.name_comment_from_type_kind
                    loc_end
                    pos_limit2
                    type_decl.Parsetree.ptype_kind
                  dans
                  soit tt_type_decl =
                    essaie Typedtree_search.search_type_declaration table name
                    avec Not_found -> raise (Failure (Odoc_messages.type_not_found_in_typedtree complete_name))
                  dans
                  soit tt_type_decl = tt_type_decl.Typedtree.typ_type dans
                  soit (com_opt, ele_comments) = (* the comment for the first type was already retrieved *)
                    si first alors
                      (comment_opt , [])
                    sinon
                      get_comments_in_module last_pos loc_start
                  dans
                  soit kind = Sig.get_type_kind
                    new_env name_comment_list
                    tt_type_decl.Types.type_kind
                  dans
                  soit new_end = loc_end + maybe_more dans
                  soit t =
                    {
                      ty_name = complete_name ;
                      ty_info = com_opt ;
                      ty_parameters =
                      List.map2
                       (fonc p v ->
                         soit (co, cn) = Types.Variance.get_upper v dans
                         (Odoc_env.subst_type new_env p, co, cn))
                       tt_type_decl.Types.type_params
                       tt_type_decl.Types.type_variance ;
                      ty_kind = kind ;
                      ty_private = tt_type_decl.Types.type_private;
                      ty_manifest =
                        (filtre tt_type_decl.Types.type_manifest avec
                           None -> None
                         | Some t -> Some (Odoc_env.subst_type new_env t));
                      ty_loc = { loc_impl = Some loc ; loc_inter = None } ;
                      ty_code =
                      (
                       si !Odoc_global.keep_code alors
                         Some (get_string_of_file loc_start new_end)
                       sinon
                         None
                      ) ;
                    }
                  dans
                  soit (maybe_more2, info_after_opt) =
                    My_ir.just_after_special
                    !file_name
                    (get_string_of_file new_end pos_limit2)
                  dans
                  t.ty_info <- Sig.merge_infos t.ty_info info_after_opt ;
                  soit (maybe_more3, eles) = f (maybe_more + maybe_more2) (new_end + maybe_more2) q dans
                  (maybe_more3, ele_comments @ ((Element_type t) :: eles))
            dans
            soit (maybe_more, eles) = f ~first: vrai 0 loc.Location.loc_start.Lexing.pos_cnum name_typedecl_list dans
            (maybe_more, new_env, eles)

      | Parsetree.Pstr_exception excep_decl ->
          soit name = excep_decl.Parsetree.pcd_name dans
          (* a new exception is defined *)
          soit complete_name = Name.concat current_module_name name.txt dans
          (* we get the exception declaration in the typed tree *)
          soit tt_excep_decl =
            essaie Typedtree_search.search_exception table name.txt
            avec Not_found ->
              raise (Failure (Odoc_messages.exception_not_found_in_typedtree complete_name))
          dans
          soit new_env = Odoc_env.add_exception env complete_name dans
          soit loc_start = loc.Location.loc_start.Lexing.pos_cnum dans
          soit loc_end =  loc.Location.loc_end.Lexing.pos_cnum dans
          soit new_ex =
            {
              ex_name = complete_name ;
              ex_info = comment_opt ;
              ex_args = List.map (fonc ctyp ->
                Odoc_env.subst_type new_env ctyp.ctyp_type)
                tt_excep_decl.cd_args;
              ex_alias = None ;
              ex_loc = { loc_impl = Some loc ; loc_inter = None } ;
              ex_code =
                (
                 si !Odoc_global.keep_code alors
                   Some (get_string_of_file loc_start loc_end)
                 sinon
                   None
                ) ;
            }
          dans
          (0, new_env, [ Element_exception new_ex ])

      | Parsetree.Pstr_exn_rebind (name,  _, _) ->
          (* a new exception is defined *)
          soit complete_name = Name.concat current_module_name name.txt dans
          (* we get the exception rebind in the typed tree *)
          soit tt_path =
            essaie Typedtree_search.search_exception_rebind table name.txt
            avec Not_found ->
              raise (Failure (Odoc_messages.exception_not_found_in_typedtree complete_name))
          dans
          soit new_env = Odoc_env.add_exception env complete_name dans
          soit new_ex =
            {
              ex_name = complete_name ;
              ex_info = comment_opt ;
              ex_args = [] ;
              ex_alias = Some { ea_name = (Odoc_env.full_exception_name env (Name.from_path tt_path)) ;
                                ea_ex = None ; } ;
              ex_loc = { loc_impl = Some loc ; loc_inter = None } ;
              ex_code = None ;
            }
          dans
          (0, new_env, [ Element_exception new_ex ])

      | Parsetree.Pstr_module {Parsetree.pmb_name=name; pmb_expr=module_expr} ->
          (
           (* of string * module_expr *)
           essaie
             soit tt_module_expr = Typedtree_search.search_module table name.txt dans
             soit new_module_pre = analyse_module
                 env
                 current_module_name
                 name.txt
                 comment_opt
                 module_expr
                 tt_module_expr
             dans
             soit code =
               si !Odoc_global.keep_code alors
                 soit loc = module_expr.Parsetree.pmod_loc dans
                 soit st = loc.Location.loc_start.Lexing.pos_cnum dans
                 soit en = loc.Location.loc_end.Lexing.pos_cnum dans
                 Some (get_string_of_file st en)
               sinon
                 None
             dans
             soit new_module =
               { new_module_pre avec m_code = code }
             dans
             soit new_env = Odoc_env.add_module env new_module.m_name dans
             soit new_env2 =
               filtre new_module.m_type avec
                 (* A VOIR : cela peut-il etre Tmty_ident ? dans ce cas, on aurait pas la signature *)
                 Types.Mty_signature s ->
                   Odoc_env.add_signature new_env new_module.m_name
                     ~rel: (Name.simple new_module.m_name) s
               | _ ->
                   new_env
             dans
             (0, new_env2, [ Element_module new_module ])
           avec
             Not_found ->
               soit complete_name = Name.concat current_module_name name.txt dans
               raise (Failure (Odoc_messages.module_not_found_in_typedtree complete_name))
          )

      | Parsetree.Pstr_recmodule mods ->
          (* A VOIR ICI pb: pas de lien avec les module type
             dans les contraintes sur les modules *)
          soit new_env =
            List.fold_left
              (fonc acc_env {Parsetree.pmb_name=name;pmb_expr=mod_exp} ->
                soit complete_name = Name.concat current_module_name name.txt dans
                soit e = Odoc_env.add_module acc_env complete_name dans
                soit tt_mod_exp =
                  essaie Typedtree_search.search_module table name.txt
                  avec Not_found -> raise (Failure (Odoc_messages.module_not_found_in_typedtree complete_name))
                dans
                soit new_module = analyse_module
                    e
                    current_module_name
                    name.txt
                    None
                    mod_exp
                    tt_mod_exp
                dans
                filtre new_module.m_type avec
                  Types.Mty_signature s ->
                    Odoc_env.add_signature e new_module.m_name
                      ~rel: (Name.simple new_module.m_name) s
                  | _ ->
                      e
              )
              env
              mods
          dans
          soit rec f ?(first=faux) last_pos name_mod_exp_list =
            filtre name_mod_exp_list avec
              [] -> []
            | {Parsetree.pmb_name=name;pmb_expr=mod_exp} :: q ->
                soit complete_name = Name.concat current_module_name name.txt dans
                soit loc_start = mod_exp.Parsetree.pmod_loc.Location.loc_start.Lexing.pos_cnum dans
                soit loc_end =  mod_exp.Parsetree.pmod_loc.Location.loc_end.Lexing.pos_cnum dans
                soit tt_mod_exp =
                  essaie Typedtree_search.search_module table name.txt
                  avec Not_found -> raise (Failure (Odoc_messages.module_not_found_in_typedtree complete_name))
                dans
                soit (com_opt, ele_comments) = (* the comment for the first type was already retrieved *)
                  si first alors
                    (comment_opt, [])
                  sinon
                    get_comments_in_module last_pos loc_start
                dans
                soit new_module = analyse_module
                    new_env
                    current_module_name
                    name.txt
                    com_opt
                    mod_exp
                    tt_mod_exp
                dans
                soit eles = f loc_end q dans
                ele_comments @ ((Element_module new_module) :: eles)
          dans
          soit eles = f ~first: vrai loc.Location.loc_start.Lexing.pos_cnum mods dans
          (0, new_env, eles)

      | Parsetree.Pstr_modtype {Parsetree.pmtd_name=name; pmtd_type=modtype} ->
          soit complete_name = Name.concat current_module_name name.txt dans
          soit tt_module_type =
            essaie Typedtree_search.search_module_type table name.txt
            avec Not_found ->
              raise (Failure (Odoc_messages.module_type_not_found_in_typedtree complete_name))
          dans
          soit kind, sig_mtype =
            filtre modtype, tt_module_type.mtd_type avec
            | Some modtype, Some mty_type ->
                Some (Sig.analyse_module_type_kind env complete_name
                        modtype mty_type.mty_type),
                Some mty_type.mty_type
            | _ -> None, None
          dans
          soit mt =
            {
              mt_name = complete_name ;
              mt_info = comment_opt ;
              mt_type = sig_mtype ;
              mt_is_interface = faux ;
              mt_file = !file_name ;
              mt_kind = kind ;
              mt_loc = { loc_impl = Some loc ; loc_inter = None } ;
            }
          dans
          soit new_env = Odoc_env.add_module_type env mt.mt_name dans
          soit new_env2 =
            filtre sig_mtype avec
              (* A VOIR : cela peut-il etre Tmty_ident ? dans ce cas, on n'aurait pas la signature *)
              Some (Types.Mty_signature s) ->
                Odoc_env.add_signature new_env mt.mt_name ~rel: (Name.simple mt.mt_name) s
            | _ ->
                new_env
          dans
          (0, new_env2, [ Element_module_type mt ])

      | Parsetree.Pstr_open (_ovf, longident, _attrs) ->
          (* A VOIR : enrichir l'environnement quand open ? *)
          soit ele_comments = filtre comment_opt avec
            None -> []
          | Some i ->
              filtre i.i_desc avec
                None -> []
              | Some t -> [Element_module_comment t]
          dans
          (0, env, ele_comments)

      | Parsetree.Pstr_class class_decl_list ->
          (* we start by extending the environment *)
          soit new_env =
            List.fold_left
              (fonc acc_env -> fonc class_decl ->
                soit complete_name = Name.concat current_module_name class_decl.Parsetree.pci_name.txt dans
                Odoc_env.add_class acc_env complete_name
              )
              env
              class_decl_list
          dans
          soit rec f ?(first=faux) last_pos class_decl_list =
            filtre class_decl_list avec
              [] ->
                []
            | class_decl :: q ->
                soit (tt_class_exp, tt_type_params) =
                  essaie Typedtree_search.search_class_exp table class_decl.Parsetree.pci_name.txt
                  avec Not_found ->
                    soit complete_name = Name.concat current_module_name class_decl.Parsetree.pci_name.txt dans
                    raise (Failure (Odoc_messages.class_not_found_in_typedtree complete_name))
                dans
                soit (com_opt, ele_comments) =
                  si first alors
                    (comment_opt, [])
                  sinon
                    get_comments_in_module last_pos class_decl.Parsetree.pci_loc.Location.loc_start.Lexing.pos_cnum
                dans
                soit last_pos2 = class_decl.Parsetree.pci_loc.Location.loc_end.Lexing.pos_cnum dans
                soit new_class = analyse_class
                    new_env
                    current_module_name
                    com_opt
                    class_decl
                    tt_type_params
                    tt_class_exp
                    table
                dans
                ele_comments @ ((Element_class new_class) :: (f last_pos2 q))
          dans
          (0, new_env, f ~first: vrai loc.Location.loc_start.Lexing.pos_cnum class_decl_list)

      | Parsetree.Pstr_class_type class_type_decl_list ->
          (* we start by extending the environment *)
          soit new_env =
            List.fold_left
              (fonc acc_env -> fonc class_type_decl ->
                soit complete_name = Name.concat current_module_name class_type_decl.Parsetree.pci_name.txt dans
                Odoc_env.add_class_type acc_env complete_name
              )
              env
              class_type_decl_list
          dans
          soit rec f ?(first=faux) last_pos class_type_decl_list =
            filtre class_type_decl_list avec
              [] ->
                []
            | class_type_decl :: q ->
                soit name = class_type_decl.Parsetree.pci_name dans
                soit complete_name = Name.concat current_module_name name.txt dans
                soit virt = class_type_decl.Parsetree.pci_virt = Asttypes.Virtual dans
                soit tt_cltype_declaration =
                  essaie Typedtree_search.search_class_type_declaration table name.txt
                  avec Not_found ->
                    raise (Failure (Odoc_messages.class_type_not_found_in_typedtree complete_name))
                  dans
                  soit tt_cltype_declaration = tt_cltype_declaration.ci_type_decl dans
                soit type_params = tt_cltype_declaration.Types.clty_params dans
                soit kind = Sig.analyse_class_type_kind
                    new_env
                    complete_name
                    class_type_decl.Parsetree.pci_loc.Location.loc_start.Lexing.pos_cnum
                    class_type_decl.Parsetree.pci_expr
                    tt_cltype_declaration.Types.clty_type
                dans
                soit (com_opt, ele_comments) =
                  si first alors
                    (comment_opt, [])
                  sinon
                    get_comments_in_module last_pos class_type_decl.Parsetree.pci_loc.Location.loc_start.Lexing.pos_cnum
                dans
                soit last_pos2 = class_type_decl.Parsetree.pci_loc.Location.loc_end.Lexing.pos_cnum dans
                soit new_ele =
                  Element_class_type
                    {
                      clt_name = complete_name ;
                      clt_info = com_opt ;
                      clt_type = Odoc_env.subst_class_type env tt_cltype_declaration.Types.clty_type ;
                      clt_type_parameters = List.map (Odoc_env.subst_type new_env) type_params ;
                      clt_virtual = virt ;
                      clt_kind = kind ;
                      clt_loc = { loc_impl = Some loc ;
                                  loc_inter = None } ;
                    }
                dans
                ele_comments @ (new_ele :: (f last_pos2 q))
          dans
          (0, new_env, f ~first: vrai loc.Location.loc_start.Lexing.pos_cnum class_type_decl_list)

      | Parsetree.Pstr_include (module_expr, _attrs) ->
          (* we add a dummy included module which will be replaced by a correct
             one at the end of the module analysis,
             to use the Path.t of the included modules in the typdtree. *)
          soit im =
            {
              im_name = "dummy" ;
              im_module = None ;
              im_info = comment_opt ;
            }
          dans
          (0, env, [ Element_included_module im ]) (* A VOIR : etendre l'environnement ? avec quoi ? *)

     (** Analysis of a [Parsetree.module_expr] and a name to return a [t_module].*)
     et analyse_module env current_module_name module_name comment_opt p_module_expr tt_module_expr =
      soit complete_name = Name.concat current_module_name module_name dans
      soit loc = p_module_expr.Parsetree.pmod_loc dans
      soit pos_start = loc.Location.loc_start.Lexing.pos_cnum dans
      soit pos_end = loc.Location.loc_end.Lexing.pos_cnum dans
      soit modtype =
        (* A VOIR : Odoc_env.subst_module_type env  ? *)
        tt_module_expr.Typedtree.mod_type
      dans
      soit m_code_intf =
        filtre p_module_expr.Parsetree.pmod_desc avec
          Parsetree.Pmod_constraint (_, pmodule_type) ->
            soit loc_start = pmodule_type.Parsetree.pmty_loc.Location.loc_start.Lexing.pos_cnum dans
            soit loc_end = pmodule_type.Parsetree.pmty_loc.Location.loc_end.Lexing.pos_cnum dans
            Some (get_string_of_file loc_start loc_end)
        | _ ->
            None
      dans
      soit m_base =
        {
          m_name = complete_name ;
          m_type = modtype ;
          m_info = comment_opt ;
          m_is_interface = faux ;
          m_file = !file_name ;
          m_kind = Module_struct [] ;
          m_loc = { loc_impl = Some loc ; loc_inter = None } ;
          m_top_deps = [] ;
          m_code = None ; (* code is set by the caller, after the module is created *)
          m_code_intf = m_code_intf ;
          m_text_only = faux ;
      }
      dans
      filtre (p_module_expr.Parsetree.pmod_desc, tt_module_expr.Typedtree.mod_desc) avec
        (Parsetree.Pmod_ident longident, Typedtree.Tmod_ident (path, _)) ->
          soit alias_name = Odoc_env.full_module_name env (Name.from_path path) dans
          { m_base avec m_kind = Module_alias { ma_name = alias_name ;
                                                ma_module = None ; } }

      | (Parsetree.Pmod_structure p_structure, Typedtree.Tmod_structure tt_structure) ->
          soit elements = analyse_structure env complete_name pos_start pos_end p_structure tt_structure dans
          (* we must complete the included modules *)
          soit included_modules_from_tt = tt_get_included_module_list tt_structure dans
          soit elements2 = replace_dummy_included_modules elements included_modules_from_tt dans
          { m_base avec m_kind = Module_struct elements2 }

      | (Parsetree.Pmod_functor (_, pmodule_type, p_module_expr2),
         Typedtree.Tmod_functor (ident, _, mtyp, tt_module_expr2)) ->
           soit loc = filtre pmodule_type avec None -> Location.none
                     | Some pmty -> pmty.Parsetree.pmty_loc dans
           soit loc_start = loc.Location.loc_start.Lexing.pos_cnum dans
           soit loc_end = loc.Location.loc_end.Lexing.pos_cnum dans
           soit mp_type_code = get_string_of_file loc_start loc_end dans
           print_DEBUG (Printf.sprintf "mp_type_code=%s" mp_type_code);
           soit mp_name = Name.from_ident ident dans
           soit mp_kind =
             filtre pmodule_type, mtyp avec
               Some pmty, Some mty ->
                 Sig.analyse_module_type_kind env current_module_name pmty
                   mty.mty_type
             | _ -> Module_type_struct []
           dans
           soit param =
             {
               mp_name = mp_name ;
               mp_type = Misc.may_map
                (fonc m -> Odoc_env.subst_module_type env m.mty_type) mtyp ;
               mp_type_code = mp_type_code ;
               mp_kind = mp_kind ;
             }
           dans
           soit dummy_complete_name = (*Name.concat "__"*) param.mp_name dans
           (* TODO: A VOIR CE __ *)
           soit new_env = Odoc_env.add_module env dummy_complete_name dans
           soit m_base2 = analyse_module
               new_env
               current_module_name
               module_name
               None
               p_module_expr2
               tt_module_expr2
           dans
           soit kind = m_base2.m_kind dans
           { m_base avec m_kind = Module_functor (param, kind) }

      | (Parsetree.Pmod_apply (p_module_expr1, p_module_expr2),
         Typedtree.Tmod_apply (tt_module_expr1, tt_module_expr2, _))
      | (Parsetree.Pmod_apply (p_module_expr1, p_module_expr2),
         Typedtree.Tmod_constraint
           ({ Typedtree.mod_desc = Typedtree.Tmod_apply (tt_module_expr1, tt_module_expr2, _)}, _,
            _, _)
        ) ->
          soit m1 = analyse_module
              env
              current_module_name
              module_name
              None
              p_module_expr1
              tt_module_expr1
          dans
          soit m2 = analyse_module
              env
              current_module_name
              module_name
              None
              p_module_expr2
              tt_module_expr2
          dans
          { m_base avec m_kind = Module_apply (m1.m_kind, m2.m_kind) }

      | (Parsetree.Pmod_constraint (p_module_expr2, p_modtype),
         Typedtree.Tmod_constraint (tt_module_expr2, tt_modtype, _, _)) ->
          print_DEBUG ("Odoc_ast: case Parsetree.Pmod_constraint + Typedtree.Tmod_constraint "^module_name);
          soit m_base2 = analyse_module
              env
              current_module_name
              module_name
              None
              p_module_expr2
              tt_module_expr2
          dans
          soit mtkind = Sig.analyse_module_type_kind env
              (Name.concat current_module_name "??")
              p_modtype tt_modtype
          dans
          soit tt_modtype = Odoc_env.subst_module_type env tt_modtype dans
          si !Odoc_global.filter_with_module_constraints alors
            filter_module_with_module_type_constraint m_base2 tt_modtype;
          {
            m_base avec
            m_type = tt_modtype ;
            m_kind = Module_constraint (m_base2.m_kind, mtkind) ;
          }

      | (Parsetree.Pmod_structure p_structure,
         Typedtree.Tmod_constraint
           ({ Typedtree.mod_desc = Typedtree.Tmod_structure tt_structure},
            tt_modtype, _, _)
        ) ->
          (* needed for recursive modules *)

          print_DEBUG ("Odoc_ast: case Parsetree.Pmod_structure + Typedtree.Tmod_constraint "^module_name);
          soit elements = analyse_structure env complete_name pos_start pos_end p_structure tt_structure dans
          (* we must complete the included modules *)
          soit included_modules_from_tt = tt_get_included_module_list tt_structure dans
          soit elements2 = replace_dummy_included_modules elements included_modules_from_tt dans
          { m_base avec
            m_type = Odoc_env.subst_module_type env tt_modtype ;
            m_kind = Module_struct elements2 ;
          }

      | (Parsetree.Pmod_unpack p_exp,
         Typedtree.Tmod_unpack (t_exp, tt_modtype)) ->
          print_DEBUG ("Odoc_ast: case Parsetree.Pmod_unpack + Typedtree.Tmod_unpack "^module_name);
          soit code =
            soit loc = p_module_expr.Parsetree.pmod_loc dans
            soit loc_end = loc.Location.loc_end.Lexing.pos_cnum dans
            soit exp_loc = p_exp.Parsetree.pexp_loc dans
            soit exp_loc_end = exp_loc.Location.loc_end.Lexing.pos_cnum dans
            soit s = get_string_of_file exp_loc_end loc_end dans
            Printf.sprintf "(val ...%s" s
          dans
          (* let name = Odoc_env.full_module_type_name env (Name.from_path (fst pkg_type)) in *)
          soit name =
            filtre tt_modtype avec
            | Mty_ident p ->
                Odoc_env.full_module_type_name env (Name.from_path p)
            | _ -> ""
          dans
          soit alias = { mta_name = name ; mta_module = None } dans
          { m_base avec
            m_type = Odoc_env.subst_module_type env tt_modtype ;
            m_kind = Module_unpack (code, alias) ;
          }

      | (parsetree, typedtree) ->
          (*DEBUG*)soit s_parse =
          (*DEBUG*)  filtre parsetree avec
          (*DEBUG*)    Parsetree.Pmod_ident _ -> "Pmod_ident"
          (*DEBUG*)  | Parsetree.Pmod_structure _ -> "Pmod_structure"
          (*DEBUG*)  | Parsetree.Pmod_functor _ -> "Pmod_functor"
          (*DEBUG*)  | Parsetree.Pmod_apply _ -> "Pmod_apply"
          (*DEBUG*)  | Parsetree.Pmod_constraint _ -> "Pmod_constraint"
          (*DEBUG*)  | Parsetree.Pmod_unpack _ -> "Pmod_unpack"
          (*DEBUG*)dans
          (*DEBUG*)soit s_typed =
          (*DEBUG*)  filtre typedtree avec
          (*DEBUG*)    Typedtree.Tmod_ident _ -> "Tmod_ident"
          (*DEBUG*)  | Typedtree.Tmod_structure _ -> "Tmod_structure"
          (*DEBUG*)  | Typedtree.Tmod_functor _ -> "Tmod_functor"
          (*DEBUG*)  | Typedtree.Tmod_apply _ -> "Tmod_apply"
          (*DEBUG*)  | Typedtree.Tmod_constraint _ -> "Tmod_constraint"
          (*DEBUG*)  | Typedtree.Tmod_unpack _ -> "Tmod_unpack"
          (*DEBUG*)dans
          (*DEBUG*)soit code = get_string_of_file pos_start pos_end dans
          print_DEBUG (Printf.sprintf "code=%s\ns_parse=%s\ns_typed=%s\n" code s_parse s_typed);

          raise (Failure "analyse_module: parsetree and typedtree don't match.")

     soit analyse_typed_tree source_file input_file
         (parsetree : Parsetree.structure) (typedtree : typedtree) =
       soit (tree_structure, _) = typedtree dans
       soit complete_source_file =
         essaie
           soit curdir = Sys.getcwd () dans
           soit (dirname, basename) = (Filename.dirname source_file, Filename.basename source_file) dans
           Sys.chdir dirname ;
           soit complete = Filename.concat (Sys.getcwd ()) basename dans
           Sys.chdir curdir ;
           complete
         avec
           Sys_error s ->
             prerr_endline s ;
             incr Odoc_global.errors ;
             source_file
       dans
       prepare_file complete_source_file input_file;
       (* We create the t_module for this file. *)
       soit mod_name = String.capitalize (Filename.basename (Filename.chop_extension source_file)) dans
       soit (len,info_opt) = My_ir.first_special !file_name !file dans

       (* we must complete the included modules *)
       soit elements = analyse_structure Odoc_env.empty mod_name len (String.length !file) parsetree tree_structure dans
       soit included_modules_from_tt = tt_get_included_module_list tree_structure dans
       soit elements2 = replace_dummy_included_modules elements included_modules_from_tt dans
       soit kind = Module_struct elements2 dans
       {
         m_name = mod_name ;
         m_type = Types.Mty_signature [] ;
         m_info = info_opt ;
         m_is_interface = faux ;
         m_file = !file_name ;
         m_kind = kind ;
         m_loc = { loc_impl = Some (Location.in_file !file_name) ; loc_inter = None } ;
         m_top_deps = [] ;
         m_code = (si !Odoc_global.keep_code alors Some !file sinon None) ;
         m_code_intf = None ;
         m_text_only = faux ;
       }
  fin
