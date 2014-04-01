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

(** Analysis of interface files. *)

ouvre Misc
ouvre Asttypes
ouvre Types
ouvre Typedtree
ouvre Path

soit print_DEBUG s = print_string s ; print_newline ();;

module Name = Odoc_name
ouvre Odoc_parameter
ouvre Odoc_value
ouvre Odoc_type
ouvre Odoc_exception
ouvre Odoc_class
ouvre Odoc_module
ouvre Odoc_types

module Signature_search =
  struct
    type ele =
      | M de string
      | MT de string
      | V de string
      | T de string
      | C de string
      | CT de string
      | E de string
      | ER de string
      | P de string

    type tab = (ele, Types.signature_item) Hashtbl.t

    soit add_to_hash table signat =
      filtre signat avec
        Types.Sig_value (ident, _) ->
          Hashtbl.add table (V (Name.from_ident ident)) signat
      | Types.Sig_exception (ident, _) ->
          Hashtbl.add table (E (Name.from_ident ident)) signat
      | Types.Sig_type (ident, _, _) ->
          Hashtbl.add table (T (Name.from_ident ident)) signat
      | Types.Sig_class (ident, _, _) ->
          Hashtbl.add table (C (Name.from_ident ident)) signat
      | Types.Sig_class_type (ident, _, _) ->
          Hashtbl.add table (CT (Name.from_ident ident)) signat
      | Types.Sig_module (ident, _, _) ->
          Hashtbl.add table (M (Name.from_ident ident)) signat
      | Types.Sig_modtype (ident,_) ->
          Hashtbl.add table (MT (Name.from_ident ident)) signat

    soit table signat =
      soit t = Hashtbl.create 13 dans
      List.iter (add_to_hash t) signat;
      t

    soit search_value table name =
      filtre Hashtbl.find table (V name) avec
      | (Types.Sig_value (_, val_desc)) ->  val_desc.Types.val_type
      | _ -> affirme faux

    soit search_exception table name =
      filtre Hashtbl.find table (E name) avec
      | (Types.Sig_exception (_, type_expr_list)) ->
          type_expr_list
      | _ -> affirme faux

    soit search_type table name =
      filtre Hashtbl.find table (T name) avec
      | (Types.Sig_type (_, type_decl, _)) -> type_decl
      | _ -> affirme faux

    soit search_class table name =
      filtre Hashtbl.find table (C name) avec
      | (Types.Sig_class (_, class_decl, _)) -> class_decl
      | _ -> affirme faux

    soit search_class_type table name =
      filtre Hashtbl.find table (CT name) avec
      | (Types.Sig_class_type (_, cltype_decl, _)) -> cltype_decl
      | _ -> affirme faux

    soit search_module table name =
      filtre Hashtbl.find table (M name) avec
      | (Types.Sig_module (ident, md, _)) -> md.Types.md_type
      | _ -> affirme faux

    soit search_module_type table name =
      filtre Hashtbl.find table (MT name) avec
      | (Types.Sig_modtype (_, {Types.mtd_type = Some module_type})) ->
          Some module_type
      | (Types.Sig_modtype (_, {Types.mtd_type = None})) ->
          None
      | _ -> affirme faux

    soit search_attribute_type name class_sig =
      soit (_, _, type_expr) = Types.Vars.find name class_sig.Types.csig_vars dans
      type_expr

    soit search_method_type name class_sig =
      soit fields = Odoc_misc.get_fields class_sig.Types.csig_self dans
      List.assoc name fields
  fin

module type Info_retriever =
  sig
    val all_special : string -> string -> int * (Odoc_types.info list)
    val blank_line_outside_simple : string -> string -> bool
    val just_after_special : string -> string -> (int * Odoc_types.info option)
    val first_special : string -> string -> (int * Odoc_types.info option)
    val get_comments :
        (Odoc_types.text -> 'a) -> string -> string -> (Odoc_types.info option * 'a list)
  fin

module Analyser =
  foncteur (My_ir : Info_retriever) ->
  struct
    (** This variable is used to load a file as a string and retrieve characters from it.*)
    soit file = ref ""
    (** The name of the analysed file. *)
    soit file_name = ref ""

    (** This function takes two indexes (start and end) and return the string
       corresponding to the indexes in the file global variable. The function
       prepare_file must have been called to fill the file global variable.*)
    soit get_string_of_file the_start the_end =
      essaie
        soit s = String.sub !file the_start (the_end-the_start) dans
        s
      avec
        Invalid_argument _ ->
          ""

    (** This function loads the given file in the file global variable,
       and sets file_name.*)
    soit prepare_file f input_f =
      essaie
        soit s = Odoc_misc.input_file_as_string input_f dans
        file := s;
        file_name := f
      avec
        e ->
          file := "";
          raise e

    (** The function used to get the comments in a class. *)
    soit get_comments_in_class pos_start pos_end =
      My_ir.get_comments (fonc t -> Class_comment t)
        !file_name
        (get_string_of_file pos_start pos_end)

    (** The function used to get the comments in a module. *)
    soit get_comments_in_module pos_start pos_end =
      My_ir.get_comments (fonc t -> Element_module_comment t)
        !file_name
        (get_string_of_file pos_start pos_end)

    soit merge_infos = Odoc_merge.merge_info_opt Odoc_types.all_merge_options

    soit name_comment_from_type_kind pos_end pos_limit tk =
      filtre tk avec
        Parsetree.Ptype_abstract ->
          (0, [])
      | Parsetree.Ptype_variant cons_core_type_list_list ->
          soit rec f acc cons_core_type_list_list =
            soit ouvre Parsetree dans
            filtre cons_core_type_list_list avec
              [] ->
                (0, acc)
            | pcd :: [] ->
                soit s = get_string_of_file
                    pcd.pcd_loc.Location.loc_end.Lexing.pos_cnum
                    pos_limit
                dans
                soit (len, comment_opt) =  My_ir.just_after_special !file_name s dans
                (len, acc @ [ (pcd.pcd_name.txt, comment_opt) ])
            | pcd :: (pcd2 :: _ tel q) ->
                soit pos_end_first = pcd.pcd_loc.Location.loc_end.Lexing.pos_cnum dans
                soit pos_start_second = pcd2.pcd_loc.Location.loc_start.Lexing.pos_cnum dans
                soit s = get_string_of_file pos_end_first pos_start_second dans
                soit (_,comment_opt) = My_ir.just_after_special !file_name  s dans
                f (acc @ [pcd.pcd_name.txt, comment_opt]) q
          dans
          f [] cons_core_type_list_list

      | Parsetree.Ptype_record name_mutable_type_list (* of (string * mutable_flag * core_type) list*) ->
          soit ouvre Parsetree dans
          soit rec f = fonction
              [] ->
                []
            | {pld_name=name; pld_type=ct} :: [] ->
                soit pos = ct.Parsetree.ptyp_loc.Location.loc_end.Lexing.pos_cnum dans
                soit s = get_string_of_file pos pos_end dans
                soit (_,comment_opt) =  My_ir.just_after_special !file_name s dans
                [name.txt, comment_opt]
            | {pld_name=name; pld_type=ct} :: ({pld_name=name2; pld_type=ct2} tel ele2) :: q ->
                soit pos = ct.Parsetree.ptyp_loc.Location.loc_end.Lexing.pos_cnum dans
                soit pos2 = ct2.Parsetree.ptyp_loc.Location.loc_start.Lexing.pos_cnum dans
                soit s = get_string_of_file pos pos2 dans
                soit (_,comment_opt) =  My_ir.just_after_special !file_name s dans
                (name.txt, comment_opt) :: (f (ele2 :: q))
          dans
          (0, f name_mutable_type_list)

    soit get_type_kind env name_comment_list type_kind =
      filtre type_kind avec
        Types.Type_abstract ->
          Odoc_type.Type_abstract
      | Types.Type_variant l ->
          soit f {Types.cd_id=constructor_name;cd_args=type_expr_list;cd_res=ret_type} =
            soit constructor_name = Ident.name constructor_name dans
            soit comment_opt =
              essaie List.assoc constructor_name name_comment_list 
              avec Not_found -> None
            dans
            {
              vc_name = constructor_name ;
              vc_args = List.map (Odoc_env.subst_type env) type_expr_list ;
              vc_ret =  may_map (Odoc_env.subst_type env) ret_type;
              vc_text = comment_opt
            }
          dans
          Odoc_type.Type_variant (List.map f l)

      | Types.Type_record (l, _) ->
          soit f {Types.ld_id=field_name;ld_mutable=mutable_flag;ld_type=type_expr} =
            soit field_name = Ident.name field_name dans
            soit comment_opt =
              essaie List.assoc field_name name_comment_list
              avec Not_found -> None
            dans
            {
              rf_name = field_name ;
              rf_mutable = mutable_flag = Mutable ;
              rf_type = Odoc_env.subst_type env type_expr ;
              rf_text = comment_opt
            }
          dans
          Odoc_type.Type_record (List.map f l)

    soit erased_names_of_constraints constraints acc =
      List.fold_right (fonc constraint_ acc ->
        filtre constraint_ avec
        | Parsetree.Pwith_type _ | Parsetree.Pwith_module _ -> acc
        | Parsetree.Pwith_typesubst {Parsetree.ptype_name=s}
        | Parsetree.Pwith_modsubst (s, _) ->
          Name.Set.add s.txt acc)
        constraints acc

    soit filter_out_erased_items_from_signature erased signature =
      si Name.Set.is_empty erased alors signature
      sinon List.fold_right (fonc sig_item acc ->
        soit take_item psig_desc = { sig_item avec Parsetree.psig_desc } :: acc dans
        filtre sig_item.Parsetree.psig_desc avec
        | Parsetree.Psig_attribute _
        | Parsetree.Psig_extension _
        | Parsetree.Psig_value _
        | Parsetree.Psig_exception _
        | Parsetree.Psig_open _
        | Parsetree.Psig_include _
        | Parsetree.Psig_class _
        | Parsetree.Psig_class_type _ tel tp -> take_item tp
        | Parsetree.Psig_type types ->
          (filtre List.filter (fonc td -> not (Name.Set.mem td.Parsetree.ptype_name.txt erased)) types avec
          | [] -> acc
          | types -> take_item (Parsetree.Psig_type types))
        | Parsetree.Psig_module {Parsetree.pmd_name=name}
        | Parsetree.Psig_modtype {Parsetree.pmtd_name=name} tel m ->
          si Name.Set.mem name.txt erased alors acc sinon take_item m
        | Parsetree.Psig_recmodule mods ->
          (filtre List.filter (fonc pmd -> not (Name.Set.mem pmd.Parsetree.pmd_name.txt erased)) mods avec
          | [] -> acc
          | mods -> take_item (Parsetree.Psig_recmodule mods)))
        signature []

    (** Analysis of the elements of a class, from the information in the parsetree and in the class
       signature. @return the couple (inherited_class list, elements).*)
    soit analyse_class_elements env current_class_name last_pos pos_limit
        class_type_field_list class_signature =
      soit get_pos_limit2 q =
        filtre q avec
          [] -> pos_limit
          | ele2 :: _ ->
              soit loc = ele2.Parsetree.pctf_loc dans
            filtre ele2.Parsetree.pctf_desc avec
              Parsetree.Pctf_val (_, _, _, _)
            | Parsetree.Pctf_method (_, _, _, _)
            | Parsetree.Pctf_constraint (_, _) -> loc.Location.loc_start.Lexing.pos_cnum
            | Parsetree.Pctf_inherit class_type ->
                class_type.Parsetree.pcty_loc.Location.loc_start.Lexing.pos_cnum
            | Parsetree.Pctf_extension _ -> affirme faux
      dans
      soit get_method name comment_opt private_flag loc q =
        soit complete_name = Name.concat current_class_name name dans
        soit typ =
          essaie Signature_search.search_method_type name class_signature
          avec Not_found ->
            raise (Failure (Odoc_messages.method_type_not_found current_class_name name))
        dans
        soit subst_typ = Odoc_env.subst_type env typ dans
        soit met =
          {
            met_value =
            {
              val_name = complete_name ;
              val_info = comment_opt ;
              val_type = subst_typ ;
              val_recursive = faux ;
              val_parameters = Odoc_value.dummy_parameter_list subst_typ ;
              val_code = None ;
              val_loc = { loc_impl = None ; loc_inter = Some loc };
            } ;
            met_private = private_flag = Asttypes.Private ;
            met_virtual = faux ;
          }
        dans
        soit pos_limit2 = get_pos_limit2 q dans
        soit pos_end = loc.Location.loc_end.Lexing.pos_cnum dans
        soit (maybe_more, info_after_opt) =
          My_ir.just_after_special
            !file_name
            (get_string_of_file pos_end pos_limit2)
        dans
        met.met_value.val_info <- merge_infos met.met_value.val_info info_after_opt ;
        (* update the parameter description *)
        Odoc_value.update_value_parameters_text met.met_value;
        (met, maybe_more)
      dans
      soit rec f last_pos class_type_field_list =
        filtre class_type_field_list avec
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
                      acc @ [Class_comment t])
                []
                ele_coms
            dans
            ([], ele_comments)

          | item :: q ->
              soit loc = item.Parsetree.pctf_loc dans
              filtre item.Parsetree.pctf_desc avec

        | Parsetree.Pctf_val (name, mutable_flag, virtual_flag, _) ->
            (* of (string * mutable_flag * core_type option * Location.t)*)
            soit (comment_opt, eles_comments) = get_comments_in_class last_pos loc.Location.loc_start.Lexing.pos_cnum dans
            soit complete_name = Name.concat current_class_name name dans
            soit typ =
              essaie Signature_search.search_attribute_type name class_signature
              avec Not_found ->
                raise (Failure (Odoc_messages.attribute_type_not_found current_class_name name))
            dans
            soit subst_typ = Odoc_env.subst_type env typ dans
            soit att =
              {
                att_value =
                {
                  val_name = complete_name ;
                  val_info = comment_opt ;
                  val_type = subst_typ;
                  val_recursive = faux ;
                  val_parameters = [] ;
                  val_code = None ;
                  val_loc = { loc_impl = None ; loc_inter = Some loc} ;
                } ;
                att_mutable = mutable_flag = Asttypes.Mutable ;
                att_virtual = virtual_flag = Asttypes.Virtual ;
              }
            dans
            soit pos_limit2 = get_pos_limit2 q dans
            soit pos_end = loc.Location.loc_end.Lexing.pos_cnum dans
            soit (maybe_more, info_after_opt) =
              My_ir.just_after_special
                !file_name
                (get_string_of_file pos_end pos_limit2)
            dans
            att.att_value.val_info <- merge_infos att.att_value.val_info info_after_opt ;
            soit (inher_l, eles) = f (pos_end + maybe_more) q dans
            (inher_l, eles_comments @ ((Class_attribute att) :: eles))

        | Parsetree.Pctf_method (name, private_flag, virtual_flag, _) ->
            (* of (string * private_flag * virtual_flag * core_type) *)
            soit (comment_opt, eles_comments) = get_comments_in_class last_pos loc.Location.loc_start.Lexing.pos_cnum dans
            soit (met, maybe_more) = get_method name comment_opt private_flag loc q dans
            soit met2 =
              filtre virtual_flag avec
              | Concrete -> met
              | Virtual -> { met avec met_virtual = vrai }
            dans
            soit (inher_l, eles) = f (loc.Location.loc_end.Lexing.pos_cnum + maybe_more) q dans
            (inher_l, eles_comments @ ((Class_method met2) :: eles))

        | (Parsetree.Pctf_constraint (_, _)) ->
            (* of (core_type * core_type) *)
            (* A VOIR : cela correspond aux contraintes, non ? on ne les garde pas pour l'instant *)
            soit (comment_opt, eles_comments) = get_comments_in_class last_pos loc.Location.loc_start.Lexing.pos_cnum dans
            soit (inher_l, eles) = f loc.Location.loc_end.Lexing.pos_cnum q dans
            (inher_l, eles_comments @ eles)

        | Parsetree.Pctf_inherit class_type ->
            soit loc = class_type.Parsetree.pcty_loc dans
            soit (comment_opt, eles_comments) =
              get_comments_in_class last_pos loc.Location.loc_start.Lexing.pos_cnum
            dans
            soit pos_limit2 = get_pos_limit2 q dans
            soit pos_end = loc.Location.loc_end.Lexing.pos_cnum dans
            soit (maybe_more, info_after_opt) =
              My_ir.just_after_special
                !file_name
                (get_string_of_file pos_end pos_limit2)
            dans
            soit comment_opt2 = merge_infos comment_opt info_after_opt dans
            soit text_opt = filtre comment_opt2 avec None -> None | Some i -> i.Odoc_types.i_desc dans
            soit inh  =
              filtre class_type.Parsetree.pcty_desc avec
                Parsetree.Pcty_constr (longident, _) ->
                  (*of Longident.t * core_type list*)
                  soit name = Name.from_longident longident.txt dans
                  soit ic =
                    {
                      ic_name = Odoc_env.full_class_or_class_type_name env name ;
                      ic_class = None ;
                      ic_text = text_opt ;
                    }
                  dans
                  ic

              | Parsetree.Pcty_signature _
              | Parsetree.Pcty_arrow _ ->
                    (* we don't have a name for the class signature, so we call it "object ... end"  *)
                  {
                    ic_name = Odoc_messages.object_end ;
                    ic_class = None ;
                    ic_text = text_opt ;
                  }
              | Parsetree.Pcty_extension _ -> affirme faux
            dans
            soit (inher_l, eles) = f (pos_end + maybe_more) q dans
            (inh :: inher_l , eles_comments @ eles)
        | Parsetree.Pctf_extension _ -> affirme faux
      dans
      f last_pos class_type_field_list

    (** Analyse of a .mli parse tree, to get the corresponding elements.
       last_pos is the position of the first character which may be used to look for special comments.
    *)
    soit rec analyse_parsetree env signat current_module_name last_pos pos_limit sig_item_list =
      soit table = Signature_search.table signat dans
      (* we look for the comment of each item then analyse the item *)
      soit rec f acc_eles acc_env last_pos = fonction
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
            acc_eles @ ele_comments

        | ele :: q ->
            soit (assoc_com, ele_comments) =  get_comments_in_module
                last_pos
                ele.Parsetree.psig_loc.Location.loc_start.Lexing.pos_cnum
            dans
            soit (maybe_more, new_env, elements) = analyse_signature_item_desc
                acc_env
                signat
                table
                current_module_name
                ele.Parsetree.psig_loc
                ele.Parsetree.psig_loc.Location.loc_start.Lexing.pos_cnum
                ele.Parsetree.psig_loc.Location.loc_end.Lexing.pos_cnum
                (filtre q avec
                  [] -> pos_limit
                | ele2 :: _ -> ele2.Parsetree.psig_loc.Location.loc_start.Lexing.pos_cnum
                )
                assoc_com
                ele.Parsetree.psig_desc
            dans
            f (acc_eles @ (ele_comments @ elements))
              new_env
              (ele.Parsetree.psig_loc.Location.loc_end.Lexing.pos_cnum + maybe_more)
                   (* for the comments of constructors in types,
                      which are after the constructor definition and can
                      go beyond ele.Parsetree.psig_loc.Location.loc_end.Lexing.pos_cnum *)
              q
      dans
      f [] env last_pos sig_item_list

    (** Analyse the given signature_item_desc to create the corresponding module element
       (with the given attached comment).*)
    et analyse_signature_item_desc env signat table current_module_name
        sig_item_loc pos_start_ele pos_end_ele pos_limit comment_opt sig_item_desc =
        filtre sig_item_desc avec
          Parsetree.Psig_value value_desc ->
            soit name_pre = value_desc.Parsetree.pval_name dans
            soit type_expr =
              essaie Signature_search.search_value table name_pre.txt
              avec Not_found ->
                raise (Failure (Odoc_messages.value_not_found current_module_name name_pre.txt))
            dans
            soit name = Name.parens_if_infix name_pre.txt dans
            soit subst_typ = Odoc_env.subst_type env type_expr dans
            soit v =
              {
                val_name = Name.concat current_module_name name ;
                val_info = comment_opt ;
                val_type = subst_typ ;
                val_recursive = faux ;
                val_parameters = Odoc_value.dummy_parameter_list subst_typ ;
                val_code = None ;
                val_loc = { loc_impl = None ; loc_inter = Some sig_item_loc } ;
              }
            dans
            soit (maybe_more, info_after_opt) =
              My_ir.just_after_special
                !file_name
                (get_string_of_file pos_end_ele pos_limit)
            dans
            v.val_info <- merge_infos v.val_info info_after_opt ;
            (* update the parameter description *)
            Odoc_value.update_value_parameters_text v;

            soit new_env = Odoc_env.add_value env v.val_name dans
            (maybe_more, new_env, [ Element_value v ])

        | Parsetree.Psig_exception exception_decl ->
            soit name = exception_decl.Parsetree.pcd_name dans
            soit types_excep_decl =
              essaie Signature_search.search_exception table name.txt
              avec Not_found ->
                raise (Failure (Odoc_messages.exception_not_found current_module_name name.txt))
            dans
            soit e =
              {
                ex_name = Name.concat current_module_name name.txt ;
                ex_info = comment_opt ;
                ex_args = List.map (Odoc_env.subst_type env) types_excep_decl.exn_args ;
                ex_alias = None ;
                ex_loc = { loc_impl = None ; loc_inter = Some sig_item_loc } ;
                ex_code =
                   (
                    si !Odoc_global.keep_code alors
                      Some (get_string_of_file pos_start_ele pos_end_ele)
                    sinon
                      None
                   ) ;
              }
            dans
            soit (maybe_more, info_after_opt) =
              My_ir.just_after_special
                !file_name
                (get_string_of_file pos_end_ele pos_limit)
            dans
            e.ex_info <- merge_infos e.ex_info info_after_opt ;
            soit new_env = Odoc_env.add_exception env e.ex_name dans
            (maybe_more, new_env, [ Element_exception e ])

        | Parsetree.Psig_type name_type_decl_list ->
            (* we start by extending the environment *)
            soit new_env =
              List.fold_left
                (fonc acc_env td ->
                  soit complete_name = Name.concat current_module_name td.Parsetree.ptype_name.txt dans
                  Odoc_env.add_type acc_env complete_name
                )
                env
                name_type_decl_list
            dans
            soit rec f ?(first=faux) acc_maybe_more last_pos name_type_decl_list =
              filtre name_type_decl_list avec
                [] ->
                  (acc_maybe_more, [])
              | type_decl :: q ->
                  soit name = type_decl.Parsetree.ptype_name dans
                  soit (assoc_com, ele_comments) =
                    si first alors
                      (comment_opt, [])
                    sinon
                      get_comments_in_module
                        last_pos
                        type_decl.Parsetree.ptype_loc.Location.loc_start.Lexing.pos_cnum
                  dans
                  soit pos_limit2 =
                    filtre q avec
                      [] -> pos_limit
                    | td :: _ -> td.Parsetree.ptype_loc.Location.loc_start.Lexing.pos_cnum
                  dans
                  soit (maybe_more, name_comment_list) =
                    name_comment_from_type_kind
                      type_decl.Parsetree.ptype_loc.Location.loc_end.Lexing.pos_cnum
                      pos_limit2
                      type_decl.Parsetree.ptype_kind
                  dans
                  print_DEBUG ("Type "^name.txt^" : "^(filtre assoc_com avec None -> "sans commentaire" | Some c -> Odoc_misc.string_of_info c));
                  soit f_DEBUG (name, c_opt) = print_DEBUG ("constructor/field "^name^": "^(filtre c_opt avec None -> "sans commentaire" | Some c -> Odoc_misc.string_of_info c)) dans
                  List.iter f_DEBUG name_comment_list;
                  (* get the information for the type in the signature *)
                  soit sig_type_decl =
                    essaie Signature_search.search_type table name.txt
                    avec Not_found ->
                      raise (Failure (Odoc_messages.type_not_found current_module_name name.txt))
                  dans
                  (* get the type kind with the associated comments *)
                  soit type_kind = get_type_kind new_env name_comment_list sig_type_decl.Types.type_kind dans
                  soit loc_start = type_decl.Parsetree.ptype_loc.Location.loc_start.Lexing.pos_cnum dans
                  soit new_end = type_decl.Parsetree.ptype_loc.Location.loc_end.Lexing.pos_cnum + maybe_more dans
                  (* associate the comments to each constructor and build the [Type.t_type] *)
                  soit new_type =
                    {
                      ty_name = Name.concat current_module_name name.txt ;
                      ty_info = assoc_com ;
                      ty_parameters =
                        List.map2 (fonc p v ->
                          soit (co, cn) = Types.Variance.get_upper v dans
                          (Odoc_env.subst_type new_env p,co, cn))
                        sig_type_decl.Types.type_params
                        sig_type_decl.Types.type_variance;
                      ty_kind = type_kind;
                      ty_private = sig_type_decl.Types.type_private;
                      ty_manifest =
                      (filtre sig_type_decl.Types.type_manifest avec
                        None -> None
                      | Some t -> Some (Odoc_env.subst_type new_env t));
                      ty_loc = { loc_impl = None ;  loc_inter = Some sig_item_loc } ;
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
                  new_type.ty_info <- merge_infos new_type.ty_info info_after_opt ;
                  soit (new_maybe_more, eles) = f
                      (maybe_more + maybe_more2)
                      (new_end + maybe_more2)
                      q
                  dans
                  (new_maybe_more, (ele_comments @ [Element_type new_type]) @ eles)
            dans
            soit (maybe_more, types) = f ~first: vrai 0 pos_start_ele name_type_decl_list dans
            (maybe_more, new_env, types)

        | Parsetree.Psig_open _ -> (* A VOIR *)
            soit ele_comments = filtre comment_opt avec
              None -> []
            | Some i ->
                filtre i.i_desc avec
                  None -> []
                | Some t -> [Element_module_comment t]
            dans
            (0, env, ele_comments)

        | Parsetree.Psig_module {Parsetree.pmd_name=name; pmd_type=module_type} ->
            soit complete_name = Name.concat current_module_name name.txt dans
            (* get the the module type in the signature by the module name *)
            soit sig_module_type =
              essaie Signature_search.search_module table name.txt
              avec Not_found ->
                raise (Failure (Odoc_messages.module_not_found current_module_name name.txt))
            dans
            soit module_kind = analyse_module_kind env complete_name module_type sig_module_type dans
            soit code_intf =
              si !Odoc_global.keep_code alors
                soit loc = module_type.Parsetree.pmty_loc dans
                soit st = loc.Location.loc_start.Lexing.pos_cnum dans
                soit en = loc.Location.loc_end.Lexing.pos_cnum dans
                Some (get_string_of_file st en)
              sinon
                None
            dans
            soit new_module =
              {
                m_name = complete_name ;
                m_type = sig_module_type;
                m_info = comment_opt ;
                m_is_interface = vrai ;
                m_file = !file_name ;
                m_kind = module_kind ;
                m_loc = { loc_impl = None ; loc_inter = Some sig_item_loc } ;
                m_top_deps = [] ;
                m_code = None ;
                m_code_intf = code_intf ;
                m_text_only = faux ;
              }
            dans
            soit (maybe_more, info_after_opt) =
              My_ir.just_after_special
                !file_name
                (get_string_of_file pos_end_ele pos_limit)
            dans
            new_module.m_info <- merge_infos new_module.m_info info_after_opt ;
            soit new_env = Odoc_env.add_module env new_module.m_name dans
            soit new_env2 =
              filtre new_module.m_type avec (* A VOIR : cela peut-il etre Tmty_ident ? dans ce cas, on aurait pas la signature *)
                Types.Mty_signature s -> Odoc_env.add_signature new_env new_module.m_name ~rel: (Name.simple new_module.m_name) s
              | _ -> new_env
            dans
            (maybe_more, new_env2, [ Element_module new_module ])

        | Parsetree.Psig_recmodule decls ->
            (* we start by extending the environment *)
            soit new_env =
              List.fold_left
                (fonc acc_env {Parsetree.pmd_name={txt=name}} ->
                  soit complete_name = Name.concat current_module_name name dans
                  soit e = Odoc_env.add_module acc_env complete_name dans
                  (* get the information for the module in the signature *)
                  soit sig_module_type =
                    essaie Signature_search.search_module table name
                    avec Not_found ->
                      raise (Failure (Odoc_messages.module_not_found current_module_name name))
                  dans
                  filtre sig_module_type avec
                    (* A VOIR : cela peut-il etre Tmty_ident ? dans ce cas, on aurait pas la signature *)
                    Types.Mty_signature s ->
                      Odoc_env.add_signature e complete_name ~rel: name s
                  | _ ->
                      print_DEBUG "not a Tmty_signature";
                      e
                )
                env
                decls
            dans
            soit rec f ?(first=faux) acc_maybe_more last_pos name_mtype_list =
              filtre name_mtype_list avec
                [] ->
                  (acc_maybe_more, [])
              | {Parsetree.pmd_name=name; pmd_type=modtype} :: q ->
                  soit complete_name = Name.concat current_module_name name.txt dans
                  soit loc = modtype.Parsetree.pmty_loc dans
                  soit loc_start = loc.Location.loc_start.Lexing.pos_cnum dans
                  soit loc_end = loc.Location.loc_end.Lexing.pos_cnum dans
                  soit (assoc_com, ele_comments) =
                    si first alors
                      (comment_opt, [])
                    sinon
                      get_comments_in_module
                        last_pos
                        loc_start
                  dans
                  soit pos_limit2 =
                    filtre q avec
                      [] -> pos_limit
                    | _ :: _ -> loc.Location.loc_start.Lexing.pos_cnum
                  dans
                  (* get the information for the module in the signature *)
                  soit sig_module_type =
                    essaie Signature_search.search_module table name.txt
                    avec Not_found ->
                      raise (Failure (Odoc_messages.module_not_found current_module_name name.txt))
                  dans
                  (* associate the comments to each constructor and build the [Type.t_type] *)
                  soit module_kind = analyse_module_kind new_env complete_name modtype sig_module_type dans
                  soit code_intf =
                    si !Odoc_global.keep_code alors
                      soit st = loc.Location.loc_start.Lexing.pos_cnum dans
                      soit en = loc.Location.loc_end.Lexing.pos_cnum dans
                      Some (get_string_of_file st en)
                    sinon
                      None
                  dans
                  soit new_module =
                    {
                      m_name = complete_name ;
                      m_type = sig_module_type;
                      m_info = assoc_com ;
                      m_is_interface = vrai ;
                      m_file = !file_name ;
                      m_kind = module_kind ;
                      m_loc = { loc_impl = None ; loc_inter = Some loc } ;
                      m_top_deps = [] ;
                      m_code = None ;
                      m_code_intf = code_intf ;
                      m_text_only = faux ;
                    }
                  dans
                  soit (maybe_more, info_after_opt) =
                    My_ir.just_after_special
                      !file_name
                      (get_string_of_file loc_end pos_limit2)
                  dans
                  new_module.m_info <- merge_infos new_module.m_info info_after_opt ;

                  soit (maybe_more2, eles) = f
                      maybe_more
                      (loc_end + maybe_more)
                      q
                  dans
                  (maybe_more2, (ele_comments @ [Element_module new_module]) @ eles)
            dans
            soit (maybe_more, mods) = f ~first: vrai 0 pos_start_ele decls dans
            (maybe_more, new_env, mods)

        | Parsetree.Psig_modtype {Parsetree.pmtd_name=name; pmtd_type=pmodtype_decl} ->
            soit complete_name = Name.concat current_module_name name.txt dans
            soit sig_mtype =
              essaie Signature_search.search_module_type table name.txt
              avec Not_found ->
                raise (Failure (Odoc_messages.module_type_not_found current_module_name name.txt))
            dans
            soit module_type_kind =
              filtre pmodtype_decl avec
                None -> None
              | Some module_type ->
                filtre sig_mtype avec
                | Some sig_mtype -> Some (analyse_module_type_kind env complete_name module_type sig_mtype)
                | None -> None
            dans

            soit mt =
              {
                mt_name = complete_name ;
                mt_info = comment_opt ;
                mt_type = sig_mtype ;
                mt_is_interface = vrai ;
                mt_file = !file_name ;
                mt_kind = module_type_kind ;
                mt_loc = { loc_impl = None ; loc_inter = Some sig_item_loc } ;
              }
            dans
            soit (maybe_more, info_after_opt) =
              My_ir.just_after_special
                !file_name
                (get_string_of_file pos_end_ele pos_limit)
            dans
            mt.mt_info <- merge_infos mt.mt_info info_after_opt ;
            soit new_env = Odoc_env.add_module_type env mt.mt_name dans
            soit new_env2 =
              filtre sig_mtype avec (* A VOIR : cela peut-il etre Tmty_ident ? dans ce cas, on aurait pas la signature *)
                Some (Types.Mty_signature s) -> Odoc_env.add_signature new_env mt.mt_name ~rel: (Name.simple mt.mt_name) s
              | _ -> new_env
            dans
            (maybe_more, new_env2, [ Element_module_type mt ])

        | Parsetree.Psig_include (module_type, _attrs) ->
            soit rec f = fonction
                Parsetree.Pmty_ident longident ->
                  Name.from_longident longident.txt
              | Parsetree.Pmty_alias longident ->
                  Name.from_longident longident.txt
              | Parsetree.Pmty_signature _ ->
                  "??"
              | Parsetree.Pmty_functor _ ->
                  "??"
              | Parsetree.Pmty_with (mt, _) ->
                  f mt.Parsetree.pmty_desc
              | Parsetree.Pmty_typeof mexpr ->
                  début filtre mexpr.Parsetree.pmod_desc avec
                    Parsetree.Pmod_ident longident -> Name.from_longident longident.txt
                  | _ -> "??"
                  fin
              | Parsetree.Pmty_extension _ -> affirme faux
            dans
            soit name = f module_type.Parsetree.pmty_desc dans
            soit full_name = Odoc_env.full_module_or_module_type_name env name dans
            soit im =
              {
                im_name = full_name ;
                im_module = None ;
                im_info = comment_opt;
              }
            dans
            (0, env, [ Element_included_module im ]) (* A VOIR : etendre l'environnement ? avec quoi ? *)

        | Parsetree.Psig_class class_description_list ->
            (* we start by extending the environment *)
            soit new_env =
              List.fold_left
                (fonc acc_env -> fonc class_desc ->
                  soit complete_name = Name.concat current_module_name class_desc.Parsetree.pci_name.txt dans
                  Odoc_env.add_class acc_env complete_name
                )
                env
                class_description_list
            dans
            soit rec f ?(first=faux) acc_maybe_more last_pos class_description_list =
              filtre class_description_list avec
                [] ->
                  (acc_maybe_more, [])
              | class_desc :: q ->
                  soit (assoc_com, ele_comments) =
                    si first alors
                      (comment_opt, [])
                    sinon
                      get_comments_in_module
                        last_pos
                        class_desc.Parsetree.pci_loc.Location.loc_start.Lexing.pos_cnum
                  dans
                  soit pos_end = class_desc.Parsetree.pci_loc.Location.loc_end.Lexing.pos_cnum dans
                  soit pos_limit2 =
                    filtre q avec
                      [] -> pos_limit
                    | cd :: _ -> cd.Parsetree.pci_loc.Location.loc_start.Lexing.pos_cnum
                  dans
                  soit name = class_desc.Parsetree.pci_name dans
                  soit complete_name = Name.concat current_module_name name.txt dans
                  soit sig_class_decl =
                    essaie Signature_search.search_class table name.txt
                    avec Not_found ->
                      raise (Failure (Odoc_messages.class_not_found current_module_name name.txt))
                  dans
                  soit sig_class_type = sig_class_decl.Types.cty_type dans
                  soit (parameters, class_kind) =
                    analyse_class_kind
                     new_env
                     complete_name
                     class_desc.Parsetree.pci_loc.Location.loc_start.Lexing.pos_cnum
                     class_desc.Parsetree.pci_expr
                     sig_class_type
                 dans
                 soit new_class =
                   {
                     cl_name = complete_name ;
                     cl_info = assoc_com ;
                     cl_type = Odoc_env.subst_class_type env sig_class_type ;
                     cl_type_parameters = sig_class_decl.Types.cty_params;
                     cl_virtual = class_desc.Parsetree.pci_virt = Asttypes.Virtual ;
                     cl_kind = class_kind ;
                     cl_parameters = parameters ;
                     cl_loc = { loc_impl = None ; loc_inter = Some class_desc.Parsetree.pci_loc } ;
                   }
                 dans
                 soit (maybe_more, info_after_opt) =
                   My_ir.just_after_special
                     !file_name
                     (get_string_of_file pos_end pos_limit2)
                 dans
                 new_class.cl_info <- merge_infos new_class.cl_info info_after_opt ;
                 Odoc_class.class_update_parameters_text new_class ;
                 soit (new_maybe_more, eles) =
                   f maybe_more (pos_end + maybe_more) q
                 dans
                 (new_maybe_more,
                  ele_comments @ (( Element_class new_class ) :: eles))
            dans
            soit (maybe_more, eles) =
              f ~first: vrai 0 pos_start_ele class_description_list
            dans
            (maybe_more, new_env, eles)

        | Parsetree.Psig_class_type class_type_declaration_list ->
            (* we start by extending the environment *)
            soit new_env =
              List.fold_left
                (fonc acc_env -> fonc class_type_decl ->
                  soit complete_name = Name.concat current_module_name class_type_decl.Parsetree.pci_name.txt dans
                  Odoc_env.add_class_type acc_env complete_name
                )
                env
                class_type_declaration_list
            dans
            soit rec f ?(first=faux) acc_maybe_more last_pos class_type_description_list =
              filtre class_type_description_list avec
                [] ->
                  (acc_maybe_more, [])
              | ct_decl :: q ->
                  soit (assoc_com, ele_comments) =
                    si first alors
                      (comment_opt, [])
                    sinon
                      get_comments_in_module
                        last_pos
                        ct_decl.Parsetree.pci_loc.Location.loc_start.Lexing.pos_cnum
                  dans
                  soit pos_end = ct_decl.Parsetree.pci_loc.Location.loc_end.Lexing.pos_cnum dans
                  soit pos_limit2 =
                    filtre q avec
                      [] -> pos_limit
                    | ct_decl2 :: _ -> ct_decl2.Parsetree.pci_loc.Location.loc_start.Lexing.pos_cnum
                  dans
                  soit name = ct_decl.Parsetree.pci_name dans
                  soit complete_name = Name.concat current_module_name name.txt dans
                  soit sig_cltype_decl =
                    essaie Signature_search.search_class_type table name.txt
                    avec Not_found ->
                      raise (Failure (Odoc_messages.class_type_not_found current_module_name name.txt))
                  dans
                  soit sig_class_type = sig_cltype_decl.Types.clty_type dans
                  soit kind = analyse_class_type_kind
                      new_env
                      complete_name
                      ct_decl.Parsetree.pci_loc.Location.loc_start.Lexing.pos_cnum
                      ct_decl.Parsetree.pci_expr
                      sig_class_type
                  dans
                  soit ct =
                    {
                      clt_name = complete_name ;
                      clt_info = assoc_com ;
                      clt_type = Odoc_env.subst_class_type env sig_class_type ;
                      clt_type_parameters = sig_cltype_decl.clty_params ;
                      clt_virtual = ct_decl.Parsetree.pci_virt = Asttypes.Virtual ;
                      clt_kind = kind ;
                      clt_loc = { loc_impl = None ; loc_inter = Some ct_decl.Parsetree.pci_loc } ;
                    }
                  dans
                  soit (maybe_more, info_after_opt) =
                    My_ir.just_after_special
                      !file_name
                      (get_string_of_file pos_end pos_limit2)
                  dans
                  ct.clt_info <- merge_infos ct.clt_info info_after_opt ;
                  soit (new_maybe_more, eles) =
                    f maybe_more (pos_end + maybe_more) q
                  dans
                 (new_maybe_more,
                  ele_comments @ (( Element_class_type ct) :: eles))
            dans
            soit (maybe_more, eles) =
              f ~first: vrai 0 pos_start_ele class_type_declaration_list
            dans
            (maybe_more, new_env, eles)
        | Parsetree.Psig_attribute _
        | Parsetree.Psig_extension _ ->
            (0, env, [])

    (** Return a module_type_kind from a Parsetree.module_type and a Types.module_type *)
    et analyse_module_type_kind
      ?(erased = Name.Set.empty) env current_module_name module_type sig_module_type =
      filtre module_type.Parsetree.pmty_desc avec
        Parsetree.Pmty_ident longident ->
          soit name =
            filtre sig_module_type avec
              Types.Mty_ident path -> Name.from_path path
            | _ -> Name.from_longident longident.txt
              (* A VOIR cela arrive quand on fait module type F : functor ... -> Toto, Toto n'est pas un ident mais une structure *)
          dans
          Module_type_alias { mta_name = Odoc_env.full_module_type_name env name ;
                              mta_module = None }

      | Parsetree.Pmty_alias longident ->
          soit name =
            filtre sig_module_type avec
              Types.Mty_alias path -> Name.from_path path
            | _ -> Name.from_longident longident.txt
          dans
          (* Wrong naming... *)
          Module_type_alias { mta_name = Odoc_env.full_module_name env name ;
                              mta_module = None }

      | Parsetree.Pmty_signature ast ->
          (
           soit ast = filter_out_erased_items_from_signature erased ast dans
           (* we must have a signature in the module type *)
           filtre sig_module_type avec
             Types.Mty_signature signat ->
               soit pos_start = module_type.Parsetree.pmty_loc.Location.loc_start.Lexing.pos_cnum dans
               soit pos_end = module_type.Parsetree.pmty_loc.Location.loc_end.Lexing.pos_cnum dans
               soit elements = analyse_parsetree env signat current_module_name pos_start pos_end ast dans
               Module_type_struct elements
           | _ ->
               raise (Failure "Parsetree.Pmty_signature signature but not Types.Mty_signature signat")
          )

      | Parsetree.Pmty_functor (_, pmodule_type2, module_type2) ->
          (
           soit loc = filtre pmodule_type2 avec None -> Location.none
                     | Some pmty -> pmty.Parsetree.pmty_loc dans
           soit loc_start = loc.Location.loc_start.Lexing.pos_cnum dans
           soit loc_end = loc.Location.loc_end.Lexing.pos_cnum dans
           soit mp_type_code = get_string_of_file loc_start loc_end dans
           print_DEBUG (Printf.sprintf "mp_type_code=%s" mp_type_code);
           filtre sig_module_type avec
             Types.Mty_functor (ident, param_module_type, body_module_type) ->
               soit mp_kind =
                 filtre pmodule_type2, param_module_type avec
                   Some pmty, Some mty ->
                     analyse_module_type_kind env current_module_name pmty mty
                 | _ -> Module_type_struct []
               dans
               soit param =
                 {
                   mp_name = Name.from_ident ident ;
                   mp_type =
                    Misc.may_map (Odoc_env.subst_module_type env)
                      param_module_type;
                   mp_type_code = mp_type_code ;
                   mp_kind = mp_kind ;
                 }
               dans
               soit k = analyse_module_type_kind ~erased env
                   current_module_name
                   module_type2
                   body_module_type
               dans
               Module_type_functor (param, k)

           | _ ->
               (* if we're here something's wrong *)
               raise (Failure "Parsetree.Pmty_functor _ but not Types.Mty_functor _")
          )

      | Parsetree.Pmty_with (module_type2, constraints) ->
          (* of module_type * (Longident.t * with_constraint) list *)
          (
           soit loc_start = module_type2.Parsetree.pmty_loc.Location.loc_end.Lexing.pos_cnum dans
           soit loc_end = module_type.Parsetree.pmty_loc.Location.loc_end.Lexing.pos_cnum dans
           soit s = get_string_of_file loc_start loc_end dans
           soit erased = erased_names_of_constraints constraints erased dans
           soit k = analyse_module_type_kind ~erased env current_module_name module_type2 sig_module_type dans

           Module_type_with (k, s)
          )

      | Parsetree.Pmty_typeof module_expr ->
          soit loc_start = module_expr.Parsetree.pmod_loc.Location.loc_start.Lexing.pos_cnum dans
          soit loc_end = module_expr.Parsetree.pmod_loc.Location.loc_end.Lexing.pos_cnum dans
          soit s = get_string_of_file loc_start loc_end dans
          Module_type_typeof s

      | Parsetree.Pmty_extension _ -> affirme faux

    (** analyse of a Parsetree.module_type and a Types.module_type.*)
    et analyse_module_kind
        ?(erased = Name.Set.empty) env current_module_name module_type sig_module_type =
      filtre module_type.Parsetree.pmty_desc avec
        Parsetree.Pmty_ident longident
      | Parsetree.Pmty_alias longident ->
          soit k = analyse_module_type_kind env current_module_name module_type sig_module_type dans
          Module_with ( k, "" )

      | Parsetree.Pmty_signature signature ->
          (
           soit signature = filter_out_erased_items_from_signature erased signature dans
           filtre sig_module_type avec
             Types.Mty_signature signat ->
               Module_struct
                 (analyse_parsetree
                    env
                    signat
                    current_module_name
                    module_type.Parsetree.pmty_loc.Location.loc_start.Lexing.pos_cnum
                    module_type.Parsetree.pmty_loc.Location.loc_end.Lexing.pos_cnum
                    signature
                 )
           | _ ->
               (* if we're here something's wrong *)
               raise (Failure "Parsetree.Pmty_signature signature but not Types.Mty_signature signat")
          )
      | Parsetree.Pmty_functor (_, pmodule_type2,module_type2) (* of string * module_type * module_type *) ->
          (
           filtre sig_module_type avec
             Types.Mty_functor (ident, param_module_type, body_module_type) ->
               soit loc = filtre pmodule_type2 avec None -> Location.none
                     | Some pmty -> pmty.Parsetree.pmty_loc dans
               soit loc_start = loc.Location.loc_start.Lexing.pos_cnum dans
               soit loc_end = loc.Location.loc_end.Lexing.pos_cnum dans
               soit mp_type_code = get_string_of_file loc_start loc_end dans
               print_DEBUG (Printf.sprintf "mp_type_code=%s" mp_type_code);
               soit mp_kind =
                 filtre pmodule_type2, param_module_type avec
                   Some pmty, Some mty ->
                     analyse_module_type_kind env current_module_name pmty mty
                 | _ -> Module_type_struct []
               dans
               soit param =
                 {
                   mp_name = Name.from_ident ident ;
                   mp_type = Misc.may_map
                    (Odoc_env.subst_module_type env) param_module_type ;
                   mp_type_code = mp_type_code ;
                   mp_kind = mp_kind ;
                 }
               dans
               soit k = analyse_module_kind ~erased env
                   current_module_name
                   module_type2
                   body_module_type
               dans
               Module_functor (param, k)

           | _ ->
               (* if we're here something's wrong *)
               raise (Failure "Parsetree.Pmty_functor _ but not Types.Mty_functor _")
          )
      | Parsetree.Pmty_with (module_type2, constraints) ->
          (*of module_type * (Longident.t * with_constraint) list*)
          (
           soit loc_start = module_type2.Parsetree.pmty_loc.Location.loc_end.Lexing.pos_cnum dans
           soit loc_end = module_type.Parsetree.pmty_loc.Location.loc_end.Lexing.pos_cnum dans
           soit s = get_string_of_file loc_start loc_end dans
           soit erased = erased_names_of_constraints constraints erased dans
           soit k = analyse_module_type_kind ~erased env current_module_name module_type2 sig_module_type dans
           Module_with (k, s)
          )
      | Parsetree.Pmty_typeof module_expr ->
          soit loc_start = module_expr.Parsetree.pmod_loc.Location.loc_start.Lexing.pos_cnum dans
          soit loc_end = module_expr.Parsetree.pmod_loc.Location.loc_end.Lexing.pos_cnum dans
          soit s = get_string_of_file loc_start loc_end dans
          Module_typeof s

      | Parsetree.Pmty_extension _ -> affirme faux


    (** Analyse of a Parsetree.class_type and a Types.class_type to return a couple
       (class parameters, class_kind).*)
    et analyse_class_kind env current_class_name last_pos parse_class_type sig_class_type =
      filtre parse_class_type.Parsetree.pcty_desc, sig_class_type avec
        (Parsetree.Pcty_constr (_, _) (*of Longident.t * core_type list *),
         Types.Cty_constr (p, typ_list, _) (*of Path.t * type_expr list * class_type*)) ->
          print_DEBUG "Cty_constr _";
           soit path_name = Name.from_path p dans
           soit name = Odoc_env.full_class_or_class_type_name env path_name dans
           soit k =
             Class_constr
               {
                 cco_name = name ;
                 cco_class = None ;
                 cco_type_parameters = List.map (Odoc_env.subst_type env) typ_list
               }
           dans
           ([], k)

      | (Parsetree.Pcty_signature { Parsetree.pcsig_fields = class_type_field_list }, Types.Cty_signature class_signature) ->
          (* we get the elements of the class in class_type_field_list *)
          soit (inher_l, ele) = analyse_class_elements env current_class_name
              last_pos
              parse_class_type.Parsetree.pcty_loc.Location.loc_end.Lexing.pos_cnum
              class_type_field_list
              class_signature
          dans
          ([], Class_structure (inher_l, ele))

      | (Parsetree.Pcty_arrow (parse_label, _, pclass_type), Types.Cty_arrow (label, type_expr, class_type)) ->
          (* label = string. Dans les signatures, pas de nom de parametres a l'interieur des tuples *)
          (* si label = "", pas de label. ici on a l'information pour savoir si on a un label explicite. *)
          si parse_label = label alors
            (
             soit new_param = Simple_name
                 {
                   sn_name = Btype.label_name label ;
                   sn_type = Odoc_env.subst_type env type_expr ;
                   sn_text = None ; (* will be updated when the class will be created *)
                 }
             dans
             soit (l, k) = analyse_class_kind env current_class_name last_pos pclass_type class_type dans
             ( (new_param :: l), k )
            )
          sinon
            (
             raise (Failure "Parsetree.Pcty_arrow (parse_label, _, pclass_type), labels differents")
            )

      | _ ->
          raise (Failure "analyse_class_kind pas de correspondance dans le match")

    (** Analyse of a Parsetree.class_type and a Types.class_type to return a class_type_kind.*)
    et analyse_class_type_kind env current_class_name last_pos parse_class_type sig_class_type =
      filtre parse_class_type.Parsetree.pcty_desc, sig_class_type avec
        (Parsetree.Pcty_constr (_, _) (*of Longident.t * core_type list *),
         Types.Cty_constr (p, typ_list, _) (*of Path.t * type_expr list * class_type*)) ->
          print_DEBUG "Cty_constr _";
           soit k =
             Class_type
               {
                 cta_name = Odoc_env.full_class_or_class_type_name env (Name.from_path p) ;
                 cta_class = None ;
                 cta_type_parameters = List.map (Odoc_env.subst_type env) typ_list
               }
           dans
           k

        | (Parsetree.Pcty_signature {
              Parsetree.pcsig_fields = class_type_field_list;
              }, Types.Cty_signature class_signature) ->
          (* we get the elements of the class in class_type_field_list *)
          soit (inher_l, ele) = analyse_class_elements env current_class_name
              last_pos
              parse_class_type.Parsetree.pcty_loc.Location.loc_end.Lexing.pos_cnum
              class_type_field_list
              class_signature
          dans
          Class_signature (inher_l, ele)

      | (Parsetree.Pcty_arrow (parse_label, _, pclass_type), Types.Cty_arrow (label, type_expr, class_type)) ->
          raise (Failure "analyse_class_type_kind : Parsetree.Pcty_arrow (...) with Types.Cty_arrow (...)")
(*
      | (Parsetree.Pcty_constr (longident, _) (*of Longident.t * core_type list *),
         Types.Cty_signature class_signature) ->
           (* A VOIR : c'est pour le cas des contraintes de classes :
              class type cons = object
                method m : int
              end

              class ['a] maxou x =
                (object
                  val a = (x : 'a)
                  method m = a
                end : cons )
                    ^^^^^^
           *)
           let k =
             Class_type
               {
                 cta_name = Odoc_env.full_class_name env (Name.from_longident longident) ;
                 cta_class = None ;
                 cta_type_parameters = List.map (Odoc_env.subst_type env) typ_list (* ?? *)
               }
           in
           ([], k)
*)
      | _ ->
          raise (Failure "analyse_class_type_kind pas de correspondance dans le match")

    soit analyse_signature source_file input_file
        (ast : Parsetree.signature) (signat : Types.signature) =
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
      soit mod_name = String.capitalize
          (Filename.basename (essaie Filename.chop_extension source_file avec _ -> source_file))
      dans
      soit (len,info_opt) = My_ir.first_special !file_name !file dans
      soit elements =
        analyse_parsetree Odoc_env.empty signat mod_name len (String.length !file) ast
      dans
      soit code_intf =
        si !Odoc_global.keep_code alors
          Some !file
        sinon
          None
      dans
      {
        m_name = mod_name ;
        m_type = Types.Mty_signature signat ;
        m_info = info_opt ;
        m_is_interface = vrai ;
        m_file = !file_name ;
        m_kind = Module_struct elements ;
        m_loc = { loc_impl = None ; loc_inter = Some (Location.in_file !file_name) } ;
        m_top_deps = [] ;
        m_code = None ;
        m_code_intf = code_intf ;
        m_text_only = faux ;
      }

    fin
