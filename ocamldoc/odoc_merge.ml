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

(** Merge of information from [.ml] and [.mli] for a module.*)

ouvre Odoc_types

module Name = Odoc_name
ouvre Odoc_parameter
ouvre Odoc_value
ouvre Odoc_type
ouvre Odoc_exception
ouvre Odoc_class
ouvre Odoc_module

soit merge_before_tags l =
  soit rec iter acc = fonction
    [] -> List.rev acc
  | (v, text) :: q ->
      soit (l1, l2) = List.partition
        (fonc (v2,_) -> v = v2) q
      dans
      soit acc =
        soit text =
          List.fold_left
            (fonc acc t -> acc @ [Raw " "] @ t)
            text (List.map snd l1)
        dans
        (v, text) :: acc
      dans
      iter acc l2
  dans
  iter [] l
;;

soit version_separators = Str.regexp "[\\.\\+]";;

(** Merge two Odoctypes.info struture, completing the information of
   the first one with the information in the second one.
   The merge treatment depends on a given merge_option list.
   @return the new info structure.*)
soit merge_info merge_options (m1 : info) (m2 : info) =
  soit new_desc_opt =
    filtre m1.i_desc, m2.i_desc avec
      None, None -> None
    | None, Some d
    | Some d, None -> Some d
    | Some d1, Some d2 ->
        si List.mem Merge_description merge_options alors
          Some (d1 @ (Newline :: d2))
        sinon
          Some d1
  dans
  soit new_authors =
    filtre m1.i_authors, m2.i_authors avec
      [], [] -> []
    | l, []
    | [], l -> l
    | l1, l2 ->
        si List.mem Merge_author merge_options alors
          l1 @ l2
        sinon
          l1
  dans
  soit new_version =
    filtre m1.i_version , m2.i_version avec
      None, None -> None
    | Some v, None
    | None, Some v -> Some v
    | Some v1, Some v2 ->
        si List.mem Merge_version merge_options alors
          Some (v1^" "^v2)
        sinon
          Some v1
  dans
  soit new_sees =
    filtre m1.i_sees, m2.i_sees avec
      [], [] -> []
    | l, []
    | [], l -> l
    | l1, l2 ->
        si List.mem Merge_see merge_options alors
          l1 @ l2
        sinon
          l1
  dans
  soit new_since =
    filtre m1.i_since, m2.i_since avec
      None, None -> None
    | Some v, None
    | None, Some v -> Some v
    | Some v1, Some v2 ->
        si List.mem Merge_since merge_options alors
          Some (v1^" "^v2)
        sinon
          Some v1
  dans
  soit new_before =
    filtre m1.i_before, m2.i_before avec
      [], [] -> []
    | l, []
    | [], l -> l
    | l1, l2 ->
        si List.mem Merge_before merge_options alors
          merge_before_tags (m1.i_before @ m2.i_before)
        sinon
          l1 dans
  soit new_before = List.map (fonc (v, t) -> (Str.split version_separators v, v, t)) new_before dans
  soit new_before = List.sort Pervasives.compare new_before dans
  soit new_before = List.map (fonc (_, v, t) -> (v, t)) new_before dans
  soit new_dep =
    filtre m1.i_deprecated, m2.i_deprecated avec
      None, None -> None
    | None, Some t
    | Some t, None -> Some t
    | Some t1, Some t2 ->
        si List.mem Merge_deprecated merge_options alors
          Some (t1 @ (Newline :: t2))
        sinon
          Some t1
  dans
  soit new_params =
    filtre m1.i_params, m2.i_params avec
      [], [] -> []
    | l, []
    | [], l -> l
    | l1, l2 ->
        si List.mem Merge_param merge_options alors
          (
           soit l_in_m1_and_m2, l_in_m2_only = List.partition
               (fonc (param2, _) -> List.mem_assoc param2 l1)
               l2
           dans
           soit rec iter = fonction
               [] -> []
             | (param2, desc2) :: q ->
                 soit desc1 = List.assoc param2 l1 dans
                 (param2, desc1 @ (Newline :: desc2)) :: (iter q)
           dans
           soit l1_completed = iter l_in_m1_and_m2 dans
           l1_completed @ l_in_m2_only
          )
        sinon
          l1
  dans
  soit new_raised_exceptions =
    filtre m1.i_raised_exceptions, m2.i_raised_exceptions avec
      [], [] -> []
    | l, []
    | [], l -> l
    | l1, l2 ->
        si List.mem Merge_raised_exception merge_options alors
          (
           soit l_in_m1_and_m2, l_in_m2_only = List.partition
               (fonc (exc2, _) -> List.mem_assoc exc2 l1)
               l2
           dans
           soit rec iter = fonction
               [] -> []
             | (exc2, desc2) :: q ->
                 soit desc1 = List.assoc exc2 l1 dans
                 (exc2, desc1 @ (Newline :: desc2)) :: (iter q)
           dans
           soit l1_completed = iter l_in_m1_and_m2 dans
           l1_completed @ l_in_m2_only
          )
        sinon
          l1
  dans
  soit new_rv =
    filtre m1.i_return_value, m2.i_return_value avec
      None, None -> None
    | None, Some t
    | Some t, None -> Some t
    | Some t1, Some t2 ->
        si List.mem Merge_return_value merge_options alors
          Some (t1 @ (Newline :: t2))
        sinon
          Some t1
  dans
  soit new_custom =
    filtre m1.i_custom, m2.i_custom avec
      [], [] -> []
    | [], l
    | l, [] -> l
    | l1, l2 ->
        si List.mem Merge_custom merge_options alors
          l1 @ l2
        sinon
          l1
  dans
  {
    Odoc_types.i_desc = new_desc_opt ;
    Odoc_types.i_authors = new_authors ;
    Odoc_types.i_version = new_version ;
    Odoc_types.i_sees = new_sees ;
    Odoc_types.i_since = new_since ;
    Odoc_types.i_before = new_before ;
    Odoc_types.i_deprecated = new_dep ;
    Odoc_types.i_params = new_params ;
    Odoc_types.i_raised_exceptions = new_raised_exceptions ;
    Odoc_types.i_return_value = new_rv ;
    Odoc_types.i_custom = new_custom ;
  }

(** Merge of two optional info structures. *)
soit merge_info_opt merge_options mli_opt ml_opt =
  filtre mli_opt, ml_opt avec
    None, Some i -> Some i
  | Some i, None -> Some i
  | None, None -> None
  | Some i1, Some i2 -> Some (merge_info merge_options i1 i2)

(** merge of two t_type, one for a .mli, another for the .ml.
   The .mli type is completed with the information in the .ml type. *)
soit merge_types merge_options mli ml =
  mli.ty_info <- merge_info_opt merge_options mli.ty_info ml.ty_info;
  mli.ty_loc <- { mli.ty_loc avec loc_impl = ml.ty_loc.loc_impl } ;
  mli.ty_code <- (filtre mli.ty_code avec None -> ml.ty_code | _ -> mli.ty_code) ;

  filtre mli.ty_kind, ml.ty_kind avec
    Type_abstract, _ ->
      ()

  | Type_variant l1, Type_variant l2 ->
      soit f cons =
        essaie
          soit cons2 = List.find
              (fonc c2 -> c2.vc_name = cons.vc_name)
              l2
          dans
          soit new_desc =
            filtre cons.vc_text, cons2.vc_text avec
              None, None -> None
            | Some d, None
            | None, Some d -> Some d
            | Some d1, Some d2 ->
                si List.mem Merge_description merge_options alors
                  Some (merge_info merge_options d1 d2)
                sinon
                  Some d1
          dans
          cons.vc_text <- new_desc
        avec
          Not_found ->
            si !Odoc_global.inverse_merge_ml_mli alors
              ()
            sinon
              raise (Failure (Odoc_messages.different_types mli.ty_name))
      dans
      List.iter f l1

  | Type_record l1, Type_record l2 ->
      soit f record =
        essaie
          soit record2= List.find
              (fonc r -> r.rf_name = record.rf_name)
              l2
          dans
          soit new_desc =
            filtre record.rf_text, record2.rf_text avec
              None, None -> None
            | Some d, None
            | None, Some d -> Some d
            | Some d1, Some d2 ->
                si List.mem Merge_description merge_options alors
                  Some (merge_info merge_options d1 d2)
                sinon
                  Some d1
          dans
          record.rf_text <- new_desc
        avec
          Not_found ->
            si !Odoc_global.inverse_merge_ml_mli alors
              ()
            sinon
              raise (Failure (Odoc_messages.different_types mli.ty_name))
      dans
      List.iter f l1

  | _ ->
      si !Odoc_global.inverse_merge_ml_mli alors
        ()
      sinon
        raise (Failure (Odoc_messages.different_types mli.ty_name))

(** Merge of two param_info, one from a .mli, one from a .ml.
   The text fields are not handled but will be recreated from the
   i_params field of the info structure.
   Here, if a parameter in the .mli has no name, we take the one
   from the .ml. When two parameters have two different forms,
   we take the one from the .mli. *)
soit rec merge_param_info pi_mli pi_ml =
  filtre (pi_mli, pi_ml) avec
    (Simple_name sn_mli, Simple_name sn_ml) ->
      si sn_mli.sn_name = "" alors
        Simple_name { sn_mli avec sn_name = sn_ml.sn_name }
      sinon
        pi_mli
  | (Simple_name _, Tuple _) ->
      pi_mli
  | (Tuple (_, t_mli), Simple_name sn_ml) ->
      (* if we're here, then the tuple in the .mli has no parameter names ;
         then we take the name of the parameter of the .ml and the type of the .mli. *)
      Simple_name { sn_ml avec sn_type = t_mli }

  | (Tuple (l_mli, t_mli), Tuple (l_ml, _)) ->
      (* if the two tuples have different lengths
         (which should not occurs), we return the pi_mli,
         without further investigation.*)
      si (List.length l_mli) <> (List.length l_ml) alors
        pi_mli
      sinon
        soit new_l = List.map2 merge_param_info l_mli l_ml dans
        Tuple (new_l, t_mli)

(** Merge of the parameters of two functions/methods/classes, one for a .mli, another for a .ml.
   The prameters in the .mli are completed by the name in the .ml.*)
soit rec merge_parameters param_mli param_ml =
  filtre (param_mli, param_ml) avec
    ([], []) -> []
  | (l, []) | ([], l) -> l
  | ((pi_mli :: li), (pi_ml :: l)) ->
      (merge_param_info pi_mli pi_ml) :: merge_parameters li l

(** Merge of two t_class, one for a .mli, another for the .ml.
   The .mli class is completed with the information in the .ml class. *)
soit merge_classes merge_options mli ml =
  mli.cl_info <- merge_info_opt merge_options mli.cl_info ml.cl_info;
  mli.cl_loc <- { mli.cl_loc avec loc_impl = ml.cl_loc.loc_impl } ;
  mli.cl_parameters <- merge_parameters mli.cl_parameters ml.cl_parameters;

  (* we must reassociate comments in @param to the the corresponding
     parameters because the associated comment of a parameter may have been changed y the merge.*)
  Odoc_class.class_update_parameters_text mli;

  (* merge values *)
  List.iter
    (fonc a ->
      essaie
        soit _ = List.find
            (fonc ele ->
              filtre ele avec
                Class_attribute a2 ->
                  si a2.att_value.val_name = a.att_value.val_name alors
                    (
                     a.att_value.val_info <- merge_info_opt merge_options
                         a.att_value.val_info a2.att_value.val_info;
                     a.att_value.val_loc <- { a.att_value.val_loc avec loc_impl = a2.att_value.val_loc.loc_impl } ;
                     si !Odoc_global.keep_code alors
                       a.att_value.val_code <- a2.att_value.val_code;
                     vrai
                    )
                  sinon
                    faux
              | _ ->
                  faux
            )
            (* we look for the last attribute with this name defined in the implementation *)
            (List.rev (Odoc_class.class_elements ml))
        dans
        ()
      avec
        Not_found ->
          ()
    )
    (Odoc_class.class_attributes mli);
  (* merge methods *)
  List.iter
    (fonc m ->
      essaie
        soit _ = List.find
            (fonc ele ->
              filtre ele avec
                Class_method m2 ->
                  si m2.met_value.val_name = m.met_value.val_name alors
                    (
                     m.met_value.val_info <- merge_info_opt
                         merge_options m.met_value.val_info m2.met_value.val_info;
                     m.met_value.val_loc <- { m.met_value.val_loc avec loc_impl = m2.met_value.val_loc.loc_impl } ;
                     (* merge the parameter names *)
                     m.met_value.val_parameters <- (merge_parameters
                                                      m.met_value.val_parameters
                                                      m2.met_value.val_parameters) ;
                     (* we must reassociate comments in @param to the corresponding
                        parameters because the associated comment of a parameter may have been changed by the merge.*)
                     Odoc_value.update_value_parameters_text m.met_value;

                     si !Odoc_global.keep_code alors
                       m.met_value.val_code <- m2.met_value.val_code;

                     vrai
                    )
                  sinon
                    faux
              | _ ->
                  faux
            )
            (* we look for the last method with this name defined in the implementation *)
            (List.rev (Odoc_class.class_elements ml))
        dans
        ()
      avec
        Not_found ->
          ()
    )
    (Odoc_class.class_methods mli)

(** merge of two t_class_type, one for a .mli, another for the .ml.
   The .mli class is completed with the information in the .ml class. *)
soit merge_class_types merge_options mli ml =
  mli.clt_info <- merge_info_opt merge_options  mli.clt_info ml.clt_info;
  mli.clt_loc <- { mli.clt_loc avec loc_impl = ml.clt_loc.loc_impl } ;
  (* merge values *)
  List.iter
    (fonc a ->
      essaie
        soit _ = List.find
            (fonc ele ->
              filtre ele avec
                Class_attribute a2 ->
                  si a2.att_value.val_name = a.att_value.val_name alors
                    (
                     a.att_value.val_info <- merge_info_opt merge_options
                         a.att_value.val_info a2.att_value.val_info;
                     a.att_value.val_loc <- { a.att_value.val_loc avec loc_impl = a2.att_value.val_loc.loc_impl } ;
                     si !Odoc_global.keep_code alors
                       a.att_value.val_code <- a2.att_value.val_code;

                     vrai
                    )
                  sinon
                    faux
              | _ ->
                  faux
            )
            (* we look for the last attribute with this name defined in the implementation *)
            (List.rev (Odoc_class.class_type_elements ml))
        dans
        ()
      avec
        Not_found ->
          ()
    )
    (Odoc_class.class_type_attributes mli);
  (* merge methods *)
  List.iter
    (fonc m ->
      essaie
        soit _ = List.find
            (fonc ele ->
              filtre ele avec
                Class_method m2 ->
                  si m2.met_value.val_name = m.met_value.val_name alors
                    (
                     m.met_value.val_info <- merge_info_opt
                         merge_options m.met_value.val_info m2.met_value.val_info;
                     m.met_value.val_loc <- { m.met_value.val_loc avec loc_impl = m2.met_value.val_loc.loc_impl } ;
                     m.met_value.val_parameters <- (merge_parameters
                                                      m.met_value.val_parameters
                                                      m2.met_value.val_parameters) ;
                     (* we must reassociate comments in @param to the the corresponding
                        parameters because the associated comment of a parameter may have been changed y the merge.*)
                     Odoc_value.update_value_parameters_text m.met_value;

                     si !Odoc_global.keep_code alors
                       m.met_value.val_code <- m2.met_value.val_code;

                     vrai
                    )
                  sinon
                    faux
              | _ ->
                  faux
            )
            (* we look for the last method with this name defined in the implementation *)
            (List.rev (Odoc_class.class_type_elements ml))
        dans
        ()
      avec
        Not_found ->
          ()
    )
    (Odoc_class.class_type_methods mli)


(** merge of two t_module_type, one for a .mli, another for the .ml.
   The .mli module is completed with the information in the .ml module. *)
soit rec merge_module_types merge_options mli ml =
  mli.mt_info <- merge_info_opt merge_options mli.mt_info ml.mt_info;
  mli.mt_loc <- { mli.mt_loc avec loc_impl = ml.mt_loc.loc_impl } ;
  (* merge exceptions *)
  List.iter
    (fonc ex ->
      essaie
        soit _ = List.find
            (fonc ele ->
              filtre ele avec
                Element_exception ex2 ->
                  si ex2.ex_name = ex.ex_name alors
                    (
                     ex.ex_info <- merge_info_opt merge_options ex.ex_info ex2.ex_info;
                     ex.ex_loc <- { ex.ex_loc avec loc_impl = ex2.ex_loc.loc_impl } ;
                     ex.ex_code <- (filtre ex.ex_code avec None -> ex2.ex_code | _ -> ex.ex_code) ;
                     vrai
                    )
                  sinon
                    faux
              | _ ->
                  faux
            )
            (* we look for the last exception with this name defined in the implementation *)
            (List.rev (Odoc_module.module_type_elements ml))
        dans
        ()
      avec
        Not_found ->
          ()
    )
    (Odoc_module.module_type_exceptions mli);
  (* merge types *)
  List.iter
    (fonc ty ->
      essaie
        soit _ = List.find
            (fonc ele ->
              filtre ele avec
                Element_type ty2 ->
                  si ty2.ty_name = ty.ty_name alors
                    (
                     merge_types merge_options ty ty2;
                     vrai
                    )
                  sinon
                    faux
              | _ ->
                  faux
            )
            (* we look for the last type with this name defined in the implementation *)
            (List.rev (Odoc_module.module_type_elements ml))
        dans
        ()
      avec
        Not_found ->
          ()
    )
    (Odoc_module.module_type_types mli);
  (* merge submodules *)
  List.iter
    (fonc m ->
      essaie
        soit _ = List.find
            (fonc ele ->
              filtre ele avec
                Element_module m2 ->
                  si m2.m_name = m.m_name alors
                    (
                     ignore (merge_modules merge_options m m2);
(*
                     m.m_info <- merge_info_opt merge_options m.m_info m2.m_info;
                     m.m_loc <- { m.m_loc with loc_impl = m2.m_loc.loc_impl } ;
*)
                     vrai
                    )
                  sinon
                    faux
              | _ ->
                  faux
            )
            (* we look for the last module with this name defined in the implementation *)
            (List.rev (Odoc_module.module_type_elements ml))
        dans
        ()
      avec
        Not_found ->
          ()
    )
    (Odoc_module.module_type_modules mli);

  (* merge module types *)
  List.iter
    (fonc m ->
      essaie
        soit _ = List.find
            (fonc ele ->
              filtre ele avec
                Element_module_type m2 ->
                  si m2.mt_name = m.mt_name alors
                    (
                     merge_module_types merge_options m m2;
                     vrai
                    )
                  sinon
                    faux
              | _ ->
                  faux
            )
            (* we look for the last module with this name defined in the implementation *)
            (List.rev (Odoc_module.module_type_elements ml))
        dans
        ()
      avec
        Not_found ->
          ()
    )
    (Odoc_module.module_type_module_types mli);

  (* A VOIR : merge included modules ? *)

  (* merge values *)
  List.iter
    (fonc v ->
      essaie
        soit _ = List.find
            (fonc ele ->
              filtre ele avec
                Element_value v2 ->
                  si v2.val_name = v.val_name alors
                    (
                     v.val_info <- merge_info_opt merge_options v.val_info v2.val_info ;
                     v.val_loc <- { v.val_loc avec loc_impl = v2.val_loc.loc_impl } ;
                     (* in the .mli we don't know any parameters so we add the ones in the .ml *)
                     v.val_parameters <- (merge_parameters
                                            v.val_parameters
                                            v2.val_parameters) ;
                     (* we must reassociate comments in @param to the the corresponding
                        parameters because the associated comment of a parameter may have been changed y the merge.*)
                     Odoc_value.update_value_parameters_text v;

                     si !Odoc_global.keep_code alors
                       v.val_code <- v2.val_code;

                     vrai
                    )
                  sinon
                    faux
              | _ ->
                  faux
            )
            (* we look for the last value with this name defined in the implementation *)
            (List.rev (Odoc_module.module_type_elements ml))
        dans
        ()
      avec
        Not_found ->
          ()
    )
    (Odoc_module.module_type_values mli);

  (* merge classes *)
  List.iter
    (fonc c ->
      essaie
        soit _ = List.find
            (fonc ele ->
              filtre ele avec
                Element_class c2 ->
                  si c2.cl_name = c.cl_name alors
                    (
                     merge_classes merge_options c c2;
                     vrai
                    )
                  sinon
                    faux
              | _ ->
                  faux
            )
            (* we look for the last value with this name defined in the implementation *)
            (List.rev (Odoc_module.module_type_elements ml))
        dans
        ()
      avec
        Not_found ->
          ()
    )
    (Odoc_module.module_type_classes mli);

  (* merge class types *)
  List.iter
    (fonc c ->
      essaie
        soit _ = List.find
            (fonc ele ->
              filtre ele avec
                Element_class_type c2 ->
                  si c2.clt_name = c.clt_name alors
                    (
                     merge_class_types merge_options c c2;
                     vrai
                    )
                  sinon
                    faux
              | _ ->
                  faux
            )
            (* we look for the last value with this name defined in the implementation *)
            (List.rev (Odoc_module.module_type_elements ml))
        dans
        ()
      avec
        Not_found ->
          ()
    )
    (Odoc_module.module_type_class_types mli)

(** merge of two t_module, one for a .mli, another for the .ml.
   The .mli module is completed with the information in the .ml module. *)
et merge_modules merge_options mli ml =
  mli.m_info <- merge_info_opt merge_options mli.m_info ml.m_info;
  mli.m_loc <- { mli.m_loc avec loc_impl = ml.m_loc.loc_impl } ;
  soit rec remove_doubles acc = fonction
      [] -> acc
    | h :: q ->
        si List.mem h acc alors remove_doubles acc q
        sinon remove_doubles (h :: acc) q
  dans
  mli.m_top_deps <- remove_doubles mli.m_top_deps ml.m_top_deps ;

  soit code =
    si !Odoc_global.keep_code alors
      filtre mli.m_code, ml.m_code avec
        Some s, _ -> Some s
      | _, Some s -> Some s
      | _ -> None
    sinon
      None
  dans
  soit code_intf =
    si !Odoc_global.keep_code alors
      filtre mli.m_code_intf, ml.m_code_intf avec
        Some s, _ -> Some s
      | _, Some s -> Some s
      | _ -> None
    sinon
      None
  dans
  mli.m_code <- code;
  mli.m_code_intf <- code_intf;

  (* merge exceptions *)
  List.iter
    (fonc ex ->
      essaie
        soit _ = List.find
            (fonc ele ->
              filtre ele avec
                Element_exception ex2 ->
                  si ex2.ex_name = ex.ex_name alors
                    (
                     ex.ex_info <- merge_info_opt merge_options ex.ex_info ex2.ex_info;
                     ex.ex_loc <- { ex.ex_loc avec loc_impl = ex.ex_loc.loc_impl } ;
                     ex.ex_code <- (filtre ex.ex_code avec None -> ex2.ex_code | _ -> ex.ex_code) ;
                     vrai
                    )
                  sinon
                    faux
              | _ ->
                  faux
            )
            (* we look for the last exception with this name defined in the implementation *)
            (List.rev (Odoc_module.module_elements ml))
        dans
        ()
      avec
        Not_found ->
          ()
    )
    (Odoc_module.module_exceptions mli);
  (* merge types *)
  List.iter
    (fonc ty ->
      essaie
        soit _ = List.find
            (fonc ele ->
              filtre ele avec
                Element_type ty2 ->
                  si ty2.ty_name = ty.ty_name alors
                    (
                     merge_types merge_options ty ty2;
                     vrai
                    )
                  sinon
                    faux
              | _ ->
                  faux
            )
            (* we look for the last type with this name defined in the implementation *)
            (List.rev (Odoc_module.module_elements ml))
        dans
        ()
      avec
        Not_found ->
          ()
    )
    (Odoc_module.module_types mli);
  (* merge submodules *)
  List.iter
    (fonc m ->
      essaie
        soit _ = List.find
            (fonc ele ->
              filtre ele avec
                Element_module m2 ->
                  si m2.m_name = m.m_name alors
                    (
                     ignore (merge_modules merge_options m m2);
(*
                     m.m_info <- merge_info_opt merge_options m.m_info m2.m_info;
                     m.m_loc <- { m.m_loc with loc_impl = m2.m_loc.loc_impl } ;
*)
                     vrai
                    )
                  sinon
                    faux
              | _ ->
                  faux
            )
            (* we look for the last module with this name defined in the implementation *)
            (List.rev (Odoc_module.module_elements ml))
        dans
        ()
      avec
        Not_found ->
          ()
    )
    (Odoc_module.module_modules mli);

  (* merge module types *)
  List.iter
    (fonc m ->
      essaie
        soit _ = List.find
            (fonc ele ->
              filtre ele avec
                Element_module_type m2 ->
                  si m2.mt_name = m.mt_name alors
                    (
                     merge_module_types merge_options m m2;
                     vrai
                    )
                  sinon
                    faux
              | _ ->
                  faux
            )
            (* we look for the last module with this name defined in the implementation *)
            (List.rev (Odoc_module.module_elements ml))
        dans
        ()
      avec
        Not_found ->
          ()
    )
    (Odoc_module.module_module_types mli);

  (* A VOIR : merge included modules ? *)

  (* merge values *)
  List.iter
    (fonc v ->
      essaie
        soit _ = List.find
            (fonc v2 ->
              si v2.val_name = v.val_name alors
                (
                 v.val_info <- merge_info_opt merge_options v.val_info v2.val_info ;
                 v.val_loc <- { v.val_loc avec loc_impl = v2.val_loc.loc_impl } ;
                 (* in the .mli we don't know any parameters so we add the ones in the .ml *)
                 v.val_parameters <- (merge_parameters
                                        v.val_parameters
                                        v2.val_parameters) ;
                 (* we must reassociate comments in @param to the the corresponding
                    parameters because the associated comment of a parameter may have been changed y the merge.*)
                 Odoc_value.update_value_parameters_text v;

                 si !Odoc_global.keep_code alors
                   v.val_code <- v2.val_code;
                 vrai
                )
              sinon
                faux
            )
            (* we look for the last value with this name defined in the implementation *)
            (List.rev (Odoc_module.module_values ml))
        dans
        ()
      avec
        Not_found ->
          ()
    )
    (Odoc_module.module_values mli);

  (* merge classes *)
  List.iter
    (fonc c ->
      essaie
        soit _ = List.find
            (fonc ele ->
              filtre ele avec
                Element_class c2 ->
                  si c2.cl_name = c.cl_name alors
                    (
                     merge_classes merge_options c c2;
                     vrai
                    )
                  sinon
                    faux
              | _ ->
                  faux
            )
            (* we look for the last value with this name defined in the implementation *)
            (List.rev (Odoc_module.module_elements ml))
        dans
        ()
      avec
        Not_found ->
          ()
    )
    (Odoc_module.module_classes mli);

  (* merge class types *)
  List.iter
    (fonc c ->
      essaie
        soit _ = List.find
            (fonc ele ->
              filtre ele avec
                Element_class_type c2 ->
                  si c2.clt_name = c.clt_name alors
                    (
                     merge_class_types merge_options c c2;
                     vrai
                    )
                  sinon
                    faux
              | _ ->
                  faux
            )
            (* we look for the last value with this name defined in the implementation *)
            (List.rev (Odoc_module.module_elements ml))
        dans
        ()
      avec
        Not_found ->
          ()
    )
    (Odoc_module.module_class_types mli);

  mli

soit merge merge_options modules_list =
  soit rec iter = fonction
      [] -> []
    | m :: q ->
        (* look for another module with the same name *)
        soit (l_same, l_others) = List.partition
            (fonc m2 -> m.m_name = m2.m_name)
            q
        dans
        filtre l_same avec
          [] ->
            (* no other module to merge with *)
            m :: (iter l_others)
        | m2 :: [] ->
            (
             (* we can merge m with m2 if there is an implementation
                and an interface.*)
             soit f b = si !Odoc_global.inverse_merge_ml_mli alors not b sinon b dans
             filtre f m.m_is_interface, f m2.m_is_interface avec
               vrai, faux -> (merge_modules merge_options m m2) :: (iter l_others)
             | faux, vrai -> (merge_modules merge_options m2 m) :: (iter l_others)
             | faux, faux ->
                 si !Odoc_global.inverse_merge_ml_mli alors
                   (* two Module.ts for the .mli ! *)
                   raise (Failure (Odoc_messages.two_interfaces m.m_name))
                 sinon
                   (* two Module.t for the .ml ! *)
                   raise (Failure (Odoc_messages.two_implementations m.m_name))
             | vrai, vrai ->
                 si !Odoc_global.inverse_merge_ml_mli alors
                   (* two Module.t for the .ml ! *)
                   raise (Failure (Odoc_messages.two_implementations m.m_name))
                 sinon
                   (* two Module.ts for the .mli ! *)
                   raise (Failure (Odoc_messages.two_interfaces m.m_name))
            )
        | _ ->
            (* too many Module.t ! *)
            raise (Failure (Odoc_messages.too_many_module_objects m.m_name))

  dans
  iter modules_list
