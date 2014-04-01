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

(** Cross referencing. *)

module Name = Odoc_name
ouvre Odoc_module
ouvre Odoc_class
ouvre Odoc_exception
ouvre Odoc_types
ouvre Odoc_value
ouvre Odoc_type
ouvre Odoc_parameter

(*** Replacements of aliases : if e1 = e2 and e2 = e3, then replace e2 by e3 to have e1 = e3,
   in order to associate the element with complete information. *)

(** The module used to keep what refs were modified. *)
module S = Set.Make
    (
     struct type t = string * ref_kind option
       soit compare = Pervasives.compare
     fin
    )

soit verified_refs = ref S.empty

soit add_verified v = verified_refs := S.add v !verified_refs
soit was_verified v = S.mem v !verified_refs

(** The module with the predicates used to get the aliased modules, classes and exceptions. *)
module P_alias =
  struct
    type t = int

    soit p_module m _ =
      (vrai,
       filtre m.m_kind avec
         Module_alias _ -> vrai
       | _ -> faux
      )
    soit p_module_type mt _ =
      (vrai,
       filtre mt.mt_kind avec
         Some (Module_type_alias _) -> vrai
       | _ -> faux
      )
    soit p_class c _ = (faux, faux)
    soit p_class_type ct _ = (faux, faux)
    soit p_value v _ = faux
    soit p_recfield _ _ _ = faux
    soit p_const _ _ _ = faux
    soit p_type t _ = (faux, faux)
    soit p_exception e _ = e.ex_alias <> None
    soit p_attribute a _ = faux
    soit p_method m _ = faux
    soit p_section s _ = faux
  fin

(** The module used to get the aliased elements. *)
module Search_alias = Odoc_search.Search (P_alias)

type alias_state =
    Alias_resolved
  | Alias_to_resolve

(** Couples of module name aliases. *)
soit (module_aliases : (Name.t, Name.t * alias_state) Hashtbl.t) = Hashtbl.create 13 ;;

(** Couples of module or module type name aliases. *)
soit module_and_modtype_aliases = Hashtbl.create 13;;

(** Couples of exception name aliases. *)
soit exception_aliases = Hashtbl.create 13;;

soit rec build_alias_list = fonction
    [] -> ()
  | (Odoc_search.Res_module m) :: q ->
      (
       filtre m.m_kind avec
         Module_alias ma ->
           Hashtbl.add module_aliases m.m_name (ma.ma_name, Alias_to_resolve);
           Hashtbl.add module_and_modtype_aliases m.m_name (ma.ma_name, Alias_to_resolve)
       | _ -> ()
      );
      build_alias_list q
  | (Odoc_search.Res_module_type mt) :: q ->
      (
       filtre mt.mt_kind avec
         Some (Module_type_alias mta) ->
           Hashtbl.add module_and_modtype_aliases
             mt.mt_name (mta.mta_name, Alias_to_resolve)
       | _ -> ()
      );
      build_alias_list q
  | (Odoc_search.Res_exception e) :: q ->
      (
       filtre e.ex_alias avec
         None -> ()
       | Some ea ->
           Hashtbl.add exception_aliases
             e.ex_name (ea.ea_name,Alias_to_resolve)
      );
      build_alias_list q
  | _ :: q ->
      build_alias_list q

(** Retrieve the aliases for modules, module types and exceptions
   and put them in global hash tables. *)
soit get_alias_names module_list =
  Hashtbl.clear module_aliases;
  Hashtbl.clear module_and_modtype_aliases;
  Hashtbl.clear exception_aliases;
  build_alias_list (Search_alias.search module_list 0)

exception Found de string
soit name_alias =
  soit rec f t name =
    essaie
      filtre Hashtbl.find t name avec
        (s, Alias_resolved) -> s
      | (s, Alias_to_resolve) -> f t s
    avec
      Not_found ->
        essaie
          Hashtbl.iter
            (fonc n2 (n3, _) ->
              si Name.prefix n2 name alors
                soit ln2 = String.length n2 dans
                soit s = n3^(String.sub name ln2 ((String.length name) - ln2)) dans
                raise (Found s)
            )
            t ;
          Hashtbl.replace t name (name, Alias_resolved);
          name
        avec
          Found s ->
            soit s2 = f t s dans
            Hashtbl.replace t s2 (s2, Alias_resolved);
            s2
  dans
  fonc name alias_tbl ->
    f alias_tbl name


module Map_ord =
  struct
    type t = string
    soit compare (x:t) y = Pervasives.compare x y
  fin

module Ele_map = Map.Make (Map_ord)

soit known_elements = ref Ele_map.empty
soit add_known_element name k =
  essaie
    soit l = Ele_map.find name !known_elements dans
    soit s = Ele_map.remove name !known_elements dans
    known_elements := Ele_map.add name (k::l) s
  avec
    Not_found ->
      known_elements := Ele_map.add name [k] !known_elements

soit rec get_known_elements name =
  essaie Ele_map.find name !known_elements
  avec Not_found -> []

soit kind_name_exists kind =
  soit pred =
    filtre kind avec
      RK_module -> (fonc e -> filtre e avec Odoc_search.Res_module _ -> vrai | _ -> faux)
    | RK_module_type -> (fonc e -> filtre e avec Odoc_search.Res_module_type _ -> vrai | _ -> faux)
    | RK_class -> (fonc e -> filtre e avec Odoc_search.Res_class _ -> vrai | _ -> faux)
    | RK_class_type -> (fonc e -> filtre e avec Odoc_search.Res_class_type _ -> vrai | _ -> faux)
    | RK_value -> (fonc e -> filtre e avec Odoc_search.Res_value _ -> vrai | _ -> faux)
    | RK_type -> (fonc e -> filtre e avec Odoc_search.Res_type _ -> vrai | _ -> faux)
    | RK_exception -> (fonc e -> filtre e avec Odoc_search.Res_exception _ -> vrai | _ -> faux)
    | RK_attribute -> (fonc e -> filtre e avec Odoc_search.Res_attribute _ -> vrai | _ -> faux)
    | RK_method -> (fonc e -> filtre e avec Odoc_search.Res_method _ -> vrai | _ -> faux)
    | RK_section _ -> affirme faux
    | RK_recfield -> (fonc e -> filtre e avec Odoc_search.Res_recfield _ -> vrai | _ -> faux)
    | RK_const -> (fonc e -> filtre e avec Odoc_search.Res_const _ -> vrai | _ -> faux)
  dans
  fonc name ->
    essaie List.exists pred (get_known_elements name)
    avec Not_found -> faux

soit module_exists = kind_name_exists RK_module
soit module_type_exists = kind_name_exists RK_module_type
soit class_exists = kind_name_exists RK_class
soit class_type_exists = kind_name_exists RK_class_type
soit value_exists = kind_name_exists RK_value
soit type_exists = kind_name_exists RK_type
soit exception_exists = kind_name_exists RK_exception
soit attribute_exists = kind_name_exists RK_attribute
soit method_exists = kind_name_exists RK_method
soit recfield_exists = kind_name_exists RK_recfield
soit const_exists = kind_name_exists RK_const

soit lookup_module name =
  filtre List.find
      (fonc k -> filtre k avec Odoc_search.Res_module _ -> vrai | _ -> faux)
      (get_known_elements name)
  avec
  | Odoc_search.Res_module m -> m
  | _ -> affirme faux

soit lookup_module_type name =
  filtre List.find
      (fonc k -> filtre k avec Odoc_search.Res_module_type _ -> vrai | _ -> faux)
      (get_known_elements name)
  avec
  | Odoc_search.Res_module_type m -> m
  | _ -> affirme faux

soit lookup_class name =
  filtre List.find
      (fonc k -> filtre k avec Odoc_search.Res_class _ -> vrai | _ -> faux)
      (get_known_elements name)
  avec
  | Odoc_search.Res_class c -> c
  | _ -> affirme faux

soit lookup_class_type name =
  filtre List.find
      (fonc k -> filtre k avec Odoc_search.Res_class_type _ -> vrai | _ -> faux)
      (get_known_elements name)
  avec
  | Odoc_search.Res_class_type c -> c
  | _ -> affirme faux

soit lookup_exception name =
  filtre List.find
      (fonc k -> filtre k avec Odoc_search.Res_exception _ -> vrai | _ -> faux)
      (get_known_elements name)
  avec
  | Odoc_search.Res_exception e -> e
  | _ -> affirme faux

classe scan =
  objet
    hérite Odoc_scan.scanner
    méthode! scan_value v =
      add_known_element v.val_name (Odoc_search.Res_value v)
    méthode! scan_type_recfield t f =
      add_known_element
        (Printf.sprintf "%s.%s" t.ty_name f.rf_name)
        (Odoc_search.Res_recfield (t, f))
    méthode! scan_type_const t f =
      add_known_element
        (Printf.sprintf "%s.%s" t.ty_name f.vc_name)
        (Odoc_search.Res_const (t, f))
    méthode! scan_type_pre t =
      add_known_element t.ty_name (Odoc_search.Res_type t);
      vrai
    méthode! scan_exception e =
      add_known_element e.ex_name (Odoc_search.Res_exception e)
    méthode! scan_attribute a =
      add_known_element a.att_value.val_name
        (Odoc_search.Res_attribute a)
    méthode! scan_method m =
      add_known_element m.met_value.val_name
        (Odoc_search.Res_method m)
    méthode! scan_class_pre c =
      add_known_element c.cl_name (Odoc_search.Res_class c);
      vrai
    méthode! scan_class_type_pre c =
      add_known_element c.clt_name (Odoc_search.Res_class_type c);
      vrai
    méthode! scan_module_pre m =
      add_known_element m.m_name (Odoc_search.Res_module m);
      vrai
    méthode! scan_module_type_pre m =
      add_known_element m.mt_name (Odoc_search.Res_module_type m);
      vrai

  fin

soit init_known_elements_map module_list =
  soit c = nouv scan dans
  c#scan_module_list module_list


(** The type to describe the names not found. *)
type not_found_name =
    NF_m de Name.t
  | NF_mt de Name.t
  | NF_mmt de Name.t
  | NF_c de Name.t
  | NF_ct de Name.t
  | NF_cct de Name.t
  | NF_ex de Name.t

(** Functions to find and associate aliases elements. *)

soit rec associate_in_module module_list (acc_b_modif, acc_incomplete_top_module_names, acc_names_not_found) m =
  soit rec iter_kind (acc_b, acc_inc, acc_names) k =
    filtre k avec
      Module_struct elements ->
        List.fold_left
          (associate_in_module_element module_list m.m_name)
          (acc_b, acc_inc, acc_names)
          elements

    | Module_alias ma ->
        (
         filtre ma.ma_module avec
           Some _ ->
             (acc_b, acc_inc, acc_names)
         | None ->
             soit mmt_opt =
               essaie Some (Mod (lookup_module ma.ma_name))
               avec Not_found ->
                 essaie Some (Modtype (lookup_module_type ma.ma_name))
                 avec Not_found -> None
             dans
             filtre mmt_opt avec
               None -> (acc_b, (Name.head m.m_name) :: acc_inc,
                        (* we don't want to output warning messages for
                           "sig ... end" or "struct ... end" modules not found *)
                        (si ma.ma_name = Odoc_messages.struct_end ||
                          ma.ma_name = Odoc_messages.sig_end alors
                          acc_names
                        sinon
                          (NF_mmt ma.ma_name) :: acc_names)
                       )
             | Some mmt ->
                 ma.ma_module <- Some mmt ;
                 (vrai, acc_inc, acc_names)
        )

    | Module_functor (_, k) ->
        iter_kind (acc_b, acc_inc, acc_names) k

    | Module_with (tk, _) ->
        associate_in_module_type module_list (acc_b, acc_inc, acc_names)
          { mt_name = "" ; mt_info = None ; mt_type = None ;
            mt_is_interface = faux ; mt_file = ""; mt_kind = Some tk ;
            mt_loc = Odoc_types.dummy_loc }

    | Module_apply (k1, k2) ->
        soit (acc_b2, acc_inc2, acc_names2) = iter_kind (acc_b, acc_inc, acc_names) k1 dans
        iter_kind (acc_b2, acc_inc2, acc_names2) k2

    | Module_constraint (k, tk) ->
        soit (acc_b2, acc_inc2, acc_names2) = iter_kind (acc_b, acc_inc, acc_names) k dans
        associate_in_module_type module_list (acc_b2, acc_inc2, acc_names2)
          { mt_name = "" ; mt_info = None ; mt_type = None ;
            mt_is_interface = faux ; mt_file = "" ; mt_kind = Some tk ;
            mt_loc = Odoc_types.dummy_loc }

     | Module_typeof _ ->
        (acc_b, acc_inc, acc_names)

     | Module_unpack (code, mta) ->
        début
          filtre mta.mta_module avec
            Some _ ->
              (acc_b, acc_inc, acc_names)
          | None ->
              soit mt_opt =
                essaie Some (lookup_module_type mta.mta_name)
                avec Not_found -> None
              dans
              filtre mt_opt avec
                None -> (acc_b, (Name.head m.m_name) :: acc_inc,
                   (* we don't want to output warning messages for
                      "sig ... end" or "struct ... end" modules not found *)
                   (si mta.mta_name = Odoc_messages.struct_end ||
                      mta.mta_name = Odoc_messages.sig_end alors
                      acc_names
                    sinon
                      (NF_mt mta.mta_name) :: acc_names)
                  )
              | Some mt ->
                  mta.mta_module <- Some mt ;
                  (vrai, acc_inc, acc_names)
        fin
  dans
  iter_kind (acc_b_modif, acc_incomplete_top_module_names, acc_names_not_found) m.m_kind

et associate_in_module_type module_list (acc_b_modif, acc_incomplete_top_module_names, acc_names_not_found) mt =
  soit rec iter_kind (acc_b, acc_inc, acc_names) k =
    filtre k avec
      Module_type_struct elements ->
        List.fold_left
          (associate_in_module_element module_list mt.mt_name)
          (acc_b, acc_inc, acc_names)
          elements

    | Module_type_functor (_, k) ->
        iter_kind (acc_b, acc_inc, acc_names) k

    | Module_type_with (k, _) ->
        iter_kind (acc_b, acc_inc, acc_names) k

    | Module_type_alias mta ->
        début
          filtre mta.mta_module avec
            Some _ ->
              (acc_b, acc_inc, acc_names)
          | None ->
              soit mt_opt =
                essaie Some (lookup_module_type mta.mta_name)
                avec Not_found -> None
              dans
              filtre mt_opt avec
                None -> (acc_b, (Name.head mt.mt_name) :: acc_inc,
                   (* we don't want to output warning messages for
                      "sig ... end" or "struct ... end" modules not found *)
                   (si mta.mta_name = Odoc_messages.struct_end ||
                      mta.mta_name = Odoc_messages.sig_end alors
                      acc_names
                    sinon
                      (NF_mt mta.mta_name) :: acc_names)
                  )
              | Some mt ->
                  mta.mta_module <- Some mt ;
                  (vrai, acc_inc, acc_names)
        fin
    | Module_type_typeof _ ->
        (acc_b, acc_inc, acc_names)
  dans
  filtre mt.mt_kind avec
    None -> (acc_b_modif, acc_incomplete_top_module_names, acc_names_not_found)
  | Some k -> iter_kind (acc_b_modif, acc_incomplete_top_module_names, acc_names_not_found) k

et associate_in_module_element module_list m_name (acc_b_modif, acc_incomplete_top_module_names, acc_names_not_found) element =
   filtre element avec
     Element_module m -> associate_in_module module_list (acc_b_modif, acc_incomplete_top_module_names, acc_names_not_found) m
   | Element_module_type mt -> associate_in_module_type module_list (acc_b_modif, acc_incomplete_top_module_names, acc_names_not_found) mt
   | Element_included_module im ->
       (
        filtre im.im_module avec
          Some _ -> (acc_b_modif, acc_incomplete_top_module_names, acc_names_not_found)
        | None ->
            soit mmt_opt =
              essaie Some (Mod (lookup_module im.im_name))
              avec Not_found ->
                essaie Some (Modtype (lookup_module_type im.im_name))
                avec Not_found -> None
            dans
            filtre mmt_opt avec
              None -> (acc_b_modif, (Name.head m_name) :: acc_incomplete_top_module_names,
                       (* we don't want to output warning messages for
                           "sig ... end" or "struct ... end" modules not found *)
                        (si im.im_name = Odoc_messages.struct_end ||
                          im.im_name = Odoc_messages.sig_end alors
                          acc_names_not_found
                        sinon
                          (NF_mmt im.im_name) :: acc_names_not_found)
                      )
            | Some mmt ->
                im.im_module <- Some mmt ;
                (vrai, acc_incomplete_top_module_names, acc_names_not_found)
       )
   | Element_class cl -> associate_in_class module_list (acc_b_modif, acc_incomplete_top_module_names, acc_names_not_found) cl
   | Element_class_type ct -> associate_in_class_type module_list (acc_b_modif, acc_incomplete_top_module_names, acc_names_not_found) ct
   | Element_value _ -> (acc_b_modif, acc_incomplete_top_module_names, acc_names_not_found)
   | Element_exception ex ->
       (
        filtre ex.ex_alias avec
          None -> (acc_b_modif, acc_incomplete_top_module_names, acc_names_not_found)
        | Some ea ->
            filtre ea.ea_ex avec
              Some _ ->
                (acc_b_modif, acc_incomplete_top_module_names, acc_names_not_found)
            | None ->
                soit ex_opt =
                  essaie Some (lookup_exception ea.ea_name)
                  avec Not_found -> None
                dans
                filtre ex_opt avec
                  None -> (acc_b_modif, (Name.head m_name) :: acc_incomplete_top_module_names, (NF_ex ea.ea_name) :: acc_names_not_found)
                | Some e ->
                    ea.ea_ex <- Some e ;
                    (vrai, acc_incomplete_top_module_names, acc_names_not_found)
       )
   | Element_type _ -> (acc_b_modif, acc_incomplete_top_module_names, acc_names_not_found)
   | Element_module_comment _ -> (acc_b_modif, acc_incomplete_top_module_names, acc_names_not_found)

et associate_in_class module_list (acc_b_modif, acc_incomplete_top_module_names, acc_names_not_found) c =
  soit rec iter_kind (acc_b, acc_inc, acc_names) k =
    filtre k avec
      Class_structure (inher_l, _) ->
        soit f (acc_b2, acc_inc2, acc_names2) ic =
          filtre ic.ic_class avec
          Some _ -> (acc_b2, acc_inc2, acc_names2)
        | None ->
            soit cct_opt =
              essaie Some (Cl (lookup_class ic.ic_name))
              avec Not_found ->
                essaie Some (Cltype (lookup_class_type ic.ic_name, []))
                avec Not_found -> None
            dans
            filtre cct_opt avec
              None -> (acc_b2, (Name.head c.cl_name) :: acc_inc2,
                       (* we don't want to output warning messages for "object ... end" classes not found *)
                       (si ic.ic_name = Odoc_messages.object_end alors acc_names2 sinon (NF_cct ic.ic_name) :: acc_names2))
            | Some cct ->
                ic.ic_class <- Some cct ;
                (vrai, acc_inc2, acc_names2)
        dans
        List.fold_left f (acc_b, acc_inc, acc_names) inher_l

    | Class_apply capp ->
        (
         filtre capp.capp_class avec
           Some _ ->  (acc_b, acc_inc, acc_names)
         | None ->
             soit cl_opt =
               essaie Some (lookup_class capp.capp_name)
               avec Not_found -> None
             dans
             filtre cl_opt avec
               None -> (acc_b, (Name.head c.cl_name) :: acc_inc,
                        (* we don't want to output warning messages for "object ... end" classes not found *)
                        (si capp.capp_name = Odoc_messages.object_end alors acc_names sinon (NF_c capp.capp_name) :: acc_names))
             | Some c ->
                 capp.capp_class <- Some c ;
                 (vrai, acc_inc, acc_names)
        )

    | Class_constr cco ->
        (
         filtre cco.cco_class avec
           Some _ ->  (acc_b, acc_inc, acc_names)
         | None ->
             soit cl_opt =
               essaie Some (lookup_class cco.cco_name)
               avec Not_found -> None
             dans
             filtre cl_opt avec
               None ->
                 (
                  soit clt_opt =
                    essaie Some (lookup_class_type cco.cco_name)
                    avec Not_found -> None
                  dans
                  filtre clt_opt avec
                    None ->
                      (acc_b, (Name.head c.cl_name) :: acc_inc,
                        (* we don't want to output warning messages for "object ... end" classes not found *)
                       (si cco.cco_name = Odoc_messages.object_end alors acc_names sinon (NF_cct cco.cco_name) :: acc_names))
                  | Some ct ->
                      cco.cco_class <- Some (Cltype (ct, [])) ;
                      (vrai, acc_inc, acc_names)
                 )
             | Some c ->
                 cco.cco_class <- Some (Cl c) ;
                 (vrai, acc_inc, acc_names)
        )
    | Class_constraint (ckind, ctkind) ->
        soit (acc_b2, acc_inc2, acc_names2) = iter_kind (acc_b, acc_inc, acc_names) ckind dans
        associate_in_class_type module_list (acc_b2, acc_inc2, acc_names2)
            { clt_name = "" ; clt_info = None ;
              clt_type = c.cl_type ; (* should be ok *)
              clt_type_parameters = [] ;
              clt_virtual = faux ;
              clt_kind = ctkind ;
              clt_loc = Odoc_types.dummy_loc }
  dans
  iter_kind (acc_b_modif, acc_incomplete_top_module_names, acc_names_not_found) c.cl_kind

et associate_in_class_type module_list (acc_b_modif, acc_incomplete_top_module_names, acc_names_not_found) ct =
  soit rec iter_kind (acc_b, acc_inc, acc_names) k =
    filtre k avec
      Class_signature (inher_l, _) ->
        soit f (acc_b2, acc_inc2, acc_names2) ic =
          filtre ic.ic_class avec
            Some _ -> (acc_b2, acc_inc2, acc_names2)
          | None ->
              soit cct_opt =
                essaie Some (Cltype (lookup_class_type ic.ic_name, []))
                avec Not_found ->
                  essaie Some (Cl (lookup_class ic.ic_name))
                  avec Not_found -> None
              dans
              filtre cct_opt avec
                None -> (acc_b2, (Name.head ct.clt_name) :: acc_inc2,
                         (* we don't want to output warning messages for "object ... end" class types not found *)
                         (si ic.ic_name = Odoc_messages.object_end alors acc_names2 sinon (NF_cct ic.ic_name) :: acc_names2))
              | Some cct ->
                  ic.ic_class <- Some cct ;
                  (vrai, acc_inc2, acc_names2)
        dans
        List.fold_left f (acc_b, acc_inc, acc_names) inher_l

    | Class_type cta ->
        (
         filtre cta.cta_class avec
           Some _ ->  (acc_b, acc_inc, acc_names)
         | None ->
             soit cct_opt =
               essaie Some (Cltype (lookup_class_type cta.cta_name, []))
               avec Not_found ->
                 essaie Some (Cl (lookup_class cta.cta_name))
                 avec Not_found -> None
             dans
             filtre cct_opt avec
               None -> (acc_b, (Name.head ct.clt_name) :: acc_inc,
                        (* we don't want to output warning messages for "object ... end" class types not found *)
                        (si cta.cta_name = Odoc_messages.object_end alors acc_names sinon (NF_cct cta.cta_name) :: acc_names))
             | Some c ->
                 cta.cta_class <- Some c ;
                 (vrai, acc_inc, acc_names)
        )
  dans
  iter_kind (acc_b_modif, acc_incomplete_top_module_names, acc_names_not_found) ct.clt_kind

(*************************************************************)
(** Association of types to elements referenced in comments .*)

soit ao = Odoc_misc.apply_opt

soit not_found_of_kind kind name =
  (filtre kind avec
    RK_module -> Odoc_messages.cross_module_not_found
  | RK_module_type -> Odoc_messages.cross_module_type_not_found
  | RK_class -> Odoc_messages.cross_class_not_found
  | RK_class_type -> Odoc_messages.cross_class_type_not_found
  | RK_value -> Odoc_messages.cross_value_not_found
  | RK_type -> Odoc_messages.cross_type_not_found
  | RK_exception -> Odoc_messages.cross_exception_not_found
  | RK_attribute -> Odoc_messages.cross_attribute_not_found
  | RK_method -> Odoc_messages.cross_method_not_found
  | RK_section _ -> Odoc_messages.cross_section_not_found
  | RK_recfield -> Odoc_messages.cross_recfield_not_found
  | RK_const -> Odoc_messages.cross_const_not_found
  ) name

soit rec assoc_comments_text_elements parent_name module_list t_ele =
  filtre t_ele avec
  | Raw _
  | Code _
  | CodePre _
  | Latex _
  | Verbatim _ -> t_ele
  | Bold t -> Bold (assoc_comments_text parent_name module_list t)
  | Italic t -> Italic (assoc_comments_text parent_name module_list t)
  | Center t -> Center (assoc_comments_text parent_name module_list t)
  | Left t -> Left (assoc_comments_text parent_name module_list t)
  | Right t -> Right (assoc_comments_text parent_name module_list t)
  | Emphasize t -> Emphasize (assoc_comments_text parent_name module_list t)
  | List l -> List (List.map (assoc_comments_text parent_name module_list) l)
  | Enum l -> Enum (List.map (assoc_comments_text parent_name module_list) l)
  | Newline -> Newline
  | Block t -> Block (assoc_comments_text parent_name module_list t)
  | Superscript t -> Superscript (assoc_comments_text parent_name module_list t)
  | Subscript t -> Subscript (assoc_comments_text parent_name module_list t)
  | Title (n, l_opt, t) -> Title (n, l_opt, (assoc_comments_text parent_name module_list t))
  | Link (s, t) -> Link (s, (assoc_comments_text parent_name module_list t))
  | Ref (initial_name, None, text_option) ->
      (
       soit rec iter_parent ?parent_name name =
         soit name = Odoc_name.normalize_name name dans
         soit res =
           filtre get_known_elements name avec
             [] ->
               (
                essaie
                  soit re = Str.regexp ("^"^(Str.quote name)^"$") dans
                  soit t = Odoc_search.find_section module_list re dans
                  soit v2 = (name, Some (RK_section t)) dans
                  add_verified v2 ;
                  (name, Some (RK_section t))
              avec
                  Not_found ->
                    (name, None)
               )
           | ele :: _ ->
           (* we look for the first element with this name *)
               soit (name, kind) =
                 filtre ele avec
                   Odoc_search.Res_module m -> (m.m_name, RK_module)
                 | Odoc_search.Res_module_type mt -> (mt.mt_name, RK_module_type)
                 | Odoc_search.Res_class c -> (c.cl_name, RK_class)
                 | Odoc_search.Res_class_type ct -> (ct.clt_name, RK_class_type)
                 | Odoc_search.Res_value v -> (v.val_name, RK_value)
                 | Odoc_search.Res_type t -> (t.ty_name, RK_type)
                 | Odoc_search.Res_exception e -> (e.ex_name, RK_exception)
                 | Odoc_search.Res_attribute a -> (a.att_value.val_name, RK_attribute)
                 | Odoc_search.Res_method m -> (m.met_value.val_name, RK_method)
                 | Odoc_search.Res_section (_ ,t)-> affirme faux
                 | Odoc_search.Res_recfield (t, f) ->
                     (Printf.sprintf "%s.%s" t.ty_name f.rf_name, RK_recfield)
                 | Odoc_search.Res_const (t, f) ->
                     (Printf.sprintf "%s.%s" t.ty_name f.vc_name, RK_const)
               dans
               add_verified (name, Some kind) ;
               (name, Some kind)
         dans
         filtre res avec
         | (name, Some k) -> Ref (name, Some k, text_option)
         | (_, None) ->
             filtre parent_name avec
               None ->
                 Odoc_global.pwarning (Odoc_messages.cross_element_not_found initial_name);
                 Ref (initial_name, None, text_option)
             | Some p ->
                 soit parent_name =
                   filtre Name.father p avec
                     "" -> None
                   | s -> Some s
                 dans
                 iter_parent ?parent_name (Name.concat p initial_name)
       dans
       iter_parent ~parent_name initial_name
      )
  | Ref (initial_name, Some kind, text_option) ->
      (
       soit rec iter_parent ?parent_name name =
         soit v = (name, Some kind) dans
         si was_verified v alors
           Ref (name, Some kind, text_option)
         sinon
           soit res =
             filtre kind avec
             | RK_section _ ->
                 (
                  (** we just verify that we find an element of this kind with this name *)
                  essaie
                    soit re = Str.regexp ("^"^(Str.quote name)^"$") dans
                    soit t = Odoc_search.find_section module_list re dans
                    soit v2 = (name, Some (RK_section t)) dans
                    add_verified v2 ;
                    (name, Some (RK_section t))
                  avec
                    Not_found ->
                      (name, None)
                 )
             | _ ->
                 soit f =
                   filtre kind avec
                     RK_module -> module_exists
                   | RK_module_type -> module_type_exists
                   | RK_class -> class_exists
                   | RK_class_type -> class_type_exists
                   | RK_value -> value_exists
                   | RK_type -> type_exists
                   | RK_exception -> exception_exists
                   | RK_attribute -> attribute_exists
                   | RK_method -> method_exists
                   | RK_section _ -> affirme faux
                   | RK_recfield -> recfield_exists
                   | RK_const -> const_exists
                 dans
                 si f name alors
                   (
                    add_verified v ;
                    (name, Some kind)
                   )
                 sinon
                   (name, None)
           dans
           filtre res avec
           | (name, Some k) -> Ref (name, Some k, text_option)
           | (_, None) ->
               filtre parent_name avec
                 None ->
                   Odoc_global.pwarning (not_found_of_kind kind initial_name);
                   Ref (initial_name, None, text_option)
               | Some p ->
                   soit parent_name =
                     filtre Name.father p avec
                       "" -> None
                     | s -> Some s
                   dans
                   iter_parent ?parent_name (Name.concat p initial_name)
       dans
       iter_parent ~parent_name initial_name
      )
  | Module_list l ->
      Module_list l
  | Index_list ->
      Index_list
  | Custom (s,t) -> Custom (s, (assoc_comments_text parent_name module_list t))
  | Target (target, code) -> Target (target, code)

et assoc_comments_text parent_name module_list text =
  List.map (assoc_comments_text_elements parent_name module_list) text

et assoc_comments_info parent_name module_list i =
  soit ft = assoc_comments_text parent_name module_list dans
  {
    i avec
    i_desc = ao ft i.i_desc ;
    i_sees = List.map (fonc (sr, t) -> (sr, ft t)) i.i_sees;
    i_deprecated = ao ft i.i_deprecated ;
    i_params = List.map (fonc (name, t) -> (name, ft t)) i.i_params;
    i_raised_exceptions = List.map (fonc (name, t) -> (name, ft t)) i.i_raised_exceptions;
    i_return_value = ao ft i.i_return_value ;
    i_custom = List.map (fonc (tag, t) -> (tag, ft t)) i.i_custom ;
  }


soit rec assoc_comments_module_element parent_name module_list m_ele =
  filtre m_ele avec
    Element_module m ->
      Element_module (assoc_comments_module module_list m)
  | Element_module_type mt ->
      Element_module_type (assoc_comments_module_type module_list mt)
  | Element_included_module _ ->
      m_ele (* don't go down into the aliases *)
  | Element_class c ->
      Element_class (assoc_comments_class module_list c)
  | Element_class_type ct ->
      Element_class_type (assoc_comments_class_type module_list ct)
  | Element_value v ->
      Element_value (assoc_comments_value module_list v)
  | Element_exception e ->
      Element_exception (assoc_comments_exception module_list e)
  | Element_type t ->
      Element_type (assoc_comments_type module_list t)
  | Element_module_comment t ->
      Element_module_comment (assoc_comments_text parent_name module_list t)

et assoc_comments_class_element parent_name module_list c_ele =
  filtre c_ele avec
    Class_attribute a ->
      Class_attribute (assoc_comments_attribute module_list a)
  | Class_method m ->
      Class_method (assoc_comments_method module_list m)
  | Class_comment t ->
      Class_comment (assoc_comments_text parent_name module_list t)

et assoc_comments_module_kind parent_name module_list mk =
  filtre mk avec
  | Module_struct eles ->
      Module_struct
        (List.map (assoc_comments_module_element parent_name module_list) eles)
  | Module_alias _
  | Module_functor _ ->
      mk
  | Module_apply (mk1, mk2) ->
      Module_apply (assoc_comments_module_kind parent_name module_list mk1,
                    assoc_comments_module_kind parent_name module_list mk2)
  | Module_with (mtk, s) ->
      Module_with (assoc_comments_module_type_kind parent_name module_list mtk, s)
  | Module_constraint (mk1, mtk) ->
      Module_constraint
        (assoc_comments_module_kind parent_name module_list mk1,
         assoc_comments_module_type_kind parent_name module_list mtk)
  | Module_typeof _ -> mk
  | Module_unpack _ -> mk

et assoc_comments_module_type_kind parent_name module_list mtk =
  filtre mtk avec
  | Module_type_struct eles ->
      Module_type_struct
        (List.map (assoc_comments_module_element parent_name module_list) eles)
  | Module_type_functor (params, mtk1) ->
      Module_type_functor
        (params, assoc_comments_module_type_kind parent_name module_list mtk1)
  | Module_type_alias _ ->
      mtk
  | Module_type_with (mtk1, s) ->
      Module_type_with
        (assoc_comments_module_type_kind parent_name module_list mtk1, s)
  | Module_type_typeof _ -> mtk

et assoc_comments_class_kind parent_name module_list ck =
  filtre ck avec
    Class_structure (inher, eles) ->
      soit inher2 =
        List.map
          (fonc ic ->
            { ic avec
              ic_text = ao (assoc_comments_text parent_name module_list) ic.ic_text })
          inher
      dans
      Class_structure
        (inher2, List.map (assoc_comments_class_element parent_name module_list) eles)

  | Class_apply _
  | Class_constr _ -> ck
  | Class_constraint (ck1, ctk) ->
      Class_constraint (assoc_comments_class_kind parent_name module_list ck1,
                        assoc_comments_class_type_kind parent_name module_list ctk)

et assoc_comments_class_type_kind parent_name module_list ctk =
  filtre ctk avec
    Class_signature (inher, eles) ->
      soit inher2 =
        List.map
          (fonc ic -> { ic avec
                       ic_text = ao (assoc_comments_text parent_name module_list) ic.ic_text })
          inher
      dans
      Class_signature (inher2, List.map (assoc_comments_class_element parent_name module_list) eles)

  | Class_type _ -> ctk


et assoc_comments_module module_list m =
  m.m_info <- ao (assoc_comments_info m.m_name module_list) m.m_info ;
  m.m_kind <- assoc_comments_module_kind m.m_name module_list m.m_kind ;
  m

et assoc_comments_module_type module_list mt =
  mt.mt_info <- ao (assoc_comments_info mt.mt_name module_list) mt.mt_info ;
  mt.mt_kind <- ao (assoc_comments_module_type_kind mt.mt_name module_list) mt.mt_kind ;
  mt

et assoc_comments_class module_list c =
  c.cl_info <- ao (assoc_comments_info c.cl_name module_list) c.cl_info ;
  c.cl_kind <- assoc_comments_class_kind c.cl_name module_list c.cl_kind ;
  assoc_comments_parameter_list c.cl_name module_list c.cl_parameters;
  c

et assoc_comments_class_type module_list ct =
  ct.clt_info <- ao (assoc_comments_info ct.clt_name module_list) ct.clt_info ;
  ct.clt_kind <- assoc_comments_class_type_kind ct.clt_name module_list ct.clt_kind ;
  ct

et assoc_comments_parameter parent_name module_list p =
  filtre p avec
    Simple_name sn ->
      sn.sn_text <- ao (assoc_comments_text parent_name module_list) sn.sn_text
  | Tuple (l, t) ->
      List.iter (assoc_comments_parameter parent_name module_list) l

et assoc_comments_parameter_list parent_name module_list pl =
  List.iter (assoc_comments_parameter parent_name module_list) pl

et assoc_comments_value module_list v =
  soit parent = Name.father v.val_name dans
  v.val_info <- ao (assoc_comments_info parent module_list) v.val_info ;
  assoc_comments_parameter_list parent module_list v.val_parameters;
  v

et assoc_comments_exception module_list e =
  soit parent = Name.father e.ex_name dans
  e.ex_info <- ao (assoc_comments_info parent module_list) e.ex_info ;
  e

et assoc_comments_type module_list t =
  soit parent = Name.father t.ty_name dans
  t.ty_info <- ao (assoc_comments_info parent module_list) t.ty_info ;
  (filtre t.ty_kind avec
    Type_abstract -> ()
  | Type_variant vl ->
      List.iter
        (fonc vc -> vc.vc_text <- ao (assoc_comments_info parent module_list) vc.vc_text)
        vl
  | Type_record fl ->
      List.iter
        (fonc rf -> rf.rf_text <- ao (assoc_comments_info parent module_list) rf.rf_text)
        fl
  );
  t

et assoc_comments_attribute module_list a =
  soit _ = assoc_comments_value module_list a.att_value dans
  a

et assoc_comments_method module_list m =
  soit parent_name = Name.father m.met_value.val_name dans
  soit _ = assoc_comments_value module_list m.met_value dans
  assoc_comments_parameter_list parent_name module_list m.met_value.val_parameters;
  m


soit associate_type_of_elements_in_comments module_list =
  List.map (assoc_comments_module module_list) module_list


(***********************************************************)
(** The function which performs all the cross referencing. *)
soit associate module_list =
  get_alias_names module_list ;
  init_known_elements_map module_list;
  soit rec remove_doubles acc = fonction
      [] -> acc
    | h :: q ->
        si List.mem h acc alors remove_doubles acc q
        sinon remove_doubles (h :: acc) q
  dans
  soit rec iter incomplete_modules =
    soit (b_modif, remaining_inc_modules, acc_names_not_found) =
      List.fold_left (associate_in_module module_list) (faux, [], []) incomplete_modules
    dans
    soit remaining_no_doubles = remove_doubles [] remaining_inc_modules dans
    soit remaining_modules = List.filter
        (fonc m -> List.mem m.m_name remaining_no_doubles)
        incomplete_modules
    dans
    si b_modif alors
      (* we may be able to associate something else *)
      iter remaining_modules
    sinon
      (* nothing changed, we won't be able to associate any more *)
      acc_names_not_found
  dans
  soit names_not_found = iter module_list dans
  (
   filtre names_not_found avec
     [] ->
       ()
   | l ->
       List.iter
         (fonc nf ->
           Odoc_global.pwarning
             (
              filtre nf avec
                NF_m n -> Odoc_messages.cross_module_not_found n
              | NF_mt n -> Odoc_messages.cross_module_type_not_found n
              | NF_mmt n -> Odoc_messages.cross_module_or_module_type_not_found n
              | NF_c n -> Odoc_messages.cross_class_not_found n
              | NF_ct n -> Odoc_messages.cross_class_type_not_found n
              | NF_cct n -> Odoc_messages.cross_class_or_class_type_not_found n
              | NF_ex n -> Odoc_messages.cross_exception_not_found n
             );
         )
         l
  ) ;

  (* Find a type for each name of element which is referenced in comments. *)
  ignore (associate_type_of_elements_in_comments module_list)
