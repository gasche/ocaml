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

(** Research of elements through modules. *)

module Name = Odoc_name
ouvre Odoc_parameter
ouvre Odoc_value
ouvre Odoc_type
ouvre Odoc_exception
ouvre Odoc_class
ouvre Odoc_module

type result_element =
    Res_module de t_module
  | Res_module_type de t_module_type
  | Res_class de t_class
  | Res_class_type de t_class_type
  | Res_value de t_value
  | Res_type de t_type
  | Res_exception de t_exception
  | Res_attribute de t_attribute
  | Res_method de t_method
  | Res_section de string * Odoc_types.text
  | Res_recfield de t_type * record_field
  | Res_const de t_type * variant_constructor

type result = result_element list

module type Predicates =
  sig
    type t
    val p_module : t_module -> t -> bool * bool
    val p_module_type : t_module_type -> t -> bool * bool
    val p_class : t_class -> t -> bool * bool
    val p_class_type : t_class_type -> t -> bool * bool
    val p_value : t_value -> t -> bool
    val p_recfield : t_type -> record_field -> t -> bool
    val p_const : t_type -> variant_constructor -> t -> bool
    val p_type : t_type -> t -> (bool * bool)
    val p_exception : t_exception -> t -> bool
    val p_attribute : t_attribute -> t -> bool
    val p_method : t_method -> t -> bool
    val p_section : string -> t -> bool
  fin

module Search =
  foncteur (P : Predicates) ->
  struct
    soit search_section t s v = si P.p_section s v alors [Res_section (s,t)] sinon []

    soit rec search_text root t v =
      List.flatten (List.map (fonc e -> search_text_ele root e v) t)

    et search_text_ele root e v =
      soit module T = Odoc_types dans
      filtre e avec
      | T.Raw _
      | T.Code _
      | T.CodePre _
      | T.Latex _
      | T.Verbatim _
      | T.Ref (_, _, _) -> []
      | T.Bold t
      | T.Italic t
      | T.Center t
      | T.Left t
      | T.Right t
      | T.Emphasize t
      | T.Block t
      | T.Superscript t
      | T.Subscript t
      | T.Custom (_,t)
      | T.Link (_, t) -> search_text root t v
      | T.List l
      | T.Enum l -> List.flatten (List.map (fonc t -> search_text root t v) l)
      | T.Newline
      | T.Module_list _
      | T.Index_list -> []
      | T.Target _ -> []
      | T.Title (n, l_opt, t) ->
          (filtre l_opt avec
            None -> []
          | Some s -> search_section t (Name.concat root s) v) @
          (search_text root t v)

    soit search_value va v = si P.p_value va v alors [Res_value va] sinon []

    soit search_recfield t f v =
      si P.p_recfield t f v alors [Res_recfield (t,f)] sinon []

    soit search_const t f v =
      si P.p_const t f v alors [Res_const (t,f)] sinon []

    soit search_type t v =
      soit (go_deeper, ok) = P.p_type t v dans
      soit l =
        filtre go_deeper avec
          faux -> []
        | vrai ->
            filtre t.ty_kind avec
              Type_abstract -> []
            | Type_record l ->
                List.flatten (List.map (fonc rf -> search_recfield t rf v) l)
            | Type_variant l ->
                List.flatten (List.map (fonc rf -> search_const t rf v) l)
      dans
      si ok alors (Res_type t) :: l sinon l

    soit search_exception e v = si P.p_exception e v alors [Res_exception e] sinon []

    soit search_attribute a v = si P.p_attribute a v alors [Res_attribute a] sinon []

    soit search_method m v = si P.p_method m v alors [Res_method m] sinon []

    soit search_class c v =
      soit (go_deeper, ok) = P.p_class c v dans
      soit l =
        si go_deeper alors
          soit res_att =
            List.fold_left
              (fonc acc -> fonc att -> acc @ (search_attribute att v))
              []
              (Odoc_class.class_attributes c)
          dans
          soit res_met =
            List.fold_left
              (fonc acc -> fonc m -> acc @ (search_method m v))
              []
              (Odoc_class.class_methods c)
          dans
          soit res_sec =
            List.fold_left
              (fonc acc -> fonc t -> acc @ (search_text c.cl_name t v))
              []
              (Odoc_class.class_comments c)
          dans
          soit l = res_att @ res_met @ res_sec dans
          l
        sinon
          []
      dans
      si ok alors
        (Res_class c) :: l
      sinon
        l

    soit search_class_type ct v =
      soit (go_deeper, ok) = P.p_class_type ct v dans
      soit l =
        si go_deeper alors
          soit res_att =
            List.fold_left
              (fonc acc -> fonc att -> acc @ (search_attribute att v))
              []
              (Odoc_class.class_type_attributes ct)
          dans
          soit res_met =
            List.fold_left
              (fonc acc -> fonc m -> acc @ (search_method m v))
              []
              (Odoc_class.class_type_methods ct)
          dans
          soit res_sec =
            List.fold_left
              (fonc acc -> fonc t -> acc @ (search_text ct.clt_name t v))
              []
              (Odoc_class.class_type_comments ct)
          dans
          soit l = res_att @ res_met @ res_sec dans
          l
        sinon
          []
      dans
      si ok alors
        (Res_class_type ct) :: l
      sinon
        l

    soit rec search_module_type mt v =
      soit (go_deeper, ok) =  P.p_module_type mt v dans
      soit l =
        si go_deeper alors
          soit res_val =
            List.fold_left
              (fonc acc -> fonc va -> acc @ (search_value va v))
              []
              (Odoc_module.module_type_values mt)
          dans
          soit res_typ =
            List.fold_left
              (fonc acc -> fonc t -> acc @ (search_type t v))
              []
              (Odoc_module.module_type_types mt)
          dans
          soit res_exc =
            List.fold_left
              (fonc acc -> fonc e -> acc @ (search_exception e v))
              []
              (Odoc_module.module_type_exceptions mt)
          dans
          soit res_mod = search (Odoc_module.module_type_modules mt) v dans
          soit res_modtyp =
            List.fold_left
              (fonc acc -> fonc mt -> acc @ (search_module_type mt v))
              []
              (Odoc_module.module_type_module_types mt)
          dans
          soit res_cl =
            List.fold_left
              (fonc acc -> fonc cl -> acc @ (search_class cl v))
              []
              (Odoc_module.module_type_classes mt)
          dans
          soit res_cltyp =
            List.fold_left
              (fonc acc -> fonc clt -> acc @ (search_class_type clt v))
              []
              (Odoc_module.module_type_class_types mt)
          dans
          soit res_sec =
            List.fold_left
              (fonc acc -> fonc t -> acc @ (search_text mt.mt_name t v))
              []
              (Odoc_module.module_type_comments mt)
          dans
          soit l = res_val @ res_typ @ res_exc @ res_mod @
            res_modtyp @ res_cl @ res_cltyp @ res_sec
          dans
          l
        sinon
          []
      dans
      si ok alors
        (Res_module_type mt) :: l
      sinon
        l

    et search_module m v =
      soit (go_deeper, ok) =  P.p_module m v dans
      soit l =
        si go_deeper alors
          soit res_val =
            List.fold_left
              (fonc acc -> fonc va -> acc @ (search_value va v))
              []
              (Odoc_module.module_values m)
          dans
          soit res_typ =
            List.fold_left
              (fonc acc -> fonc t -> acc @ (search_type t v))
              []
              (Odoc_module.module_types m)
          dans
          soit res_exc =
            List.fold_left
              (fonc acc -> fonc e -> acc @ (search_exception e v))
              []
              (Odoc_module.module_exceptions m)
          dans
          soit res_mod = search (Odoc_module.module_modules m) v dans
          soit res_modtyp =
            List.fold_left
              (fonc acc -> fonc mt -> acc @ (search_module_type mt v))
              []
              (Odoc_module.module_module_types m)
          dans
          soit res_cl =
            List.fold_left
              (fonc acc -> fonc cl -> acc @ (search_class cl v))
              []
              (Odoc_module.module_classes m)
          dans
          soit res_cltyp =
            List.fold_left
              (fonc acc -> fonc clt -> acc @ (search_class_type clt v))
              []
              (Odoc_module.module_class_types m)
          dans
          soit res_sec =
            List.fold_left
              (fonc acc -> fonc t -> acc @ (search_text m.m_name t v))
              []
              (Odoc_module.module_comments m)
          dans
          soit l = res_val @ res_typ @ res_exc @ res_mod @
            res_modtyp @ res_cl @ res_cltyp @ res_sec
          dans
          l
        sinon
          []
      dans
      si ok alors
        (Res_module m) :: l
      sinon
        l

    et search module_list v =
      List.fold_left
        (fonc acc -> fonc m ->
          List.fold_left
            (fonc acc2 -> fonc ele ->
              si List.mem ele acc2 alors acc2 sinon acc2 @ [ele]
            )
            acc
            (search_module m v)
        )
        []
        module_list
  fin

module P_name =
  struct
    type t = Str.regexp
    soit (=~) name regexp = Str.string_match regexp name 0
    soit p_module m r = (vrai, m.m_name =~ r)
    soit p_module_type mt r = (vrai, mt.mt_name =~ r)
    soit p_class c r = (vrai, c.cl_name =~ r)
    soit p_class_type ct r = (vrai, ct.clt_name =~ r)
    soit p_value v r = v.val_name =~ r
    soit p_recfield t f r =
      soit name = Printf.sprintf "%s.%s" t.ty_name f.rf_name dans
      name =~ r
    soit p_const t f r =
      soit name = Printf.sprintf "%s.%s" t.ty_name f.vc_name dans
      name =~ r
    soit p_type t r = (vrai, t.ty_name =~ r)
    soit p_exception e r = e.ex_name =~ r
    soit p_attribute a r = a.att_value.val_name =~ r
    soit p_method m r = m.met_value.val_name =~ r
    soit p_section s r = s =~ r
  fin

module Search_by_name = Search ( P_name )

module P_values =
  struct
    type t = unit
    soit p_module _ _ = (vrai, faux)
    soit p_module_type _ _ = (vrai, faux)
    soit p_class _ _ = (faux, faux)
    soit p_class_type _ _ = (faux, faux)
    soit p_value _ _ = vrai
    soit p_recfield _ _ _ = faux
    soit p_const _ _ _ = faux
    soit p_type _ _ = (faux, faux)
    soit p_exception _ _ = faux
    soit p_attribute _ _ = faux
    soit p_method _ _ = faux
    soit p_section _ _ = faux
  fin
module Search_values = Search ( P_values )
soit values l =
  soit l_ele = Search_values.search l () dans
  soit p v1 v2 = v1.val_name = v2.val_name dans
  soit rec iter acc = fonction
      (Res_value v) :: q -> si List.exists (p v) acc alors iter acc q sinon iter (v :: acc) q
    | _ :: q -> iter acc q
    | [] -> acc
  dans
  iter [] l_ele

module P_exceptions =
  struct
    type t = unit
    soit p_module _ _ = (vrai, faux)
    soit p_module_type _ _ = (vrai, faux)
    soit p_class _ _ = (faux, faux)
    soit p_class_type _ _ = (faux, faux)
    soit p_value _ _ = faux
    soit p_recfield _ _ _ = faux
    soit p_const _ _ _ = faux
    soit p_type _ _ = (faux, faux)
    soit p_exception _ _ = vrai
    soit p_attribute _ _ = faux
    soit p_method _ _ = faux
    soit p_section _ _ = faux
  fin
module Search_exceptions = Search ( P_exceptions )
soit exceptions l =
  soit l_ele = Search_exceptions.search l () dans
  soit p e1 e2 = e1.ex_name = e2.ex_name dans
  soit rec iter acc = fonction
      (Res_exception t) :: q -> si List.exists (p t) acc alors iter acc q sinon iter (t :: acc) q
    | _ :: q -> iter acc q
    | [] -> acc
  dans
  iter [] l_ele

module P_types =
  struct
    type t = unit
    soit p_module _ _ = (vrai, faux)
    soit p_module_type _ _ = (vrai, faux)
    soit p_class _ _ = (faux, faux)
    soit p_class_type _ _ = (faux, faux)
    soit p_value _ _ = faux
    soit p_recfield _ _ _ = faux
    soit p_const _ _ _ = faux
    soit p_type _ _ = (faux, vrai)
    soit p_exception _ _ = faux
    soit p_attribute _ _ = faux
    soit p_method _ _ = faux
    soit p_section _ _ = faux
  fin
module Search_types = Search ( P_types )
soit types l =
  soit l_ele = Search_types.search l () dans
  soit p t1 t2 = t1.ty_name = t2.ty_name dans
  soit rec iter acc = fonction
      (Res_type t) :: q -> si List.exists (p t) acc alors iter acc q sinon iter (t :: acc) q
    | _ :: q -> iter acc q
    | [] -> acc
  dans
  iter [] l_ele

module P_attributes =
  struct
    type t = unit
    soit p_module _ _ = (vrai, faux)
    soit p_module_type _ _ = (vrai, faux)
    soit p_class _ _ = (vrai, faux)
    soit p_class_type _ _ = (vrai, faux)
    soit p_value _ _ = faux
    soit p_recfield _ _ _ = faux
    soit p_const _ _ _ = faux
    soit p_type _ _ = (faux, faux)
    soit p_exception _ _ = faux
    soit p_attribute _ _ = vrai
    soit p_method _ _ = faux
    soit p_section _ _ = faux
  fin
module Search_attributes = Search ( P_attributes )
soit attributes l =
  soit l_ele = Search_attributes.search l () dans
  soit p a1 a2 = a1.att_value.val_name = a2.att_value.val_name dans
  soit rec iter acc = fonction
      (Res_attribute t) :: q -> si List.exists (p t) acc alors iter acc q sinon iter (t :: acc) q
    | _ :: q -> iter acc q
    | [] -> acc
  dans
  iter [] l_ele

module P_methods =
  struct
    type t = unit
    soit p_module _ _ = (vrai, faux)
    soit p_module_type _ _ = (vrai, faux)
    soit p_class _ _ = (vrai, faux)
    soit p_class_type _ _ = (vrai, faux)
    soit p_value _ _ = faux
    soit p_recfield _ _ _ = faux
    soit p_const _ _ _ = faux
    soit p_type _ _ = (faux, faux)
    soit p_exception _ _ = faux
    soit p_attribute _ _ = faux
    soit p_method _ _ = vrai
    soit p_section _ _ = vrai
  fin
module Search_methods = Search ( P_methods )
soit methods l =
  soit l_ele = Search_methods.search l () dans
  soit p m1 m2 = m1.met_value.val_name = m2.met_value.val_name dans
  soit rec iter acc = fonction
      (Res_method t) :: q -> si List.exists (p t) acc alors iter acc q sinon iter (t :: acc) q
    | _ :: q -> iter acc q
    | [] -> acc
  dans
  iter [] l_ele

module P_classes =
  struct
    type t = unit
    soit p_module _ _ = (vrai, faux)
    soit p_module_type _ _ = (vrai, faux)
    soit p_class _ _ = (faux, vrai)
    soit p_class_type _ _ = (faux, faux)
    soit p_value _ _ = faux
    soit p_recfield _ _ _ = faux
    soit p_const _ _ _ = faux
    soit p_type _ _ = (faux, faux)
    soit p_exception _ _ = faux
    soit p_attribute _ _ = faux
    soit p_method _ _ = faux
    soit p_section _ _ = faux
  fin
module Search_classes = Search ( P_classes )
soit classes l =
  soit l_ele = Search_classes.search l () dans
  soit p c1 c2 = c1.cl_name = c2.cl_name dans
  soit rec iter acc = fonction
      (Res_class c) :: q -> si List.exists (p c) acc alors iter acc q sinon iter (c :: acc) q
    | _ :: q -> iter acc q
    | [] -> acc
  dans
  iter [] l_ele

module P_class_types =
  struct
    type t = unit
    soit p_module _ _ = (vrai, faux)
    soit p_module_type _ _ = (vrai, faux)
    soit p_class _ _ = (faux, faux)
    soit p_class_type _ _ = (faux, vrai)
    soit p_value _ _ = faux
    soit p_recfield _ _ _ = faux
    soit p_const _ _ _ = faux
    soit p_type _ _ = (faux, faux)
    soit p_exception _ _ = faux
    soit p_attribute _ _ = faux
    soit p_method _ _ = faux
    soit p_section _ _ = faux
  fin
module Search_class_types = Search ( P_class_types )
soit class_types l =
  soit l_ele = Search_class_types.search l () dans
  soit p c1 c2 = c1.clt_name = c2.clt_name dans
  soit rec iter acc = fonction
      (Res_class_type c) :: q -> si List.exists (p c) acc alors iter acc q sinon iter (c :: acc) q
    | _ :: q -> iter acc q
    | [] -> acc
  dans
  iter [] l_ele

module P_modules =
  struct
    type t = unit
    soit p_module _ _ = (vrai, vrai)
    soit p_module_type _ _ = (vrai, faux)
    soit p_class _ _ = (faux, faux)
    soit p_class_type _ _ = (faux, faux)
    soit p_value _ _ = faux
    soit p_recfield _ _ _ = faux
    soit p_const _ _ _ = faux
    soit p_type _ _ = (faux, faux)
    soit p_exception _ _ = faux
    soit p_attribute _ _ = faux
    soit p_method _ _ = faux
    soit p_section _ _ = faux
  fin
module Search_modules = Search ( P_modules )
soit modules l =
  soit l_ele = Search_modules.search l () dans
  soit p m1 m2 = m1.m_name = m2.m_name dans
  soit rec iter acc = fonction
      (Res_module m) :: q -> si List.exists (p m) acc alors iter acc q sinon iter (m :: acc) q
    | _ :: q -> iter acc q
    | [] -> acc
  dans
  iter [] l_ele

module P_module_types =
  struct
    type t = unit
    soit p_module _ _ = (vrai, faux)
    soit p_module_type _ _ = (vrai, vrai)
    soit p_class _ _ = (faux, faux)
    soit p_class_type _ _ = (faux, faux)
    soit p_value _ _ = faux
    soit p_recfield _ _ _ = faux
    soit p_const _ _ _ = faux
    soit p_type _ _ = (faux, faux)
    soit p_exception _ _ = faux
    soit p_attribute _ _ = faux
    soit p_method _ _ = faux
    soit p_section _ _ = faux
  fin
module Search_module_types = Search ( P_module_types )
soit module_types l =
  soit l_ele = Search_module_types.search l () dans
  soit p m1 m2 = m1.mt_name = m2.mt_name dans
  soit rec iter acc = fonction
      (Res_module_type m) :: q -> si List.exists (p m) acc alors iter acc q sinon iter (m :: acc) q
    | _ :: q -> iter acc q
    | [] -> acc
  dans
  iter [] l_ele

soit type_exists mods regexp =
  soit l = Search_by_name.search mods regexp dans
  List.exists
    (fonction
        Res_type _ -> vrai
      | _ -> faux
    )
    l

soit value_exists mods regexp =
  soit l = Search_by_name.search mods regexp dans
  List.exists
    (fonction
        Res_value _ -> vrai
      | _ -> faux
    )
    l

soit class_exists mods regexp =
  soit l = Search_by_name.search mods regexp dans
  List.exists
    (fonction
        Res_class _ -> vrai
      | _ -> faux
    )
    l

soit class_type_exists mods regexp =
  soit l = Search_by_name.search mods regexp dans
  List.exists
    (fonction
        Res_class_type _ -> vrai
      | _ -> faux
    )
    l

soit module_exists mods regexp =
  soit l = Search_by_name.search mods regexp dans
  List.exists
    (fonction
        Res_module _ -> vrai
      | _ -> faux
    )
    l

soit module_type_exists mods regexp =
  soit l = Search_by_name.search mods regexp dans
  List.exists
    (fonction
        Res_module_type _ -> vrai
      | _ -> faux
    )
    l

soit exception_exists mods regexp =
  soit l = Search_by_name.search mods regexp dans
  List.exists
    (fonction
        Res_exception _ -> vrai
      | _ -> faux
    )
    l

soit attribute_exists mods regexp =
  soit l = Search_by_name.search mods regexp dans
  List.exists
    (fonction
        Res_attribute _ -> vrai
      | _ -> faux
    )
    l

soit method_exists mods regexp =
  soit l = Search_by_name.search mods regexp dans
  List.exists
    (fonction
        Res_method _ -> vrai
      | _ -> faux
    )
    l

soit find_section mods regexp =
  soit l = Search_by_name.search mods regexp dans
  filtre
    List.find
      (fonction
          Res_section _ -> vrai
        | _ -> faux
      )
      l
  avec
    Res_section (_,t) -> t
  | _ -> affirme faux
