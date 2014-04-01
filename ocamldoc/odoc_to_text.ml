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

(** Text generation.

   This module contains the class [to_text] with methods used to transform
   information about elements to a [text] structure.*)

ouvre Odoc_info
ouvre Exception
ouvre Type
ouvre Value
ouvre Module
ouvre Class
ouvre Parameter

(** A class used to get a [text] for info structures. *)
classe virtuelle info =
  objet (self)
    (** The list of pairs [(tag, f)] where [f] is a function taking
       the [text] associated to [tag] and returning a [text].
       Add a pair here to handle a tag.*)
    val modifiable tag_functions = ([] : (string * (Odoc_info.text -> Odoc_info.text)) list)

    (** @return [etxt] value for an authors list. *)
    méthode text_of_author_list l =
      filtre l avec
        [] ->
          []
      | _ ->
          [ Bold [Raw (Odoc_messages.authors^": ")] ;
            Raw (String.concat ", " l) ;
            Newline
          ]

    (** @return [text] value for the given optional version information.*)
    méthode text_of_version_opt v_opt =
      filtre v_opt avec
        None -> []
      | Some v -> [ Bold [Raw (Odoc_messages.version^": ")] ;
                    Raw v ;
                    Newline
                  ]

    (** @return [text] value for the given optional since information.*)
    méthode text_of_since_opt s_opt =
      filtre s_opt avec
        None -> []
      | Some s -> [ Bold [Raw (Odoc_messages.since^": ")] ;
                    Raw s ;
                    Newline
                  ]

    (** @return [text] value to represent the list of "before" information. *)
    méthode text_of_before = fonction
      [] -> []
    | l ->
        soit f (v, text) =
          (Bold [Raw (Printf.sprintf "%s %s " Odoc_messages.before v) ]) ::
            text @
            [Newline]
        dans
        List.flatten (List.map f l)

    (** @return [text] value for the given list of raised exceptions.*)
    méthode text_of_raised_exceptions l =
      filtre l avec
        [] -> []
      | (s, t) :: [] ->
          [ Bold [ Raw Odoc_messages.raises ] ;
            Raw " " ;
            Code s ;
            Raw " "
          ]
          @ t
          @ [ Newline ]
      | _ ->
          [ Bold [ Raw Odoc_messages.raises ] ;
            Raw " " ;
            List
              (List.map
                (fonc (ex, desc) ->(Code ex) :: (Raw " ") :: desc )
                 l
              ) ;
            Newline
          ]

    (** Return [text] value for the given "see also" reference. *)
    méthode text_of_see (see_ref, t)  =
      soit t_ref =
        filtre see_ref avec
          Odoc_info.See_url s -> [ Odoc_info.Link (s, t) ]
        | Odoc_info.See_file s -> (Odoc_info.Code s) :: (Odoc_info.Raw " ") :: t
        | Odoc_info.See_doc s -> (Odoc_info.Italic [Odoc_info.Raw s]) :: (Odoc_info.Raw " ") :: t
      dans
      t_ref

    (** Return [text] value for the given list of "see also" references.*)
    méthode text_of_sees l =
      filtre l avec
        [] -> []
      | see :: [] ->
          (Bold [ Raw Odoc_messages.see_also ]) ::
          (Raw " ") ::
          (self#text_of_see see) @ [ Newline ]
      | _ ->
          (Bold [ Raw Odoc_messages.see_also ]) ::
          [ List
              (List.map
                 (fonc see -> self#text_of_see see)
                 l
              );
            Newline
          ]

    (** @return [text] value for the given optional return information.*)
    méthode text_of_return_opt return_opt =
      filtre return_opt avec
        None -> []
      | Some t -> (Bold [Raw (Odoc_messages.returns^" ")]) :: t @ [ Newline ]

    (** Return a [text] for the given list of custom tagged texts. *)
    méthode text_of_custom l =
      List.fold_left
        (fonc acc -> fonc (tag, text) ->
          essaie
            soit f = List.assoc tag tag_functions dans
            filtre acc avec
              [] -> f text
            | _ -> acc @ (Newline :: (f text))
          avec
            Not_found ->
              Odoc_info.warning (Odoc_messages.tag_not_handled tag) ;
              acc
        )
        []
        l

    (** @return [text] value for a description, except for the i_params field. *)
    méthode text_of_info ?(block=vrai) info_opt =
      filtre info_opt avec
        None ->
          []
      | Some info ->
          soit t =
            (filtre info.i_deprecated avec
              None -> []
            | Some t -> ( Italic [Raw (Odoc_messages.deprecated^" ")] ) :: t
             ) @
            (filtre info.i_desc avec
              None -> []
            | Some t quand t = [Odoc_info.Raw ""] -> []
            | Some t -> t @ [ Newline ]
            ) @
            (self#text_of_author_list info.i_authors) @
            (self#text_of_version_opt info.i_version) @
            (self#text_of_before info.i_before) @
            (self#text_of_since_opt info.i_since) @
            (self#text_of_raised_exceptions info.i_raised_exceptions) @
            (self#text_of_return_opt info.i_return_value) @
            (self#text_of_sees info.i_sees) @
            (self#text_of_custom info.i_custom)
          dans
          si block alors
            [Block t]
          sinon
            t
  fin

(** This class defines methods to generate a [text] structure from elements. *)
classe virtuelle to_text =
  objet (self)
    hérite info

    méthode virtuelle label : ?no_: bool -> string -> string

    (** Take a string and return the string where fully qualified idents
       have been replaced by idents relative to the given module name.
       Also remove the "hidden modules".*)
    méthode relative_idents m_name s =
      soit f str_t =
        soit match_s = Str.matched_string str_t dans
        soit rel = Name.get_relative m_name match_s dans
        Odoc_info.apply_if_equal Odoc_info.use_hidden_modules match_s rel
      dans
      soit s2 = Str.global_substitute
          (Str.regexp "\\([A-Z]\\([a-zA-Z_'0-9]\\)*\\.\\)+\\([a-z][a-zA-Z_'0-9]*\\)")
          f
          s
      dans
      s2

    (** Take a string and return the string where fully qualified idents
       have been replaced by idents relative to the given module name.
       Also remove the "hidden modules".*)
    méthode relative_module_idents m_name s =
      soit f str_t =
        soit match_s = Str.matched_string str_t dans
        soit rel = Name.get_relative m_name match_s dans
        Odoc_info.apply_if_equal Odoc_info.use_hidden_modules match_s rel
      dans
      soit s2 = Str.global_substitute
          (Str.regexp "\\([A-Z]\\([a-zA-Z_'0-9]\\)*\\.\\)+\\([A-Z][a-zA-Z_'0-9]*\\)")
          f
          s
      dans
      s2

    (** Get a string for a [Types.class_type] where all idents are relative. *)
    méthode normal_class_type m_name t =
      self#relative_idents m_name (Odoc_info.string_of_class_type t)

    (** Get a string for a [Types.module_type] where all idents are relative. *)
    méthode normal_module_type ?code m_name t =
      self#relative_module_idents m_name (Odoc_info.string_of_module_type ?code t)

    (** Get a string for a type where all idents are relative. *)
    méthode normal_type m_name t =
      self#relative_idents m_name (Odoc_info.string_of_type_expr t)

    (** Get a string for a list of types where all idents are relative. *)
    méthode normal_type_list ?par m_name sep t =
      self#relative_idents m_name (Odoc_info.string_of_type_list ?par sep t)

    (** Get a string for a list of class or class type type parameters
       where all idents are relative. *)
    méthode normal_class_type_param_list m_name t =
      self#relative_idents m_name (Odoc_info.string_of_class_type_param_list t)

    (** Get a string for the parameters of a class (with arrows) where all idents are relative. *)
    méthode normal_class_params m_name c =
      soit s = Odoc_info.string_of_class_params c dans
      self#relative_idents m_name
        (Odoc_info.remove_ending_newline s)

    (** @return [text] value to represent a [Types.type_expr].*)
    méthode text_of_type_expr module_name t =
      soit t = List.flatten
          (List.map
             (fonc s -> [Code s ; Newline ])
             (Str.split (Str.regexp "\n")
                (self#normal_type module_name t))
          )
      dans
      t

    (** Return [text] value for a given short [Types.type_expr].*)
    méthode text_of_short_type_expr module_name t =
      [ Code (self#normal_type module_name t) ]

    (** Return [text] value or the given list of [Types.type_expr], with
       the given separator. *)
    méthode text_of_type_expr_list module_name sep l =
      [ Code (self#normal_type_list module_name sep l) ]

    (** Return [text] value or the given list of [Types.type_expr],
       as type parameters of a class of class type. *)
    méthode text_of_class_type_param_expr_list module_name l =
      [ Code (self#normal_class_type_param_list module_name l) ]

    (** @return [text] value to represent parameters of a class (with arraows).*)
    méthode text_of_class_params module_name c =
      soit t = Odoc_info.text_concat
          [Newline]
          (List.map
             (fonc s -> [Code s])
             (Str.split (Str.regexp "\n")
                (self#normal_class_params module_name c))
          )
      dans
      t

    (** @return [text] value to represent a [Types.module_type]. *)
    méthode text_of_module_type t =
      soit s = String.concat "\n"
          (Str.split (Str.regexp "\n") (Odoc_info.string_of_module_type t))
      dans
      [ Code s ]

    (** @return [text] value for a value. *)
    méthode text_of_value v =
      soit name = v.val_name dans
      soit s_name = Name.simple name dans
      soit s =
        Format.fprintf Format.str_formatter "@[<hov 2>val %s :@ %s"
          s_name
          (self#normal_type (Name.father v.val_name) v.val_type);
        Format.flush_str_formatter ()
      dans
      [ CodePre s ] @
      [Latex ("\\index{"^(self#label s_name)^"@\\verb`"^(self#label ~no_:faux s_name)^"`}\n")] @
      (self#text_of_info v.val_info)

    (** @return [text] value for a class attribute. *)
    méthode text_of_attribute a =
      soit s_name = Name.simple a.att_value.val_name dans
      soit mod_name = Name.father a.att_value.val_name dans
      soit s =
        Format.fprintf Format.str_formatter "@[<hov 2>val %s%s%s :@ %s"
          (si a.att_virtual alors "virtual " sinon "")
          (si a.att_mutable alors "mutable " sinon "")
          s_name
          (self#normal_type mod_name a.att_value.val_type);
        Format.flush_str_formatter ()
      dans
      (CodePre s) ::
      [Latex ("\\index{"^(self#label s_name)^"@\\verb`"^(self#label ~no_:faux s_name)^"`}\n")] @
      (self#text_of_info a.att_value.val_info)

    (** @return [text] value for a class method. *)
    méthode text_of_method m =
      soit s_name = Name.simple m.met_value.val_name dans
      soit mod_name = Name.father m.met_value.val_name dans
      soit s =
        Format.fprintf Format.str_formatter "@[<hov 2>method %s%s%s :@ %s"
          (si m.met_private alors "private " sinon "")
          (si m.met_virtual alors "virtual " sinon "")
          s_name
          (self#normal_type mod_name m.met_value.val_type);
        Format.flush_str_formatter ()
      dans
      (CodePre s) ::
      [Latex ("\\index{"^(self#label s_name)^"@\\verb`"^(self#label ~no_:faux s_name)^"`}\n")] @
      (self#text_of_info m.met_value.val_info)


    (** @return [text] value for an exception. *)
    méthode text_of_exception e =
      soit s_name = Name.simple e.ex_name dans
      Format.fprintf Format.str_formatter "@[<hov 2>exception %s" s_name ;
        (filtre e.ex_args avec
          [] -> ()
        | _ ->
            Format.fprintf Format.str_formatter "@ of "
        );
      soit s = self#normal_type_list
          ~par: faux (Name.father e.ex_name) " * " e.ex_args
      dans
      soit s2 =
        Format.fprintf Format.str_formatter "%s" s ;
        (filtre e.ex_alias avec
          None -> ()
        | Some ea ->
            Format.fprintf Format.str_formatter " = %s"
              (
               filtre ea.ea_ex avec
                 None -> ea.ea_name
               | Some e -> e.ex_name
              )
        );
        Format.flush_str_formatter ()
      dans
      [ CodePre s2 ] @
      [Latex ("\\index{"^(self#label s_name)^"@\\verb`"^(self#label ~no_:faux s_name)^"`}\n")] @
      (self#text_of_info e.ex_info)

    (** Return [text] value for the description of a function parameter. *)
    méthode text_of_parameter_description p =
      filtre Parameter.names p avec
        [] -> []
      | name :: [] ->
          (
           (* Only one name, no need for label for the description. *)
           filtre Parameter.desc_by_name p name avec
             None -> []
           | Some t -> t
          )
      | l ->
          (*  A list of names, we display those with a description. *)
          soit l2 = List.filter (fonc n -> (Parameter.desc_by_name p n) <> None) l dans
          filtre l2 avec
            [] -> []
          | _ ->
              [List
                  (List.map
                     (fonc n ->
                       filtre Parameter.desc_by_name p n avec
                         None -> [] (* should not occur *)
                       | Some t -> [Code (n^" ") ; Raw ": "] @ t
                     )
                     l2
                  )
              ]


    (** Return [text] value for a list of parameters. *)
    méthode text_of_parameter_list m_name l =
      filtre l avec
        [] ->
          []
      | _ ->
          [ Bold [Raw Odoc_messages.parameters] ;
            Raw ":" ;
            List
              (List.map
                 (fonc p ->
                   (filtre Parameter.complete_name p avec
                     "" -> Code "?"
                   | s -> Code s
                   ) ::
                   [Code " : "] @
                   (self#text_of_short_type_expr m_name (Parameter.typ p)) @
                   [Newline] @
                   (self#text_of_parameter_description p)
                 )
                 l
              )
          ]

    (** Return [text] value for a list of module parameters. *)
    méthode text_of_module_parameter_list l =
      filtre l avec
        [] ->
          []
      | _ ->
          [ Newline ;
            Bold [Raw Odoc_messages.parameters] ;
            Raw ":" ;
            List
              (List.map
                 (fonc (p, desc_opt) ->
                   début filtre p.mp_type avec None -> [Raw ""]
                   | Some mty ->
                       [Code (p.mp_name^" : ")] @
                       (self#text_of_module_type mty)
                   fin @
                   (filtre desc_opt avec
                     None -> []
                   | Some t -> (Raw " ") :: t)
                 )
                 l
              )
          ]

(**/**)

    (** Return [text] value for the given [class_kind].*)
    méthode text_of_class_kind father ckind =
      filtre ckind avec
        Class_structure _ ->
          [Code Odoc_messages.object_end]

      | Class_apply capp ->
          [Code
              (
               (
                filtre capp.capp_class avec
                  None -> capp.capp_name
                | Some cl -> cl.cl_name
               )^
               " "^
               (String.concat " "
                  (List.map
                     (fonc s -> "("^s^")")
                     capp.capp_params_code))
              )
          ]

      | Class_constr cco ->
          (
           filtre cco.cco_type_parameters avec
             [] -> []
           | l ->
               (Code "[")::
               (self#text_of_type_expr_list father ", " l)@
               [Code "] "]
          )@
          [Code (
            filtre cco.cco_class avec
              None -> cco.cco_name
            | Some (Cl cl) -> Name.get_relative father cl.cl_name
            | Some (Cltype (clt,_)) -> Name.get_relative father clt.clt_name
           )
          ]

      | Class_constraint (ck, ctk) ->
          [Code "( "] @
          (self#text_of_class_kind father ck) @
          [Code " : "] @
          (self#text_of_class_type_kind father ctk) @
          [Code " )"]


    (** Return [text] value for the given [class_type_kind].*)
    méthode text_of_class_type_kind father ctkind =
      filtre ctkind avec
        Class_type cta ->
          (
           filtre cta.cta_type_parameters avec
             [] -> []
           | l ->
               (Code "[") ::
               (self#text_of_class_type_param_expr_list father l) @
               [Code "] "]
          ) @
          (
           filtre cta.cta_class avec
             None -> [ Code cta.cta_name ]
           | Some (Cltype (clt, _)) ->
               soit rel = Name.get_relative father clt.clt_name dans
               [Code rel]
           | Some (Cl cl) ->
               soit rel = Name.get_relative father cl.cl_name dans
               [Code rel]
          )
      | Class_signature _ ->
          [Code Odoc_messages.object_end]

    (** Return [text] value for a [module_kind]. *)
    méthode text_of_module_kind ?(with_def_syntax=vrai) k =
      filtre k avec
        Module_alias m_alias ->
          (filtre m_alias.ma_module avec
            None ->
              [Code ((si with_def_syntax alors " = " sinon "")^m_alias.ma_name)]
          | Some (Mod m) ->
              [Code ((si with_def_syntax alors " = " sinon "")^m.m_name)]
          | Some (Modtype mt) ->
              [Code ((si with_def_syntax alors " = " sinon "")^mt.mt_name)]
          )
      | Module_apply (k1, k2) ->
          (si with_def_syntax alors [Code " = "] sinon []) @
          (self#text_of_module_kind ~with_def_syntax: faux k1) @
          [Code " ( "] @
          (self#text_of_module_kind ~with_def_syntax: faux k2) @
          [Code " ) "]

      | Module_with (tk, code) ->
          (si with_def_syntax alors [Code " : "] sinon []) @
          (self#text_of_module_type_kind ~with_def_syntax: faux tk) @
          [Code code]

      | Module_constraint (k, tk) ->
          (si with_def_syntax alors [Code " : "] sinon []) @
          [Code "( "] @
          (self#text_of_module_kind ~with_def_syntax: faux k) @
          [Code " : "] @
          (self#text_of_module_type_kind ~with_def_syntax: faux tk) @
          [Code " )"]

      | Module_struct _ ->
          [Code ((si with_def_syntax alors " : " sinon "")^
                 Odoc_messages.struct_end^" ")]

      | Module_functor (p, k)  ->
          (si with_def_syntax alors [Code " : "] sinon []) @
          [Code "functor ... "] @
          [Code " -> "] @
          (self#text_of_module_kind ~with_def_syntax: faux k)

      | Module_typeof s ->
          soit code = Printf.sprintf "%smodule type of %s"
            (si with_def_syntax alors " : " sinon "")
            s
          dans
          [Code code]
      | Module_unpack (code, _) ->
          soit code = Printf.sprintf "%s%s"
            (si with_def_syntax alors " : " sinon "")
            code
          dans
          [Code code]

    (** Return html code for a [module_type_kind].*)
    méthode text_of_module_type_kind ?(with_def_syntax=vrai) tk =
      filtre tk avec
      | Module_type_struct _ ->
          [Code ((si with_def_syntax alors " = " sinon "")^Odoc_messages.sig_end)]

      | Module_type_functor (p, k) ->
          soit t1 =
            [Code ("("^p.mp_name^" : ")] @
            (self#text_of_module_type_kind p.mp_kind) @
            [Code ") -> "]
          dans
          soit t2 = self#text_of_module_type_kind ~with_def_syntax: faux k dans
          (si with_def_syntax alors [Code " = "] sinon []) @ t1 @ t2

      | Module_type_with (tk2, code) ->
          soit t = self#text_of_module_type_kind ~with_def_syntax: faux tk2 dans
          (si with_def_syntax alors [Code " = "] sinon []) @
          t @ [Code code]

      | Module_type_alias mt_alias ->
          [Code ((si with_def_syntax alors " = " sinon "")^
                 (filtre mt_alias.mta_module avec
                   None -> mt_alias.mta_name
                 | Some mt -> mt.mt_name))
          ]

      | Odoc_module.Module_type_typeof s ->
          soit code = Printf.sprintf "%smodule type of %s"
            (si with_def_syntax alors " = " sinon "") s
          dans
          [ Code code ]
  fin
