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

(** Generation of LaTeX documentation. *)

soit print_DEBUG s = print_string s ; print_newline ()

ouvre Odoc_info
ouvre Parameter
ouvre Value
ouvre Type
ouvre Exception
ouvre Class
ouvre Module



soit separate_files = ref faux

soit latex_titles = ref [
  1, "section" ;
  2, "subsection" ;
  3, "subsubsection" ;
  4, "paragraph" ;
  5, "subparagraph" ;
]

soit latex_value_prefix = ref Odoc_messages.default_latex_value_prefix
soit latex_type_prefix = ref Odoc_messages.default_latex_type_prefix
soit latex_type_elt_prefix = ref Odoc_messages.default_latex_type_elt_prefix
soit latex_exception_prefix = ref Odoc_messages.default_latex_exception_prefix
soit latex_module_prefix = ref Odoc_messages.default_latex_module_prefix
soit latex_module_type_prefix = ref Odoc_messages.default_latex_module_type_prefix
soit latex_class_prefix = ref Odoc_messages.default_latex_class_prefix
soit latex_class_type_prefix = ref Odoc_messages.default_latex_class_type_prefix
soit latex_attribute_prefix = ref Odoc_messages.default_latex_attribute_prefix
soit latex_method_prefix = ref Odoc_messages.default_latex_method_prefix

soit new_buf () = Buffer.create 1024
soit new_fmt () =
  soit b = new_buf () dans
  soit fmt = Format.formatter_of_buffer b dans
  (fmt,
   fonc () ->
    Format.pp_print_flush fmt ();
    soit s = Buffer.contents b dans
    Buffer.reset b;
    s
  )

soit p = Format.fprintf
soit ps f s = Format.fprintf f "%s" s


soit bp = Printf.bprintf
soit bs = Buffer.add_string

soit print_concat fmt sep f =
  soit rec iter = fonction
      [] -> ()
    | [c] -> f c
    | c :: q ->
        f c;
        ps fmt sep;
        iter q
  dans
  iter

(** Generation of LaTeX code from text structures. *)
classe text =
  objet (self)
    (** Return latex code to make a sectionning according to the given level,
       and with the given latex code. *)
    méthode section_style level s =
      essaie
        soit sec = List.assoc level !latex_titles dans
        "\\"^sec^"{"^s^"}\n"
      avec Not_found -> s

    (** Associations of strings to substitute in latex code. *)
    val subst_strings = List.map (fonc (x, y) -> (Str.regexp x, y))
      [
        "\001", "\001\002";
        "\\\\", "\001b";

        "{", "\\\\{";
        "}", "\\\\}";
        "\\$", "\\\\$";
        "\\^", "{\\\\textasciicircum}";
        "\xE0", "\\\\`a";
        "\xE2", "\\\\^a";
        "\xE9", "\\\\'e";
        "\xE8", "\\\\`e";
        "\xEA", "\\\\^e";
        "\xEB", "\\\\\"e";
        "\xE7", "\\\\c{c}";
        "\xF4", "\\\\^o";
        "\xF6", "\\\\\"o";
        "\xEE", "\\\\^i";
        "\xEF", "\\\\\"i";
        "\xF9", "\\\\`u";
        "\xFB", "\\\\^u";
        "%", "\\\\%";
        "_", "\\\\_";
        "~", "\\\\~{}";
        "#", "{\\char35}";
        "->", "$\\\\rightarrow$";
        "<-", "$\\\\leftarrow$";
        ">=", "$\\\\geq$";
        "<=", "$\\\\leq$";
        ">", "$>$";
        "<", "$<$";
        "=", "$=$";
        "|", "{\\\\textbar}";
        "\\.\\.\\.", "$\\\\ldots$";
        "&", "\\\\&";

        "\001b", "{\\\\char92}";
        "\001\002", "\001";
      ]

    val subst_strings_simple = List.map (fonc (x, y) -> (Str.regexp x, y))
      [
        "\001", "\001\002";
        "\\\\", "\001b";
        "{", "\001l";

        "}", "{\\\\char125}";
        "'", "{\\\\textquotesingle}";
        "`", "{\\\\textasciigrave}";

        "\001b", "{\\\\char92}";
        "\001l", "{\\\\char123}";
        "\001\002", "\001";
      ]

    val subst_strings_code = List.map (fonc (x, y) -> (Str.regexp x, y))
      [
        "\001", "\001\002";
        "\\\\", "\001b";
        "{", "\001l";

        "}", "{\\\\char125}";
        "'", "{\\\\textquotesingle}";
        "`", "{\\\\textasciigrave}";
        "%", "\\\\%";
        "_", "\\\\_";
        "~", "{\\\\char126}";
        "#", "{\\\\char35}";
        "&", "\\\\&";
        "\\$", "\\\\$";
        "\\^", "{\\\\char94}";

        "\001b", "{\\\\char92}";
        "\001l", "{\\\\char123}";
        "\001\002", "\001";
      ]

    méthode subst l s =
      List.fold_left (fonc acc (re, st) -> Str.global_replace re st acc) s l

    (** Escape the strings which would clash with LaTeX syntax. *)
    méthode escape s = self#subst subst_strings s

    (** Escape the ['\'], ['{'] and ['}'] characters. *)
    méthode escape_simple s = self#subst subst_strings_simple s

    (** Escape some characters for the code style. *)
    méthode escape_code s = self#subst subst_strings_code s

    (** Make a correct latex label from a name. *)
    (* The following characters are forbidden in LaTeX \index:
       \ { } $ & # ^ _ % ~ ! " @ | (" to close the double quote)
       The following characters are forbidden in LaTeX \label:
       \ { } $ & # ^ _ % ~
       So we will use characters not forbidden in \index if no_ = true.
    *)
    méthode label ?(no_=vrai) name =
      soit len = String.length name dans
      soit buf = Buffer.create len dans
      pour i = 0 à len - 1 faire
        soit (s_no_, s) =
          filtre name.[i] avec
          '_' -> ("-underscore", "_")
        | '~' -> ("-tilde", "~")
        | '%' -> ("-percent", "%")
        | '@' -> ("-at", "\"@")
        | '!' -> ("-bang", "\"!")
        | '|' -> ("-pipe", "\"|")
        | '<' -> ("-lt", "<")
        | '>' -> ("-gt", ">")
        | '^' -> ("-exp", "^")
        | '&' -> ("-ampersand", "&")
        | '+' -> ("-plus", "+")
        | '-' -> ("-minus", "-")
        | '*' -> ("-star", "*")
        | '/' -> ("-slash", "/")
        | '$' -> ("-dollar", "$")
        | '=' -> ("-equal", "=")
        | ':' -> ("-colon", ":")
        | c -> (String.make 1 c, String.make 1 c)
        dans
        Buffer.add_string buf (si no_ alors s_no_ sinon s)
      fait;
      Buffer.contents buf

    (** Make a correct label from a value name. *)
    méthode value_label ?no_ name = !latex_value_prefix^(self#label ?no_ name)

    (** Make a correct label from an attribute name. *)
    méthode attribute_label ?no_ name = !latex_attribute_prefix^(self#label ?no_ name)

    (** Make a correct label from a method name. *)
    méthode method_label ?no_ name = !latex_method_prefix^(self#label ?no_ name)

    (** Make a correct label from a class name. *)
    méthode class_label ?no_ name = !latex_class_prefix^(self#label ?no_ name)

    (** Make a correct label from a class type name. *)
    méthode class_type_label ?no_ name = !latex_class_type_prefix^(self#label ?no_ name)

    (** Make a correct label from a module name. *)
    méthode module_label ?no_ name = !latex_module_prefix^(self#label ?no_ name)

    (** Make a correct label from a module type name. *)
    méthode module_type_label ?no_ name = !latex_module_type_prefix^(self#label ?no_ name)

    (** Make a correct label from an exception name. *)
    méthode exception_label ?no_ name = !latex_exception_prefix^(self#label ?no_ name)

    (** Make a correct label from a type name. *)
    méthode type_label ?no_ name = !latex_type_prefix^(self#label ?no_ name)

    (** Make a correct label from a record field. *)
    méthode recfield_label ?no_ name = !latex_type_elt_prefix^(self#label ?no_ name)

    (** Make a correct label from a variant constructor. *)
    méthode const_label ?no_ name = !latex_type_elt_prefix^(self#label ?no_ name)

    (** Return latex code for the label of a given label. *)
    méthode make_label label = "\\label{"^label^"}"

    (** Return latex code for the ref to a given label. *)
    méthode make_ref label = "\\ref{"^label^"}"

    (** Print the LaTeX code corresponding to the [text] parameter.*)
    méthode latex_of_text fmt t =
      List.iter (self#latex_of_text_element fmt) t

    (** Print the LaTeX code for the [text_element] in parameter. *)
    méthode latex_of_text_element fmt te =
      filtre te avec
      | Odoc_info.Raw s -> self#latex_of_Raw fmt s
      | Odoc_info.Code s -> self#latex_of_Code fmt s
      | Odoc_info.CodePre s -> self#latex_of_CodePre fmt s
      | Odoc_info.Verbatim s -> self#latex_of_Verbatim fmt s
      | Odoc_info.Bold t -> self#latex_of_Bold fmt t
      | Odoc_info.Italic t -> self#latex_of_Italic fmt t
      | Odoc_info.Emphasize t -> self#latex_of_Emphasize fmt t
      | Odoc_info.Center t -> self#latex_of_Center fmt t
      | Odoc_info.Left t -> self#latex_of_Left fmt t
      | Odoc_info.Right t -> self#latex_of_Right fmt t
      | Odoc_info.List tl -> self#latex_of_List fmt tl
      | Odoc_info.Enum tl -> self#latex_of_Enum fmt tl
      | Odoc_info.Newline -> self#latex_of_Newline fmt
      | Odoc_info.Block t -> self#latex_of_Block fmt t
      | Odoc_info.Title (n, l_opt, t) -> self#latex_of_Title fmt n l_opt t
      | Odoc_info.Latex s -> self#latex_of_Latex fmt s
      | Odoc_info.Link (s, t) -> self#latex_of_Link fmt s t
      | Odoc_info.Ref (name, ref_opt, text_opt) ->
          self#latex_of_Ref fmt name ref_opt text_opt
      | Odoc_info.Superscript t -> self#latex_of_Superscript fmt t
      | Odoc_info.Subscript t -> self#latex_of_Subscript fmt t
      | Odoc_info.Module_list _ -> ()
      | Odoc_info.Index_list -> ()
      | Odoc_info.Custom (s,t) -> self#latex_of_custom_text fmt s t
      | Odoc_info.Target (target, code) -> self#latex_of_Target fmt ~target ~code

    méthode latex_of_custom_text fmt s t = ()

    méthode latex_of_Target fmt ~target ~code =
      si String.lowercase target = "latex" alors
        self#latex_of_Latex fmt code
      sinon
        ()

    méthode latex_of_Raw fmt s =
      ps fmt (self#escape s)

    méthode latex_of_Code fmt s =
      soit s2 = self#escape_code s dans
      soit s3 = Str.global_replace (Str.regexp "\n") ("\\\\\n") s2 dans
      p fmt "{\\tt{%s}}" s3

    méthode latex_of_CodePre fmt s =
      ps fmt "\\begin{ocamldoccode}\n";
      ps fmt (self#escape_simple s);
      ps fmt "\n\\end{ocamldoccode}\n"

    méthode latex_of_Verbatim fmt s =
      ps fmt "\n\\begin{verbatim}\n";
      ps fmt s;
      ps fmt "\n\\end{verbatim}\n"

    méthode latex_of_Bold fmt t =
      ps fmt "{\\bf ";
      self#latex_of_text fmt t;
      ps fmt "}"

    méthode latex_of_Italic fmt t =
      ps fmt "{\\it ";
      self#latex_of_text fmt t;
      ps fmt "}"

    méthode latex_of_Emphasize fmt t =
      ps fmt "{\\em ";
      self#latex_of_text fmt t;
      ps fmt "}"

    méthode latex_of_Center fmt t =
      ps fmt "\\begin{center}\n";
      self#latex_of_text fmt t;
      ps fmt "\\end{center}\n"

    méthode latex_of_Left fmt t =
      ps fmt "\\begin{flushleft}\n";
      self#latex_of_text fmt t;
      ps fmt "\\end{flushleft}\n"

    méthode latex_of_Right fmt t =
      ps fmt "\\begin{flushright}\n";
      self#latex_of_text fmt t;
      ps fmt "\\end{flushright}\n"

    méthode latex_of_List fmt tl =
      ps fmt "\\begin{itemize}\n";
      List.iter
        (fonc t ->
          ps fmt "\\item ";
          self#latex_of_text fmt t;
          ps fmt "\n"
        )
        tl;
      ps fmt "\\end{itemize}\n"

    méthode latex_of_Enum fmt tl =
      ps fmt "\\begin{enumerate}\n";
      List.iter
        (fonc t ->
          ps fmt "\\item ";
          self#latex_of_text fmt t;
          ps fmt "\n"
        )
        tl;
      ps fmt "\\end{enumerate}\n"

    méthode latex_of_Newline fmt = ps fmt "\n\n"

    méthode latex_of_Block fmt t =
      ps fmt "\\begin{ocamldocdescription}\n";
      self#latex_of_text fmt t;
      ps fmt "\n\\end{ocamldocdescription}\n"

    méthode latex_of_Title fmt n label_opt t =
      soit (fmt2, flush) = new_fmt () dans
      self#latex_of_text fmt2 t;
      soit s_title2 = self#section_style n (flush ()) dans
      ps fmt s_title2;
      (
       filtre label_opt avec
         None -> ()
       | Some l ->
           ps fmt (self#make_label (self#label ~no_: faux l))
      )

    méthode latex_of_Latex fmt s = ps fmt s

    méthode latex_of_Link fmt s t =
      self#latex_of_text fmt t ;
      ps fmt "[\\url{";
      ps fmt s ;
      ps fmt "}]"

    méthode latex_of_Ref fmt name ref_opt text_opt =
      filtre ref_opt avec
        None ->
          self#latex_of_text fmt
          (filtre text_opt avec
             None ->
               [Odoc_info.Code (Odoc_info.use_hidden_modules name)]
           | Some t -> t
           )
      | Some (RK_section _) ->
          self#latex_of_text_element fmt
            (Latex ("["^(self#make_ref (self#label ~no_:faux (Name.simple name)))^"]"))
      | Some kind ->
          soit f_label =
            filtre kind avec
              Odoc_info.RK_module -> self#module_label
            | Odoc_info.RK_module_type -> self#module_type_label
            | Odoc_info.RK_class -> self#class_label
            | Odoc_info.RK_class_type -> self#class_type_label
            | Odoc_info.RK_value -> self#value_label
            | Odoc_info.RK_type -> self#type_label
            | Odoc_info.RK_exception -> self#exception_label
            | Odoc_info.RK_attribute -> self#attribute_label
            | Odoc_info.RK_method -> self#method_label
            | Odoc_info.RK_section _ -> affirme faux
            | Odoc_info.RK_recfield -> self#recfield_label
            | Odoc_info.RK_const -> self#const_label
          dans
          soit text =
            filtre text_opt avec
              None -> [Odoc_info.Code (Odoc_info.use_hidden_modules name)]
            | Some t -> t
          dans
          self#latex_of_text fmt
             (text @ [Latex ("["^(self#make_ref (f_label name))^"]")])

    méthode latex_of_Superscript fmt t =
      ps fmt "$^{";
      self#latex_of_text fmt t;
      ps fmt "}$"

    méthode latex_of_Subscript fmt t =
      ps fmt "$_{";
      self#latex_of_text fmt t;
      ps fmt "}$"

  fin

(** A class used to generate LaTeX code for info structures. *)
classe virtuelle info =
  objet (self)
    (** The method used to get LaTeX code from a [text]. *)
    méthode virtuelle latex_of_text : Format.formatter -> Odoc_info.text -> unit

    (** The method used to get a [text] from an optionel info structure. *)
    méthode virtuelle text_of_info : ?block: bool -> Odoc_info.info option -> Odoc_info.text

    (** Print LaTeX code for a description, except for the [i_params] field. *)
    méthode latex_of_info fmt ?(block=faux) info_opt =
      self#latex_of_text fmt
        (self#text_of_info ~block info_opt)
  fin

module Generator =
struct
(** This class is used to create objects which can generate a simple LaTeX documentation. *)
classe latex =
  objet (self)
    hérite text
    hérite Odoc_to_text.to_text tel to_text
    hérite info

    (** Get the first sentence and the rest of a description,
       from an optional [info] structure. The first sentence
       can be empty if it would not appear right in a title.
       In the first sentence, the titles and lists has been removed,
       since it is used in LaTeX titles and would make LaTeX complain
       if we has two nested \section commands.
    *)
    méthode first_and_rest_of_info i_opt =
      filtre i_opt avec
        None -> ([], [])
      | Some i ->
            filtre i.Odoc_info.i_desc avec
              None -> ([], self#text_of_info ~block: vrai i_opt)
            | Some t ->
                soit (first,_) = Odoc_info.first_sentence_and_rest_of_text t dans
                soit (_, rest) = Odoc_info.first_sentence_and_rest_of_text (self#text_of_info ~block: faux i_opt) dans
                (Odoc_info.text_no_title_no_list first, rest)

    (** Print LaTeX code for a value. *)
    méthode latex_of_value fmt v =
      Odoc_info.reset_type_names () ;
      soit label = self#value_label v.val_name dans
      soit latex = self#make_label label dans
      self#latex_of_text fmt
        ((Latex latex) ::
         (to_text#text_of_value v))

    (** Print LaTeX code for a class attribute. *)
    méthode latex_of_attribute fmt a =
      self#latex_of_text fmt
        ((Latex (self#make_label (self#attribute_label a.att_value.val_name))) ::
         (to_text#text_of_attribute a))

    (** Print LaTeX code for a class method. *)
    méthode latex_of_method fmt m =
      self#latex_of_text fmt
        ((Latex (self#make_label (self#method_label m.met_value.val_name))) ::
         (to_text#text_of_method m))

    (** Print LaTeX code for the parameters of a type. *)
    méthode latex_of_type_params fmt m_name t =
      soit print_one (p, co, cn) =
        ps fmt (Odoc_info.string_of_variance t (co,cn));
        ps fmt (self#normal_type m_name p)
      dans
      filtre t.ty_parameters avec
        [] -> ()
      | [(p,co,cn)] -> print_one (p, co, cn)
      | l ->
          ps fmt "(";
          print_concat fmt ", " print_one t.ty_parameters;
          ps fmt ")"

    méthode latex_of_class_parameter_list fmt father c =
      self#latex_of_text fmt
        (self#text_of_class_params father c)

    (** Print LaTeX code for a type. *)
    méthode latex_of_type fmt t =
      soit s_name = Name.simple t.ty_name dans
      soit text =
        soit (fmt2, flush2) = new_fmt () dans
        Odoc_info.reset_type_names () ;
        soit mod_name = Name.father t.ty_name dans
        Format.fprintf fmt2 "@[<h 2>type ";
        self#latex_of_type_params fmt2 mod_name t;
        (filtre t.ty_parameters avec [] -> () | _ -> ps fmt2 " ");
        ps fmt2 s_name;
        soit priv = t.ty_private = Asttypes.Private dans
        (
         filtre t.ty_manifest avec
           None -> ()
         | Some typ ->
             p fmt2 " = %s%s" (si priv alors "private " sinon "") (self#normal_type mod_name typ)
        );
        soit s_type3 =
          p fmt2
            " %s"
            (
             filtre t.ty_kind avec
               Type_abstract -> ""
             | Type_variant _ -> "="^(si priv alors " private" sinon "")
             | Type_record _ -> "= "^(si priv alors "private " sinon "")^"{"
            ) ;
          flush2 ()
        dans

        soit defs =
          filtre t.ty_kind avec
            Type_abstract -> []
          | Type_variant l ->
              (List.flatten
               (List.map
                  (fonc constr ->
                    soit s_cons =
                      p fmt2 "@[<h 6>  | %s" constr.vc_name;
                      (
                       filtre constr.vc_args, constr.vc_ret avec
                         [], None -> ()
                       | l, None ->
                           p fmt2 " %s@ %s"
                             "of"
                             (self#normal_type_list ~par: faux mod_name " * " l)
                       | [], Some r ->
                           p fmt2 " %s@ %s"
                             ":"
                             (self#normal_type mod_name r)
                       | l, Some r ->
                           p fmt2 " %s@ %s@ %s@ %s"
                             ":"
                             (self#normal_type_list ~par: faux mod_name " * " l)
                             "->"
                             (self#normal_type mod_name r)
                      );
                      flush2 ()
                    dans
                    [ CodePre s_cons ] @
                    (filtre constr.vc_text avec
                      None -> []
                    | Some t ->
                        soit s =
                          ps fmt2 "\\begin{ocamldoccomment}\n";
                          self#latex_of_info fmt2 (Some t);
                          ps fmt2 "\n\\end{ocamldoccomment}\n";
                          flush2 ()
                        dans
                        [ Latex s]
                    )
                  )
                  l
               )
              )
          | Type_record l ->
              (List.flatten
                 (List.map
                    (fonc r ->
                      soit s_field =
                        p fmt2
                          "@[<h 6>  %s%s :@ %s ;"
                          (si r.rf_mutable alors "mutable " sinon "")
                          r.rf_name
                          (self#normal_type mod_name r.rf_type);
                        flush2 ()
                      dans
                      [ CodePre s_field ] @
                      (filtre r.rf_text avec
                        None -> []
                      | Some t ->
                          soit s =
                            ps fmt2 "\\begin{ocamldoccomment}\n";
                            self#latex_of_info fmt2 (Some t);
                            ps fmt2 "\n\\end{ocamldoccomment}\n";
                            flush2 ()
                        dans
                        [ Latex s]
                      )
                    )
                    l
                 )
              ) @
              [ CodePre "}" ]
        dans
        soit defs2 = (CodePre s_type3) :: defs dans
        soit rec iter = fonction
            [] -> []
          | [e] -> [e]
          | (CodePre s1) :: (CodePre s2) :: q ->
              iter ((CodePre (s1^"\n"^s2)) :: q)
          | e :: q ->
              e :: (iter q)
        dans
        (iter defs2) @
        [Latex ("\\index{"^(self#label s_name)^"@\\verb`"^(self#label ~no_:faux s_name)^"`}\n")] @
        (self#text_of_info t.ty_info)
      dans
      self#latex_of_text fmt
        ((Latex (self#make_label (self#type_label t.ty_name))) :: text)

    (** Print LaTeX code for an exception. *)
    méthode latex_of_exception fmt e =
      Odoc_info.reset_type_names () ;
      self#latex_of_text fmt
        ((Latex (self#make_label (self#exception_label e.ex_name))) ::
         (to_text#text_of_exception e))

    méthode latex_of_module_parameter fmt m_name p =
      self#latex_of_text fmt
        [
          Code "functor (";
          Code p.mp_name ;
          Code " : ";
        ] ;
      self#latex_of_module_type_kind fmt m_name p.mp_kind;
      self#latex_of_text fmt [ Code ") -> "]


    méthode latex_of_module_type_kind fmt father kind =
      filtre kind avec
        Module_type_struct eles ->
          self#latex_of_text fmt [Latex "\\begin{ocamldocsigend}\n"];
          List.iter (self#latex_of_module_element fmt father) eles;
          self#latex_of_text fmt [Latex "\\end{ocamldocsigend}\n"]
      | Module_type_functor (p, k) ->
          self#latex_of_module_parameter fmt father p;
          self#latex_of_module_type_kind fmt father k
      | Module_type_alias a ->
          self#latex_of_text fmt
            [Code (self#relative_module_idents father a.mta_name)]
      | Module_type_with (k, s) ->
          self#latex_of_module_type_kind fmt father k;
          self#latex_of_text fmt
            [ Code " ";
              Code (self#relative_idents father s);
            ]
      | Module_type_typeof s ->
          self#latex_of_text fmt
            [ Code "module type of ";
              Code (self#relative_idents father s);
            ]

    méthode latex_of_module_kind fmt father kind =
      filtre kind avec
        Module_struct eles ->
          self#latex_of_text fmt [Latex "\\begin{ocamldocsigend}\n"];
          List.iter (self#latex_of_module_element fmt father) eles;
          self#latex_of_text fmt [Latex "\\end{ocamldocsigend}\n"]
      | Module_alias a ->
          self#latex_of_text fmt
            [Code (self#relative_module_idents father a.ma_name)]
      | Module_functor (p, k) ->
          self#latex_of_module_parameter fmt father p;
          self#latex_of_module_kind fmt father k
      | Module_apply (k1, k2) ->
          (* TODO: l'application n'est pas correcte dans un .mli.
             Que faire ? -> afficher le module_type du typedtree  *)
          self#latex_of_module_kind fmt father k1;
          self#latex_of_text fmt [Code "("];
          self#latex_of_module_kind fmt father k2;
          self#latex_of_text fmt [Code ")"]
      | Module_with (k, s) ->
          (* TODO: a modifier quand Module_with sera plus detaille *)
          self#latex_of_module_type_kind fmt father k;
          self#latex_of_text fmt
            [ Code " ";
              Code (self#relative_idents father s) ;
            ]
      | Module_constraint (k, tk) ->
          (* TODO: on affiche quoi ? *)
          self#latex_of_module_kind fmt father k
      | Module_typeof s ->
          self#latex_of_text fmt
            [ Code "module type of ";
              Code (self#relative_idents father s);
            ]
      | Module_unpack (s, _) ->
          self#latex_of_text fmt
            [
              Code (self#relative_idents father s);
            ]

    méthode latex_of_class_kind fmt father kind =
      filtre kind avec
        Class_structure (inh, eles) ->
          self#latex_of_text fmt [Latex "\\begin{ocamldocobjectend}\n"];
          self#generate_inheritance_info fmt inh;
          List.iter (self#latex_of_class_element fmt father) eles;
          self#latex_of_text fmt [Latex "\\end{ocamldocobjectend}\n"]

      | Class_apply capp ->
          (* TODO: afficher le type final a partir du typedtree *)
          self#latex_of_text fmt [Raw "class application not handled yet"]

      | Class_constr cco ->
          (
           filtre cco.cco_type_parameters avec
             [] -> ()
           | l ->
               self#latex_of_text fmt
                 (
                  Code "[" ::
                  (self#text_of_class_type_param_expr_list father l) @
                  [Code "] "]
                 )
          );
          self#latex_of_text fmt
            [Code (self#relative_idents father cco.cco_name)]

      | Class_constraint (ck, ctk) ->
          self#latex_of_text fmt [Code "( "] ;
          self#latex_of_class_kind fmt father ck;
          self#latex_of_text fmt [Code " : "] ;
          self#latex_of_class_type_kind fmt father ctk;
          self#latex_of_text fmt [Code " )"]

    méthode latex_of_class_type_kind fmt father kind =
      filtre kind avec
        Class_type cta ->
          (
           filtre cta.cta_type_parameters avec
             [] -> ()
           | l ->
               self#latex_of_text fmt
                 (Code "[" ::
                  (self#text_of_class_type_param_expr_list father l) @
                  [Code "] "]
                 )
          );
          self#latex_of_text fmt
            [Code (self#relative_idents father cta.cta_name)]

      | Class_signature (inh, eles) ->
          self#latex_of_text fmt [Latex "\\begin{ocamldocobjectend}\n"];
          self#generate_inheritance_info fmt inh;
          List.iter (self#latex_of_class_element fmt father) eles;
          self#latex_of_text fmt [Latex "\\end{ocamldocobjectend}\n"]

    méthode latex_for_module_index fmt m =
      soit s_name = Name.simple m.m_name dans
      self#latex_of_text fmt
        [Latex ("\\index{"^(self#label s_name)^"@\\verb`"^
                (self#label ~no_:faux s_name)^"`}\n"
               )
        ]

    méthode latex_for_module_type_index fmt mt =
      soit s_name = Name.simple mt.mt_name dans
      self#latex_of_text fmt
        [Latex ("\\index{"^(self#label s_name)^"@\\verb`"^
                (self#label ~no_:faux (Name.simple s_name))^"`}\n"
               )
        ]

    méthode latex_for_module_label fmt m =
      ps fmt (self#make_label (self#module_label m.m_name))

    méthode latex_for_module_type_label fmt mt =
      ps fmt (self#make_label (self#module_type_label mt.mt_name))


    méthode latex_for_class_index fmt c =
      soit s_name = Name.simple c.cl_name dans
      self#latex_of_text fmt
        [Latex ("\\index{"^(self#label s_name)^"@\\verb`"^
                (self#label ~no_:faux s_name)^"`}\n"
               )
        ]

    méthode latex_for_class_type_index fmt ct =
      soit s_name = Name.simple ct.clt_name dans
      self#latex_of_text fmt
        [Latex ("\\index{"^(self#label s_name)^"@\\verb`"^
                (self#label ~no_:faux s_name)^"`}\n"
               )
        ]

    méthode latex_for_class_label fmt c =
      ps fmt (self#make_label (self#class_label c.cl_name))

    méthode latex_for_class_type_label fmt ct =
      ps fmt (self#make_label (self#class_type_label ct.clt_name))

    (** Print the LaTeX code for the given module. *)
    méthode latex_of_module fmt m =
      soit father = Name.father m.m_name dans
      soit t =
        [
          Latex "\\begin{ocamldoccode}\n" ;
          Code "module ";
          Code (Name.simple m.m_name);
          Code " : ";
        ]
      dans
      self#latex_of_text fmt t;
      self#latex_of_text fmt [ Latex "\\end{ocamldoccode}\n" ];
      self#latex_for_module_label fmt m;
      self#latex_for_module_index fmt m;
      p fmt "@[<h 4>";
      self#latex_of_module_kind fmt father m.m_kind;
      (
       filtre Module.module_is_functor m avec
         faux -> ()
       | vrai ->
           self#latex_of_text fmt  [Newline];
           (
            filtre List.filter (fonc (_,d) -> d <> None)
                (module_parameters ~trans: faux m)
            avec
              [] -> ()
            | l ->
                soit t =
                  [ Bold [Raw "Parameters: "];
                    List
                      (List.map
                         (fonc (p,text_opt) ->
                           soit t = filtre text_opt avec None -> [] | Some t -> t dans
                           ( Raw p.mp_name :: Raw ": " :: t)
                         )
                         l
                      )
                  ]
           dans
           self#latex_of_text fmt t
           );
      );
      self#latex_of_text fmt [Newline];
      self#latex_of_info fmt ~block: vrai m.m_info;
      p fmt "@]";


    (** Print the LaTeX code for the given module type. *)
    méthode latex_of_module_type fmt mt =
      soit father = Name.father mt.mt_name dans
      soit t =
        [
          Latex "\\begin{ocamldoccode}\n" ;
          Code "module type " ;
          Code (Name.simple mt.mt_name);
        ]
      dans
      self#latex_of_text fmt t;
      (
       filtre mt.mt_type, mt.mt_kind avec
       | Some mtyp, Some kind ->
           self#latex_of_text fmt [ Code " = " ];
           self#latex_of_text fmt [ Latex "\\end{ocamldoccode}\n" ];
           self#latex_for_module_type_label fmt mt;
           self#latex_for_module_type_index fmt mt;
           p fmt "@[<h 4>";
           self#latex_of_module_type_kind fmt father kind
       | _ ->
           self#latex_of_text fmt [ Latex "\\end{ocamldoccode}\n" ];
           self#latex_for_module_type_index fmt mt;
           p fmt "@[<h 4>";
      );
      (
       filtre Module.module_type_is_functor mt avec
         faux -> ()
       | vrai ->
           self#latex_of_text fmt [Newline];
           (
            filtre List.filter (fonc (_,d) -> d <> None)
                (module_type_parameters ~trans: faux mt)
            avec
              [] -> ()
            | l ->
                soit t =
                  [ Bold [Raw "Parameters: "];
                    List
                      (List.map
                         (fonc (p,text_opt) ->
                           soit t = filtre text_opt avec None -> [] | Some t -> t dans
                           ( Raw p.mp_name :: Raw ": " :: t)
                         )
                         l
                      )
                  ]
                dans
                self#latex_of_text fmt t
           );
      );
      self#latex_of_text fmt [Newline];
      self#latex_of_info fmt ~block: vrai mt.mt_info;
      p fmt "@]";

    (** Print the LaTeX code for the given included module. *)
    méthode latex_of_included_module fmt im =
      self#latex_of_text fmt
        ((Code "include ") ::
         (Code
            (filtre im.im_module avec
              None -> im.im_name
            | Some (Mod m) -> m.m_name
            | Some (Modtype mt) -> mt.mt_name)
         ) ::
         (self#text_of_info im.im_info)
        )

    (** Print the LaTeX code for the given class. *)
    méthode latex_of_class fmt c =
      Odoc_info.reset_type_names () ;
      soit father = Name.father c.cl_name dans
      soit type_params =
        filtre c.cl_type_parameters avec
          [] -> ""
        | l -> (self#normal_class_type_param_list father l)^" "
      dans
      soit t =
        [
          Latex "\\begin{ocamldoccode}\n" ;
          Code (Printf.sprintf
                  "class %s%s%s : "
                  (si c.cl_virtual alors "virtual " sinon "")
                  type_params
                  (Name.simple c.cl_name)
               )
        ]
      dans
      self#latex_of_text fmt t;
      self#latex_of_class_parameter_list fmt father c;
      (* avoid a big gap if the kind is a consrt *)
      (
       filtre c.cl_kind avec
         Class.Class_constr _ ->
           self#latex_of_class_kind fmt father c.cl_kind
       | _ ->
           ()
      );
      self#latex_of_text fmt [ Latex "\\end{ocamldoccode}\n" ];
      self#latex_for_class_label fmt c;
      self#latex_for_class_index fmt c;
      p fmt "@[<h 4>";
      (filtre c.cl_kind avec
        Class.Class_constr _ -> ()
      |        _ -> self#latex_of_class_kind fmt father c.cl_kind
      );
      self#latex_of_text fmt [Newline];
      self#latex_of_info fmt ~block: vrai c.cl_info;
      p fmt "@]"

    (** Print the LaTeX code for the given class type. *)
    méthode latex_of_class_type fmt ct =
      Odoc_info.reset_type_names () ;
      soit father = Name.father ct.clt_name dans
      soit type_params =
        filtre ct.clt_type_parameters avec
          [] -> ""
        | l -> (self#normal_class_type_param_list father l)^" "
      dans
      soit t =
        [
          Latex "\\begin{ocamldoccode}\n" ;
          Code (Printf.sprintf
                  "class type %s%s%s = "
                  (si ct.clt_virtual alors "virtual " sinon "")
                  type_params
                  (Name.simple ct.clt_name)
               )
        ]
      dans
      self#latex_of_text fmt t;

      self#latex_of_text fmt [ Latex "\\end{ocamldoccode}\n" ];
      self#latex_for_class_type_label fmt ct;
      self#latex_for_class_type_index fmt ct;
      p fmt "@[<h 4>";
      self#latex_of_class_type_kind fmt father ct.clt_kind;
      self#latex_of_text fmt [Newline];
      self#latex_of_info fmt ~block: vrai ct.clt_info;
      p fmt "@]"

    (** Print the LaTeX code for the given class element. *)
    méthode latex_of_class_element fmt class_name class_ele =
      self#latex_of_text fmt [Newline];
      filtre class_ele avec
        Class_attribute att -> self#latex_of_attribute fmt att
      | Class_method met -> self#latex_of_method fmt met
      | Class_comment t ->
          filtre t avec
          | [] -> ()
          | (Title (_,_,_)) :: _ -> self#latex_of_text fmt t
          | _ -> self#latex_of_text fmt [ Title ((Name.depth class_name) + 2, None, t) ]

    (** Print the LaTeX code for the given module element. *)
    méthode latex_of_module_element fmt module_name module_ele =
      self#latex_of_text fmt [Newline];
      filtre module_ele avec
        Element_module m -> self#latex_of_module fmt m
      | Element_module_type mt -> self#latex_of_module_type fmt mt
      | Element_included_module im -> self#latex_of_included_module fmt im
      | Element_class c -> self#latex_of_class fmt c
      | Element_class_type ct -> self#latex_of_class_type fmt ct
      | Element_value v -> self#latex_of_value fmt v
      | Element_exception e -> self#latex_of_exception fmt e
      | Element_type t -> self#latex_of_type fmt t
      | Element_module_comment t -> self#latex_of_text fmt t

    (** Generate the LaTeX code for the given list of inherited classes.*)
    méthode generate_inheritance_info fmt inher_l =
      soit f inh =
        filtre inh.ic_class avec
          None -> (* we can't make the reference *)
            Newline ::
            Code ("inherit "^inh.ic_name) ::
            (filtre inh.ic_text avec
              None -> []
            | Some t -> Newline :: t
            )
        | Some cct ->
            soit label =
              filtre cct avec
                Cl _ -> self#class_label inh.ic_name
              | Cltype _ -> self#class_type_label inh.ic_name
            dans
            (* we can create the reference *)
            Newline ::
            Odoc_info.Code ("inherit "^inh.ic_name) ::
            (Odoc_info.Latex (" ["^(self#make_ref label)^"]")) ::
            (filtre inh.ic_text avec
              None -> []
            | Some t -> Newline :: t
            )
      dans
      List.iter (self#latex_of_text fmt) (List.map f inher_l)

    (** Generate the LaTeX code for the inherited classes of the given class. *)
    méthode generate_class_inheritance_info fmt cl =
      soit rec iter_kind k =
        filtre k avec
          Class_structure ([], _) ->
            ()
        | Class_structure (l, _) ->
            self#generate_inheritance_info fmt l
        | Class_constraint (k, _) ->
            iter_kind k
        | Class_apply _
        | Class_constr _ ->
            ()
      dans
      iter_kind cl.cl_kind

    (** Generate the LaTeX code for the inherited classes of the given class type. *)
    méthode generate_class_type_inheritance_info fmt clt =
      filtre clt.clt_kind avec
        Class_signature ([], _) ->
          ()
      | Class_signature (l, _) ->
          self#generate_inheritance_info fmt l
      | Class_type _ ->
          ()

    (** Generate the LaTeX code for the given top module, in the given buffer. *)
    méthode generate_for_top_module fmt m =
      soit (first_t, rest_t) = self#first_and_rest_of_info m.m_info dans
      soit text =
        si m.m_text_only alors
          [ Title (1, None, [Raw m.m_name]  @
                   (filtre first_t avec
                     [] -> []
                   | t -> (Raw " : ") :: t)
                  ) ;
          ]
        sinon
          [ Title (1, None,
                   [ Raw (Odoc_messages.modul^" ") ; Code m.m_name ] @
                   (filtre first_t avec
                     [] -> []
                   | t -> (Raw " : ") :: t)) ;
          ]
      dans
      self#latex_of_text fmt text;
      self#latex_for_module_label fmt m;
      self#latex_for_module_index fmt m;
      self#latex_of_text fmt rest_t ;

      self#latex_of_text fmt [ Newline ] ;
      si not m.m_text_only alors ps fmt "\\ocamldocvspace{0.5cm}\n\n";
      List.iter
        (fonc ele ->
          self#latex_of_module_element fmt m.m_name ele;
          ps fmt "\n\n"
        )
        (Module.module_elements ~trans: faux m)

    (** Print the header of the TeX document. *)
    méthode latex_header fmt module_list =
      ps fmt "\\documentclass[11pt]{article} \n";
      ps fmt "\\usepackage[latin1]{inputenc} \n";
      ps fmt "\\usepackage[T1]{fontenc} \n";
      ps fmt "\\usepackage{textcomp}\n";
      ps fmt "\\usepackage{fullpage} \n";
      ps fmt "\\usepackage{url} \n";
      ps fmt "\\usepackage{ocamldoc}\n";
      (
       filtre !Global.title avec
         None -> ()
       | Some s ->
           ps fmt "\\title{";
           ps fmt (self#escape s);
           ps fmt "}\n"
      );
      ps fmt "\\begin{document}\n";
      (filtre !Global.title avec
        None -> () |
        Some _ -> ps fmt "\\maketitle\n"
      );
      si !Global.with_toc alors ps fmt "\\tableofcontents\n";
      (
       soit info = Odoc_info.apply_opt
           (Odoc_info.info_of_comment_file module_list)
           !Odoc_info.Global.intro_file
       dans
       (filtre info avec None -> () | Some _ -> ps fmt "\\vspace{0.2cm}");
       self#latex_of_info fmt info;
       (filtre info avec None -> () | Some _ -> ps fmt "\n\n")
      )


    (** Generate the LaTeX style file, if it does not exists. *)
    méthode generate_style_file =
      essaie
        soit dir = Filename.dirname !Global.out_file dans
        soit file = Filename.concat dir "ocamldoc.sty" dans
        si Sys.file_exists file alors
          Odoc_info.verbose (Odoc_messages.file_exists_dont_generate file)
        sinon
          (
           soit chanout = open_out file dans
           output_string chanout Odoc_latex_style.content ;
           flush chanout ;
           close_out chanout;
           Odoc_info.verbose (Odoc_messages.file_generated file)
          )
      avec
        Sys_error s ->
          prerr_endline s ;
          incr Odoc_info.errors ;

    (** Generate the LaTeX file from a module list, in the {!Odoc_info.Global.out_file} file. *)
    méthode generate module_list =
      self#generate_style_file ;
      soit main_file = !Global.out_file dans
      soit dir = Filename.dirname main_file dans
      si !separate_files alors
        (
         soit f m =
           essaie
             soit chanout =
               open_out ((Filename.concat dir (Name.simple m.m_name))^".tex")
             dans
             soit fmt = Format.formatter_of_out_channel chanout dans
             self#generate_for_top_module fmt m ;
             Format.pp_print_flush fmt ();
             close_out chanout
           avec
             Failure s
           | Sys_error s ->
               prerr_endline s ;
               incr Odoc_info.errors
         dans
         List.iter f module_list
        );

      essaie
        soit chanout = open_out main_file dans
        soit fmt = Format.formatter_of_out_channel chanout dans
        si !Global.with_header alors self#latex_header fmt module_list;
        List.iter
          (fonc m ->
            si !separate_files alors
              ps fmt ("\\input{"^((Name.simple m.m_name))^".tex}\n")
            sinon
              self#generate_for_top_module fmt m
          )
          module_list ;
        si !Global.with_trailer alors ps fmt "\\end{document}";
        Format.pp_print_flush fmt ();
        close_out chanout
      avec
        Failure s
      | Sys_error s ->
          prerr_endline s ;
          incr Odoc_info.errors
  fin
fin

module type Latex_generator = module type de Generator
