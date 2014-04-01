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

(** Generation of html documentation.*)

soit print_DEBUG s = print_string s ; print_newline ()

ouvre Odoc_info
ouvre Parameter
ouvre Value
ouvre Type
ouvre Exception
ouvre Class
ouvre Module

soit with_parameter_list = ref faux
soit css_style = ref None
soit index_only = ref faux
soit colorize_code = ref faux
soit html_short_functors = ref faux
soit charset = ref "iso-8859-1"


(** The functions used for naming files and html marks.*)
module Naming =
  struct
    (** The prefix for types marks. *)
    soit mark_type = "TYPE"

    (** The prefix for types elements (record fields or constructors). *)
    soit mark_type_elt = "TYPEELT"

    (** The prefix for functions marks. *)
    soit mark_function = "FUN"

    (** The prefix for exceptions marks. *)
    soit mark_exception = "EXCEPTION"

    (** The prefix for values marks. *)
    soit mark_value = "VAL"

    (** The prefix for attributes marks. *)
    soit mark_attribute = "ATT"

    (** The prefix for methods marks. *)
    soit mark_method = "METHOD"

    (** The prefix for code files.. *)
    soit code_prefix = "code_"

    (** The prefix for type files.. *)
    soit type_prefix = "type_"

    (** Return the two html files names for the given module or class name.*)
    soit html_files name =
      soit qual =
        essaie
          soit i = String.rindex name '.' dans
          filtre name.[i + 1] avec
          | 'A'..'Z' -> ""
          | _ -> "-c"
        avec Not_found -> ""
      dans
      soit prefix = name^qual dans
      soit html_file = prefix^".html" dans
      soit html_frame_file = prefix^"-frame.html" dans
      (html_file, html_frame_file)

    (** Return the target for the given prefix and simple name. *)
    soit target pref simple_name = pref^simple_name

    (** Return the complete link target (file#target) for the given prefix string and complete name.*)
    soit complete_target pref complete_name =
      soit simple_name = Name.simple complete_name dans
      soit module_name =
        soit s = Name.father complete_name dans
        si s = "" alors simple_name sinon s
      dans
      soit (html_file, _) = html_files module_name dans
      html_file^"#"^(target pref simple_name)

    (** Return the link target for the given type. *)
    soit type_target t = target mark_type (Name.simple t.ty_name)

    (** Return the link target for the given variant constructor. *)
    soit const_target t f =
      soit name = Printf.sprintf "%s.%s" (Name.simple t.ty_name) f.vc_name dans
      target mark_type_elt name

    (** Return the link target for the given record field. *)
    soit recfield_target t f = target mark_type_elt
      (Printf.sprintf "%s.%s" (Name.simple t.ty_name) f.rf_name)

    (** Return the complete link target for the given type. *)
    soit complete_type_target t = complete_target mark_type t.ty_name

    soit complete_recfield_target name =
      soit typ = Name.father name dans
      soit field = Name.simple name dans
      Printf.sprintf "%s.%s" (complete_target mark_type_elt typ) field

    soit complete_const_target = complete_recfield_target

    (** Return the link target for the given exception. *)
    soit exception_target e = target mark_exception (Name.simple e.ex_name)

    (** Return the complete link target for the given exception. *)
    soit complete_exception_target e = complete_target mark_exception e.ex_name

    (** Return the link target for the given value. *)
    soit value_target v = target mark_value (Name.simple v.val_name)

    (** Return the given value name where symbols accepted in infix values
       are replaced by strings, to avoid clashes with the filesystem.*)
    soit subst_infix_symbols name =
      soit len = String.length name dans
      soit buf = Buffer.create len dans
      soit ch c = Buffer.add_char buf c dans
      soit st s = Buffer.add_string buf s dans
      pour i = 0 à len - 1 faire
        filtre name.[i] avec
        | '|' -> st "_pipe_"
        | '<' -> st "_lt_"
        | '>' -> st "_gt_"
        | '@' -> st "_at_"
        | '^' -> st "_exp_"
        | '&' -> st "_amp_"
        | '+' -> st "_plus_"
        | '-' -> st "_minus_"
        | '*' -> st "_star_"
        | '/' -> st "_slash_"
        | '$' -> st "_dollar_"
        | '%' -> st "_percent_"
        | '=' -> st "_equal_"
        | ':' -> st "_column_"
        | '~' -> st "_tilde_"
        | '!' -> st "_bang_"
        | '?' -> st "_questionmark_"
        | c -> ch c
      fait;
      Buffer.contents buf

    (** Return the complete link target for the given value. *)
    soit complete_value_target v = complete_target mark_value v.val_name

    (** Return the complete filename for the code of the given value. *)
    soit file_code_value_complete_target v =
      soit f = code_prefix^mark_value^(subst_infix_symbols v.val_name)^".html" dans
      f

    (** Return the link target for the given attribute. *)
    soit attribute_target a = target mark_attribute (Name.simple a.att_value.val_name)

    (** Return the complete link target for the given attribute. *)
    soit complete_attribute_target a = complete_target mark_attribute a.att_value.val_name

    (** Return the complete filename for the code of the given attribute. *)
    soit file_code_attribute_complete_target a =
      soit f = code_prefix^mark_attribute^a.att_value.val_name^".html" dans
      f

    (** Return the link target for the given method. *)
    soit method_target m = target mark_method (Name.simple m.met_value.val_name)

    (** Return the complete link target for the given method. *)
    soit complete_method_target m = complete_target mark_method m.met_value.val_name

    (** Return the complete filename for the code of the given method. *)
    soit file_code_method_complete_target m =
      soit f = code_prefix^mark_method^m.met_value.val_name^".html" dans
      f

    (** Return the link target for the given label section. *)
    soit label_target l = target "" l

    (** Return the complete link target for the given section label. *)
    soit complete_label_target l = complete_target "" l

    (** Return the complete filename for the code of the type of the
       given module or module type name. *)
    soit file_type_module_complete_target name =
      soit f = type_prefix^name^".html" dans
      f

    (** Return the complete filename for the code of the
       given module name. *)
    soit file_code_module_complete_target name =
      soit f = code_prefix^name^".html" dans
      f

    (** Return the complete filename for the code of the type of the
       given class or class type name. *)
    soit file_type_class_complete_target name =
      soit f = type_prefix^name^".html" dans
      f
  fin

module StringSet = Set.Make (struct
  type t = string
  soit compare (x:t) y = compare x y
fin)

(** A class with a method to colorize a string which represents OCaml code. *)
classe ocaml_code =
  objet(self)
    méthode html_of_code b ?(with_pre=vrai) code =
      Odoc_ocamlhtml.html_of_code b ~with_pre: with_pre code
  fin

soit new_buf () = Buffer.create 1024
soit bp = Printf.bprintf
soit bs = Buffer.add_string


(** Generation of html code from text structures. *)
classe virtuelle text =
  objet (self)
    (** We want to display colorized code. *)
    hérite ocaml_code

    (** Escape the strings which would clash with html syntax, and
       make some replacements (double newlines replaced by <br>). *)
    méthode escape s = Odoc_ocamlhtml.escape_base s

    méthode keep_alpha_num s =
      soit len = String.length s dans
      soit buf = Buffer.create len dans
      pour i = 0 à len - 1 faire
        filtre s.[i] avec
          'a'..'z' | 'A'..'Z' | '0'..'9' -> Buffer.add_char buf s.[i]
        | _ -> ()
      fait;
      Buffer.contents buf

    (** Return a label created from the first sentence of a text. *)
    méthode label_of_text t=
      soit t2 = Odoc_info.first_sentence_of_text t dans
      soit s = Odoc_info.string_of_text t2 dans
      soit s2 = self#keep_alpha_num s dans
      s2

    (** Create a label for the associated title.
       Return the label specified by the user or a label created
       from the title level and the first sentence of the title. *)
    méthode create_title_label (n,label_opt,t) =
      filtre label_opt avec
        Some s -> s
      | None -> Printf.sprintf "%d_%s" n (self#label_of_text t)

    (** Print the html code corresponding to the [text] parameter. *)
    méthode html_of_text b t =
      List.iter (self#html_of_text_element b) t

    (** Print the html code for the [text_element] in parameter. *)
    méthode html_of_text_element b te =
      print_DEBUG "text::html_of_text_element";
      filtre te avec
      | Odoc_info.Raw s -> self#html_of_Raw b s
      | Odoc_info.Code s -> self#html_of_Code b s
      | Odoc_info.CodePre s -> self#html_of_CodePre b s
      | Odoc_info.Verbatim s -> self#html_of_Verbatim b s
      | Odoc_info.Bold t -> self#html_of_Bold b t
      | Odoc_info.Italic t -> self#html_of_Italic b t
      | Odoc_info.Emphasize t -> self#html_of_Emphasize b t
      | Odoc_info.Center t -> self#html_of_Center b t
      | Odoc_info.Left t -> self#html_of_Left b t
      | Odoc_info.Right t -> self#html_of_Right b t
      | Odoc_info.List tl -> self#html_of_List b tl
      | Odoc_info.Enum tl -> self#html_of_Enum b tl
      | Odoc_info.Newline -> self#html_of_Newline b
      | Odoc_info.Block t -> self#html_of_Block b t
      | Odoc_info.Title (n, l_opt, t) -> self#html_of_Title b n l_opt t
      | Odoc_info.Latex s -> self#html_of_Latex b s
      | Odoc_info.Link (s, t) -> self#html_of_Link b s t
      | Odoc_info.Ref (name, ref_opt, text_opt) ->
          self#html_of_Ref b name ref_opt text_opt
      | Odoc_info.Superscript t -> self#html_of_Superscript b t
      | Odoc_info.Subscript t -> self#html_of_Subscript b t
      | Odoc_info.Module_list l -> self#html_of_Module_list b l
      | Odoc_info.Index_list -> self#html_of_Index_list b
      | Odoc_info.Custom (s,t) -> self#html_of_custom_text b s t
      | Odoc_info.Target (target, code) -> self#html_of_Target b ~target ~code

    méthode html_of_custom_text b s t = ()

    méthode html_of_Target b ~target ~code =
      si String.lowercase target = "html" alors bs b code sinon ()

    méthode html_of_Raw b s = bs b (self#escape s)

    méthode html_of_Code b s =
      si !colorize_code alors
        self#html_of_code b ~with_pre: faux s
      sinon
        (
         bs b "<code class=\"";
         bs b Odoc_ocamlhtml.code_class ;
         bs b "\">";
         bs b (self#escape s);
         bs b "</code>"
        )

    méthode html_of_CodePre =
        soit remove_useless_newlines s =
          soit len = String.length s dans
          soit rec iter_first n =
            si n >= len alors
              None
            sinon
              filtre s.[n] avec
              | '\n' -> iter_first (n+1)
              | _ -> Some n
          dans
          filtre iter_first 0 avec
            None -> ""
          | Some first ->
              soit rec iter_last n =
                si n <= first alors
                  None
                sinon
                  filtre s.[n] avec
                    '\t'  -> iter_last (n-1)
                  | _ -> Some n
              dans
              filtre iter_last (len-1) avec
                None -> String.sub s first 1
              | Some last -> String.sub s first ((last-first)+1)
        dans
        fonc b s ->
      si !colorize_code alors
          (
           bs b "<pre class=\"codepre\">";
           self#html_of_code b (remove_useless_newlines s);
           bs b "</pre>"
          )
      sinon
        (
         bs b "<pre class=\"codepre\"><code class=\"";
         bs b Odoc_ocamlhtml.code_class;
         bs b "\">" ;
         bs b (self#escape (remove_useless_newlines s));
         bs b "</code></pre>"
        )

    méthode html_of_Verbatim b s =
      bs b "<pre class=\"verbatim\">";
      bs b (self#escape s);
      bs b "</pre>"

    méthode html_of_Bold b t =
      bs b "<b>";
      self#html_of_text b t;
      bs b "</b>"

    méthode html_of_Italic b t =
      bs b "<i>" ;
      self#html_of_text b t;
      bs b "</i>"

    méthode html_of_Emphasize b t =
      bs b "<em>" ;
      self#html_of_text b t ;
      bs b "</em>"

    méthode html_of_Center b t =
      bs b "<center>";
      self#html_of_text b t;
      bs b "</center>"

    méthode html_of_Left b t =
      bs b "<div align=left>";
      self#html_of_text b t;
      bs b "</div>"

    méthode html_of_Right b t =
      bs b "<div align=right>";
      self#html_of_text b t;
      bs b "</div>"

    méthode html_of_List b tl =
      bs b "<ul>\n";
      List.iter
        (fonc t -> bs b "<li>"; self#html_of_text b t; bs b "</li>\n")
        tl;
      bs b "</ul>\n"

    méthode html_of_Enum b tl =
      bs b "<OL>\n";
      List.iter
        (fonc t -> bs b "<li>"; self#html_of_text b t; bs b"</li>\n")
        tl;
      bs b "</OL>\n"

    méthode html_of_Newline b = bs b "\n<p>\n"

    méthode html_of_Block b t =
      bs b "<blockquote>\n";
      self#html_of_text b t;
      bs b "</blockquote>\n"

    méthode html_of_Title b n label_opt t =
      soit label1 = self#create_title_label (n, label_opt, t) dans
      soit (tag_o, tag_c) =
        si n > 6 alors
          (Printf.sprintf "div class=\"h%d\"" n, "div")
        sinon
          soit t = Printf.sprintf "h%d" n dans (t, t)
      dans
      bs b "<";
      bp b "%s id=\"%s\"" tag_o (Naming.label_target label1);
      bs b ">";
      self#html_of_text b t;
      bs b "</";
      bs b tag_c;
      bs b ">"

    méthode html_of_Latex b _ = ()
      (* don't care about LaTeX stuff in HTML. *)

    méthode html_of_Link b s t =
      bs b "<a href=\"";
      bs b s ;
      bs b "\">";
      self#html_of_text b t;
      bs b "</a>"

    méthode html_of_Ref b name ref_opt text_opt =
      filtre ref_opt avec
        None ->
          soit text =
            filtre text_opt avec
              None -> [Odoc_info.Code name]
            | Some t -> t
          dans
          self#html_of_text b text
      | Some kind ->
          soit h name = Odoc_info.Code (Odoc_info.use_hidden_modules name) dans
          soit (target, text) =
            filtre kind avec
              Odoc_info.RK_module
            | Odoc_info.RK_module_type
            | Odoc_info.RK_class
            | Odoc_info.RK_class_type ->
                soit (html_file, _) = Naming.html_files name dans
                (html_file, h name)
            | Odoc_info.RK_value -> (Naming.complete_target Naming.mark_value name, h name)
            | Odoc_info.RK_type -> (Naming.complete_target Naming.mark_type name, h name)
            | Odoc_info.RK_exception -> (Naming.complete_target Naming.mark_exception name, h name)
            | Odoc_info.RK_attribute -> (Naming.complete_target Naming.mark_attribute name, h name)
            | Odoc_info.RK_method -> (Naming.complete_target Naming.mark_method name, h name)
            | Odoc_info.RK_section t -> (Naming.complete_label_target name,
                                         Odoc_info.Italic [Raw (Odoc_info.string_of_text t)])
            | Odoc_info.RK_recfield -> (Naming.complete_recfield_target name, h name)
            | Odoc_info.RK_const -> (Naming.complete_const_target name, h name)
          dans
          soit text =
            filtre text_opt avec
              None -> [text]
            | Some text -> text
          dans
          bs b ("<a href=\""^target^"\">");
          self#html_of_text b text;
          bs b "</a>"

    méthode html_of_Superscript b t =
      bs b "<sup class=\"superscript\">";
      self#html_of_text b t;
      bs b "</sup>"

    méthode html_of_Subscript b t =
      bs b "<sub class=\"subscript\">";
      self#html_of_text b t;
      bs b "</sub>"

    méthode virtuelle html_of_info_first_sentence : _

    méthode html_of_Module_list b l =
      bs b "<br>\n<table class=\"indextable\">\n";
      List.iter
        (fonc name ->
          bs b "<tr><td class=\"module\">";
          (
           essaie
             soit m =
               List.find (fonc m -> m.m_name = name) self#list_modules
             dans
             soit (html, _) = Naming.html_files m.m_name dans
             bp b "<a href=\"%s\">%s</a></td>" html m.m_name;
             bs b "<td>";
             self#html_of_info_first_sentence b m.m_info;
           avec
             Not_found ->
               Odoc_global.pwarning (Odoc_messages.cross_module_not_found name);
               bp b "%s</td><td>" name
          );
          bs b "</td></tr>\n"
        )
        l;
      bs b "</table>\n"

    méthode html_of_Index_list b =
      soit index_if_not_empty l url m =
        filtre l avec
          [] -> ()
        | _ -> bp b "<li><a href=\"%s\">%s</a></li>\n" url m
      dans
      bp b "<ul class=\"indexlist\">\n";
      index_if_not_empty self#list_types self#index_types Odoc_messages.index_of_types;
      index_if_not_empty self#list_exceptions self#index_exceptions Odoc_messages.index_of_exceptions;
      index_if_not_empty self#list_values self#index_values Odoc_messages.index_of_values;
      index_if_not_empty self#list_attributes self#index_attributes Odoc_messages.index_of_attributes;
      index_if_not_empty self#list_methods self#index_methods Odoc_messages.index_of_methods;
      index_if_not_empty self#list_classes self#index_classes Odoc_messages.index_of_classes;
      index_if_not_empty self#list_class_types self#index_class_types Odoc_messages.index_of_class_types;
      index_if_not_empty self#list_modules self#index_modules Odoc_messages.index_of_modules;
      index_if_not_empty self#list_module_types self#index_module_types Odoc_messages.index_of_module_types;
      bp b "</ul>\n"

    méthode virtuelle list_types : Odoc_info.Type.t_type list
    méthode virtuelle index_types : string
    méthode virtuelle list_exceptions : Odoc_info.Exception.t_exception list
    méthode virtuelle index_exceptions : string
    méthode virtuelle list_values : Odoc_info.Value.t_value list
    méthode virtuelle index_values : string
    méthode virtuelle list_attributes : Odoc_info.Value.t_attribute list
    méthode virtuelle index_attributes : string
    méthode virtuelle list_methods : Odoc_info.Value.t_method list
    méthode virtuelle index_methods : string
    méthode virtuelle list_classes : Odoc_info.Class.t_class list
    méthode virtuelle index_classes : string
    méthode virtuelle list_class_types : Odoc_info.Class.t_class_type list
    méthode virtuelle index_class_types : string
    méthode virtuelle list_modules : Odoc_info.Module.t_module list
    méthode virtuelle index_modules : string
    méthode virtuelle list_module_types : Odoc_info.Module.t_module_type list
    méthode virtuelle index_module_types : string

  fin

(** A class used to generate html code for info structures. *)
classe virtuelle info =
  objet (self)
    (** The list of pairs [(tag, f)] where [f] is a function taking
       the [text] associated to [tag] and returning html code.
       Add a pair here to handle a tag.*)
    val modifiable tag_functions = ([] : (string * (Odoc_info.text -> string)) list)

    (** The method used to get html code from a [text]. *)
    méthode virtuelle html_of_text : Buffer.t -> Odoc_info.text -> unit

    (** Print html for an author list. *)
    méthode html_of_author_list b l =
      filtre l avec
        [] -> ()
      | _ ->
          bp b "<b>%s:</b> " Odoc_messages.authors;
          self#html_of_text b [Raw (String.concat ", " l)];
          bs b "<br>\n"

    (** Print html code for the given optional version information.*)
    méthode html_of_version_opt b v_opt =
      filtre v_opt avec
        None -> ()
      | Some v ->
           bp b "<b>%s:</b> " Odoc_messages.version;
           self#html_of_text b [Raw v];
           bs b "<br>\n"

    (** Print html code for the given optional since information.*)
    méthode html_of_since_opt b s_opt =
      filtre s_opt avec
        None -> ()
      | Some s ->
          bp b "<b>%s</b> " Odoc_messages.since;
          self#html_of_text b [Raw s];
          bs b "<br>\n"

    (** Print html code for the given "before" information.*)
    méthode html_of_before b l =
      soit f (v, text) =
        bp b "<b>%s " Odoc_messages.before;
        self#html_of_text b [Raw v];
        bs b " </b> ";
        self#html_of_text b text;
        bs b "<br>\n"
      dans
      List.iter f l

    (** Print html code for the given list of raised exceptions.*)
    méthode html_of_raised_exceptions b l =
      filtre l avec
        [] -> ()
      | (s, t) :: [] ->
          bp b "<b>%s</b> <code>%s</code> "
            Odoc_messages.raises
            s;
          self#html_of_text b t;
          bs b "<br>\n"
      | _ ->
          bp b "<b>%s</b><ul>" Odoc_messages.raises;
          List.iter
            (fonc (ex, desc) ->
              bp b "<li><code>%s</code> " ex ;
              self#html_of_text b desc;
              bs b "</li>\n"
            )
            l;
          bs b "</ul>\n"

    (** Print html code for the given "see also" reference. *)
    méthode html_of_see b (see_ref, t)  =
      soit t_ref =
        filtre see_ref avec
          Odoc_info.See_url s -> [ Odoc_info.Link (s, t) ]
        | Odoc_info.See_file s -> (Odoc_info.Code s) :: (Odoc_info.Raw " ") :: t
        | Odoc_info.See_doc s -> (Odoc_info.Italic [Odoc_info.Raw s]) :: (Odoc_info.Raw " ") :: t
      dans
      self#html_of_text b t_ref

    (** Print html code for the given list of "see also" references.*)
    méthode html_of_sees b l =
      filtre l avec
        [] -> ()
      | see :: [] ->
          bp b "<b>%s</b> " Odoc_messages.see_also;
          self#html_of_see b see;
          bs b "<br>\n"
      | _ ->
          bp b "<b>%s</b><ul>" Odoc_messages.see_also;
          List.iter
            (fonc see ->
              bs b "<li>" ;
              self#html_of_see b see;
              bs b "</li>\n"
            )
            l;
          bs b "</ul>\n"

    (** Print html code for the given optional return information.*)
    méthode html_of_return_opt b return_opt =
      filtre return_opt avec
        None -> ()
      | Some s ->
          bp b "<b>%s</b> " Odoc_messages.returns;
          self#html_of_text b s;
          bs b "<br>\n"

    (** Print html code for the given list of custom tagged texts. *)
    méthode html_of_custom b l =
      List.iter
        (fonc (tag, text) ->
          essaie
            soit f = List.assoc tag tag_functions dans
            Buffer.add_string b (f text)
          avec
            Not_found ->
              Odoc_info.warning (Odoc_messages.tag_not_handled tag)
        )
        l

    (** Print html code for a description, except for the [i_params] field.
       @param indent can be specified not to use the style of info comments;
       default is [true].
    *)
    méthode html_of_info ?(cls="") ?(indent=vrai) b info_opt =
      filtre info_opt avec
        None ->
          ()
      | Some info ->
          soit module M = Odoc_info dans
          si indent alors bs b ("<div class=\"info "^cls^"\">\n");
          (
           filtre info.M.i_deprecated avec
            None -> ()
           | Some d ->
               bs b "<span class=\"warning\">";
               bs b Odoc_messages.deprecated ;
               bs b "</span>" ;
               self#html_of_text b d;
               bs b "<br>\n"
          );
          (
           filtre info.M.i_desc avec
             None -> ()
           | Some d quand d = [Odoc_info.Raw ""] -> ()
           | Some d -> self#html_of_text b d; bs b "<br>\n"
          );
          self#html_of_author_list b info.M.i_authors;
          self#html_of_version_opt b info.M.i_version;
          self#html_of_before b info.M.i_before;
          self#html_of_since_opt b info.M.i_since;
          self#html_of_raised_exceptions b info.M.i_raised_exceptions;
          self#html_of_return_opt b info.M.i_return_value;
          self#html_of_sees b info.M.i_sees;
          self#html_of_custom b info.M.i_custom;
          si indent alors bs b "</div>\n"

    (** Print html code for the first sentence of a description.
       The titles and lists in this first sentence has been removed.*)
    méthode html_of_info_first_sentence b info_opt =
      filtre info_opt avec
        None -> ()
      | Some info ->
          soit module M = Odoc_info dans
          soit dep = info.M.i_deprecated <> None dans
          bs b "<div class=\"info\">\n";
          si dep alors bs b "<span class=\"deprecated\">";
          (
           filtre info.M.i_desc avec
             None -> ()
           | Some d quand d = [Odoc_info.Raw ""] -> ()
           | Some d ->
               self#html_of_text b
                 (Odoc_info.text_no_title_no_list
                    (Odoc_info.first_sentence_of_text d));
               bs b "\n"
          );
          si dep alors bs b "</span>";
          bs b "</div>\n"

  fin



soit opt = Odoc_info.apply_opt

soit print_concat b sep f =
  soit rec iter = fonction
      [] -> ()
    | [c] -> f c
    | c :: q ->
        f c;
        bs b sep;
        iter q
  dans
  iter

soit newline_to_indented_br s =
  soit len = String.length s dans
  soit b = Buffer.create len dans
  pour i = 0 à len - 1 faire
    filtre s.[i] avec
      '\n' -> Buffer.add_string b "<br>     "
    | c -> Buffer.add_char b c
  fait;
  Buffer.contents b

module Generator =
  struct
(** This class is used to create objects which can generate a simple html documentation. *)
classe html =
  objet (self)
    hérite text
    hérite info

    val modifiable doctype =
      "<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.01 Transitional//EN\">\n"
    méthode character_encoding () =
      Printf.sprintf
        "<meta content=\"text/html; charset=%s\" http-equiv=\"Content-Type\">\n"
        !charset

    (** The default style options. *)
    val modifiable default_style_options =
      [ ".keyword { font-weight : bold ; color : Red }" ;
        ".keywordsign { color : #C04600 }" ;
        ".superscript { font-size : 4 }" ;
        ".subscript { font-size : 4 }" ;
        ".comment { color : Green }" ;
        ".constructor { color : Blue }" ;
        ".type { color : #5C6585 }" ;
        ".string { color : Maroon }" ;
        ".warning { color : Red ; font-weight : bold }" ;
        ".info { margin-left : 3em; margin-right: 3em }" ;
        ".param_info { margin-top: 4px; margin-left : 3em; margin-right : 3em }" ;
        ".code { color : #465F91 ; }" ;
        ".typetable { border-style : hidden }" ;
        ".paramstable { border-style : hidden ; padding: 5pt 5pt}" ;
        "tr { background-color : White }" ;
        "td.typefieldcomment { background-color : #FFFFFF ; font-size: smaller ;}" ;
        "div.sig_block {margin-left: 2em}" ;
        "*:target { background: yellow; }" ;

        "body {font: 13px sans-serif; color: black; text-align: left; padding: 5px; margin: 0}";

        "h1 { font-size : 20pt ; text-align: center; }" ;

        "h2 { font-size : 20pt ; border: 1px solid #000000; "^
        "margin-top: 5px; margin-bottom: 2px;"^
        "text-align: center; background-color: #90BDFF ;"^
        "padding: 2px; }" ;

        "h3 { font-size : 20pt ; border: 1px solid #000000; "^
        "margin-top: 5px; margin-bottom: 2px;"^
        "text-align: center; background-color: #90DDFF ;"^
        "padding: 2px; }" ;

        "h4 { font-size : 20pt ; border: 1px solid #000000; "^
        "margin-top: 5px; margin-bottom: 2px;"^
        "text-align: center; background-color: #90EDFF ;"^
        "padding: 2px; }" ;

        "h5 { font-size : 20pt ; border: 1px solid #000000; "^
        "margin-top: 5px; margin-bottom: 2px;"^
        "text-align: center; background-color: #90FDFF ;"^
        "padding: 2px; }" ;

        "h6 { font-size : 20pt ; border: 1px solid #000000; "^
        "margin-top: 5px; margin-bottom: 2px;"^
        "text-align: center; background-color: #90BDFF ; "^
        "padding: 2px; }" ;

        "div.h7 { font-size : 20pt ; border: 1px solid #000000; "^
        "margin-top: 5px; margin-bottom: 2px;"^
        "text-align: center; background-color: #E0FFFF ; "^
        "padding: 2px; }" ;

        "div.h8 { font-size : 20pt ; border: 1px solid #000000; "^
        "margin-top: 5px; margin-bottom: 2px;"^
        "text-align: center; background-color: #F0FFFF ; "^
        "padding: 2px; }" ;

        "div.h9 { font-size : 20pt ; border: 1px solid #000000; "^
        "margin-top: 5px; margin-bottom: 2px;"^
        "text-align: center; background-color: #FFFFFF ; "^
        "padding: 2px; }" ;

        "a {color: #416DFF; text-decoration: none}";
        "a:hover {background-color: #ddd; text-decoration: underline}";
        "pre { margin-bottom: 4px; font-family: monospace; }" ;
        "pre.verbatim, pre.codepre { }";

        ".indextable {border: 1px #ddd solid; border-collapse: collapse}";
        ".indextable td, .indextable th {border: 1px #ddd solid; min-width: 80px}";
        ".indextable td.module {background-color: #eee ;  padding-left: 2px; padding-right: 2px}";
        ".indextable td.module a {color: 4E6272; text-decoration: none; display: block; width: 100%}";
        ".indextable td.module a:hover {text-decoration: underline; background-color: transparent}";
        ".deprecated {color: #888; font-style: italic}" ;

        ".indextable tr td div.info { margin-left: 2px; margin-right: 2px }" ;

        "ul.indexlist { margin-left: 0; padding-left: 0;}";
        "ul.indexlist li { list-style-type: none ; margin-left: 0; padding-left: 0; }";
      ]

    (** The style file for all pages. *)
    val modifiable style_file = "style.css"

    (** The code to import the style. Initialized in [init_style]. *)
    val modifiable style = ""

    (** The known types names.
       Used to know if we must create a link to a type
       when printing a type. *)
    val modifiable known_types_names = StringSet.empty

    (** The known class and class type names.
       Used to know if we must create a link to a class
       or class type or not when printing a type. *)
    val modifiable known_classes_names = StringSet.empty

    (** The known modules and module types names.
       Used to know if we must create a link to a type or not
       when printing a module type. *)
    val modifiable known_modules_names = StringSet.empty

    méthode index_prefix =
      si !Odoc_global.out_file = Odoc_messages.default_out_file alors
        "index"
      sinon
        Filename.basename !Odoc_global.out_file

    (** The main file. *)
    méthode index =
      soit p = self#index_prefix dans
      Printf.sprintf "%s.html" p

    (** The file for the index of values. *)
    méthode index_values = Printf.sprintf "%s_values.html" self#index_prefix
    (** The file for the index of types. *)
    méthode index_types = Printf.sprintf "%s_types.html" self#index_prefix
    (** The file for the index of exceptions. *)
    méthode index_exceptions = Printf.sprintf "%s_exceptions.html" self#index_prefix
    (** The file for the index of attributes. *)
    méthode index_attributes = Printf.sprintf "%s_attributes.html" self#index_prefix
    (** The file for the index of methods. *)
    méthode index_methods = Printf.sprintf "%s_methods.html" self#index_prefix
    (** The file for the index of classes. *)
    méthode index_classes = Printf.sprintf "%s_classes.html" self#index_prefix
    (** The file for the index of class types. *)
    méthode index_class_types = Printf.sprintf "%s_class_types.html" self#index_prefix
    (** The file for the index of modules. *)
    méthode index_modules = Printf.sprintf "%s_modules.html" self#index_prefix
    (** The file for the index of module types. *)
    méthode index_module_types = Printf.sprintf "%s_module_types.html" self#index_prefix


    (** The list of attributes. Filled in the [generate] method. *)
    val modifiable list_attributes = []
    méthode list_attributes = list_attributes
    (** The list of methods. Filled in the [generate] method. *)
    val modifiable list_methods = []
    méthode list_methods = list_methods
    (** The list of values. Filled in the [generate] method. *)
    val modifiable list_values = []
    méthode list_values = list_values
    (** The list of exceptions. Filled in the [generate] method. *)
    val modifiable list_exceptions = []
    méthode list_exceptions = list_exceptions
    (** The list of types. Filled in the [generate] method. *)
    val modifiable list_types = []
    méthode list_types = list_types
    (** The list of modules. Filled in the [generate] method. *)
    val modifiable list_modules = []
    méthode list_modules = list_modules
    (** The list of module types. Filled in the [generate] method. *)
    val modifiable list_module_types = []
    méthode list_module_types = list_module_types
    (** The list of classes. Filled in the [generate] method. *)
    val modifiable list_classes = []
    méthode list_classes = list_classes
    (** The list of class types. Filled in the [generate] method. *)
    val modifiable list_class_types = []
    méthode list_class_types = list_class_types

    (** The header of pages. Must be prepared by the [prepare_header] method.*)
    val modifiable header = fonc b -> fonc ?(nav=None) -> fonc ?(comments=[]) -> fonc _ -> ()

    (** Init the style. *)
    méthode init_style =
      (filtre !css_style avec
        None ->
          soit default_style = String.concat "\n" default_style_options dans
          (
           essaie
             soit file = Filename.concat !Global.target_dir style_file dans
             si Sys.file_exists file alors
               Odoc_info.verbose (Odoc_messages.file_exists_dont_generate file)
             sinon
               (
                soit chanout = open_out file dans
                output_string chanout default_style ;
                flush chanout ;
                close_out chanout;
                Odoc_info.verbose (Odoc_messages.file_generated file)
               )
           avec
             Sys_error s ->
               prerr_endline s ;
               incr Odoc_info.errors ;
          )
      | Some f ->
          style_file <- f
      );
      style <- "<link rel=\"stylesheet\" href=\""^style_file^"\" type=\"text/css\">\n"

    (** Get the title given by the user *)
    méthode title = filtre !Global.title avec None -> "" | Some t -> self#escape t

    (** Get the title given by the user completed with the given subtitle. *)
    méthode inner_title s =
      (filtre self#title avec "" -> "" | t -> t^" : ")^
      (self#escape s)

    (** Get the page header. *)
    méthode print_header b ?nav ?comments title = header b ?nav ?comments title

    (** A function to build the header of pages. *)
    méthode prepare_header module_list =
      soit f b ?(nav=None) ?(comments=[]) t  =
        soit link_if_not_empty l m url =
          filtre l avec
            [] -> ()
          | _ ->
              bp b "<link title=\"%s\" rel=Appendix href=\"%s\">\n" m url
        dans
        bs b "<head>\n";
        bs b style;
        bs b (self#character_encoding ()) ;
        bs b "<link rel=\"Start\" href=\"";
        bs b self#index;
        bs b "\">\n" ;
        (
         filtre nav avec
           None -> ()
         | Some (pre_opt, post_opt, name) ->
             (filtre pre_opt avec
               None -> ()
             | Some name ->
                 bp b "<link rel=\"previous\" href=\"%s\">\n"
                   (fst (Naming.html_files name));
             );
             (filtre post_opt avec
               None -> ()
             | Some name ->
                 bp b "<link rel=\"next\" href=\"%s\">\n"
                   (fst (Naming.html_files name));
             );
             (
              soit father = Name.father name dans
              soit href = si father = "" alors self#index sinon fst (Naming.html_files father) dans
              bp b "<link rel=\"Up\" href=\"%s\">\n" href
             )
        );
        link_if_not_empty self#list_types Odoc_messages.index_of_types self#index_types;
        link_if_not_empty self#list_exceptions Odoc_messages.index_of_exceptions self#index_exceptions;
        link_if_not_empty self#list_values Odoc_messages.index_of_values self#index_values;
        link_if_not_empty self#list_attributes Odoc_messages.index_of_attributes self#index_attributes;
        link_if_not_empty self#list_methods Odoc_messages.index_of_methods self#index_methods;
        link_if_not_empty self#list_classes Odoc_messages.index_of_classes self#index_classes;
        link_if_not_empty self#list_class_types Odoc_messages.index_of_class_types self#index_class_types;
        link_if_not_empty self#list_modules Odoc_messages.index_of_modules self#index_modules;
        link_if_not_empty self#list_module_types Odoc_messages.index_of_module_types self#index_module_types;
        soit print_one m =
          soit html_file = fst (Naming.html_files m.m_name) dans
          bp b "<link title=\"%s\" rel=\"Chapter\" href=\"%s\">"
            m.m_name html_file
        dans
        print_concat b "\n" print_one module_list;
        self#html_sections_links b comments;
        bs b "<title>";
        bs b t ;
        bs b "</title>\n</head>\n"
      dans
      header <- f

    (** Build the html code for the link tags in the header, defining section and
       subsections for the titles found in the given comments.*)
    méthode html_sections_links b comments =
      soit titles = List.flatten (List.map Odoc_info.get_titles_in_text comments) dans
      soit levels =
        soit rec iter acc l =
          filtre l avec
            [] -> acc
          | (n,_,_) :: q ->
              si List.mem n acc
              alors iter acc q
              sinon iter (n::acc) q
        dans
        iter [] titles
      dans
      soit sorted_levels = List.sort compare levels dans
      soit (section_level, subsection_level) =
        filtre sorted_levels avec
          [] -> (None, None)
        | [n] -> (Some n, None)
        | n :: m :: _ -> (Some n, Some m)
      dans
      soit titles_per_level level_opt =
        filtre level_opt avec
          None -> []
        | Some n -> List.filter (fonc (m,_,_) -> m = n) titles
      dans
      soit section_titles = titles_per_level section_level dans
      soit subsection_titles = titles_per_level subsection_level dans
      soit print_lines s_rel titles =
        List.iter
          (fonc (n,lopt,t) ->
            soit s = Odoc_info.string_of_text t dans
            soit label = self#create_title_label (n,lopt,t) dans
            bp b "<link title=\"%s\" rel=\"%s\" href=\"#%s\">\n" s s_rel label
          )
          titles
      dans
      print_lines "Section" section_titles ;
      print_lines "Subsection" subsection_titles


    (** Html code for navigation bar.
       @param pre optional name for optional previous module/class
       @param post optional name for optional next module/class
       @param name name of current module/class *)
    méthode print_navbar b pre post name =
      bs b "<div class=\"navbar\">";
      (
       filtre pre avec
         None -> ()
       | Some name ->
           bp b "<a class=\"pre\" href=\"%s\" title=\"%s\">%s</a>\n"
             (fst (Naming.html_files name))
             name
             Odoc_messages.previous
      );
      bs b "&nbsp;";
      soit father = Name.father name dans
      soit href = si father = "" alors self#index sinon fst (Naming.html_files father) dans
      soit father_name = si father = "" alors "Index" sinon father dans
      bp b "<a class=\"up\" href=\"%s\" title=\"%s\">%s</a>\n" href father_name Odoc_messages.up;
      bs b "&nbsp;";
      (
       filtre post avec
         None -> ()
       | Some name ->
           bp b "<a class=\"post\" href=\"%s\" title=\"%s\">%s</a>\n"
             (fst (Naming.html_files name))
             name
             Odoc_messages.next
      );
      bs b "</div>\n"

    (** Return html code with the given string in the keyword style.*)
    méthode keyword s =
      "<span class=\"keyword\">"^s^"</span>"

    (** Return html code with the given string in the constructor style. *)
    méthode constructor s = "<span class=\"constructor\">"^s^"</span>"

    (** Output the given ocaml code to the given file name. *)
    méthode privée output_code in_title file code =
      essaie
        soit chanout = open_out file dans
        soit b = new_buf () dans
        bs b "<html>";
        self#print_header b (self#inner_title in_title);
        bs b"<body>\n";
        self#html_of_code b code;
        bs b "</body></html>";
        Buffer.output_buffer chanout b;
        close_out chanout
      avec
        Sys_error s ->
          incr Odoc_info.errors ;
          prerr_endline s

    (** Take a string and return the string where fully qualified
       type (or class or class type) idents
       have been replaced by links to the type referenced by the ident.*)
    méthode create_fully_qualified_idents_links m_name s =
      soit f str_t =
        soit match_s = Str.matched_string str_t dans
        soit rel = Name.get_relative m_name match_s dans
        soit s_final = Odoc_info.apply_if_equal
            Odoc_info.use_hidden_modules
            match_s
            rel
        dans
        si StringSet.mem match_s known_types_names alors
           "<a href=\""^(Naming.complete_target Naming.mark_type match_s)^"\">"^
           s_final^
           "</a>"
        sinon
          si StringSet.mem match_s known_classes_names alors
            soit (html_file, _) = Naming.html_files match_s dans
            "<a href=\""^html_file^"\">"^s_final^"</a>"
          sinon
            s_final
      dans
      soit s2 = Str.global_substitute
          (Str.regexp "\\([A-Z]\\([a-zA-Z_'0-9]\\)*\\.\\)+\\([a-z][a-zA-Z_'0-9]*\\)")
          f
          s
      dans
      s2

    (** Take a string and return the string where fully qualified module idents
       have been replaced by links to the module referenced by the ident.*)
    méthode create_fully_qualified_module_idents_links m_name s =
      soit f str_t =
        soit match_s = Str.matched_string str_t dans
        soit rel = Name.get_relative m_name match_s dans
        soit s_final = Odoc_info.apply_if_equal
            Odoc_info.use_hidden_modules
            match_s
            rel
        dans
        si StringSet.mem match_s known_modules_names alors
          soit (html_file, _) = Naming.html_files match_s dans
          "<a href=\""^html_file^"\">"^s_final^"</a>"
        sinon
          s_final
      dans
      soit s2 = Str.global_substitute
          (Str.regexp "\\([A-Z]\\([a-zA-Z_'0-9]\\)*\\.\\)+\\([A-Z][a-zA-Z_'0-9]*\\)")
          f
          s
      dans
      s2

    (** Print html code to display a [Types.type_expr]. *)
    méthode html_of_type_expr b m_name t =
      soit s = Odoc_info.remove_ending_newline (Odoc_info.string_of_type_expr t) dans
      soit s2 = newline_to_indented_br s dans
      bs b "<code class=\"type\">";
      bs b (self#create_fully_qualified_idents_links m_name s2);
      bs b "</code>"

    (** Print html code to display a [Types.type_expr list]. *)
    méthode html_of_type_expr_list ?par b m_name sep l =
      print_DEBUG "html#html_of_type_expr_list";
      soit s = Odoc_info.string_of_type_list ?par sep l dans
      print_DEBUG "html#html_of_type_expr_list: 1";
      soit s2 = newline_to_indented_br s dans
      print_DEBUG "html#html_of_type_expr_list: 2";
      bs b "<code class=\"type\">";
      bs b (self#create_fully_qualified_idents_links m_name s2);
      bs b "</code>"

    (** Print html code to display a [Types.type_expr list] as type parameters
       of a class of class type. *)
    méthode html_of_class_type_param_expr_list b m_name l =
      soit s = Odoc_info.string_of_class_type_param_list l dans
      soit s2 = newline_to_indented_br s dans
      bs b "<code class=\"type\">[";
      bs b (self#create_fully_qualified_idents_links m_name s2);
      bs b "]</code>"

    méthode html_of_class_parameter_list b father c =
      soit s = Odoc_info.string_of_class_params c dans
      soit s = Odoc_info.remove_ending_newline s dans
      soit s2 = newline_to_indented_br s dans
      bs b "<code class=\"type\">";
      bs b (self#create_fully_qualified_idents_links father s2);
      bs b "</code>"

    (** Print html code to display a list of type parameters for the given type.*)
    méthode html_of_type_expr_param_list b m_name t =
      soit s = Odoc_info.string_of_type_param_list t dans
      soit s2 = newline_to_indented_br s dans
      bs b "<code class=\"type\">";
      bs b (self#create_fully_qualified_idents_links m_name s2);
      bs b "</code>"

    (** Print html code to display a [Types.module_type]. *)
    méthode html_of_module_type b ?code m_name t =
      soit s = Odoc_info.remove_ending_newline (Odoc_info.string_of_module_type ?code t) dans
      bs b "<code class=\"type\">";
      bs b (self#create_fully_qualified_module_idents_links m_name s);
      bs b "</code>"

    (** Print html code to display the given module kind. *)
    méthode html_of_module_kind b father ?modu kind =
      filtre kind avec
        Module_struct eles ->
          self#html_of_text b [Code "sig"];
          (
           filtre modu avec
             None ->
               bs b "<div class=\"sig_block\">";
               List.iter (self#html_of_module_element b father) eles;
               bs b "</div>"
           | Some m ->
               soit (html_file, _) = Naming.html_files m.m_name dans
               bp b " <a href=\"%s\">..</a> " html_file
          );
          self#html_of_text b [Code "end"]
      | Module_alias a ->
          bs b "<code class=\"type\">";
          bs b (self#create_fully_qualified_module_idents_links father a.ma_name);
          bs b "</code>"
      | Module_functor (p, k) ->
          si !html_short_functors alors
            bs b " "
          sinon
            bs b "<div class=\"sig_block\">";
          self#html_of_module_parameter b father p;
          (
           filtre k avec
             Module_functor _ -> ()
           | _ quand !html_short_functors ->
               bs b ": "
           | _ -> ()
          );
          self#html_of_module_kind b father ?modu k;
          si not !html_short_functors alors
            bs b "</div>"
      | Module_apply (k1, k2) ->
          (* TODO: l'application n'est pas correcte dans un .mli.
             Que faire ? -> afficher le module_type du typedtree  *)
          self#html_of_module_kind b father k1;
          self#html_of_text b [Code "("];
          self#html_of_module_kind b father k2;
          self#html_of_text b [Code ")"]
      | Module_with (k, s) ->
          (* TODO: modify when Module_with will be more detailed *)
          self#html_of_module_type_kind b father ?modu k;
          bs b "<code class=\"type\"> ";
          bs b (self#create_fully_qualified_module_idents_links father s);
          bs b "</code>"
      | Module_constraint (k, tk) ->
          (* TODO: on affiche quoi ? *)
          self#html_of_module_kind b father ?modu k
      | Module_typeof s ->
          bs b "<code class=\"type\">module type of ";
          bs b (self#create_fully_qualified_module_idents_links father s);
          bs b "</code>"
      | Module_unpack (code, mta) ->
          bs b "<code class=\"type\">";
          début
            filtre mta.mta_module avec
              None ->
                bs b (self#create_fully_qualified_module_idents_links father (self#escape code))
            | Some mt ->
                soit (html_file, _) = Naming.html_files mt.mt_name dans
                bp b " <a href=\"%s\">%s</a> " html_file (self#escape code)
          fin;
          bs b "</code>"


    méthode html_of_module_parameter b father p =
      soit (s_functor,s_arrow) =
        si !html_short_functors alors
          "", ""
        sinon
          "functor ", "-> "
      dans
      self#html_of_text b
        [
          Code (s_functor^"(");
          Code p.mp_name ;
          Code " : ";
        ] ;
      self#html_of_module_type_kind b father p.mp_kind;
      self#html_of_text b [ Code (") "^s_arrow)]

    méthode html_of_module_element b father ele =
      filtre ele avec
        Element_module m ->
          self#html_of_module b ~complete: faux m
      | Element_module_type mt ->
          self#html_of_modtype b ~complete: faux mt
      | Element_included_module im ->
          self#html_of_included_module b im
      | Element_class c ->
          self#html_of_class b ~complete: faux c
      | Element_class_type ct ->
          self#html_of_class_type b ~complete: faux ct
      | Element_value v ->
          self#html_of_value b v
      | Element_exception e ->
          self#html_of_exception b e
      | Element_type t ->
          self#html_of_type b t
      | Element_module_comment text ->
          self#html_of_module_comment b text

    (** Print html code to display the given module type kind. *)
    méthode html_of_module_type_kind b father ?modu ?mt kind =
      filtre kind avec
        Module_type_struct eles ->
          self#html_of_text b [Code "sig"];
          (
           filtre mt avec
             None ->
               (
                filtre modu avec
                  None ->
                    bs b "<div class=\"sig_block\">";
                    List.iter (self#html_of_module_element b father) eles;
                    bs b "</div>"
                | Some m ->
                    soit (html_file, _) = Naming.html_files m.m_name dans
                    bp b " <a href=\"%s\">..</a> " html_file
               )
           | Some mt ->
               soit (html_file, _) = Naming.html_files mt.mt_name dans
               bp b " <a href=\"%s\">..</a> " html_file
          );
          self#html_of_text b [Code "end"]
      | Module_type_functor (p, k) ->
          self#html_of_module_parameter b father p;
          self#html_of_module_type_kind b father ?modu ?mt k
      | Module_type_alias a ->
          bs b "<code class=\"type\">";
          bs b (self#create_fully_qualified_module_idents_links father a.mta_name);
          bs b "</code>"
      | Module_type_with (k, s) ->
          self#html_of_module_type_kind b father ?modu ?mt k;
          bs b "<code class=\"type\"> ";
          bs b (self#create_fully_qualified_module_idents_links father s);
          bs b "</code>"
      | Module_type_typeof s ->
          bs b "<code class=\"type\">module type of ";
          bs b (self#create_fully_qualified_module_idents_links father s);
          bs b "</code>"

    (** Print html code to display the type of a module parameter.. *)
    méthode html_of_module_parameter_type b m_name p =
      filtre p.mp_type avec None -> bs b "<code>()</code>"
      | Some mty -> self#html_of_module_type b m_name ~code: p.mp_type_code mty

    (** Generate a file containing the module type in the given file name. *)
    méthode output_module_type in_title file mtyp =
      soit s = Odoc_info.remove_ending_newline (Odoc_info.string_of_module_type ~complete: vrai mtyp) dans
      self#output_code in_title file s

    (** Generate a file containing the class type in the given file name. *)
    méthode output_class_type in_title file ctyp =
      soit s = Odoc_info.remove_ending_newline (Odoc_info.string_of_class_type ~complete: vrai ctyp) dans
      self#output_code in_title file s

    (** Print html code for a value. *)
    méthode html_of_value b v =
      Odoc_info.reset_type_names ();
      bs b "\n<pre>" ;
      bp b "<span id=\"%s\">" (Naming.value_target v);
      bs b (self#keyword "val");
      bs b " ";
      (
       filtre v.val_code avec
         None -> bs b (self#escape (Name.simple v.val_name))
       | Some c ->
           soit file = Naming.file_code_value_complete_target v dans
           self#output_code v.val_name (Filename.concat !Global.target_dir file) c;
           bp b "<a href=\"%s\">%s</a>" file (self#escape (Name.simple v.val_name))
      );
      bs b "</span>";
      bs b " : ";
      self#html_of_type_expr b (Name.father v.val_name) v.val_type;
      bs b "</pre>";
      self#html_of_info b v.val_info;
      (
       si !with_parameter_list alors
         self#html_of_parameter_list b (Name.father v.val_name) v.val_parameters
       sinon
         self#html_of_described_parameter_list b (Name.father v.val_name) v.val_parameters
      )

    (** Print html code for an exception. *)
    méthode html_of_exception b e =
      Odoc_info.reset_type_names ();
      bs b "\n<pre>";
      bp b "<span id=\"%s\">" (Naming.exception_target e);
      bs b (self#keyword "exception");
      bs b " ";
      bs b (Name.simple e.ex_name);
      bs b "</span>";
      (
       filtre e.ex_args avec
         [] -> ()
       | _ ->
           bs b (" "^(self#keyword "of")^" ");
           self#html_of_type_expr_list
             ~par: faux b (Name.father e.ex_name) " * " e.ex_args
      );
      (
       filtre e.ex_alias avec
         None -> ()
       | Some ea ->
           bs b " = ";
           (
            filtre ea.ea_ex avec
              None -> bs b ea.ea_name
            | Some e ->
                bp b "<a href=\"%s\">%s</a>" (Naming.complete_exception_target e) e.ex_name
           )
      );
      bs b "</pre>\n";
      self#html_of_info b e.ex_info

    (** Print html code for a type. *)
    méthode html_of_type b t =
      Odoc_info.reset_type_names ();
      soit father = Name.father t.ty_name dans
      bs b
        (filtre t.ty_manifest, t.ty_kind avec
          None, Type_abstract -> "\n<pre>"
        | None, Type_variant _
        | None, Type_record _ -> "\n<pre><code>"
        | Some _, Type_abstract -> "\n<pre>"
        | Some _, Type_variant _
        | Some _, Type_record _ -> "\n<pre>"
        );
      bp b "<span id=\"%s\">" (Naming.type_target t);
      bs b ((self#keyword "type")^" ");
      self#html_of_type_expr_param_list b father t;
      (filtre t.ty_parameters avec [] -> () | _ -> bs b " ");
      bs b (Name.simple t.ty_name);
      bs b "</span> ";
      soit priv = t.ty_private = Asttypes.Private dans
      (
       filtre t.ty_manifest avec
         None -> ()
       | Some typ ->
           bs b "= ";
           si priv alors bs b "private ";
           self#html_of_type_expr b father typ;
           bs b " "
      );
      (filtre t.ty_kind avec
        Type_abstract -> bs b "</pre>"
      | Type_variant l ->
          bs b "= ";
          si priv alors bs b "private ";
          bs b
            (
             filtre t.ty_manifest avec
               None -> "</code></pre>"
             | Some _ -> "</pre>"
            );
          bs b "<table class=\"typetable\">\n";
          soit print_one constr =
            bs b "<tr>\n<td align=\"left\" valign=\"top\" >\n";
            bs b "<code>";
            bs b (self#keyword "|");
            bs b "</code></td>\n<td align=\"left\" valign=\"top\" >\n";
            bs b "<code>";
            bp b "<span id=\"%s\">%s</span>"
              (Naming.const_target t constr)
              (self#constructor constr.vc_name);
            (
             filtre constr.vc_args, constr.vc_ret avec
               [], None -> ()
             | l,None ->
                 bs b (" " ^ (self#keyword "of") ^ " ");
                 self#html_of_type_expr_list ~par: faux b father " * " l;
             | [],Some r ->
                 bs b (" " ^ (self#keyword ":") ^ " ");
                 self#html_of_type_expr b father r;
             | l,Some r ->
                 bs b (" " ^ (self#keyword ":") ^ " ");
                 self#html_of_type_expr_list ~par: faux b father " * " l;
                 bs b (" " ^ (self#keyword "->") ^ " ");
                 self#html_of_type_expr b father r;
            );
            bs b "</code></td>\n";
            (
             filtre constr.vc_text avec
               None -> ()
             | Some t ->
                 bs b "<td class=\"typefieldcomment\" align=\"left\" valign=\"top\" >";
                 bs b "<code>";
                 bs b "(*";
                 bs b "</code></td>";
                 bs b "<td class=\"typefieldcomment\" align=\"left\" valign=\"top\" >";
                 self#html_of_info b (Some t);
                 bs b "</td>";
                 bs b "<td class=\"typefieldcomment\" align=\"left\" valign=\"bottom\" >";
                 bs b "<code>";
                 bs b "*)";
                 bs b "</code></td>";
            );
            bs b "\n</tr>"
          dans
          print_concat b "\n" print_one l;
          bs b "</table>\n"

      | Type_record l ->
          bs b "= ";
          si priv alors bs b "private " ;
          bs b "{";
          bs b
            (
             filtre t.ty_manifest avec
               None -> "</code></pre>"
             | Some _ -> "</pre>"
            );
          bs b "<table class=\"typetable\">\n" ;
          soit print_one r =
            bs b "<tr>\n<td align=\"left\" valign=\"top\" >\n";
            bs b "<code>&nbsp;&nbsp;</code>";
            bs b "</td>\n<td align=\"left\" valign=\"top\" >\n";
            bs b "<code>";
            si r.rf_mutable alors bs b (self#keyword "mutable&nbsp;") ;
            bp b "<span id=\"%s\">%s</span>&nbsp;: "
              (Naming.recfield_target t r)
              r.rf_name;
            self#html_of_type_expr b father r.rf_type;
            bs b ";</code></td>\n";
            (
             filtre r.rf_text avec
               None -> ()
             | Some t ->
                 bs b "<td class=\"typefieldcomment\" align=\"left\" valign=\"top\" >";
                 bs b "<code>";
                 bs b "(*";
                 bs b "</code></td>";
                 bs b "<td class=\"typefieldcomment\" align=\"left\" valign=\"top\" >";
                 self#html_of_info b (Some t);
                 bs b "</td><td class=\"typefieldcomment\" align=\"left\" valign=\"bottom\" >";
                 bs b "<code>*)</code></td>";
            );
            bs b "\n</tr>"
          dans
          print_concat b "\n" print_one l;
          bs b "</table>\n}\n"
      );
      bs b "\n";
      self#html_of_info b t.ty_info;
      bs b "\n"

    (** Print html code for a class attribute. *)
    méthode html_of_attribute b a =
      soit module_name = Name.father (Name.father a.att_value.val_name) dans
      bs b "\n<pre>" ;
      bp b "<span id=\"%s\">" (Naming.attribute_target a);
      bs b (self#keyword "val");
      bs b " ";
      (
       si a.att_virtual alors
         bs b ((self#keyword "virtual")^ " ")
       sinon
         ()
      );
      (
       si a.att_mutable alors
         bs b ((self#keyword Odoc_messages.mutab)^ " ")
       sinon
         ()
      );(
       filtre a.att_value.val_code avec
         None -> bs b (Name.simple a.att_value.val_name)
       | Some c ->
           soit file = Naming.file_code_attribute_complete_target a dans
           self#output_code a.att_value.val_name (Filename.concat !Global.target_dir file) c;
           bp b "<a href=\"%s\">%s</a>" file (Name.simple a.att_value.val_name);
      );
      bs b "</span>";
      bs b " : ";
      self#html_of_type_expr b module_name a.att_value.val_type;
      bs b "</pre>";
      self#html_of_info b a.att_value.val_info

    (** Print html code for a class method. *)
    méthode html_of_method b m =
      soit module_name = Name.father (Name.father m.met_value.val_name) dans
      bs b "\n<pre>";
      (* html mark *)
      bp b "<span id=\"%s\">" (Naming.method_target m);
     bs b ((self#keyword "method")^" ");
       si m.met_private alors bs b ((self#keyword "private")^" ");
      si m.met_virtual alors bs b ((self#keyword "virtual")^" ");
      (
       filtre m.met_value.val_code avec
         None -> bs b  (Name.simple m.met_value.val_name)
       | Some c ->
           soit file = Naming.file_code_method_complete_target m dans
           self#output_code m.met_value.val_name (Filename.concat !Global.target_dir file) c;
           bp b "<a href=\"%s\">%s</a>" file (Name.simple m.met_value.val_name);
      );
      bs b "</span>";
      bs b " : ";
      self#html_of_type_expr b module_name m.met_value.val_type;
      bs b "</pre>";
      self#html_of_info b m.met_value.val_info;
      (
       si !with_parameter_list alors
         self#html_of_parameter_list b
           module_name m.met_value.val_parameters
       sinon
         self#html_of_described_parameter_list b
           module_name m.met_value.val_parameters
      )

    (** Print html code for the description of a function parameter. *)
    méthode html_of_parameter_description b p =
      filtre Parameter.names p avec
        [] ->
          ()
      | name :: [] ->
          (
           (* Only one name, no need for label for the description. *)
           filtre Parameter.desc_by_name p name avec
             None -> ()
           | Some t -> self#html_of_text b t
          )
      | l ->
          (*  A list of names, we display those with a description. *)
          soit l2 = List.filter
              (fonc n -> (Parameter.desc_by_name p n) <> None)
              l
          dans
          soit print_one n =
            filtre Parameter.desc_by_name p n avec
              None -> ()
            | Some t ->
                bs b "<code>";
                bs b n;
                bs b "</code> : ";
                self#html_of_text b t
          dans
          print_concat b "<br>\n" print_one l2

    (** Print html code for a list of parameters. *)
    méthode html_of_parameter_list b m_name l =
      filtre l avec
        [] -> ()
      | _ ->
          bs b "<div class=\"param_info\">";
          bs b "<table border=\"0\" cellpadding=\"3\" width=\"100%\">\n";
          bs b "<tr>\n<td align=\"left\" valign=\"top\" width=\"1%\">";
          bs b "<b>";
          bs b Odoc_messages.parameters;
          bs b ": </b></td>\n" ;
          bs b "<td>\n<table class=\"paramstable\">\n";
          soit print_one p =
            bs b "<tr>\n<td align=\"center\" valign=\"top\" width=\"15%\" class=\"code\">\n";
            bs b
              (
               filtre Parameter.complete_name p avec
                 "" -> "?"
               | s -> s
              );
            bs b "</td>\n<td align=\"center\" valign=\"top\">:</td>\n";
            bs b "<td>";
            self#html_of_type_expr b m_name (Parameter.typ p);
            bs b "<br>\n";
            self#html_of_parameter_description b p;
            bs b "\n</tr>\n";
          dans
          List.iter print_one l;
          bs b "</table>\n</td>\n</tr>\n</table></div>\n"

    (** Print html code for the parameters which have a name and description. *)
    méthode html_of_described_parameter_list b m_name l =
      (* get the params which have a name, and at least one name described. *)
      soit l2 = List.filter
          (fonc p ->
            List.exists
              (fonc n -> (Parameter.desc_by_name p n) <> None)
              (Parameter.names p))
          l
      dans
      soit f p =
        bs b "<div class=\"param_info\"><code class=\"code\">";
        bs b (Parameter.complete_name p);
        bs b "</code> : " ;
        self#html_of_parameter_description b p;
        bs b "</div>\n"
      dans
      List.iter f l2

    (** Print html code for a list of module parameters. *)
    méthode html_of_module_parameter_list b m_name l =
      filtre l avec
        [] ->
          ()
      | _ ->
          bs b "<table border=\"0\" cellpadding=\"3\" width=\"100%\">\n";
          bs b "<tr>\n";
          bs b "<td align=\"left\" valign=\"top\" width=\"1%%\"><b>";
          bs b Odoc_messages.parameters ;
          bs b ": </b></td>\n<td>\n";
          bs b "<table class=\"paramstable\">\n";
          List.iter
            (fonc (p, desc_opt) ->
              bs b "<tr>\n";
              bs b "<td align=\"center\" valign=\"top\" width=\"15%\">\n<code>" ;
              bs b p.mp_name;
              bs b "</code></td>\n" ;
              bs b "<td align=\"center\" valign=\"top\">:</td>\n";
              bs b "<td>" ;
              self#html_of_module_parameter_type b m_name p;
              bs b "\n";
              (
               filtre desc_opt avec
                 None -> ()
               | Some t ->
                   bs b "<br>";
                   self#html_of_text b t;
                   bs b "\n</tr>\n" ;
              )
            )
            l;
          bs b "</table>\n</td>\n</tr>\n</table>\n"

    (** Print html code for a module. *)
    méthode html_of_module b ?(info=vrai) ?(complete=vrai) ?(with_link=vrai) m =
      soit (html_file, _) = Naming.html_files m.m_name dans
      soit father = Name.father m.m_name dans
      bs b "\n<pre>";
      bs b ((self#keyword "module")^" ");
      (
       si with_link alors
         bp b "<a href=\"%s\">%s</a>" html_file (Name.simple m.m_name)
       sinon
         bs b (Name.simple m.m_name)
      );
      (
       filtre m.m_kind avec
         Module_functor _ quand !html_short_functors  ->
           ()
       | _ -> bs b ": "
      );
      self#html_of_module_kind b father ~modu: m m.m_kind;
      bs b "</pre>";
      si info alors
        (
         si complete alors
           self#html_of_info ~cls: "module top" ~indent: vrai
         sinon
           self#html_of_info_first_sentence
        ) b m.m_info
      sinon
        ()

    (** Print html code for a module type. *)
    méthode html_of_modtype b ?(info=vrai) ?(complete=vrai) ?(with_link=vrai) mt =
      soit (html_file, _) = Naming.html_files mt.mt_name dans
      soit father = Name.father mt.mt_name dans
      bs b "\n<pre>";
      bs b ((self#keyword "module type")^" ");
      (
       si with_link alors
         bp b "<a href=\"%s\">%s</a>" html_file (Name.simple mt.mt_name)
         sinon
         bs b (Name.simple mt.mt_name)
      );
      (filtre mt.mt_kind avec
        None -> ()
      | Some k ->
          bs b " = ";
          self#html_of_module_type_kind b father ~mt k
      );
      bs b "</pre>";
      si info alors
        (
         si complete alors
           self#html_of_info ~cls: "modtype top" ~indent: vrai
         sinon
           self#html_of_info_first_sentence
        ) b mt.mt_info
      sinon
        ()

    (** Print html code for an included module. *)
    méthode html_of_included_module b im =
      bs b "\n<pre>";
      bs b ((self#keyword "include")^" ");
      (
       filtre im.im_module avec
         None ->
           bs b im.im_name
       | Some mmt ->
           soit (file, name) =
             filtre mmt avec
               Mod m ->
                 soit (html_file, _) = Naming.html_files m.m_name dans
                 (html_file, m.m_name)
             | Modtype mt ->
                 soit (html_file, _) = Naming.html_files mt.mt_name dans
                 (html_file, mt.mt_name)
           dans
           bp b "<a href=\"%s\">%s</a>" file name
      );
      bs b "</pre>\n";
      self#html_of_info b im.im_info

    méthode html_of_class_element b element =
      filtre element avec
        Class_attribute a ->
          self#html_of_attribute b a
      | Class_method m ->
          self#html_of_method b m
      | Class_comment t ->
          self#html_of_class_comment b t

    méthode html_of_class_kind b father ?cl kind =
      filtre kind avec
        Class_structure (inh, eles) ->
          self#html_of_text b [Code "object"];
          (
           filtre cl avec
             None ->
               bs b "\n";
               (
                filtre inh avec
                  [] -> ()
                | _ ->
                    self#generate_inheritance_info b inh
               );
               List.iter (self#html_of_class_element b) eles;
           | Some cl ->
               soit (html_file, _) = Naming.html_files cl.cl_name dans
               bp b " <a href=\"%s\">..</a> " html_file
          );
          self#html_of_text b [Code "end"]

      | Class_apply capp ->
          (* TODO: display final type from typedtree *)
          self#html_of_text b [Raw "class application not handled yet"]

      | Class_constr cco ->
          (
           filtre cco.cco_type_parameters avec
             [] -> ()
           | l ->
               self#html_of_class_type_param_expr_list b father l;
               bs b " "
          );
          bs b "<code class=\"type\">";
          bs b (self#create_fully_qualified_idents_links father cco.cco_name);
          bs b "</code>"

      | Class_constraint (ck, ctk) ->
          self#html_of_text b [Code "( "] ;
          self#html_of_class_kind b father ck;
          self#html_of_text b [Code " : "] ;
          self#html_of_class_type_kind b father ctk;
          self#html_of_text b [Code " )"]

    méthode html_of_class_type_kind b father ?ct kind =
      filtre kind avec
        Class_type cta ->
          (
           filtre cta.cta_type_parameters avec
             [] -> ()
           | l ->
               self#html_of_class_type_param_expr_list b father l;
               bs b " "
          );
          bs b "<code class=\"type\">";
          bs b (self#create_fully_qualified_idents_links father cta.cta_name);
          bs b "</code>"

      | Class_signature (inh, eles) ->
          self#html_of_text b [Code "object"];
          (
           filtre ct avec
             None ->
               bs b "\n";
               (
                filtre inh avec
                  [] -> ()
                | _ -> self#generate_inheritance_info b inh
               );
               List.iter (self#html_of_class_element b) eles
           | Some ct ->
               soit (html_file, _) = Naming.html_files ct.clt_name dans
               bp b " <a href=\"%s\">..</a> " html_file
          );
          self#html_of_text b [Code "end"]

    (** Print html code for a class. *)
    méthode html_of_class b ?(complete=vrai) ?(with_link=vrai) c =
      soit father = Name.father c.cl_name dans
      Odoc_info.reset_type_names ();
      soit (html_file, _) = Naming.html_files c.cl_name dans
      bs b "\n<pre>";
      (* we add a html id, the same as for a type so we can
         go directly here when the class name is used as a type name *)
      bp b "<span name=\"%s\">"
        (Naming.type_target
           { ty_name = c.cl_name ;
             ty_info = None ; ty_parameters = [] ;
             ty_kind = Type_abstract ; ty_private = Asttypes.Public; ty_manifest = None ;
             ty_loc = Odoc_info.dummy_loc ;
             ty_code = None ;
           }
        );
      bs b ((self#keyword "class")^" ");
      print_DEBUG "html#html_of_class : virtual or not" ;
      si c.cl_virtual alors bs b ((self#keyword "virtual")^" ");
      (
       filtre c.cl_type_parameters avec
         [] -> ()
       | l ->
           self#html_of_class_type_param_expr_list b father l;
           bs b " "
      );
      print_DEBUG "html#html_of_class : with link or not" ;
      (
       si with_link alors
         bp b "<a href=\"%s\">%s</a>" html_file (Name.simple c.cl_name)
       sinon
         bs b (Name.simple c.cl_name)
      );
      bs b "</span>";
      bs b " : " ;
      self#html_of_class_parameter_list b father c ;
      self#html_of_class_kind b father ~cl: c c.cl_kind;
      bs b "</pre>" ;
      print_DEBUG "html#html_of_class : info" ;
      (
       si complete alors
         self#html_of_info ~cls: "class top" ~indent: vrai
       sinon
         self#html_of_info_first_sentence
      ) b c.cl_info

    (** Print html code for a class type. *)
    méthode html_of_class_type b ?(complete=vrai) ?(with_link=vrai) ct =
      Odoc_info.reset_type_names ();
      soit father = Name.father ct.clt_name dans
      soit (html_file, _) = Naming.html_files ct.clt_name dans
      bs b "\n<pre>";
      (* we add a html id, the same as for a type so we can
         go directly here when the class type name is used as a type name *)
      bp b "<span id=\"%s\">"
        (Naming.type_target
           { ty_name = ct.clt_name ;
             ty_info = None ; ty_parameters = [] ;
             ty_kind = Type_abstract ; ty_private = Asttypes.Public; ty_manifest = None ;
             ty_loc = Odoc_info.dummy_loc ;
             ty_code = None ;
           }
        );
      bs b ((self#keyword "class type")^" ");
      si ct.clt_virtual alors bs b ((self#keyword "virtual")^" ");
      (
       filtre ct.clt_type_parameters avec
        [] -> ()
      | l ->
          self#html_of_class_type_param_expr_list b father l;
          bs b " "
      );

      si with_link alors
        bp b "<a href=\"%s\">%s</a>" html_file (Name.simple ct.clt_name)
      sinon
        bs b (Name.simple ct.clt_name);

      bs b "</span>";
      bs b " = ";
      self#html_of_class_type_kind b father ~ct ct.clt_kind;
      bs b "</pre>";
      (
       si complete alors
         self#html_of_info ~cls: "classtype top" ~indent: vrai
       sinon
         self#html_of_info_first_sentence
      ) b ct.clt_info

    (** Return html code to represent a dag, represented as in Odoc_dag2html. *)
    méthode html_of_dag dag =
      soit f n =
        soit (name, cct_opt) = n.Odoc_dag2html.valu dans
        (* if we have a c_opt = Some class then we take its information
           because we are sure the name is complete. *)
        soit (name2, html_file) =
          filtre cct_opt avec
            None -> (name, fst (Naming.html_files name))
          | Some (Cl c) -> (c.cl_name, fst (Naming.html_files c.cl_name))
          | Some (Cltype (ct, _)) -> (ct.clt_name, fst (Naming.html_files ct.clt_name))
        dans
        soit new_v =
          "<table border=1>\n<tr><td>"^
          "<a href=\""^html_file^"\">"^name2^"</a>"^
          "</td></tr>\n</table>\n"
        dans
        { n avec Odoc_dag2html.valu = new_v }
      dans
      soit a = Array.map f dag.Odoc_dag2html.dag dans
      Odoc_dag2html.html_of_dag { Odoc_dag2html.dag = a }

    (** Print html code for a module comment.*)
    méthode html_of_module_comment b text =
      bs b "<br>\n";
      self#html_of_text b text;
      bs b "<br>\n"

    (** Print html code for a class comment.*)
    méthode html_of_class_comment b text =
      (* Add some style if there is no style for the first part of the text. *)
      soit text2 =
        filtre text avec
        | (Odoc_info.Raw s) :: q ->
            (Odoc_info.Title (2, None, [Odoc_info.Raw s])) :: q
        | _ -> text
      dans
      self#html_of_text b text2

    (** Generate html code for the given list of inherited classes.*)
    méthode generate_inheritance_info b inher_l =
      soit f inh =
        filtre inh.ic_class avec
          None -> (* we can't make the link. *)
            (Odoc_info.Code inh.ic_name) ::
            (filtre inh.ic_text avec
              None -> []
            | Some t -> (Odoc_info.Raw "    ") :: t)
        | Some cct ->
            (* we can create the link. *)
            soit real_name = (* even if it should be the same *)
              filtre cct avec
                Cl c -> c.cl_name
              | Cltype (ct, _) -> ct.clt_name
            dans
            soit (class_file, _) = Naming.html_files real_name dans
            (Odoc_info.Link (class_file, [Odoc_info.Code real_name])) ::
            (filtre inh.ic_text avec
              None -> []
            | Some t -> (Odoc_info.Raw "    ") :: t)
      dans
      soit text = [
        Odoc_info.Bold [Odoc_info.Raw Odoc_messages.inherits] ;
        Odoc_info.List (List.map f inher_l)
      ]
      dans
      self#html_of_text b text

    (** Generate html code for the inherited classes of the given class. *)
    méthode generate_class_inheritance_info b cl =
      soit rec iter_kind k =
        filtre k avec
          Class_structure ([], _) ->
            ()
        | Class_structure (l, _) ->
            self#generate_inheritance_info b l
        | Class_constraint (k, ct) ->
            iter_kind k
        | Class_apply _
        | Class_constr _ ->
            ()
      dans
      iter_kind cl.cl_kind

    (** Generate html code for the inherited classes of the given class type. *)
    méthode generate_class_type_inheritance_info b clt =
      filtre clt.clt_kind avec
        Class_signature ([], _) ->
          ()
      | Class_signature (l, _) ->
          self#generate_inheritance_info b l
      | Class_type _ ->
          ()

    (** A method to create index files. *)
    méthode generate_elements_index :
        'a.
        'a list ->
          ('a -> Odoc_info.Name.t) ->
            ('a -> Odoc_info.info option) ->
              ('a -> string) -> string -> string -> unit =
    fonc elements name info target title simple_file ->
      essaie
        soit chanout = open_out (Filename.concat !Global.target_dir simple_file) dans
        soit b = new_buf () dans
        bs b "<html>\n";
        self#print_header b (self#inner_title title);
        bs b "<body>\n";
        self#print_navbar b None None "";
        bs b "<h1>";
        bs b title;
        bs b "</h1>\n" ;

        soit sorted_elements = List.sort
            (fonc e1 e2 -> compare (Name.simple (name e1)) (Name.simple (name e2)))
            elements
        dans
        soit groups = Odoc_info.create_index_lists sorted_elements (fonc e -> Name.simple (name e)) dans
        soit f_ele e =
          soit simple_name = Name.simple (name e) dans
          soit father_name = Name.father (name e) dans
          bp b "<tr><td><a href=\"%s\">%s</a> " (target e) (self#escape simple_name);
          si simple_name <> father_name && father_name <> "" alors
            bp b "[<a href=\"%s\">%s</a>]" (fst (Naming.html_files father_name)) father_name;
          bs b "</td>\n<td>";
          self#html_of_info_first_sentence b (info e);
          bs b "</td></tr>\n";
        dans
        soit f_group l =
          filtre l avec
            [] -> ()
          | e :: _ ->
              soit s =
                filtre (Char.uppercase (Name.simple (name e)).[0]) avec
                  'A'..'Z' tel c -> String.make 1 c
                | _ -> ""
              dans
              bs b "<tr><td align=\"left\"><br>";
              bs b s ;
              bs b "</td></tr>\n" ;
              List.iter f_ele l
        dans
        bs b "<table>\n";
        List.iter f_group groups ;
        bs b "</table>\n" ;
        bs b "</body>\n</html>";
        Buffer.output_buffer chanout b;
        close_out chanout
      avec
        Sys_error s ->
          raise (Failure s)

    (** A method to generate a list of module/class files. *)
    méthode generate_elements :
        'a. ('a option -> 'a option -> 'a -> unit) -> 'a list -> unit =
      fonc f_generate l ->
        soit rec iter pre_opt = fonction
            [] -> ()
          | ele :: [] -> f_generate pre_opt None ele
          | ele1 :: ele2 :: q ->
              f_generate pre_opt (Some ele2) ele1 ;
              iter (Some ele1) (ele2 :: q)
        dans
        iter None l

    (** Generate the code of the html page for the given class.*)
    méthode generate_for_class pre post cl =
      Odoc_info.reset_type_names ();
      soit (html_file, _) = Naming.html_files cl.cl_name dans
      soit type_file = Naming.file_type_class_complete_target cl.cl_name dans
      essaie
        soit chanout = open_out (Filename.concat !Global.target_dir html_file) dans
        soit b = new_buf () dans
        soit pre_name = opt (fonc c -> c.cl_name) pre dans
        soit post_name = opt (fonc c -> c.cl_name) post dans
        bs b doctype ;
        bs b "<html>\n";
        self#print_header b
          ~nav: (Some (pre_name, post_name, cl.cl_name))
          ~comments: (Class.class_comments cl)
          (self#inner_title cl.cl_name);
        bs b "<body>\n";
        self#print_navbar b pre_name post_name cl.cl_name;
        bs b "<h1>";
        bs b (Odoc_messages.clas^" ");
        si cl.cl_virtual alors bs b "virtual " ;
        bp b "<a href=\"%s\">%s</a>" type_file cl.cl_name;
        bs b "</h1>\n";
        self#html_of_class b ~with_link: faux cl;
        (* parameters *)
        self#html_of_described_parameter_list b
          (Name.father cl.cl_name) cl.cl_parameters;
        (* class inheritance *)
        self#generate_class_inheritance_info b cl;
        (* a horizontal line *)
        bs b "<hr width=\"100%\">\n";
        (* the various elements *)
        List.iter (self#html_of_class_element b)
          (Class.class_elements ~trans:faux cl);
        bs b "</body></html>";
        Buffer.output_buffer chanout b;
        close_out chanout;

        (* generate the file with the complete class type *)
        self#output_class_type
          cl.cl_name
          (Filename.concat !Global.target_dir type_file)
          cl.cl_type
      avec
        Sys_error s ->
          raise (Failure s)

    (** Generate the code of the html page for the given class type.*)
    méthode generate_for_class_type pre post clt =
      Odoc_info.reset_type_names ();
      soit (html_file, _) = Naming.html_files clt.clt_name dans
      soit type_file = Naming.file_type_class_complete_target clt.clt_name dans
      essaie
        soit chanout = open_out (Filename.concat !Global.target_dir html_file) dans
        soit b = new_buf () dans
        soit pre_name = opt (fonc ct -> ct.clt_name) pre dans
        soit post_name = opt (fonc ct -> ct.clt_name) post dans
        bs b doctype ;
        bs b "<html>\n";
        self#print_header b
          ~nav: (Some (pre_name, post_name, clt.clt_name))
          ~comments: (Class.class_type_comments clt)
          (self#inner_title clt.clt_name);

        bs b "<body>\n";
        self#print_navbar b pre_name post_name clt.clt_name;
        bs b "<h1>";
        bs b (Odoc_messages.class_type^" ");
        si clt.clt_virtual alors bs b "virtual ";
        bp b "<a href=\"%s\">%s</a>" type_file clt.clt_name;
        bs b "</h1>\n";
        self#html_of_class_type b ~with_link: faux clt;

        (* class inheritance *)
        self#generate_class_type_inheritance_info b clt;
        (* a horizontal line *)
        bs b "<hr width=\"100%\">\n";
        (* the various elements *)
        List.iter (self#html_of_class_element b)
          (Class.class_type_elements ~trans: faux clt);
        bs b "</body></html>";
        Buffer.output_buffer chanout b;
        close_out chanout;

        (* generate the file with the complete class type *)
        self#output_class_type
          clt.clt_name
          (Filename.concat !Global.target_dir type_file)
          clt.clt_type
      avec
        Sys_error s ->
          raise (Failure s)

    (** Generate the html file for the given module type.
       @raise Failure if an error occurs.*)
    méthode generate_for_module_type pre post mt =
      essaie
        soit (html_file, _) = Naming.html_files mt.mt_name dans
        soit type_file = Naming.file_type_module_complete_target mt.mt_name dans
        soit chanout = open_out (Filename.concat !Global.target_dir html_file) dans
        soit b = new_buf () dans
        soit pre_name = opt (fonc mt -> mt.mt_name) pre dans
        soit post_name = opt (fonc mt -> mt.mt_name) post dans
        bs b doctype ;
        bs b "<html>\n";
        self#print_header b
          ~nav: (Some (pre_name, post_name, mt.mt_name))
          ~comments: (Module.module_type_comments mt)
          (self#inner_title mt.mt_name);
        bs b "<body>\n";
        self#print_navbar b pre_name post_name mt.mt_name;
        bp b "<h1>";
        bs b (Odoc_messages.module_type^" ");
        (
         filtre mt.mt_type avec
           Some _ -> bp b "<a href=\"%s\">%s</a>" type_file mt.mt_name
         | None-> bs b mt.mt_name
        );
        bs b "</h1>\n" ;
        self#html_of_modtype b ~with_link: faux mt;

        (* parameters for functors *)
        self#html_of_module_parameter_list b
          (Name.father mt.mt_name)
          (Module.module_type_parameters mt);
        (* a horizontal line *)
        bs b "<hr width=\"100%\">\n";
        (* module elements *)
        List.iter
          (self#html_of_module_element b (Name.father mt.mt_name))
          (Module.module_type_elements mt);

        bs b "</body></html>";
        Buffer.output_buffer chanout b;
        close_out chanout;

        (* generate html files for submodules *)
        self#generate_elements self#generate_for_module (Module.module_type_modules mt);
        (* generate html files for module types *)
        self#generate_elements self#generate_for_module_type (Module.module_type_module_types mt);
        (* generate html files for classes *)
        self#generate_elements self#generate_for_class (Module.module_type_classes mt);
        (* generate html files for class types *)
        self#generate_elements self#generate_for_class_type (Module.module_type_class_types mt);

        (* generate the file with the complete module type *)
        (
         filtre mt.mt_type avec
           None -> ()
         | Some mty ->
             self#output_module_type
               mt.mt_name
               (Filename.concat !Global.target_dir type_file)
               mty
        )
      avec
        Sys_error s ->
          raise (Failure s)

    (** Generate the html file for the given module.
       @raise Failure if an error occurs.*)
    méthode generate_for_module pre post modu =
      essaie
        Odoc_info.verbose ("Generate for module "^modu.m_name);
        soit (html_file, _) = Naming.html_files modu.m_name dans
        soit type_file = Naming.file_type_module_complete_target modu.m_name dans
        soit code_file = Naming.file_code_module_complete_target modu.m_name dans
        soit chanout = open_out (Filename.concat !Global.target_dir html_file) dans
        soit b = new_buf () dans
        soit pre_name = opt (fonc m -> m.m_name) pre dans
        soit post_name = opt (fonc m -> m.m_name) post dans
        bs b doctype ;
        bs b "<html>\n";
        self#print_header b
          ~nav: (Some (pre_name, post_name, modu.m_name))
          ~comments: (Module.module_comments modu)
          (self#inner_title modu.m_name);
        bs b "<body>\n" ;
        self#print_navbar b pre_name post_name modu.m_name ;
        bs b "<h1>";
        si modu.m_text_only alors
          bs b modu.m_name
        sinon
          (
           bs b
             (
              si Module.module_is_functor modu alors
                Odoc_messages.functo
              sinon
                Odoc_messages.modul
             );
           bp b " <a href=\"%s\">%s</a>" type_file modu.m_name;
           (
            filtre modu.m_code avec
              None -> ()
            | Some _ -> bp b " (<a href=\"%s\">.ml</a>)" code_file
           )
          );
        bs b "</h1>\n";

        si not modu.m_text_only alors self#html_of_module b ~with_link: faux modu;

        (* parameters for functors *)
        self#html_of_module_parameter_list b
          (Name.father modu.m_name)
          (Module.module_parameters modu);

        (* a horizontal line *)
        si not modu.m_text_only alors bs b "<hr width=\"100%\">\n";

        (* module elements *)
        List.iter
          (self#html_of_module_element b (Name.father modu.m_name))
          (Module.module_elements modu);

        bs b "</body></html>";
        Buffer.output_buffer chanout b;
        close_out chanout;

        (* generate html files for submodules *)
        self#generate_elements  self#generate_for_module (Module.module_modules modu);
        (* generate html files for module types *)
        self#generate_elements  self#generate_for_module_type (Module.module_module_types modu);
        (* generate html files for classes *)
        self#generate_elements  self#generate_for_class (Module.module_classes modu);
        (* generate html files for class types *)
        self#generate_elements  self#generate_for_class_type (Module.module_class_types modu);

        (* generate the file with the complete module type *)
        self#output_module_type
          modu.m_name
          (Filename.concat !Global.target_dir type_file)
          modu.m_type;

        filtre modu.m_code avec
          None -> ()
        | Some code ->
            self#output_code
              modu.m_name
              (Filename.concat !Global.target_dir code_file)
              code
      avec
        Sys_error s ->
          raise (Failure s)

    (** Generate the [<index_prefix>.html] file corresponding to the given module list.
       @raise Failure if an error occurs.*)
    méthode generate_index module_list =
      essaie
        soit chanout = open_out (Filename.concat !Global.target_dir self#index) dans
        soit b = new_buf () dans
        soit title = filtre !Global.title avec None -> "" | Some t -> self#escape t dans
        bs b doctype ;
        bs b "<html>\n";
        self#print_header b self#title;
        bs b "<body>\n";

        bs b "<h1>";
        bs b title;
        bs b "</h1>\n" ;
        soit info = Odoc_info.apply_opt
            (Odoc_info.info_of_comment_file module_list)
            !Odoc_info.Global.intro_file
        dans
        (
         filtre info avec
           None ->
             self#html_of_Index_list b;
             bs b "<br/>";
             self#html_of_Module_list b
               (List.map (fonc m -> m.m_name) module_list);
         | Some i -> self#html_of_info ~indent: faux b info
        );
        bs b "</body>\n</html>";
        Buffer.output_buffer chanout b;
        close_out chanout
      avec
        Sys_error s ->
          raise (Failure s)

    (** Generate the values index in the file [index_values.html]. *)
    méthode generate_values_index module_list =
      self#generate_elements_index
        self#list_values
        (fonc v -> v.val_name)
        (fonc v -> v.val_info)
        Naming.complete_value_target
        Odoc_messages.index_of_values
        self#index_values

    (** Generate the exceptions index in the file [index_exceptions.html]. *)
    méthode generate_exceptions_index module_list =
      self#generate_elements_index
        self#list_exceptions
        (fonc e -> e.ex_name)
        (fonc e -> e.ex_info)
        Naming.complete_exception_target
        Odoc_messages.index_of_exceptions
        self#index_exceptions

    (** Generate the types index in the file [index_types.html]. *)
    méthode generate_types_index module_list =
      self#generate_elements_index
        self#list_types
        (fonc t -> t.ty_name)
        (fonc t -> t.ty_info)
        Naming.complete_type_target
        Odoc_messages.index_of_types
        self#index_types

    (** Generate the attributes index in the file [index_attributes.html]. *)
    méthode generate_attributes_index module_list =
      self#generate_elements_index
        self#list_attributes
        (fonc a -> a.att_value.val_name)
        (fonc a -> a.att_value.val_info)
        Naming.complete_attribute_target
        Odoc_messages.index_of_attributes
        self#index_attributes

    (** Generate the methods index in the file [index_methods.html]. *)
    méthode generate_methods_index module_list =
      self#generate_elements_index
        self#list_methods
        (fonc m -> m.met_value.val_name)
        (fonc m -> m.met_value.val_info)
        Naming.complete_method_target
        Odoc_messages.index_of_methods
        self#index_methods

    (** Generate the classes index in the file [index_classes.html]. *)
    méthode generate_classes_index module_list =
      self#generate_elements_index
        self#list_classes
        (fonc c -> c.cl_name)
        (fonc c -> c.cl_info)
        (fonc c -> fst (Naming.html_files c.cl_name))
        Odoc_messages.index_of_classes
        self#index_classes

    (** Generate the class types index in the file [index_class_types.html]. *)
    méthode generate_class_types_index module_list =
      self#generate_elements_index
        self#list_class_types
        (fonc ct -> ct.clt_name)
        (fonc ct -> ct.clt_info)
        (fonc ct -> fst (Naming.html_files ct.clt_name))
        Odoc_messages.index_of_class_types
        self#index_class_types

    (** Generate the modules index in the file [index_modules.html]. *)
    méthode generate_modules_index module_list =
      self#generate_elements_index
        self#list_modules
        (fonc m -> m.m_name)
        (fonc m -> m.m_info)
        (fonc m -> fst (Naming.html_files m.m_name))
        Odoc_messages.index_of_modules
        self#index_modules

    (** Generate the module types index in the file [index_module_types.html]. *)
    méthode generate_module_types_index module_list =
      self#generate_elements_index
        self#list_module_types
        (fonc mt -> mt.mt_name)
        (fonc mt -> mt.mt_info)
        (fonc mt -> fst (Naming.html_files mt.mt_name))
        Odoc_messages.index_of_module_types
        self#index_module_types

    (** Generate all the html files from a module list. The main
       file is [<index_prefix>.html]. *)
    méthode generate module_list =
      (* init the style *)
      self#init_style ;
      (* init the lists of elements *)
      list_values <- Odoc_info.Search.values module_list ;
      list_exceptions <- Odoc_info.Search.exceptions module_list ;
      list_types <- Odoc_info.Search.types module_list ;
      list_attributes <- Odoc_info.Search.attributes module_list ;
      list_methods <- Odoc_info.Search.methods module_list ;
      list_classes <- Odoc_info.Search.classes module_list ;
      list_class_types <- Odoc_info.Search.class_types module_list ;
      list_modules <- Odoc_info.Search.modules module_list ;
      list_module_types <- Odoc_info.Search.module_types module_list ;

      (* prepare the page header *)
      self#prepare_header module_list ;
      (* Get the names of all known types. *)
      soit types = Odoc_info.Search.types module_list dans
      known_types_names <-
        List.fold_left
          (fonc acc t -> StringSet.add t.ty_name acc)
          known_types_names
          types ;
      (* Get the names of all class and class types. *)
      soit classes = Odoc_info.Search.classes module_list dans
      soit class_types = Odoc_info.Search.class_types module_list dans
      known_classes_names <-
        List.fold_left
          (fonc acc c -> StringSet.add c.cl_name acc)
          known_classes_names
          classes ;
      known_classes_names <-
        List.fold_left
          (fonc acc ct -> StringSet.add ct.clt_name acc)
          known_classes_names
          class_types ;
      (* Get the names of all known modules and module types. *)
      soit module_types = Odoc_info.Search.module_types module_list dans
      soit modules = Odoc_info.Search.modules module_list dans
      known_modules_names <-
        List.fold_left
          (fonc acc m -> StringSet.add m.m_name acc)
          known_modules_names
          modules ;
      known_modules_names <-
        List.fold_left
          (fonc acc mt -> StringSet.add mt.mt_name acc)
          known_modules_names
          module_types ;
      (* generate html for each module *)
      si not !index_only alors
        self#generate_elements self#generate_for_module module_list ;

      essaie
        self#generate_index module_list;
        self#generate_values_index module_list ;
        self#generate_exceptions_index module_list ;
        self#generate_types_index module_list ;
        self#generate_attributes_index module_list ;
        self#generate_methods_index module_list ;
        self#generate_classes_index module_list ;
        self#generate_class_types_index module_list ;
        self#generate_modules_index module_list ;
        self#generate_module_types_index module_list ;
      avec
        Failure s ->
          prerr_endline s ;
          incr Odoc_info.errors

    initialisateur
      Odoc_ocamlhtml.html_of_comment :=
        (fonc s ->
          soit b = new_buf () dans
          self#html_of_text b (Odoc_text.Texter.text_of_string s);
          Buffer.contents b
        )
  fin
fin

module type Html_generator = module type de Generator
