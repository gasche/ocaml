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

(** The man pages generator. *)
ouvre Odoc_info
ouvre Parameter
ouvre Value
ouvre Type
ouvre Exception
ouvre Class
ouvre Module
ouvre Search

soit man_suffix = ref Odoc_messages.default_man_suffix
soit man_section = ref Odoc_messages.default_man_section

soit man_mini = ref faux

soit new_buf () = Buffer.create 1024
soit bp = Printf.bprintf
soit bs = Buffer.add_string

soit linebreak = "\n.sp\n";;

(** A class used to get a [text] for info structures. *)
classe virtuelle info =
  objet (self)
    (** The list of pairs [(tag, f)] where [f] is a function taking
       the [text] associated to [tag] and returning man code.
       Add a pair here to handle a tag.*)
    val modifiable tag_functions = ([] : (string * (Odoc_info.text -> string)) list)

    (** Return man code for a [text]. *)
    méthode virtuelle man_of_text : Buffer.t -> Odoc_info.text -> unit

    méthode str_man_of_text t =
      soit b = Buffer.create 256 dans
      self#man_of_text b t ;
      Buffer.contents b

    (** Print groff string for an author list. *)
    méthode str_man_of_author_list l =
      filtre l avec
        [] -> ""
      | _ ->
          soit b = Buffer.create 256 dans
          bs b ".B \"";
          bs b Odoc_messages.authors;
          bs b "\"\n:\n";
          bs b (String.concat ", " l);
          bs b "\n";
          (*bs b "\n.sp\n"*)
          Buffer.contents b

    (** Print groff string for the given optional version information.*)
    méthode str_man_of_version_opt v_opt =
      filtre v_opt avec
        None -> ""
      | Some v ->
          soit b = Buffer.create 256 dans
          bs b ".B \"";
          bs b Odoc_messages.version;
          bs b "\"\n:\n";
          bs b v;
          bs b "\n";
          (*".sp\n"*)
          Buffer.contents b

    (** Printf groff string for the \@before information. *)
    méthode str_man_of_before = fonction
      [] -> ""
    | l ->
        soit b = Buffer.create 256 dans
        soit rec iter = fonction
          [] -> ()
        | (v, text) :: q ->
             bp b ".B \"%s" Odoc_messages.before;
             bs b v;
             bs b "\"\n";
             self#man_of_text b text;
             bs b "\n";
             bs b "\n";
             filtre q avec
               [] -> ()
             | _ -> bs b linebreak ; iter q
        dans
        iter l;
        Buffer.contents b

    (** Print groff string for the given optional since information.*)
    méthode str_man_of_since_opt s_opt =
      filtre s_opt avec
        None -> ""
      | Some s ->
          soit b = Buffer.create 256 dans
          bs b ".B \"";
          bs b Odoc_messages.since;
          bs b "\"\n";
          bs b s;
          bs b "\n";(*".sp\n"*)
          Buffer.contents b

    (** Print groff string for the given list of raised exceptions.*)
    méthode str_man_of_raised_exceptions l =
      filtre l avec
        [] -> ""
      | _ ->
          soit b = Buffer.create 256 dans
          soit rec iter = fonction
            [] -> ()
          | (s, t) :: q ->
              bs b ".B \"";
              bs b Odoc_messages.raises;
              bs b (" "^s^"\"\n");
              self#man_of_text b t;
              bs b "\n";
              filtre q avec
                [] -> ()
              | _ -> bs b linebreak; iter q
          dans
          iter l;
          Buffer.contents b

    (** Print groff string for the given "see also" reference. *)
    méthode str_man_of_see (see_ref, t)  =
      soit t_ref =
        filtre see_ref avec
          Odoc_info.See_url s -> [ Odoc_info.Link (s, t) ]
        | Odoc_info.See_file s -> (Odoc_info.Code s) :: (Odoc_info.Raw " ") :: t
        | Odoc_info.See_doc s -> (Odoc_info.Italic [Odoc_info.Raw s]) :: (Odoc_info.Raw " ") :: t
      dans
      self#str_man_of_text t_ref

    (** Print groff string for the given list of "see also" references.*)
    méthode str_man_of_sees l =
      filtre l avec
        [] -> ""
      | _ ->
          soit b = Buffer.create 256 dans
          soit rec iter = fonction
            [] -> ()
          | see :: q ->
              bs b ".B \"";
              bs b Odoc_messages.see_also;
              bs b "\"\n";
              bs b (self#str_man_of_see see);
              bs b "\n";
              filtre q avec
                [] -> ()
              | _ -> bs b linebreak; iter q
          dans
          iter l;
          Buffer.contents b

    (** Print groff string for the given optional return information.*)
    méthode str_man_of_return_opt return_opt =
      filtre return_opt avec
        None -> ""
      | Some s ->
          soit b = Buffer.create 256 dans
          bs b ".B ";
          bs b Odoc_messages.returns;
          bs b "\n";
          self#man_of_text b s;
          bs b "\n";
          Buffer.contents b

    (** Print man code for the given list of custom tagged texts. *)
    méthode str_man_of_custom l =
      List.fold_left
        (fonc acc (tag, text) ->
           essaie
             soit f = List.assoc tag tag_functions dans
             soit buf = Buffer.create 50 dans
             Buffer.add_string buf (f text);
             (Buffer.contents buf) :: acc
          avec
            Not_found ->
              Odoc_info.warning (Odoc_messages.tag_not_handled tag);
              acc
        )
        [] l

    (** Print the groff string to display an optional info structure. *)
    méthode man_of_info ?(margin=0) b info_opt =
        filtre info_opt avec
        None -> ()
      | Some info ->
          soit module M = Odoc_info dans
          soit l =
            (
           filtre info.M.i_deprecated avec
             None -> []
           | Some d ->
               soit b = Buffer.create 256 dans
               bs b ".B \"";
               bs b Odoc_messages.deprecated;
               bs b "\"\n";
               self#man_of_text b d;
               bs b "\n";
               [ Buffer.contents b ]
            ) @
              (
               filtre info.M.i_desc avec
                 None -> []
               | Some d quand d = [Odoc_info.Raw ""] -> []
               | Some d ->
                   [ (self#str_man_of_text d)^"\n" ]
              ) @
              [
                self#str_man_of_author_list info.M.i_authors;
                self#str_man_of_version_opt info.M.i_version;
                self#str_man_of_before info.M.i_before;
                self#str_man_of_since_opt info.M.i_since;
                self#str_man_of_raised_exceptions info.M.i_raised_exceptions;
                self#str_man_of_return_opt info.M.i_return_value;
                self#str_man_of_sees info.M.i_sees;
              ] @
                (self#str_man_of_custom info.M.i_custom)
          dans
          soit l = List.filter ((<>) "") l dans
          Buffer.add_string b (String.concat "\n.sp\n" l)
  fin

module Generator =
struct

(** This class is used to create objects which can generate a simple html documentation. *)
classe man =
  soit re_slash = Str.regexp_string "/" dans
  objet (self)
    hérite info

    (** Get a file name from a complete name. *)
    méthode file_name name =
      soit s = Printf.sprintf "%s.%s" name !man_suffix dans
      Str.global_replace re_slash "slash" s

    (** Escape special sequences of characters in a string. *)
    méthode escape (s : string) =
      soit len = String.length s dans
      soit b = Buffer.create len dans
      pour i = 0 à len - 1 faire
        filtre s.[i] avec
          '\\' -> Buffer.add_string b "\\(rs"
        | '.' -> Buffer.add_string b "\\&."
        | '\'' -> Buffer.add_string b "\\&'"
        | '-' -> Buffer.add_string b "\\-"
        | c -> Buffer.add_char b c
      fait;
      Buffer.contents b

    (** Open a file for output. Add the target directory.*)
    méthode open_out file =
      soit f = Filename.concat !Global.target_dir file dans
      open_out f

    (** Print groff string for a text, without correction of blanks. *)
    méthode privée man_of_text2 b t =
      List.iter (self#man_of_text_element b) t

    (** Print the groff string for a text, with blanks corrected. *)
    méthode man_of_text b t =
      soit b2 = new_buf () dans
      self#man_of_text2 b2 t ;
      soit s = Buffer.contents b2 dans
      soit s2 = Str.global_replace (Str.regexp "\n[ ]*") "\n" s dans
      bs b (Str.global_replace (Str.regexp "\n\n") "\n" s2)

    (** Return the given string without no newlines. *)
    méthode remove_newlines s =
      Str.global_replace (Str.regexp "[ ]*\n[ ]*") " " s

    (** Print the groff string for a text element. *)
    méthode man_of_text_element b te =
      filtre te avec
      | Odoc_info.Raw s -> bs b (self#escape s)
      | Odoc_info.Code s ->
          bs b "\n.B ";
          bs b ((Str.global_replace (Str.regexp "\n") "\n.B " (self#escape s))^"\n")
      | Odoc_info.CodePre s ->
          bs b "\n.B ";
          bs b ((Str.global_replace (Str.regexp "\n") "\n.B " (self#escape s))^"\n")
      | Odoc_info.Verbatim s ->
          bs b (self#escape s)
      | Odoc_info.Bold t
      | Odoc_info.Italic t
      | Odoc_info.Emphasize t
      | Odoc_info.Center t
      | Odoc_info.Left t
      | Odoc_info.Right t ->
          self#man_of_text2 b t
      | Odoc_info.List tl ->
          List.iter
            (fonc t -> bs b "\n.sp\n \\-"; self#man_of_text2 b t; bs b "\n")
            tl;
          bs b "\n"
      | Odoc_info.Enum tl ->
          List.iter
            (fonc t -> bs b "\n.sp\n \\-"; self#man_of_text2 b t; bs b "\n")
            tl;
          bs b "\n"
      | Odoc_info.Newline ->
          bs b "\n.sp\n"
      | Odoc_info.Block t ->
          bs b "\n.sp\n";
          self#man_of_text2 b t;
          bs b "\n.sp\n"
      | Odoc_info.Title (n, l_opt, t) ->
          self#man_of_text2 b [Odoc_info.Code (Odoc_info.string_of_text t)]
      | Odoc_info.Latex _ ->
          (* don't care about LaTeX stuff in HTML. *)
          ()
      | Odoc_info.Link (s, t) ->
          self#man_of_text2 b t
      | Odoc_info.Ref (name, _, _) ->
          self#man_of_text_element b
            (Odoc_info.Code (Odoc_info.use_hidden_modules name))
      | Odoc_info.Superscript t ->
          bs b "^{"; self#man_of_text2 b t
      | Odoc_info.Subscript t ->
          bs b "_{"; self#man_of_text2 b t
      | Odoc_info.Module_list _ ->
          ()
      | Odoc_info.Index_list ->
          ()
      | Odoc_info.Custom (s,t) -> self#man_of_custom_text b s t
      | Odoc_info.Target (target, code) -> self#man_of_Target b ~target ~code

    méthode man_of_custom_text b s t = ()

    méthode man_of_Target b ~target ~code =
      si String.lowercase target = "man" alors bs b code sinon ()

    (** Print groff string to display code. *)
    méthode man_of_code b s = self#man_of_text b [ Code s ]

    (** Take a string and return the string where fully qualified idents
       have been replaced by idents relative to the given module name.*)
    méthode relative_idents m_name s =
      soit f str_t =
        soit match_s = Str.matched_string str_t dans
        Odoc_info.apply_if_equal
          Odoc_info.use_hidden_modules
          match_s
          (Name.get_relative m_name match_s)
      dans
      soit s2 = Str.global_substitute
          (Str.regexp "\\([A-Z]\\([a-zA-Z_'0-9]\\)*\\.\\)+\\([a-z][a-zA-Z_'0-9]*\\)")
          f
          s
      dans
      s2

    (** Print groff string to display a [Types.type_expr].*)
    méthode man_of_type_expr b m_name t =
      soit s = String.concat "\n"
          (Str.split (Str.regexp "\n") (Odoc_print.string_of_type_expr t))
      dans
      soit s2 = Str.global_replace (Str.regexp "\n") "\n.B " s dans
      bs b "\n.B ";
      bs b (self#relative_idents m_name s2);
      bs b "\n"

    (** Print groff string to display a [Types.class_type].*)
    méthode man_of_class_type_expr b m_name t =
      soit s = String.concat "\n"
          (Str.split (Str.regexp "\n") (Odoc_print.string_of_class_type t))
      dans
      soit s2 = Str.global_replace (Str.regexp "\n") "\n.B " s dans
      bs b "\n.B ";
      bs b (self#relative_idents m_name s2);
      bs b "\n"

    (** Print groff string to display a [Types.type_expr list].*)
    méthode man_of_type_expr_list ?par b m_name sep l =
      soit s = Odoc_str.string_of_type_list ?par sep l dans
      soit s2 = Str.global_replace (Str.regexp "\n") "\n.B " s dans
      bs b "\n.B ";
      bs b (self#relative_idents m_name s2);
      bs b "\n"

    (** Print groff string to display the parameters of a type.*)
    méthode man_of_type_expr_param_list b m_name t =
      filtre t.ty_parameters avec
        [] -> ()
      | l ->
          soit s = Odoc_str.string_of_type_param_list t dans
          soit s2 = Str.global_replace (Str.regexp "\n") "\n.B " s dans
          bs b "\n.B ";
          bs b (self#relative_idents m_name s2);
          bs b "\n"

    (** Print groff string to display a [Types.module_type]. *)
    méthode man_of_module_type b m_name t =
      soit s = String.concat "\n"
          (Str.split (Str.regexp "\n") (Odoc_print.string_of_module_type t))
      dans
      soit s2 = Str.global_replace (Str.regexp "\n") "\n.B " s dans
      bs b "\n.B ";
      bs b (self#relative_idents m_name s2);
      bs b "\n"

    (** Print groff string code for a value. *)
    méthode man_of_value b v =
      Odoc_info.reset_type_names () ;
      bs b "\n.I val ";
      bs b (Name.simple v.val_name);
      bs b " \n: ";
      self#man_of_type_expr b (Name.father v.val_name) v.val_type;
      bs b ".sp\n";
      self#man_of_info b v.val_info;
      bs b "\n.sp\n"

    (** Print groff string code for an exception. *)
    méthode man_of_exception b e =
      Odoc_info.reset_type_names () ;
      bs b "\n.I exception ";
      bs b (Name.simple e.ex_name);
      bs b " \n";
      (
       filtre e.ex_args avec
         [] -> ()
       | _ ->
           bs b ".B of ";
           self#man_of_type_expr_list
             ~par: faux
             b (Name.father e.ex_name) " * " e.ex_args
      );
      (
       filtre e.ex_alias avec
         None -> ()
       | Some ea ->
           bs b " = ";
           bs b
             (
              filtre ea.ea_ex avec
                None -> ea.ea_name
              | Some e -> e.ex_name
             )
      );
      bs b "\n.sp\n";
      self#man_of_info b e.ex_info;
      bs b "\n.sp\n"

    (** Print groff string for a type. *)
    méthode man_of_type b t =
      Odoc_info.reset_type_names () ;
      soit father = Name.father t.ty_name dans
      bs b ".I type ";
      self#man_of_type_expr_param_list b father t;
      (
       filtre t.ty_parameters avec
         [] -> ()
       | _ -> bs b ".I "
      );
      bs b (Name.simple t.ty_name);
      bs b " \n";
      soit priv = t.ty_private = Asttypes.Private dans
      (
       filtre t.ty_manifest avec
         None -> ()
       | Some typ ->
           bs b "= ";
           si priv alors bs b "private ";
           self#man_of_type_expr b father typ
      );
      (
       filtre t.ty_kind avec
        Type_abstract -> ()
      | Type_variant l ->
          bs b "=";
          si priv alors bs b " private";
          bs b "\n ";
          List.iter
            (fonc constr ->
              bs b ("| "^constr.vc_name);
              (
               filtre constr.vc_args, constr.vc_text,constr.vc_ret avec
               | [], None, None -> bs b "\n "
               | [], (Some t), None ->
                   bs b "  (*\n";
                   self#man_of_info b (Some t);
                   bs b "*)\n "
               | l, None, None ->
                   bs b "\n.B of ";
                   self#man_of_type_expr_list ~par: faux b father " * " l;
                   bs b " "
               | l, (Some t), None ->
                   bs b "\n.B of ";
                   self#man_of_type_expr_list ~par: faux b father " * " l;
                   bs b ".I \"  \"\n";
                   bs b "(*\n";
                   self#man_of_info b (Some t);
                   bs b "*)\n"
               | [], None, Some r ->
                   bs b "\n.B : ";
                   self#man_of_type_expr b father r;
                   bs b " "
               | [], (Some t), Some r ->
                   bs b "\n.B : ";
                   self#man_of_type_expr b father r;
                   bs b ".I \"  \"\n";
                   bs b "(*\n";
                   self#man_of_info b (Some t);
                   bs b "*)\n "
               | l, None, Some r ->
                   bs b "\n.B : ";
                   self#man_of_type_expr_list ~par: faux b father " * " l;
                   bs b ".B -> ";
                   self#man_of_type_expr b father r;
                   bs b " "
               | l, (Some t), Some r ->
                   bs b "\n.B of ";
                   self#man_of_type_expr_list ~par: faux b father " * " l;
                   bs b ".B -> ";
                   self#man_of_type_expr b father r;
                   bs b ".I \"  \"\n";
                   bs b "(*\n";
                   self#man_of_info b (Some t);
                   bs b "*)\n "
              )
            )
            l
      | Type_record l ->
          bs b "= ";
          si priv alors bs b "private ";
          bs b "{";
          List.iter
            (fonc r ->
              bs b (si r.rf_mutable alors "\n\n.B mutable \n" sinon "\n ");
              bs b (r.rf_name^" : ");
              self#man_of_type_expr b father r.rf_type;
              bs b ";";
              (
               filtre r.rf_text avec
                 None -> ()
               | Some t ->
                   bs b "  (*\n";
                   self#man_of_info b (Some t);
                   bs b "*) "
              );
            )
            l;
          bs b "\n }\n"
      );
      bs b "\n.sp\n";
      self#man_of_info b t.ty_info;
      bs b "\n.sp\n"

    (** Print groff string for a class attribute. *)
    méthode man_of_attribute b a =
      bs b ".I val ";
      si a.att_virtual alors bs b ("virtual ");
      si a.att_mutable alors bs b (Odoc_messages.mutab^" ");
      bs b ((Name.simple a.att_value.val_name)^" : ");
      self#man_of_type_expr b (Name.father a.att_value.val_name) a.att_value.val_type;
      bs b "\n.sp\n";
      self#man_of_info b a.att_value.val_info;
      bs b "\n.sp\n"

    (** Print groff string for a class method. *)
    méthode man_of_method b m =
      bs b ".I method ";
      si m.met_private alors bs b "private ";
      si m.met_virtual alors bs b "virtual ";
      bs b ((Name.simple m.met_value.val_name)^" : ");
      self#man_of_type_expr b
        (Name.father m.met_value.val_name) m.met_value.val_type;
      bs b "\n.sp\n";
      self#man_of_info b m.met_value.val_info;
      bs b "\n.sp\n"

    (** Groff for a list of parameters. *)
    méthode man_of_parameter_list b m_name l =
      filtre l avec
        [] -> ()
      | _ ->
          bs b "\n.B ";
          bs b Odoc_messages.parameters;
          bs b ": \n";
          List.iter
            (fonc p ->
              bs b ".sp\n";
              bs b "\"";
              bs b (Parameter.complete_name p);
              bs b "\"\n";
              self#man_of_type_expr b m_name (Parameter.typ p);
              bs b "\n";
              self#man_of_parameter_description b p;
              bs b "\n"
            )
            l;
          bs b "\n"

    (** Groff for the description of a function parameter. *)
    méthode man_of_parameter_description b p =
      filtre Parameter.names p avec
        [] -> ()
      | name :: [] ->
          (
           (* Only one name, no need for label for the description. *)
           filtre Parameter.desc_by_name p name avec
             None -> ()
           | Some t -> bs b "\n "; self#man_of_text b t
          )
      | l ->
          (*  A list of names, we display those with a description. *)
          List.iter
            (fonc n ->
              filtre Parameter.desc_by_name p n avec
                None -> ()
              | Some t ->
                  self#man_of_code b (n^" : ");
                  self#man_of_text b t
            )
            l

    (** Print groff string for a list of module parameters. *)
    méthode man_of_module_parameter_list b m_name l =
      filtre l avec
        [] -> ()
      | _ ->
          bs b ".B \"";
          bs b Odoc_messages.parameters;
          bs b ":\"\n";
          List.iter
            (fonc (p, desc_opt) ->
              bs b ".sp\n";
              bs b ("\""^p.mp_name^"\"\n");
              Misc.may (self#man_of_module_type b m_name) p.mp_type;
              bs b "\n";
              (
               filtre desc_opt avec
                 None -> ()
               | Some t -> self#man_of_text b t
              );
              bs b "\n"
            )
            l;
          bs b "\n\n"

    (** Print groff string for a class. *)
    méthode man_of_class b c =
      Odoc_info.reset_type_names () ;
      soit father = Name.father c.cl_name dans
      bs b  ".I class ";
      si c.cl_virtual alors bs b "virtual ";
      (
       filtre c.cl_type_parameters avec
         [] -> ()
       | l ->
           bs b (Odoc_str.string_of_class_type_param_list l);
           bs b " "
      );
      bs b (Name.simple c.cl_name);
      bs b " : " ;
      self#man_of_class_type_expr b father c.cl_type;
      bs b "\n.sp\n";
      self#man_of_info b c.cl_info;
      bs b "\n.sp\n"

    (** Print groff string for a class type. *)
    méthode man_of_class_type b ct =
      Odoc_info.reset_type_names () ;
      bs b ".I class type ";
      si ct.clt_virtual alors bs b "virtual " ;
      (
       filtre ct.clt_type_parameters avec
        [] -> ()
      | l ->
          bs b (Odoc_str.string_of_class_type_param_list l);
          bs b " "
      );
      bs b (Name.simple ct.clt_name);
      bs b  " = " ;
      self#man_of_class_type_expr b (Name.father ct.clt_name) ct.clt_type;
      bs b  "\n.sp\n";
      self#man_of_info b ct.clt_info;
      bs b "\n.sp\n"

    (** Print groff string for a module. *)
    méthode man_of_module b m =
      bs b ".I module ";
      bs b (Name.simple m.m_name);
      bs b " : ";
      self#man_of_module_type b (Name.father m.m_name) m.m_type;
      bs b "\n.sp\n";
      self#man_of_info b m.m_info;
      bs b "\n.sp\n"

    (** Print groff string for a module type. *)
    méthode man_of_modtype b mt =
      bs b ".I module type ";
      bs b (Name.simple mt.mt_name);
      bs b " = ";
      (filtre mt.mt_type avec
        None -> ()
      | Some t ->
          self#man_of_module_type b (Name.father mt.mt_name) t
      );
      bs b "\n.sp\n";
      self#man_of_info b mt.mt_info;
      bs b "\n.sp\n"

    (** Print groff string for a module comment.*)
    méthode man_of_module_comment b text =
      bs b "\n.PP\n";
      self#man_of_text b [Code ("=== "^(Odoc_misc.string_of_text text)^" ===")];
      bs b "\n.PP\n"

    (** Print groff string for a class comment.*)
    méthode man_of_class_comment b text =
      bs b "\n.PP\n";
      self#man_of_text b [Code ("=== "^(Odoc_misc.string_of_text text)^" ===")];
      bs b "\n.PP\n"

    (** Print groff string for an included module. *)
    méthode man_of_included_module b m_name im =
      bs b ".I include ";
      (
       filtre im.im_module avec
         None -> bs b im.im_name
       | Some mmt ->
           soit name =
             filtre mmt avec
               Mod m -> m.m_name
             | Modtype mt -> mt.mt_name
           dans
           bs b (self#relative_idents m_name name)
      );
      bs b "\n.sp\n";
      self#man_of_info b im.im_info;
      bs b "\n.sp\n"

    (** Generate the man page for the given class.*)
    méthode generate_for_class cl =
      Odoc_info.reset_type_names () ;
      soit date = Unix.time () dans
      soit file = self#file_name cl.cl_name dans
      essaie
        soit chanout = self#open_out file dans
        soit b = new_buf () dans
        bs b (".TH \""^cl.cl_name^"\" ");
        bs b !man_section ;
        bs b (" "^(Odoc_misc.string_of_date ~hour: faux date)^" ");
        bs b "OCamldoc ";
        bs b ("\""^(filtre !Global.title avec Some t -> t | None -> "")^"\"\n");

        soit abstract =
          filtre cl.cl_info avec
            None | Some { i_desc = None } -> "no description"
          | Some { i_desc = Some t } ->
              soit s = Odoc_info.string_of_text (Odoc_info.first_sentence_of_text t) dans
              self#remove_newlines s
        dans

        bs b ".SH NAME\n";
        bs b (cl.cl_name^" \\- "^abstract^"\n");
        bs b (".SH "^Odoc_messages.clas^"\n");
        bs b (Odoc_messages.clas^"   "^cl.cl_name^"\n");
        bs b (".SH "^Odoc_messages.documentation^"\n");
        bs b ".sp\n";
        self#man_of_class b cl;

        (* parameters *)
        self#man_of_parameter_list b "" cl.cl_parameters;
        (* a large blank *)
        bs b  "\n.sp\n.sp\n";

(*
        (* class inheritance *)
        self#generate_class_inheritance_info chanout cl;
*)
        (* the various elements *)
        List.iter
          (fonc element ->
            filtre element avec
              Class_attribute a ->
                self#man_of_attribute b a
            | Class_method m ->
                self#man_of_method b m
            | Class_comment t ->
                self#man_of_class_comment b t
          )
          (Class.class_elements cl);

        Buffer.output_buffer chanout b;
        close_out chanout
      avec
        Sys_error s ->
          incr Odoc_info.errors ;
          prerr_endline s

    (** Generate the man page for the given class type.*)
    méthode generate_for_class_type ct =
      Odoc_info.reset_type_names () ;
      soit date = Unix.time () dans
      soit file = self#file_name ct.clt_name dans
      essaie
        soit chanout = self#open_out file dans
        soit b = new_buf () dans
        bs b (".TH \""^ct.clt_name^"\" ");
        bs b !man_section ;
        bs b (" "^(Odoc_misc.string_of_date ~hour: faux date)^" ");
        bs b "OCamldoc ";
        bs b ("\""^(filtre !Global.title avec Some t -> t | None -> "")^"\"\n");

        soit abstract =
          filtre ct.clt_info avec
            None | Some { i_desc = None } -> "no description"
          | Some { i_desc = Some t } ->
              soit s = Odoc_info.string_of_text (Odoc_info.first_sentence_of_text t) dans
              self#remove_newlines s
        dans

        bs b ".SH NAME\n";
        bs b (ct.clt_name^" \\- "^abstract^"\n");
        bs b (".SH "^Odoc_messages.class_type^"\n");
        bs b (Odoc_messages.class_type^"   "^ct.clt_name^"\n");
        bs b (".SH "^Odoc_messages.documentation^"\n");
        bs b ".sp\n";

        self#man_of_class_type b ct;

        (* a large blank *)
        bs b "\n.sp\n.sp\n";
(*
        (* class inheritance *)
        self#generate_class_inheritance_info chanout cl;
*)
        (* the various elements *)
        List.iter
          (fonc element ->
            filtre element avec
              Class_attribute a ->
                self#man_of_attribute b a
            | Class_method m ->
                self#man_of_method b m
            | Class_comment t ->
                self#man_of_class_comment b t
          )
          (Class.class_type_elements ct);

        Buffer.output_buffer chanout b;
        close_out chanout
      avec
        Sys_error s ->
          incr Odoc_info.errors ;
          prerr_endline s

    (** Generate the man file for the given module type.
       @raise Failure if an error occurs.*)
    méthode generate_for_module_type mt =
      soit date = Unix.time () dans
      soit file = self#file_name mt.mt_name dans
      essaie
        soit chanout = self#open_out file dans
        soit b = new_buf () dans
        bs b (".TH \""^mt.mt_name^"\" ");
        bs b !man_section ;
        bs b (" "^(Odoc_misc.string_of_date ~hour: faux date)^" ");
        bs b "OCamldoc ";
        bs b ("\""^(filtre !Global.title avec Some t -> t | None -> "")^"\"\n");

        soit abstract =
          filtre mt.mt_info avec
            None | Some { i_desc = None } -> "no description"
          | Some { i_desc = Some t } ->
              soit s = Odoc_info.string_of_text (Odoc_info.first_sentence_of_text t) dans
              self#remove_newlines s
        dans
        bs b ".SH NAME\n";
        bs b (mt.mt_name^" \\- "^abstract^"\n");
        bs b (".SH "^Odoc_messages.module_type^"\n");
        bs b (Odoc_messages.module_type^"   "^mt.mt_name^"\n");
        bs b (".SH "^Odoc_messages.documentation^"\n");
        bs b ".sp\n";
        bs b (Odoc_messages.module_type^"\n");
        bs b (".BI \""^(Name.simple mt.mt_name)^"\"\n");
        bs b " = ";
        (
         filtre mt.mt_type avec
           None -> ()
         | Some t ->
             self#man_of_module_type b (Name.father mt.mt_name) t
        );
        bs b "\n.sp\n";
        self#man_of_info b mt.mt_info;
        bs b "\n.sp\n";

        (* parameters for functors *)
        self#man_of_module_parameter_list b "" (Module.module_type_parameters mt);
        (* a large blank *)
        bs b "\n.sp\n.sp\n";

        (* module elements *)
        List.iter
          (fonc ele ->
            filtre ele avec
              Element_module m ->
                self#man_of_module b m
            | Element_module_type mt ->
                self#man_of_modtype b mt
            | Element_included_module im ->
                self#man_of_included_module b mt.mt_name im
            | Element_class c ->
                self#man_of_class b c
            | Element_class_type ct ->
                self#man_of_class_type b ct
            | Element_value v ->
                self#man_of_value b v
            | Element_exception e ->
                self#man_of_exception b e
            | Element_type t ->
                self#man_of_type b t
            | Element_module_comment text ->
                self#man_of_module_comment b text
          )
          (Module.module_type_elements mt);

        Buffer.output_buffer chanout b;
        close_out chanout

      avec
        Sys_error s ->
          incr Odoc_info.errors ;
          prerr_endline s

    (** Generate the man file for the given module.
       @raise Failure if an error occurs.*)
    méthode generate_for_module m =
      soit date = Unix.time () dans
      soit file = self#file_name m.m_name dans
      essaie
        soit chanout = self#open_out file dans
        soit b = new_buf () dans
        bs b (".TH \""^m.m_name^"\" ");
        bs b !man_section ;
        bs b (" "^(Odoc_misc.string_of_date ~hour: faux date)^" ");
        bs b "OCamldoc ";
        bs b ("\""^(filtre !Global.title avec Some t -> t | None -> "")^"\"\n");

        soit abstract =
          filtre m.m_info avec
            None | Some { i_desc = None } -> "no description"
          | Some { i_desc = Some t } ->
              soit s = Odoc_info.string_of_text (Odoc_info.first_sentence_of_text t) dans
              self#remove_newlines s
        dans

        bs b ".SH NAME\n";
        bs b (m.m_name^" \\- "^abstract^"\n");
        bs b (".SH "^Odoc_messages.modul^"\n");
        bs b (Odoc_messages.modul^"   "^m.m_name^"\n");
        bs b (".SH "^Odoc_messages.documentation^"\n");
        bs b ".sp\n";
        bs b (Odoc_messages.modul^"\n");
        bs b (".BI \""^(Name.simple m.m_name)^"\"\n");
        bs b " : ";
        self#man_of_module_type b (Name.father m.m_name) m.m_type;
        bs b "\n.sp\n";
        self#man_of_info b m.m_info;
        bs b "\n.sp\n";

        (* parameters for functors *)
        self#man_of_module_parameter_list b "" (Module.module_parameters m);
        (* a large blank *)
        bs b "\n.sp\n.sp\n";

        (* module elements *)
        List.iter
          (fonc ele ->
            filtre ele avec
              Element_module m ->
                self#man_of_module b m
            | Element_module_type mt ->
                self#man_of_modtype b mt
            | Element_included_module im ->
                self#man_of_included_module b m.m_name im
            | Element_class c ->
                self#man_of_class b c
            | Element_class_type ct ->
                self#man_of_class_type b ct
            | Element_value v ->
                self#man_of_value b v
            | Element_exception e ->
                self#man_of_exception b e
            | Element_type t ->
                self#man_of_type b t
            | Element_module_comment text ->
                self#man_of_module_comment b text
          )
          (Module.module_elements m);

        Buffer.output_buffer chanout b;
        close_out chanout

      avec
        Sys_error s ->
          raise (Failure s)

    (** Create the groups of elements to generate pages for. *)
    méthode create_groups module_list =
      soit name res_ele =
        filtre res_ele avec
          Res_module m -> m.m_name
        | Res_module_type mt -> mt.mt_name
        | Res_class c -> c.cl_name
        | Res_class_type ct -> ct.clt_name
        | Res_value v -> Name.simple v.val_name
        | Res_type t -> Name.simple t.ty_name
        | Res_exception e -> Name.simple e.ex_name
        | Res_attribute a -> Name.simple a.att_value.val_name
        | Res_method m -> Name.simple m.met_value.val_name
        | Res_section _ -> affirme faux
        | Res_recfield (_,f) -> f.rf_name
        | Res_const (_,f) -> f.vc_name
      dans
      soit all_items_pre = Odoc_info.Search.search_by_name module_list (Str.regexp ".*")  dans
      soit all_items = List.filter
          (fonc r -> filtre r avec Res_section _ -> faux | _ -> vrai)
          all_items_pre
      dans
      soit sorted_items = List.sort (fonc e1 -> fonc e2 -> compare (name e1) (name e2)) all_items dans
      soit rec f acc1 acc2 l =
        filtre l avec
          [] -> acc2 :: acc1
        | h :: q ->
            filtre acc2 avec
              [] -> f acc1 [h] q
            | h2 :: q2 ->
                si (name h) = (name h2) alors
                  si List.mem h acc2 alors
                    f acc1 acc2 q
                  sinon
                    f acc1 (acc2 @ [h]) q
                sinon
                  f (acc2 :: acc1) [h] q
      dans
      f [] [] sorted_items

    (** Generate a man page for a group of elements with the same name.
       A group must not be empty.*)
    méthode generate_for_group l =
     soit name =
       Name.simple
         (
          filtre List.hd l avec
            Res_module m -> m.m_name
          | Res_module_type mt -> mt.mt_name
          | Res_class c -> c.cl_name
          | Res_class_type ct -> ct.clt_name
          | Res_value v -> v.val_name
          | Res_type t -> t.ty_name
          | Res_exception e -> e.ex_name
          | Res_attribute a -> a.att_value.val_name
          | Res_method m -> m.met_value.val_name
          | Res_section (s,_) -> s
          | Res_recfield (_,f) -> f.rf_name
          | Res_const (_,f) -> f.vc_name
         )
     dans
     soit date = Unix.time () dans
      soit file = self#file_name name dans
      essaie
        soit chanout = self#open_out file dans
        soit b = new_buf () dans
        bs b (".TH \""^name^"\" ");
        bs b !man_section ;
        bs b (" "^(Odoc_misc.string_of_date ~hour: faux date)^" ");
        bs b "OCamldoc ";
        bs b ("\""^(filtre !Global.title avec Some t -> t | None -> "")^"\"\n");
        bs b ".SH NAME\n";
        bs b (name^" \\- all "^name^" elements\n\n");

        soit f ele =
          filtre ele avec
            Res_value v ->
              bs b ("\n.SH "^Odoc_messages.modul^" "^(Name.father v.val_name)^"\n");
              self#man_of_value b v
          | Res_type t ->
              bs b ("\n.SH "^Odoc_messages.modul^" "^(Name.father t.ty_name)^"\n");
              self#man_of_type b t
          | Res_exception e ->
              bs b ("\n.SH "^Odoc_messages.modul^" "^(Name.father e.ex_name)^"\n");
              self#man_of_exception b e
          | Res_attribute a ->
              bs b ("\n.SH "^Odoc_messages.clas^" "^(Name.father a.att_value.val_name)^"\n");
              self#man_of_attribute b a
          | Res_method m ->
              bs b ("\n.SH "^Odoc_messages.clas^" "^(Name.father m.met_value.val_name)^"\n");
              self#man_of_method b m
          | Res_class c ->
              bs b ("\n.SH "^Odoc_messages.modul^" "^(Name.father c.cl_name)^"\n");
              self#man_of_class b c
          | Res_class_type ct ->
              bs b ("\n.SH "^Odoc_messages.modul^" "^(Name.father ct.clt_name)^"\n");
              self#man_of_class_type b ct
          | _ ->
              (* normalement on ne peut pas avoir de module ici. *)
              ()
        dans
        List.iter f l;
        Buffer.output_buffer chanout b;
        close_out chanout
      avec
        Sys_error s ->
          incr Odoc_info.errors ;
          prerr_endline s

    (** Generate all the man pages from a module list. *)
    méthode generate module_list =
      soit sorted_module_list = Sort.list (fonc m1 -> fonc m2 -> m1.m_name < m2.m_name) module_list dans
      soit groups = self#create_groups sorted_module_list dans
      soit f group =
        filtre group avec
          [] ->
            ()
        | [Res_module m] -> self#generate_for_module m
        | [Res_module_type mt] -> self#generate_for_module_type mt
        | [Res_class cl] -> self#generate_for_class cl
        | [Res_class_type ct] -> self#generate_for_class_type ct
        | l ->
            si !man_mini alors
              ()
            sinon
              self#generate_for_group l
      dans
      List.iter f groups
  fin
fin

module type Man_generator = module type de Generator
