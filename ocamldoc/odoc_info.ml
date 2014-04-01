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

(** Interface for analysing documented OCaml source files and to the collected information. *)

type ref_kind = Odoc_types.ref_kind =
    RK_module
  | RK_module_type
  | RK_class
  | RK_class_type
  | RK_value
  | RK_type
  | RK_exception
  | RK_attribute
  | RK_method
  | RK_section de text
  | RK_recfield
  | RK_const

et text_element = Odoc_types.text_element =
  | Raw de string
  | Code de string
  | CodePre de string
  | Verbatim de string
  | Bold de text
  | Italic de text
  | Emphasize de text
  | Center de text
  | Left de text
  | Right de text
  | List de text list
  | Enum de text list
  | Newline
  | Block de text
  | Title de int * string option * text
  | Latex de string
  | Link de string * text
  | Ref de string * ref_kind option * text option
  | Superscript de text
  | Subscript de text
  | Module_list de string list
  | Index_list
  | Custom de string * text
  | Target de string * string

et text = text_element list

exception Text_syntax = Odoc_text.Text_syntax

type see_ref = Odoc_types.see_ref =
    See_url de string
  | See_file de string
  | See_doc de string

type see = see_ref * text

type param = (string * text)

type raised_exception = (string * text)

type info = Odoc_types.info = {
    i_desc : text option;
    i_authors : string list;
    i_version : string option;
    i_sees : see list;
    i_since : string option;
    i_before : (string * text) list ;
    i_deprecated : text option;
    i_params : param list;
    i_raised_exceptions : raised_exception list;
    i_return_value : text option ;
    i_custom : (string * text) list ;
  }

type location = Odoc_types.location = {
    loc_impl : Location.t option ;
    loc_inter : Location.t option ;
  }

soit dummy_loc = { loc_impl = None ; loc_inter = None }

module Name = Odoc_name
module Parameter = Odoc_parameter
module Exception = Odoc_exception
module Type = Odoc_type
module Value = Odoc_value
module Class = Odoc_class
module Module = Odoc_module


soit analyse_files
    ?(merge_options=([] : Odoc_types.merge_option list))
    ?(include_dirs=([] : string list))
    ?(labels=faux)
    ?(sort_modules=faux)
    ?(no_stop=faux)
    ?(init=[])
    files =
  Odoc_global.merge_options := merge_options;
  Odoc_global.include_dirs := include_dirs;
  Odoc_global.classic := not labels;
  Odoc_global.sort_modules := sort_modules;
  Odoc_global.no_stop := no_stop;
  Odoc_analyse.analyse_files ~init: init files

soit dump_modules = Odoc_analyse.dump_modules

soit load_modules = Odoc_analyse.load_modules

soit reset_type_names = Printtyp.reset

soit string_of_variance t (co,cn) = Odoc_str.string_of_variance t (co, cn)

soit string_of_type_expr t = Odoc_print.string_of_type_expr t

soit string_of_class_params = Odoc_str.string_of_class_params

soit string_of_type_list ?par sep type_list = Odoc_str.string_of_type_list ?par sep type_list

soit string_of_type_param_list t = Odoc_str.string_of_type_param_list t

soit string_of_class_type_param_list l = Odoc_str.string_of_class_type_param_list l

soit string_of_module_type = Odoc_print.string_of_module_type

soit string_of_class_type = Odoc_print.string_of_class_type

soit string_of_text t = Odoc_misc.string_of_text t

soit string_of_info i = Odoc_misc.string_of_info i

soit string_of_type t = Odoc_str.string_of_type t

soit string_of_exception e = Odoc_str.string_of_exception e

soit string_of_value v = Odoc_str.string_of_value v

soit string_of_attribute att = Odoc_str.string_of_attribute att

soit string_of_method m = Odoc_str.string_of_method m

soit first_sentence_of_text = Odoc_misc.first_sentence_of_text

soit first_sentence_and_rest_of_text = Odoc_misc.first_sentence_and_rest_of_text

soit text_no_title_no_list = Odoc_misc.text_no_title_no_list

soit text_concat = Odoc_misc.text_concat

soit get_titles_in_text = Odoc_misc.get_titles_in_text

soit create_index_lists = Odoc_misc.create_index_lists

soit remove_ending_newline = Odoc_misc.remove_ending_newline

soit remove_option = Odoc_misc.remove_option

soit is_optional = Odoc_misc.is_optional

soit label_name = Odoc_misc.label_name

soit use_hidden_modules n =
  Odoc_name.hide_given_modules !Odoc_global.hidden_modules n

soit verbose s =
  si !Odoc_global.verbose alors
    (print_string s ; print_newline ())
  sinon
    ()

soit warning s = Odoc_global.pwarning s
soit print_warnings = Odoc_config.print_warnings

soit errors = Odoc_global.errors

soit apply_opt = Odoc_misc.apply_opt

soit apply_if_equal f v1 v2 =
  si v1 = v2 alors
    f v1
  sinon
    v2

soit text_of_string = Odoc_text.Texter.text_of_string

soit text_string_of_text = Odoc_text.Texter.string_of_text


soit escape_arobas s =
  soit len = String.length s dans
  soit b = Buffer.create len dans
  pour i = 0 à len - 1 faire
    filtre s.[i] avec
      '@' -> Buffer.add_string b "\\@"
    | c -> Buffer.add_char b c
  fait;
  Buffer.contents b

soit info_string_of_info i =
  soit b = Buffer.create 256 dans
  soit p = Printf.bprintf dans
  (
   filtre i.i_desc avec
     None -> ()
   | Some t -> p b "%s" (escape_arobas (text_string_of_text t))
  );
  List.iter
    (fonc s -> p b "\n@@author %s" (escape_arobas s))
    i.i_authors;
  (
   filtre i.i_version avec
     None -> ()
   | Some s -> p b "\n@@version %s" (escape_arobas s)
  );
  (
   (* TODO: escape characters ? *)
   soit f_see_ref = fonction
       See_url s -> Printf.sprintf "<%s>" s
     | See_file s -> Printf.sprintf "'%s'" s
     | See_doc s -> Printf.sprintf "\"%s\"" s
   dans
   List.iter
     (fonc (sref, t) ->
       p b "\n@@see %s %s"
         (escape_arobas (f_see_ref sref))
         (escape_arobas (text_string_of_text t))
     )
     i.i_sees
  );
  (
   filtre i.i_since avec
     None -> ()
   | Some s -> p b "\n@@since %s" (escape_arobas s)
  );
  (
   filtre i.i_deprecated avec
     None -> ()
   | Some t ->
       p b "\n@@deprecated %s"
         (escape_arobas (text_string_of_text t))
  );
  List.iter
    (fonc (s, t) ->
      p b "\n@@param %s %s"
        (escape_arobas s)
        (escape_arobas (text_string_of_text t))
    )
    i.i_params;
  List.iter
    (fonc (s, t) ->
      p b "\n@@raise %s %s"
        (escape_arobas s)
        (escape_arobas (text_string_of_text t))
    )
    i.i_raised_exceptions;
  (
   filtre i.i_return_value avec
     None -> ()
   | Some t ->
       p b "\n@@return %s"
         (escape_arobas (text_string_of_text t))
  );
  List.iter
    (fonc (s, t) ->
      p b "\n@@%s %s" s
        (escape_arobas (text_string_of_text t))
    )
    i.i_custom;

  Buffer.contents b

soit info_of_string = Odoc_comments.info_of_string
soit info_of_comment_file = Odoc_comments.info_of_comment_file

module Search =
  struct
    type result_element = Odoc_search.result_element =
          Res_module de Module.t_module
        | Res_module_type de Module.t_module_type
        | Res_class de Class.t_class
        | Res_class_type de Class.t_class_type
        | Res_value de Value.t_value
        | Res_type de Type.t_type
        | Res_exception de Exception.t_exception
        | Res_attribute de Value.t_attribute
        | Res_method de Value.t_method
        | Res_section de string * text
        | Res_recfield de Type.t_type * Type.record_field
        | Res_const de Type.t_type * Type.variant_constructor

    type search_result = result_element list

    soit search_by_name = Odoc_search.Search_by_name.search

    soit values = Odoc_search.values
    soit exceptions = Odoc_search.exceptions
    soit types = Odoc_search.types
    soit attributes = Odoc_search.attributes
    soit methods = Odoc_search.methods
    soit classes = Odoc_search.classes
    soit class_types = Odoc_search.class_types
    soit modules = Odoc_search.modules
    soit module_types = Odoc_search.module_types
  fin

module Scan =
  struct
    classe scanner = Odoc_scan.scanner
  fin

module Dep =
  struct
    soit kernel_deps_of_modules = Odoc_dep.kernel_deps_of_modules
    soit deps_of_types = Odoc_dep.deps_of_types
  fin

module Global = Odoc_global
