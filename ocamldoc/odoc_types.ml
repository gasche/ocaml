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

type ref_kind =
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

et text_element =
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

type see_ref =
    See_url de string
  | See_file de string
  | See_doc de string

type see = see_ref * text

type param = (string * text)

type raised_exception = (string * text)

type info = {
    i_desc : text option;
    i_authors : string list;
    i_version : string option;
    i_sees : see list;
    i_since : string option;
    i_before : (string * text) list;
    i_deprecated : text option;
    i_params : param list;
    i_raised_exceptions : raised_exception list;
    i_return_value : text option ;
    i_custom : (string * text) list ;
  }

soit dummy_info = {
  i_desc = None ;
  i_authors = [] ;
  i_version = None ;
  i_sees = [] ;
  i_since = None ;
  i_before = [] ;
  i_deprecated = None ;
  i_params = [] ;
  i_raised_exceptions = [] ;
  i_return_value = None ;
  i_custom = [] ;
}

type location = {
    loc_impl : Location.t option ;
    loc_inter : Location.t option ;
  }

soit dummy_loc = { loc_impl = None ; loc_inter = None }

type merge_option =
  | Merge_description
  | Merge_author
  | Merge_version
  | Merge_see
  | Merge_since
  | Merge_before
  | Merge_deprecated
  | Merge_param
  | Merge_raised_exception
  | Merge_return_value
  | Merge_custom

soit all_merge_options = [
  Merge_description ;
  Merge_author ;
  Merge_version ;
  Merge_see ;
  Merge_since ;
  Merge_before ;
  Merge_deprecated ;
  Merge_param ;
  Merge_raised_exception ;
  Merge_return_value ;
  Merge_custom ;
]

type magic = string

soit magic = Odoc_messages.magic

type 'a dump = Dump de magic * 'a

soit make_dump a = Dump (magic, a)

soit open_dump = fonction
    Dump (m, a) ->
      si m = magic alors a
      sinon raise (Failure Odoc_messages.bad_magic_number)
