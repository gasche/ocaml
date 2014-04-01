(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Hongbo Zhang (University of Pennsylvania)                *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

type space_formatter = (unit, Format.formatter, unit) format
classe printer :
  unit ->
  objet ('b)
    val pipe : bool
    val semi : bool
    méthode binding :
      Format.formatter -> Parsetree.value_binding -> unit
    méthode bindings:
        Format.formatter ->
          Asttypes.rec_flag * Parsetree.value_binding list ->
            unit
    méthode case_list :
      Format.formatter -> Parsetree.case list -> unit
    méthode class_expr : Format.formatter -> Parsetree.class_expr -> unit
    méthode class_field : Format.formatter -> Parsetree.class_field -> unit
    méthode class_params_def :
      Format.formatter -> (string Asttypes.loc * Asttypes.variance) list -> unit
    méthode class_signature :
      Format.formatter -> Parsetree.class_signature -> unit
    méthode class_structure :
      Format.formatter -> Parsetree.class_structure -> unit
    méthode class_type : Format.formatter -> Parsetree.class_type -> unit
    méthode class_type_declaration_list :
      Format.formatter -> Parsetree.class_type_declaration list -> unit
    méthode constant : Format.formatter -> Asttypes.constant -> unit
    méthode constant_string : Format.formatter -> string -> unit
    méthode core_type : Format.formatter -> Parsetree.core_type -> unit
    méthode core_type1 : Format.formatter -> Parsetree.core_type -> unit
    méthode direction_flag :
      Format.formatter -> Asttypes.direction_flag -> unit
    méthode directive_argument :
      Format.formatter -> Parsetree.directive_argument -> unit
    méthode exception_declaration :
      Format.formatter -> Parsetree.constructor_declaration -> unit
    méthode expression : Format.formatter -> Parsetree.expression -> unit
    méthode expression1 : Format.formatter -> Parsetree.expression -> unit
    méthode expression2 : Format.formatter -> Parsetree.expression -> unit
    méthode label_exp :
      Format.formatter ->
      Asttypes.label * Parsetree.expression option * Parsetree.pattern ->
      unit
    méthode label_x_expression_param :
      Format.formatter -> Asttypes.label * Parsetree.expression -> unit
    méthode list :
      ?sep:space_formatter ->
      ?first:space_formatter ->
      ?last:space_formatter ->
      (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a list -> unit
    méthode longident : Format.formatter -> Longident.t -> unit
    méthode longident_loc :
      Format.formatter -> Longident.t Asttypes.loc -> unit
    méthode module_expr : Format.formatter -> Parsetree.module_expr -> unit
    méthode module_type : Format.formatter -> Parsetree.module_type -> unit
    méthode mutable_flag : Format.formatter -> Asttypes.mutable_flag -> unit
    méthode option :
      ?first:space_formatter ->
      ?last:space_formatter ->
      (Format.formatter -> 'a -> unit) ->
      Format.formatter -> 'a option -> unit
    méthode paren :
        ?first:space_formatter -> ?last:space_formatter -> bool ->
          (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a -> unit
    méthode pattern : Format.formatter -> Parsetree.pattern -> unit
    méthode pattern1 : Format.formatter -> Parsetree.pattern -> unit
    méthode payload : Format.formatter -> Parsetree.payload -> unit
    méthode private_flag : Format.formatter -> Asttypes.private_flag -> unit
    méthode rec_flag : Format.formatter -> Asttypes.rec_flag -> unit

    méthode reset : 'b
    méthode reset_semi : 'b
    méthode reset_ifthenelse : 'b
    méthode reset_pipe : 'b

    méthode signature :
      Format.formatter -> Parsetree.signature_item list -> unit
    méthode signature_item :
      Format.formatter -> Parsetree.signature_item -> unit
    méthode simple_expr : Format.formatter -> Parsetree.expression -> unit
    méthode simple_pattern : Format.formatter -> Parsetree.pattern -> unit
    méthode string_quot : Format.formatter -> Asttypes.label -> unit
    méthode structure :
      Format.formatter -> Parsetree.structure_item list -> unit
    méthode structure_item :
      Format.formatter -> Parsetree.structure_item -> unit
    méthode sugar_expr : Format.formatter -> Parsetree.expression -> bool
    méthode toplevel_phrase :
      Format.formatter -> Parsetree.toplevel_phrase -> unit
    méthode type_declaration :
      Format.formatter -> Parsetree.type_declaration -> unit
    méthode type_def_list :
      Format.formatter -> Parsetree.type_declaration list -> unit
    méthode type_param :
      Format.formatter -> string Asttypes.loc option * Asttypes.variance -> unit
    méthode type_var_option :
      Format.formatter -> string Asttypes.loc option -> unit
    méthode type_with_label :
      Format.formatter -> Asttypes.label * Parsetree.core_type -> unit
    méthode tyvar : Format.formatter -> string -> unit
    méthode under_pipe : 'b
    méthode under_semi : 'b
    méthode under_ifthenelse : 'b
    méthode value_description :
      Format.formatter -> Parsetree.value_description -> unit
    méthode virtual_flag : Format.formatter -> Asttypes.virtual_flag -> unit
    méthode attribute : Format.formatter -> Parsetree.attribute -> unit
    méthode attributes : Format.formatter -> Parsetree.attributes -> unit
  fin
val default : printer
val toplevel_phrase : Format.formatter -> Parsetree.toplevel_phrase -> unit
val expression : Format.formatter -> Parsetree.expression -> unit
val string_of_expression : Parsetree.expression -> string
val top_phrase: Format.formatter -> Parsetree.toplevel_phrase -> unit
val core_type: Format.formatter -> Parsetree.core_type -> unit
val pattern: Format.formatter -> Parsetree.pattern -> unit
val signature: Format.formatter -> Parsetree.signature -> unit
val structure: Format.formatter -> Parsetree.structure -> unit
val string_of_structure: Parsetree.structure -> string
