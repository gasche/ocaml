(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Predefined type constructors (with special typing rules in typecore) *)

ouvre Path
ouvre Types
ouvre Btype

soit builtin_idents = ref []

soit wrap create s =
  soit id = create s dans
  builtin_idents := (s, id) :: !builtin_idents;
  id

soit ident_create = wrap Ident.create
soit ident_create_predef_exn = wrap Ident.create_predef_exn

soit ident_int = ident_create "int"
et ident_char = ident_create "char"
et ident_string = ident_create "string"
et ident_float = ident_create "float"
et ident_bool = ident_create "bool"
et ident_unit = ident_create "unit"
et ident_exn = ident_create "exn"
et ident_array = ident_create "array"
et ident_list = ident_create "list"
et ident_format6 = ident_create "format6"
et ident_option = ident_create "option"
et ident_nativeint = ident_create "nativeint"
et ident_int32 = ident_create "int32"
et ident_int64 = ident_create "int64"
et ident_lazy_t = ident_create "lazy_t"

soit path_int = Pident ident_int
et path_char = Pident ident_char
et path_string = Pident ident_string
et path_float = Pident ident_float
et path_bool = Pident ident_bool
et path_unit = Pident ident_unit
et path_exn = Pident ident_exn
et path_array = Pident ident_array
et path_list = Pident ident_list
et path_format6 = Pident ident_format6
et path_option = Pident ident_option
et path_nativeint = Pident ident_nativeint
et path_int32 = Pident ident_int32
et path_int64 = Pident ident_int64
et path_lazy_t = Pident ident_lazy_t

soit type_int = newgenty (Tconstr(path_int, [], ref Mnil))
et type_char = newgenty (Tconstr(path_char, [], ref Mnil))
et type_string = newgenty (Tconstr(path_string, [], ref Mnil))
et type_float = newgenty (Tconstr(path_float, [], ref Mnil))
et type_bool = newgenty (Tconstr(path_bool, [], ref Mnil))
et type_unit = newgenty (Tconstr(path_unit, [], ref Mnil))
et type_exn = newgenty (Tconstr(path_exn, [], ref Mnil))
et type_array t = newgenty (Tconstr(path_array, [t], ref Mnil))
et type_list t = newgenty (Tconstr(path_list, [t], ref Mnil))
et type_option t = newgenty (Tconstr(path_option, [t], ref Mnil))
et type_nativeint = newgenty (Tconstr(path_nativeint, [], ref Mnil))
et type_int32 = newgenty (Tconstr(path_int32, [], ref Mnil))
et type_int64 = newgenty (Tconstr(path_int64, [], ref Mnil))
et type_lazy_t t = newgenty (Tconstr(path_lazy_t, [t], ref Mnil))

soit ident_match_failure = ident_create_predef_exn "Match_failure"
et ident_out_of_memory = ident_create_predef_exn "Out_of_memory"
et ident_invalid_argument = ident_create_predef_exn "Invalid_argument"
et ident_failure = ident_create_predef_exn "Failure"
et ident_not_found = ident_create_predef_exn "Not_found"
et ident_sys_error = ident_create_predef_exn "Sys_error"
et ident_end_of_file = ident_create_predef_exn "End_of_file"
et ident_division_by_zero = ident_create_predef_exn "Division_by_zero"
et ident_stack_overflow = ident_create_predef_exn "Stack_overflow"
et ident_sys_blocked_io = ident_create_predef_exn "Sys_blocked_io"
et ident_assert_failure = ident_create_predef_exn "Assert_failure"
et ident_undefined_recursive_module =
        ident_create_predef_exn "Undefined_recursive_module"

soit path_match_failure = Pident ident_match_failure
et path_assert_failure = Pident ident_assert_failure
et path_undefined_recursive_module = Pident ident_undefined_recursive_module

soit decl_abstr =
  {type_params = [];
   type_arity = 0;
   type_kind = Type_abstract;
   type_loc = Location.none;
   type_private = Asttypes.Public;
   type_manifest = None;
   type_variance = [];
   type_newtype_level = None;
   type_attributes = [];
  }

soit cstr id args =
  {
    cd_id = id;
    cd_args = args;
    cd_res = None;
    cd_loc = Location.none;
    cd_attributes = [];
  }

soit ident_false = ident_create "false"
et ident_true = ident_create "true"
et ident_void = ident_create "()"
et ident_nil = ident_create "[]"
et ident_cons = ident_create "::"
et ident_none = ident_create "None"
et ident_some = ident_create "Some"
soit build_initial_env add_type add_exception empty_env =
  soit decl_bool =
    {decl_abstr avec
     type_kind = Type_variant([cstr ident_false []; cstr ident_true []])}
  et decl_unit =
    {decl_abstr avec
     type_kind = Type_variant([cstr ident_void []])}
  et decl_exn =
    {decl_abstr avec
     type_kind = Type_variant []}
  et decl_array =
    soit tvar = newgenvar() dans
    {decl_abstr avec
     type_params = [tvar];
     type_arity = 1;
     type_variance = [Variance.full]}
  et decl_list =
    soit tvar = newgenvar() dans
    {decl_abstr avec
     type_params = [tvar];
     type_arity = 1;
     type_kind =
     Type_variant([cstr ident_nil []; cstr ident_cons [tvar; type_list tvar]]);
     type_variance = [Variance.covariant]}
  et decl_format6 =
    soit params = List.map (newgenvar ?name:None) [();();();();();()] dans
    {decl_abstr avec
     type_params = params;
     type_arity = 6;
     type_variance = List.map (fonc _ -> Variance.full) params}
  et decl_option =
    soit tvar = newgenvar() dans
    {decl_abstr avec
     type_params = [tvar];
     type_arity = 1;
     type_kind = Type_variant([cstr ident_none []; cstr ident_some [tvar]]);
     type_variance = [Variance.covariant]}
  et decl_lazy_t =
    soit tvar = newgenvar() dans
    {decl_abstr avec
     type_params = [tvar];
     type_arity = 1;
     type_variance = [Variance.covariant]}
  dans

  soit add_exception id l =
    add_exception id
      { exn_args = l; exn_loc = Location.none; exn_attributes = [] }
  dans
  add_exception ident_match_failure
                         [newgenty (Ttuple[type_string; type_int; type_int])] (
  add_exception ident_out_of_memory [] (
  add_exception ident_stack_overflow [] (
  add_exception ident_invalid_argument [type_string] (
  add_exception ident_failure [type_string] (
  add_exception ident_not_found [] (
  add_exception ident_sys_blocked_io [] (
  add_exception ident_sys_error [type_string] (
  add_exception ident_end_of_file [] (
  add_exception ident_division_by_zero [] (
  add_exception ident_assert_failure
                         [newgenty (Ttuple[type_string; type_int; type_int])] (
  add_exception ident_undefined_recursive_module
                         [newgenty (Ttuple[type_string; type_int; type_int])] (
  add_type ident_int64 decl_abstr (
  add_type ident_int32 decl_abstr (
  add_type ident_nativeint decl_abstr (
  add_type ident_lazy_t decl_lazy_t (
  add_type ident_option decl_option (
  add_type ident_format6 decl_format6 (
  add_type ident_list decl_list (
  add_type ident_array decl_array (
  add_type ident_exn decl_exn (
  add_type ident_unit decl_unit (
  add_type ident_bool decl_bool (
  add_type ident_float decl_abstr (
  add_type ident_string decl_abstr (
  add_type ident_char decl_abstr (
  add_type ident_int decl_abstr (
    empty_env)))))))))))))))))))))))))))

soit builtin_values =
  List.map (fonc id -> Ident.make_global id; (Ident.name id, id))
      [ident_match_failure; ident_out_of_memory; ident_stack_overflow;
       ident_invalid_argument;
       ident_failure; ident_not_found; ident_sys_error; ident_end_of_file;
       ident_division_by_zero; ident_sys_blocked_io;
       ident_assert_failure; ident_undefined_recursive_module ]

(* Start non-predef identifiers at 1000.  This way, more predefs can
   be defined in this file (above!) without breaking .cmi
   compatibility. *)

soit _ = Ident.set_current_time 999
soit builtin_idents = List.rev !builtin_idents
