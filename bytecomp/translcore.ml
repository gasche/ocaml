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

(* Translation from typed abstract syntax to lambda terms,
   for the core language *)

ouvre Misc
ouvre Asttypes
ouvre Primitive
ouvre Types
ouvre Typedtree
ouvre Typeopt
ouvre Lambda

type error =
    Illegal_letrec_pat
  | Illegal_letrec_expr
  | Free_super_var
  | Unknown_builtin_primitive de string

exception Error de Location.t * error

(* Forward declaration -- to be filled in by Translmod.transl_module *)
soit transl_module =
  ref((fonc cc rootpath modl -> affirme faux) :
      module_coercion -> Path.t option -> module_expr -> lambda)

soit transl_object =
  ref (fonc id s cl -> affirme faux :
       Ident.t -> string list -> class_expr -> lambda)

(* Translation of primitives *)

soit comparisons_table = create_hashtable 11 [
  "%equal",
      (Pccall{prim_name = "caml_equal"; prim_arity = 2; prim_alloc = vrai;
              prim_native_name = ""; prim_native_float = faux},
       Pintcomp Ceq,
       Pfloatcomp Ceq,
       Pccall{prim_name = "caml_string_equal"; prim_arity = 2;
              prim_alloc = faux;
              prim_native_name = ""; prim_native_float = faux},
       Pbintcomp(Pnativeint, Ceq),
       Pbintcomp(Pint32, Ceq),
       Pbintcomp(Pint64, Ceq),
       vrai);
  "%notequal",
      (Pccall{prim_name = "caml_notequal"; prim_arity = 2; prim_alloc = vrai;
              prim_native_name = ""; prim_native_float = faux},
       Pintcomp Cneq,
       Pfloatcomp Cneq,
       Pccall{prim_name = "caml_string_notequal"; prim_arity = 2;
              prim_alloc = faux; prim_native_name = "";
              prim_native_float = faux},
       Pbintcomp(Pnativeint, Cneq),
       Pbintcomp(Pint32, Cneq),
       Pbintcomp(Pint64, Cneq),
       vrai);
  "%lessthan",
      (Pccall{prim_name = "caml_lessthan"; prim_arity = 2; prim_alloc = vrai;
              prim_native_name = ""; prim_native_float = faux},
       Pintcomp Clt,
       Pfloatcomp Clt,
       Pccall{prim_name = "caml_string_lessthan"; prim_arity = 2;
              prim_alloc = faux; prim_native_name = "";
              prim_native_float = faux},
       Pbintcomp(Pnativeint, Clt),
       Pbintcomp(Pint32, Clt),
       Pbintcomp(Pint64, Clt),
       faux);
  "%greaterthan",
      (Pccall{prim_name = "caml_greaterthan"; prim_arity = 2; prim_alloc = vrai;
              prim_native_name = ""; prim_native_float = faux},
       Pintcomp Cgt,
       Pfloatcomp Cgt,
       Pccall{prim_name = "caml_string_greaterthan"; prim_arity = 2;
              prim_alloc = faux; prim_native_name = "";
              prim_native_float = faux},
       Pbintcomp(Pnativeint, Cgt),
       Pbintcomp(Pint32, Cgt),
       Pbintcomp(Pint64, Cgt),
       faux);
  "%lessequal",
      (Pccall{prim_name = "caml_lessequal"; prim_arity = 2; prim_alloc = vrai;
              prim_native_name = ""; prim_native_float = faux},
       Pintcomp Cle,
       Pfloatcomp Cle,
       Pccall{prim_name = "caml_string_lessequal"; prim_arity = 2;
              prim_alloc = faux; prim_native_name = "";
              prim_native_float = faux},
       Pbintcomp(Pnativeint, Cle),
       Pbintcomp(Pint32, Cle),
       Pbintcomp(Pint64, Cle),
       faux);
  "%greaterequal",
      (Pccall{prim_name = "caml_greaterequal"; prim_arity = 2;
              prim_alloc = vrai;
              prim_native_name = ""; prim_native_float = faux},
       Pintcomp Cge,
       Pfloatcomp Cge,
       Pccall{prim_name = "caml_string_greaterequal"; prim_arity = 2;
              prim_alloc = faux; prim_native_name = "";
              prim_native_float = faux},
       Pbintcomp(Pnativeint, Cge),
       Pbintcomp(Pint32, Cge),
       Pbintcomp(Pint64, Cge),
       faux);
  "%compare",
      (Pccall{prim_name = "caml_compare"; prim_arity = 2; prim_alloc = vrai;
              prim_native_name = ""; prim_native_float = faux},
       Pccall{prim_name = "caml_int_compare"; prim_arity = 2;
              prim_alloc = faux; prim_native_name = "";
              prim_native_float = faux},
       Pccall{prim_name = "caml_float_compare"; prim_arity = 2;
              prim_alloc = faux; prim_native_name = "";
              prim_native_float = faux},
       Pccall{prim_name = "caml_string_compare"; prim_arity = 2;
              prim_alloc = faux; prim_native_name = "";
              prim_native_float = faux},
       Pccall{prim_name = "caml_nativeint_compare"; prim_arity = 2;
              prim_alloc = faux; prim_native_name = "";
              prim_native_float = faux},
       Pccall{prim_name = "caml_int32_compare"; prim_arity = 2;
              prim_alloc = faux; prim_native_name = "";
              prim_native_float = faux},
       Pccall{prim_name = "caml_int64_compare"; prim_arity = 2;
              prim_alloc = faux; prim_native_name = "";
              prim_native_float = faux},
       faux)
]

soit primitives_table = create_hashtable 57 [
  "%identity", Pidentity;
  "%ignore", Pignore;
  "%field0", Pfield 0;
  "%field1", Pfield 1;
  "%setfield0", Psetfield(0, vrai);
  "%makeblock", Pmakeblock(0, Immutable);
  "%makemutable", Pmakeblock(0, Mutable);
  "%raise", Praise Raise_regular;
  "%reraise", Praise Raise_reraise;
  "%raise_notrace", Praise Raise_notrace;
  "%sequand", Psequand;
  "%sequor", Psequor;
  "%boolnot", Pnot;
  "%big_endian", Pctconst Big_endian;
  "%word_size", Pctconst Word_size;
  "%ostype_unix", Pctconst Ostype_unix;
  "%ostype_win32", Pctconst Ostype_win32;
  "%ostype_cygwin", Pctconst Ostype_cygwin;
  "%negint", Pnegint;
  "%succint", Poffsetint 1;
  "%predint", Poffsetint(-1);
  "%addint", Paddint;
  "%subint", Psubint;
  "%mulint", Pmulint;
  "%divint", Pdivint;
  "%modint", Pmodint;
  "%andint", Pandint;
  "%orint", Porint;
  "%xorint", Pxorint;
  "%lslint", Plslint;
  "%lsrint", Plsrint;
  "%asrint", Pasrint;
  "%eq", Pintcomp Ceq;
  "%noteq", Pintcomp Cneq;
  "%ltint", Pintcomp Clt;
  "%leint", Pintcomp Cle;
  "%gtint", Pintcomp Cgt;
  "%geint", Pintcomp Cge;
  "%incr", Poffsetref(1);
  "%decr", Poffsetref(-1);
  "%intoffloat", Pintoffloat;
  "%floatofint", Pfloatofint;
  "%negfloat", Pnegfloat;
  "%absfloat", Pabsfloat;
  "%addfloat", Paddfloat;
  "%subfloat", Psubfloat;
  "%mulfloat", Pmulfloat;
  "%divfloat", Pdivfloat;
  "%eqfloat", Pfloatcomp Ceq;
  "%noteqfloat", Pfloatcomp Cneq;
  "%ltfloat", Pfloatcomp Clt;
  "%lefloat", Pfloatcomp Cle;
  "%gtfloat", Pfloatcomp Cgt;
  "%gefloat", Pfloatcomp Cge;
  "%string_length", Pstringlength;
  "%string_safe_get", Pstringrefs;
  "%string_safe_set", Pstringsets;
  "%string_unsafe_get", Pstringrefu;
  "%string_unsafe_set", Pstringsetu;
  "%array_length", Parraylength Pgenarray;
  "%array_safe_get", Parrayrefs Pgenarray;
  "%array_safe_set", Parraysets Pgenarray;
  "%array_unsafe_get", Parrayrefu Pgenarray;
  "%array_unsafe_set", Parraysetu Pgenarray;
  "%obj_size", Parraylength Pgenarray;
  "%obj_field", Parrayrefu Pgenarray;
  "%obj_set_field", Parraysetu Pgenarray;
  "%obj_is_int", Pisint;
  "%lazy_force", Plazyforce;
  "%nativeint_of_int", Pbintofint Pnativeint;
  "%nativeint_to_int", Pintofbint Pnativeint;
  "%nativeint_neg", Pnegbint Pnativeint;
  "%nativeint_add", Paddbint Pnativeint;
  "%nativeint_sub", Psubbint Pnativeint;
  "%nativeint_mul", Pmulbint Pnativeint;
  "%nativeint_div", Pdivbint Pnativeint;
  "%nativeint_mod", Pmodbint Pnativeint;
  "%nativeint_and", Pandbint Pnativeint;
  "%nativeint_or",  Porbint Pnativeint;
  "%nativeint_xor", Pxorbint Pnativeint;
  "%nativeint_lsl", Plslbint Pnativeint;
  "%nativeint_lsr", Plsrbint Pnativeint;
  "%nativeint_asr", Pasrbint Pnativeint;
  "%int32_of_int", Pbintofint Pint32;
  "%int32_to_int", Pintofbint Pint32;
  "%int32_neg", Pnegbint Pint32;
  "%int32_add", Paddbint Pint32;
  "%int32_sub", Psubbint Pint32;
  "%int32_mul", Pmulbint Pint32;
  "%int32_div", Pdivbint Pint32;
  "%int32_mod", Pmodbint Pint32;
  "%int32_and", Pandbint Pint32;
  "%int32_or",  Porbint Pint32;
  "%int32_xor", Pxorbint Pint32;
  "%int32_lsl", Plslbint Pint32;
  "%int32_lsr", Plsrbint Pint32;
  "%int32_asr", Pasrbint Pint32;
  "%int64_of_int", Pbintofint Pint64;
  "%int64_to_int", Pintofbint Pint64;
  "%int64_neg", Pnegbint Pint64;
  "%int64_add", Paddbint Pint64;
  "%int64_sub", Psubbint Pint64;
  "%int64_mul", Pmulbint Pint64;
  "%int64_div", Pdivbint Pint64;
  "%int64_mod", Pmodbint Pint64;
  "%int64_and", Pandbint Pint64;
  "%int64_or",  Porbint Pint64;
  "%int64_xor", Pxorbint Pint64;
  "%int64_lsl", Plslbint Pint64;
  "%int64_lsr", Plsrbint Pint64;
  "%int64_asr", Pasrbint Pint64;
  "%nativeint_of_int32", Pcvtbint(Pint32, Pnativeint);
  "%nativeint_to_int32", Pcvtbint(Pnativeint, Pint32);
  "%int64_of_int32", Pcvtbint(Pint32, Pint64);
  "%int64_to_int32", Pcvtbint(Pint64, Pint32);
  "%int64_of_nativeint", Pcvtbint(Pnativeint, Pint64);
  "%int64_to_nativeint", Pcvtbint(Pint64, Pnativeint);
  "%caml_ba_ref_1",
    Pbigarrayref(faux, 1, Pbigarray_unknown, Pbigarray_unknown_layout);
  "%caml_ba_ref_2",
    Pbigarrayref(faux, 2, Pbigarray_unknown, Pbigarray_unknown_layout);
  "%caml_ba_ref_3",
    Pbigarrayref(faux, 3, Pbigarray_unknown, Pbigarray_unknown_layout);
  "%caml_ba_set_1",
    Pbigarrayset(faux, 1, Pbigarray_unknown, Pbigarray_unknown_layout);
  "%caml_ba_set_2",
    Pbigarrayset(faux, 2, Pbigarray_unknown, Pbigarray_unknown_layout);
  "%caml_ba_set_3",
    Pbigarrayset(faux, 3, Pbigarray_unknown, Pbigarray_unknown_layout);
  "%caml_ba_unsafe_ref_1",
    Pbigarrayref(vrai, 1, Pbigarray_unknown, Pbigarray_unknown_layout);
  "%caml_ba_unsafe_ref_2",
    Pbigarrayref(vrai, 2, Pbigarray_unknown, Pbigarray_unknown_layout);
  "%caml_ba_unsafe_ref_3",
    Pbigarrayref(vrai, 3, Pbigarray_unknown, Pbigarray_unknown_layout);
  "%caml_ba_unsafe_set_1",
    Pbigarrayset(vrai, 1, Pbigarray_unknown, Pbigarray_unknown_layout);
  "%caml_ba_unsafe_set_2",
    Pbigarrayset(vrai, 2, Pbigarray_unknown, Pbigarray_unknown_layout);
  "%caml_ba_unsafe_set_3",
    Pbigarrayset(vrai, 3, Pbigarray_unknown, Pbigarray_unknown_layout);
  "%caml_ba_dim_1", Pbigarraydim(1);
  "%caml_ba_dim_2", Pbigarraydim(2);
  "%caml_ba_dim_3", Pbigarraydim(3);
  "%caml_string_get16", Pstring_load_16(faux);
  "%caml_string_get16u", Pstring_load_16(vrai);
  "%caml_string_get32", Pstring_load_32(faux);
  "%caml_string_get32u", Pstring_load_32(vrai);
  "%caml_string_get64", Pstring_load_64(faux);
  "%caml_string_get64u", Pstring_load_64(vrai);
  "%caml_string_set16", Pstring_set_16(faux);
  "%caml_string_set16u", Pstring_set_16(vrai);
  "%caml_string_set32", Pstring_set_32(faux);
  "%caml_string_set32u", Pstring_set_32(vrai);
  "%caml_string_set64", Pstring_set_64(faux);
  "%caml_string_set64u", Pstring_set_64(vrai);
  "%caml_bigstring_get16", Pbigstring_load_16(faux);
  "%caml_bigstring_get16u", Pbigstring_load_16(vrai);
  "%caml_bigstring_get32", Pbigstring_load_32(faux);
  "%caml_bigstring_get32u", Pbigstring_load_32(vrai);
  "%caml_bigstring_get64", Pbigstring_load_64(faux);
  "%caml_bigstring_get64u", Pbigstring_load_64(vrai);
  "%caml_bigstring_set16", Pbigstring_set_16(faux);
  "%caml_bigstring_set16u", Pbigstring_set_16(vrai);
  "%caml_bigstring_set32", Pbigstring_set_32(faux);
  "%caml_bigstring_set32u", Pbigstring_set_32(vrai);
  "%caml_bigstring_set64", Pbigstring_set_64(faux);
  "%caml_bigstring_set64u", Pbigstring_set_64(vrai);
  "%bswap16", Pbswap16;
  "%bswap_int32", Pbbswap(Pint32);
  "%bswap_int64", Pbbswap(Pint64);
  "%bswap_native", Pbbswap(Pnativeint);
]

soit prim_makearray =
  { prim_name = "caml_make_vect"; prim_arity = 2; prim_alloc = vrai;
    prim_native_name = ""; prim_native_float = faux }

soit prim_obj_dup =
  { prim_name = "caml_obj_dup"; prim_arity = 1; prim_alloc = vrai;
    prim_native_name = ""; prim_native_float = faux }

soit find_primitive loc prim_name =
  filtre prim_name avec
      "%revapply" -> Prevapply loc
    | "%apply" -> Pdirapply loc
    | name -> Hashtbl.find primitives_table name

soit transl_prim loc prim args =
  soit prim_name = prim.prim_name dans
  essaie
    soit (gencomp, intcomp, floatcomp, stringcomp,
         nativeintcomp, int32comp, int64comp,
         simplify_constant_constructor) =
      Hashtbl.find comparisons_table prim_name dans
    début filtre args avec
      [arg1; {exp_desc = Texp_construct(_, {cstr_tag = Cstr_constant _}, _)}]
      quand simplify_constant_constructor ->
        intcomp
    | [{exp_desc = Texp_construct(_, {cstr_tag = Cstr_constant _}, _)}; arg2]
      quand simplify_constant_constructor ->
        intcomp
    | [arg1; {exp_desc = Texp_variant(_, None)}]
      quand simplify_constant_constructor ->
        intcomp
    | [{exp_desc = Texp_variant(_, None)}; exp2]
      quand simplify_constant_constructor ->
        intcomp
    | [arg1; arg2] quand has_base_type arg1 Predef.path_int
                     || has_base_type arg1 Predef.path_char ->
        intcomp
    | [arg1; arg2] quand has_base_type arg1 Predef.path_float ->
        floatcomp
    | [arg1; arg2] quand has_base_type arg1 Predef.path_string ->
        stringcomp
    | [arg1; arg2] quand has_base_type arg1 Predef.path_nativeint ->
        nativeintcomp
    | [arg1; arg2] quand has_base_type arg1 Predef.path_int32 ->
        int32comp
    | [arg1; arg2] quand has_base_type arg1 Predef.path_int64 ->
        int64comp
    | _ ->
        gencomp
    fin
  avec Not_found ->
  essaie
    soit p = find_primitive loc prim_name dans
    (* Try strength reduction based on the type of the argument *)
    début filtre (p, args) avec
        (Psetfield(n, _), [arg1; arg2]) -> Psetfield(n, maybe_pointer arg2)
      | (Parraylength Pgenarray, [arg])   -> Parraylength(array_kind arg)
      | (Parrayrefu Pgenarray, arg1 :: _) -> Parrayrefu(array_kind arg1)
      | (Parraysetu Pgenarray, arg1 :: _) -> Parraysetu(array_kind arg1)
      | (Parrayrefs Pgenarray, arg1 :: _) -> Parrayrefs(array_kind arg1)
      | (Parraysets Pgenarray, arg1 :: _) -> Parraysets(array_kind arg1)
      | (Pbigarrayref(unsafe, n, Pbigarray_unknown, Pbigarray_unknown_layout),
                      arg1 :: _) ->
            soit (k, l) = bigarray_kind_and_layout arg1 dans
            Pbigarrayref(unsafe, n, k, l)
      | (Pbigarrayset(unsafe, n, Pbigarray_unknown, Pbigarray_unknown_layout),
                      arg1 :: _) ->
            soit (k, l) = bigarray_kind_and_layout arg1 dans
            Pbigarrayset(unsafe, n, k, l)
      | _ -> p
    fin
  avec Not_found ->
    si String.length prim_name > 0 && prim_name.[0] = '%' alors
      raise(Error(loc, Unknown_builtin_primitive prim_name));
    Pccall prim


(* Eta-expand a primitive without knowing the types of its arguments *)

soit transl_primitive loc p =
  soit prim =
    essaie
      soit (gencomp, _, _, _, _, _, _, _) =
        Hashtbl.find comparisons_table p.prim_name dans
      gencomp
    avec Not_found ->
    essaie
      find_primitive loc p.prim_name
    avec Not_found ->
      Pccall p dans
  filtre prim avec
    Plazyforce ->
      soit parm = Ident.create "prim" dans
      Lfunction(Curried, [parm],
                Matching.inline_lazy_force (Lvar parm) Location.none)
  | _ ->
      soit rec make_params n =
        si n <= 0 alors [] sinon Ident.create "prim" :: make_params (n-1) dans
      soit params = make_params p.prim_arity dans
      Lfunction(Curried, params,
                Lprim(prim, List.map (fonc id -> Lvar id) params))

(* To check the well-formedness of r.h.s. of "let rec" definitions *)

soit check_recursive_lambda idlist lam =
  soit rec check_top idlist = fonction
    | Lvar v -> not (List.mem v idlist)
    | Llet (_, _, _, _) tel lam quand check_recursive_recordwith idlist lam ->
        vrai
    | Llet(str, id, arg, body) ->
        check idlist arg && check_top (add_let id arg idlist) body
    | Lletrec(bindings, body) ->
        soit idlist' = add_letrec bindings idlist dans
        List.for_all (fonc (id, arg) -> check idlist' arg) bindings &&
        check_top idlist' body
    | Lprim (Pmakearray (Pgenarray), args) -> faux
    | Lsequence (lam1, lam2) -> check idlist lam1 && check_top idlist lam2
    | Levent (lam, _) -> check_top idlist lam
    | lam -> check idlist lam

  et check idlist = fonction
    | Lvar _ -> vrai
    | Lfunction(kind, params, body) -> vrai
    | Llet (_, _, _, _) tel lam quand check_recursive_recordwith idlist lam ->
        vrai
    | Llet(str, id, arg, body) ->
        check idlist arg && check (add_let id arg idlist) body
    | Lletrec(bindings, body) ->
        soit idlist' = add_letrec bindings idlist dans
        List.for_all (fonc (id, arg) -> check idlist' arg) bindings &&
        check idlist' body
    | Lprim(Pmakeblock(tag, mut), args) ->
        List.for_all (check idlist) args
    | Lprim(Pmakearray(_), args) ->
        List.for_all (check idlist) args
    | Lsequence (lam1, lam2) -> check idlist lam1 && check idlist lam2
    | Levent (lam, _) -> check idlist lam
    | lam ->
        soit fv = free_variables lam dans
        not (List.exists (fonc id -> IdentSet.mem id fv) idlist)

  et add_let id arg idlist =
    soit fv = free_variables arg dans
    si List.exists (fonc id -> IdentSet.mem id fv) idlist
    alors id :: idlist
    sinon idlist

  et add_letrec bindings idlist =
    List.fold_right (fonc (id, arg) idl -> add_let id arg idl)
                    bindings idlist

  (* reverse-engineering the code generated by transl_record case 2 *)
  (* If you change this, you probably need to change Bytegen.size_of_lambda. *)
  et check_recursive_recordwith idlist = fonction
    | Llet (Strict, id1, Lprim (Pduprecord _, [e1]), body) ->
       check_top idlist e1
       && check_recordwith_updates idlist id1 body
    | _ -> faux

  et check_recordwith_updates idlist id1 = fonction
    | Lsequence (Lprim ((Psetfield _ | Psetfloatfield _), [Lvar id2; e1]), cont)
        -> id2 = id1 && check idlist e1
           && check_recordwith_updates idlist id1 cont
    | Lvar id2 -> id2 = id1
    | _ -> faux

  dans check_top idlist lam

(* To propagate structured constants *)

exception Not_constant

soit extract_constant = fonction
    Lconst sc -> sc
  | _ -> raise Not_constant

soit extract_float = fonction
    Const_base(Const_float f) -> f
  | _ -> fatal_error "Translcore.extract_float"

(* To find reasonable names for let-bound and lambda-bound idents *)

soit rec name_pattern default = fonction
    [] -> Ident.create default
  | {c_lhs=p; _} :: rem ->
      filtre p.pat_desc avec
        Tpat_var (id, _) -> id
      | Tpat_alias(p, id, _) -> id
      | _ -> name_pattern default rem

(* Push the default values under the functional abstractions *)

soit rec push_defaults loc bindings cases partial =
  filtre cases avec
    [{c_lhs=pat; c_guard=None;
      c_rhs={exp_desc = Texp_function(l, pl,partial)} tel exp}] ->
      soit pl = push_defaults exp.exp_loc bindings pl partial dans
      [{c_lhs=pat; c_guard=None; c_rhs={exp avec exp_desc = Texp_function(l, pl, partial)}}]
  | [{c_lhs=pat; c_guard=None;
      c_rhs={exp_attributes=[{txt="#default"},_];
             exp_desc = Texp_let
               (Nonrecursive, binds, ({exp_desc = Texp_function _} tel e2))}}] ->
      push_defaults loc (binds :: bindings) [{c_lhs=pat;c_guard=None;c_rhs=e2}] partial
  | [case] ->
      soit exp =
        List.fold_left
          (fonc exp binds ->
            {exp avec exp_desc = Texp_let(Nonrecursive, binds, exp)})
          case.c_rhs bindings
      dans
      [{case avec c_rhs=exp}]
  | {c_lhs=pat; c_rhs=exp; c_guard=_} :: _ quand bindings <> [] ->
      soit param = name_pattern "param" cases dans
      soit name = Ident.name param dans
      soit exp =
        { exp avec exp_loc = loc; exp_desc =
          Texp_match
            ({exp avec exp_type = pat.pat_type; exp_desc =
              Texp_ident (Path.Pident param, mknoloc (Longident.Lident name),
                          {val_type = pat.pat_type; val_kind = Val_reg;
                           val_attributes = [];
                           Types.val_loc = Location.none;
                          })},
             cases, partial) }
      dans
      push_defaults loc bindings
        [{c_lhs={pat avec pat_desc = Tpat_var (param, mknoloc name)}; c_guard=None; c_rhs=exp}] Total
  | _ ->
      cases

(* Insertion of debugging events *)

soit event_before exp lam = filtre lam avec
| Lstaticraise (_,_) -> lam
| _ ->
  si !Clflags.debug
  alors Levent(lam, {lev_loc = exp.exp_loc;
                    lev_kind = Lev_before;
                    lev_repr = None;
                    lev_env = Env.summary exp.exp_env})
  sinon lam

soit event_after exp lam =
  si !Clflags.debug
  alors Levent(lam, {lev_loc = exp.exp_loc;
                    lev_kind = Lev_after exp.exp_type;
                    lev_repr = None;
                    lev_env = Env.summary exp.exp_env})
  sinon lam

soit event_function exp lam =
  si !Clflags.debug alors
    soit repr = Some (ref 0) dans
    soit (info, body) = lam repr dans
    (info,
     Levent(body, {lev_loc = exp.exp_loc;
                   lev_kind = Lev_function;
                   lev_repr = repr;
                   lev_env = Env.summary exp.exp_env}))
  sinon
    lam None

soit primitive_is_ccall = fonction
  (* Determine if a primitive is a Pccall or will be turned later into
     a C function call that may raise an exception *)
  | Pccall _ | Pstringrefs | Pstringsets | Parrayrefs _ | Parraysets _ |
    Pbigarrayref _ | Pbigarrayset _ | Pduprecord _ -> vrai
  | _ -> faux

(* Assertions *)

soit assert_failed exp =
  soit (fname, line, char) =
    Location.get_pos_info exp.exp_loc.Location.loc_start dans
  Lprim(Praise Raise_regular, [event_after exp
    (Lprim(Pmakeblock(0, Immutable),
          [transl_normal_path Predef.path_assert_failure;
           Lconst(Const_block(0,
              [Const_base(Const_string (fname, None));
               Const_base(Const_int line);
               Const_base(Const_int char)]))]))])
;;

soit rec cut n l =
  si n = 0 alors ([],l) sinon
  filtre l avec [] -> failwith "Translcore.cut"
  | a::l -> soit (l1,l2) = cut (n-1) l dans (a::l1,l2)

(* Translation of expressions *)

soit try_ids = Hashtbl.create 8

soit rec transl_exp e =
  soit eval_once =
    (* Whether classes for immediate objects must be cached *)
    filtre e.exp_desc avec
      Texp_function _ | Texp_for _ | Texp_while _ -> faux
    | _ -> vrai
  dans
  si eval_once alors transl_exp0 e sinon
  Translobj.oo_wrap e.exp_env vrai transl_exp0 e

et transl_exp0 e =
  filtre e.exp_desc avec
    Texp_ident(path, _, {val_kind = Val_prim p}) ->
      soit public_send = p.prim_name = "%send" dans
      si public_send || p.prim_name = "%sendself" alors
        soit kind = si public_send alors Public sinon Self dans
        soit obj = Ident.create "obj" et meth = Ident.create "meth" dans
        Lfunction(Curried, [obj; meth], Lsend(kind, Lvar meth, Lvar obj, [],
                                              e.exp_loc))
      sinon si p.prim_name = "%sendcache" alors
        soit obj = Ident.create "obj" et meth = Ident.create "meth" dans
        soit cache = Ident.create "cache" et pos = Ident.create "pos" dans
        Lfunction(Curried, [obj; meth; cache; pos],
                  Lsend(Cached, Lvar meth, Lvar obj, [Lvar cache; Lvar pos],
                        e.exp_loc))
      sinon
        transl_primitive e.exp_loc p
  | Texp_ident(path, _, {val_kind = Val_anc _}) ->
      raise(Error(e.exp_loc, Free_super_var))
  | Texp_ident(path, _, {val_kind = Val_reg | Val_self _}) ->
      transl_path ~loc:e.exp_loc e.exp_env path
  | Texp_ident _ -> fatal_error "Translcore.transl_exp: Texp_ident incorrect"
  | Texp_constant cst ->
      Lconst(Const_base cst)
  | Texp_let(rec_flag, pat_expr_list, body) ->
      transl_let rec_flag pat_expr_list (event_before body (transl_exp body))
  | Texp_function (_, pat_expr_list, partial) ->
      soit ((kind, params), body) =
        event_function e
          (fonction repr ->
            soit pl = push_defaults e.exp_loc [] pat_expr_list partial dans
            transl_function e.exp_loc !Clflags.native_code repr partial pl)
      dans
      Lfunction(kind, params, body)
  | Texp_apply({exp_desc = Texp_ident(path, _, {val_kind = Val_prim p})} tel fn,
               oargs)
    quand List.length oargs >= p.prim_arity
    && List.for_all (fonc (_, arg,_) -> arg <> None) oargs ->
      soit args, args' = cut p.prim_arity oargs dans
      soit wrap f =
        si args' = []
        alors event_after e f
        sinon event_after e (transl_apply f args' e.exp_loc)
      dans
      soit wrap0 f =
        si args' = [] alors f sinon wrap f dans
      soit args =
         List.map (fonction _, Some x, _ -> x | _ -> affirme faux) args dans
      soit argl = transl_list args dans
      soit public_send = p.prim_name = "%send"
        || not !Clflags.native_code && p.prim_name = "%sendcache"dans
      si public_send || p.prim_name = "%sendself" alors
        soit kind = si public_send alors Public sinon Self dans
        soit obj = List.hd argl dans
        wrap (Lsend (kind, List.nth argl 1, obj, [], e.exp_loc))
      sinon si p.prim_name = "%sendcache" alors
        filtre argl avec [obj; meth; cache; pos] ->
          wrap (Lsend(Cached, meth, obj, [cache; pos], e.exp_loc))
        | _ -> affirme faux
      sinon début
        si p.prim_name = "%sequand" && Path.last path = "&" alors
          Location.prerr_warning fn.exp_loc
            (Warnings.Deprecated "operateur (&); vous devriez plutôt utiliser (&&)");
        si p.prim_name = "%sequor" && Path.last path = "or" alors
          Location.prerr_warning fn.exp_loc
            (Warnings.Deprecated "operater (or); vous devriez plutôt utiliser (||)");
        soit prim = transl_prim e.exp_loc p args dans
        filtre (prim, args) avec
          (Praise k, [arg1]) ->
            soit targ = List.hd argl dans
            soit k =
              filtre k, targ avec
              | Raise_regular, Lvar id
                quand Hashtbl.mem try_ids id ->
                  Raise_reraise
              | _ ->
                  k
            dans
            wrap0 (Lprim(Praise k, [event_after arg1 targ]))
        | (_, _) ->
            début filtre (prim, argl) avec
            | (Plazyforce, [a]) ->
                wrap (Matching.inline_lazy_force a e.exp_loc)
            | (Plazyforce, _) -> affirme faux
            |_ -> soit p = Lprim(prim, argl) dans
               si primitive_is_ccall prim alors wrap p sinon wrap0 p
            fin
      fin
  | Texp_apply(funct, oargs) ->
      event_after e (transl_apply (transl_exp funct) oargs e.exp_loc)
  | Texp_match({exp_desc = Texp_tuple argl}, pat_expr_list, partial) ->
      Matching.for_multiple_match e.exp_loc
        (transl_list argl) (transl_cases pat_expr_list) partial
  | Texp_match(arg, pat_expr_list, partial) ->
      Matching.for_function e.exp_loc None
        (transl_exp arg) (transl_cases pat_expr_list) partial
  | Texp_try(body, pat_expr_list) ->
      soit id = name_pattern "exn" pat_expr_list dans
      Ltrywith(transl_exp body, id,
               Matching.for_trywith (Lvar id) (transl_cases_try pat_expr_list))
  | Texp_tuple el ->
      soit ll = transl_list el dans
      début essaie
        Lconst(Const_block(0, List.map extract_constant ll))
      avec Not_constant ->
        Lprim(Pmakeblock(0, Immutable), ll)
      fin
  | Texp_construct(_, cstr, args) ->
      soit ll = transl_list args dans
      début filtre cstr.cstr_tag avec
        Cstr_constant n ->
          Lconst(Const_pointer n)
      | Cstr_block n ->
          début essaie
            Lconst(Const_block(n, List.map extract_constant ll))
          avec Not_constant ->
            Lprim(Pmakeblock(n, Immutable), ll)
          fin
      | Cstr_exception (path, _) ->
          soit slot = transl_path ~loc:e.exp_loc e.exp_env path dans
          si cstr.cstr_arity = 0 alors slot
          sinon Lprim(Pmakeblock(0, Immutable), slot :: ll)
      fin
  | Texp_variant(l, arg) ->
      soit tag = Btype.hash_variant l dans
      début filtre arg avec
        None -> Lconst(Const_pointer tag)
      | Some arg ->
          soit lam = transl_exp arg dans
          essaie
            Lconst(Const_block(0, [Const_base(Const_int tag);
                                   extract_constant lam]))
          avec Not_constant ->
            Lprim(Pmakeblock(0, Immutable),
                  [Lconst(Const_base(Const_int tag)); lam])
      fin
  | Texp_record ((_, lbl1, _) :: _ tel lbl_expr_list, opt_init_expr) ->
      transl_record lbl1.lbl_all lbl1.lbl_repres lbl_expr_list opt_init_expr
  | Texp_record ([], _) ->
      fatal_error "Translcore.transl_exp: Texp_record incorrect"
  | Texp_field(arg, _, lbl) ->
      soit access =
        filtre lbl.lbl_repres avec
          Record_regular -> Pfield lbl.lbl_pos
        | Record_float -> Pfloatfield lbl.lbl_pos dans
      Lprim(access, [transl_exp arg])
  | Texp_setfield(arg, _, lbl, newval) ->
      soit access =
        filtre lbl.lbl_repres avec
          Record_regular -> Psetfield(lbl.lbl_pos, maybe_pointer newval)
        | Record_float -> Psetfloatfield lbl.lbl_pos dans
      Lprim(access, [transl_exp arg; transl_exp newval])
  | Texp_array expr_list ->
      soit kind = array_kind e dans
      soit ll = transl_list expr_list dans
      début essaie
        (* Deactivate constant optimization if array is small enough *)
        si List.length ll <= 4 alors raise Not_constant;
        soit cl = List.map extract_constant ll dans
        soit master =
          filtre kind avec
          | Paddrarray | Pintarray ->
              Lconst(Const_block(0, cl))
          | Pfloatarray ->
              Lconst(Const_float_array(List.map extract_float cl))
          | Pgenarray ->
              raise Not_constant dans             (* can this really happen? *)
        Lprim(Pccall prim_obj_dup, [master])
      avec Not_constant ->
        Lprim(Pmakearray kind, ll)
      fin
  | Texp_ifthenelse(cond, ifso, Some ifnot) ->
      Lifthenelse(transl_exp cond,
                  event_before ifso (transl_exp ifso),
                  event_before ifnot (transl_exp ifnot))
  | Texp_ifthenelse(cond, ifso, None) ->
      Lifthenelse(transl_exp cond,
                  event_before ifso (transl_exp ifso),
                  lambda_unit)
  | Texp_sequence(expr1, expr2) ->
      Lsequence(transl_exp expr1, event_before expr2 (transl_exp expr2))
  | Texp_while(cond, body) ->
      Lwhile(transl_exp cond, event_before body (transl_exp body))
  | Texp_for(param, _, low, high, dir, body) ->
      Lfor(param, transl_exp low, transl_exp high, dir,
           event_before body (transl_exp body))
  | Texp_send(_, _, Some exp) -> transl_exp exp
  | Texp_send(expr, met, None) ->
      soit obj = transl_exp expr dans
      soit lam =
        filtre met avec
          Tmeth_val id -> Lsend (Self, Lvar id, obj, [], e.exp_loc)
        | Tmeth_name nm ->
            soit (tag, cache) = Translobj.meth obj nm dans
            soit kind = si cache = [] alors Public sinon Cached dans
            Lsend (kind, tag, obj, cache, e.exp_loc)
      dans
      event_after e lam
  | Texp_new (cl, {Location.loc=loc}, _) ->
      Lapply(Lprim(Pfield 0, [transl_path ~loc e.exp_env cl]),
             [lambda_unit], Location.none)
  | Texp_instvar(path_self, path, _) ->
      Lprim(Parrayrefu Paddrarray,
            [transl_normal_path path_self; transl_normal_path path])
  | Texp_setinstvar(path_self, path, _, expr) ->
      transl_setinstvar (transl_normal_path path_self) path expr
  | Texp_override(path_self, modifs) ->
      soit cpy = Ident.create "copy" dans
      Llet(Strict, cpy,
           Lapply(Translobj.oo_prim "copy", [transl_normal_path path_self],
                  Location.none),
           List.fold_right
             (fonc (path, _, expr) rem ->
                Lsequence(transl_setinstvar (Lvar cpy) path expr, rem))
             modifs
             (Lvar cpy))
  | Texp_letmodule(id, _, modl, body) ->
      Llet(Strict, id, !transl_module Tcoerce_none None modl, transl_exp body)
  | Texp_pack modl ->
      !transl_module Tcoerce_none None modl
  | Texp_assert {exp_desc=Texp_construct(_, {cstr_name="false"}, _)} ->
      assert_failed e
  | Texp_assert (cond) ->
      si !Clflags.noassert
      alors lambda_unit
      sinon Lifthenelse (transl_exp cond, lambda_unit, assert_failed e)
  | Texp_lazy e ->
      (* when e needs no computation (constants, identifiers, ...), we
         optimize the translation just as Lazy.lazy_from_val would
         do *)
      début filtre e.exp_desc avec
        (* a constant expr of type <> float gets compiled as itself *)
      | Texp_constant
          ( Const_int _ | Const_char _ | Const_string _
          | Const_int32 _ | Const_int64 _ | Const_nativeint _ )
      | Texp_function(_, _, _)
      | Texp_construct (_, {cstr_arity = 0}, _)
        -> transl_exp e
      | Texp_constant(Const_float _) ->
          Lprim(Pmakeblock(Obj.forward_tag, Immutable), [transl_exp e])
      | Texp_ident(_, _, _) -> (* according to the type *)
          début filtre e.exp_type.desc avec
          (* the following may represent a float/forward/lazy: need a
             forward_tag *)
          | Tvar _ | Tlink _ | Tsubst _ | Tunivar _
          | Tpoly(_,_) | Tfield(_,_,_,_) ->
              Lprim(Pmakeblock(Obj.forward_tag, Immutable), [transl_exp e])
          (* the following cannot be represented as float/forward/lazy:
             optimize *)
          | Tarrow(_,_,_,_) | Ttuple _ | Tpackage _ | Tobject(_,_) | Tnil
          | Tvariant _
              -> transl_exp e
          (* optimize predefined types (excepted float) *)
          | Tconstr(_,_,_) ->
              si has_base_type e Predef.path_int
                || has_base_type e Predef.path_char
                || has_base_type e Predef.path_string
                || has_base_type e Predef.path_bool
                || has_base_type e Predef.path_unit
                || has_base_type e Predef.path_exn
                || has_base_type e Predef.path_array
                || has_base_type e Predef.path_list
                || has_base_type e Predef.path_format6
                || has_base_type e Predef.path_option
                || has_base_type e Predef.path_nativeint
                || has_base_type e Predef.path_int32
                || has_base_type e Predef.path_int64
              alors transl_exp e
              sinon
                Lprim(Pmakeblock(Obj.forward_tag, Immutable), [transl_exp e])
          fin
      (* other cases compile to a lazy block holding a function *)
      | _ ->
          soit fn = Lfunction (Curried, [Ident.create "param"], transl_exp e) dans
          Lprim(Pmakeblock(Config.lazy_tag, Mutable), [fn])
      fin
  | Texp_object (cs, meths) ->
      soit cty = cs.cstr_type dans
      soit cl = Ident.create "class" dans
      !transl_object cl meths
        { cl_desc = Tcl_structure cs;
          cl_loc = e.exp_loc;
          cl_type = Cty_signature cty;
          cl_env = e.exp_env;
          cl_attributes = [];
         }

et transl_list expr_list =
  List.map transl_exp expr_list

et transl_guard guard rhs =
  soit expr = event_before rhs (transl_exp rhs) dans
  filtre guard avec
  | None -> expr
  | Some cond ->
      event_before cond (Lifthenelse(transl_exp cond, expr, staticfail))

et transl_case {c_lhs; c_guard; c_rhs} =
  c_lhs, transl_guard c_guard c_rhs

et transl_cases cases =
  List.map transl_case cases

et transl_case_try {c_lhs; c_guard; c_rhs} =
  filtre c_lhs.pat_desc avec
  | Tpat_var (id, _)
  | Tpat_alias (_, id, _) ->
      Hashtbl.replace try_ids id ();
      Misc.try_finally
        (fonc () -> c_lhs, transl_guard c_guard c_rhs)
        (fonc () -> Hashtbl.remove try_ids id)
  | _ ->
      c_lhs, transl_guard c_guard c_rhs

et transl_cases_try cases =
  List.map transl_case_try cases

et transl_tupled_cases patl_expr_list =
  List.map (fonc (patl, guard, expr) -> (patl, transl_guard guard expr))
    patl_expr_list

et transl_apply lam sargs loc =
  soit lapply funct args =
    filtre funct avec
      Lsend(k, lmet, lobj, largs, loc) ->
        Lsend(k, lmet, lobj, largs @ args, loc)
    | Levent(Lsend(k, lmet, lobj, largs, loc), _) ->
        Lsend(k, lmet, lobj, largs @ args, loc)
    | Lapply(lexp, largs, _) ->
        Lapply(lexp, largs @ args, loc)
    | lexp ->
        Lapply(lexp, args, loc)
  dans
  soit rec build_apply lam args = fonction
      (None, optional) :: l ->
        soit defs = ref [] dans
        soit protect name lam =
          filtre lam avec
            Lvar _ | Lconst _ -> lam
          | _ ->
              soit id = Ident.create name dans
              defs := (id, lam) :: !defs;
              Lvar id
        dans
        soit args, args' =
          si List.for_all (fonc (_,opt) -> opt = Optional) args alors [], args
          sinon args, [] dans
        soit lam =
          si args = [] alors lam sinon lapply lam (List.rev_map fst args) dans
        soit handle = protect "func" lam
        et l = List.map (fonc (arg, opt) -> may_map (protect "arg") arg, opt) l
        et id_arg = Ident.create "param" dans
        soit body =
          filtre build_apply handle ((Lvar id_arg, optional)::args') l avec
            Lfunction(Curried, ids, lam) ->
              Lfunction(Curried, id_arg::ids, lam)
          | Levent(Lfunction(Curried, ids, lam), _) ->
              Lfunction(Curried, id_arg::ids, lam)
          | lam ->
              Lfunction(Curried, [id_arg], lam)
        dans
        List.fold_left
          (fonc body (id, lam) -> Llet(Strict, id, lam, body))
          body !defs
    | (Some arg, optional) :: l ->
        build_apply lam ((arg, optional) :: args) l
    | [] ->
        lapply lam (List.rev_map fst args)
  dans
  build_apply lam [] (List.map (fonc (l, x,o) -> may_map transl_exp x, o) sargs)

et transl_function loc untuplify_fn repr partial cases =
  filtre cases avec
    [{c_lhs=pat; c_guard=None;
      c_rhs={exp_desc = Texp_function(_, pl,partial')} tel exp}]
    quand Parmatch.fluid pat ->
      soit param = name_pattern "param" cases dans
      soit ((_, params), body) =
        transl_function exp.exp_loc faux repr partial' pl dans
      ((Curried, param :: params),
       Matching.for_function loc None (Lvar param) [pat, body] partial)
  | {c_lhs={pat_desc = Tpat_tuple pl}} :: _ quand untuplify_fn ->
      début essaie
        soit size = List.length pl dans
        soit pats_expr_list =
          List.map
            (fonc {c_lhs; c_guard; c_rhs} ->
              (Matching.flatten_pattern size c_lhs, c_guard, c_rhs))
            cases dans
        soit params = List.map (fonc p -> Ident.create "param") pl dans
        ((Tupled, params),
         Matching.for_tupled_function loc params
           (transl_tupled_cases pats_expr_list) partial)
      avec Matching.Cannot_flatten ->
        soit param = name_pattern "param" cases dans
        ((Curried, [param]),
         Matching.for_function loc repr (Lvar param)
           (transl_cases cases) partial)
      fin
  | _ ->
      soit param = name_pattern "param" cases dans
      ((Curried, [param]),
       Matching.for_function loc repr (Lvar param)
         (transl_cases cases) partial)

et transl_let rec_flag pat_expr_list body =
  filtre rec_flag avec
    Nonrecursive ->
      soit rec transl = fonction
        [] ->
          body
      | {vb_pat=pat; vb_expr=expr} :: rem ->
          Matching.for_let pat.pat_loc (transl_exp expr) pat (transl rem)
      dans transl pat_expr_list
  | Recursive ->
      soit idlist =
        List.map
          (fonc {vb_pat=pat} -> filtre pat.pat_desc avec
              Tpat_var (id,_) -> id
            | Tpat_alias ({pat_desc=Tpat_any}, id,_) -> id
            | _ -> raise(Error(pat.pat_loc, Illegal_letrec_pat)))
        pat_expr_list dans
      soit transl_case {vb_pat=pat; vb_expr=expr} id =
        soit lam = transl_exp expr dans
        si not (check_recursive_lambda idlist lam) alors
          raise(Error(expr.exp_loc, Illegal_letrec_expr));
        (id, lam) dans
      Lletrec(List.map2 transl_case pat_expr_list idlist, body)

et transl_setinstvar self var expr =
  Lprim(Parraysetu (si maybe_pointer expr alors Paddrarray sinon Pintarray),
                    [self; transl_normal_path var; transl_exp expr])

et transl_record all_labels repres lbl_expr_list opt_init_expr =
  soit size = Array.length all_labels dans
  (* Determine if there are "enough" new fields *)
  si 3 + 2 * List.length lbl_expr_list >= size
  alors début
    (* Allocate new record with given fields (and remaining fields
       taken from init_expr if any *)
    soit lv = Array.create (Array.length all_labels) staticfail dans
    soit init_id = Ident.create "init" dans
    début filtre opt_init_expr avec
      None -> ()
    | Some init_expr ->
        pour i = 0 à Array.length all_labels - 1 faire
          soit access =
            filtre all_labels.(i).lbl_repres avec
              Record_regular -> Pfield i
            | Record_float -> Pfloatfield i dans
          lv.(i) <- Lprim(access, [Lvar init_id])
        fait
    fin;
    List.iter
      (fonc (_, lbl, expr) -> lv.(lbl.lbl_pos) <- transl_exp expr)
      lbl_expr_list;
    soit ll = Array.to_list lv dans
    soit mut =
      si List.exists (fonc (_, lbl, expr) -> lbl.lbl_mut = Mutable) lbl_expr_list
      alors Mutable
      sinon Immutable dans
    soit lam =
      essaie
        si mut = Mutable alors raise Not_constant;
        soit cl = List.map extract_constant ll dans
        filtre repres avec
          Record_regular -> Lconst(Const_block(0, cl))
        | Record_float ->
            Lconst(Const_float_array(List.map extract_float cl))
      avec Not_constant ->
        filtre repres avec
          Record_regular -> Lprim(Pmakeblock(0, mut), ll)
        | Record_float -> Lprim(Pmakearray Pfloatarray, ll) dans
    début filtre opt_init_expr avec
      None -> lam
    | Some init_expr -> Llet(Strict, init_id, transl_exp init_expr, lam)
    fin
  fin sinon début
    (* Take a shallow copy of the init record, then mutate the fields
       of the copy *)
    (* If you change anything here, you will likely have to change
       [check_recursive_recordwith] in this file. *)
    soit copy_id = Ident.create "newrecord" dans
    soit update_field (_, lbl, expr) cont =
      soit upd =
        filtre lbl.lbl_repres avec
          Record_regular -> Psetfield(lbl.lbl_pos, maybe_pointer expr)
        | Record_float -> Psetfloatfield lbl.lbl_pos dans
      Lsequence(Lprim(upd, [Lvar copy_id; transl_exp expr]), cont) dans
    début filtre opt_init_expr avec
      None -> affirme faux
    | Some init_expr ->
        Llet(Strict, copy_id,
             Lprim(Pduprecord (repres, size), [transl_exp init_expr]),
             List.fold_right update_field lbl_expr_list (Lvar copy_id))
    fin
  fin

(* Wrapper for class compilation *)

(*
let transl_exp = transl_exp_wrap

let transl_let rec_flag pat_expr_list body =
  match pat_expr_list with
    [] -> body
  | (_, expr) :: _ ->
      Translobj.oo_wrap expr.exp_env false
        (transl_let rec_flag pat_expr_list) body
*)

(* Error report *)

ouvre Format

soit report_error ppf = fonction
  | Illegal_letrec_pat ->
      fprintf ppf
        "Seules les variables sont autorisées comme membre gauche de `soit rec'"
  | Illegal_letrec_expr ->
      fprintf ppf
        "Cette sorte d'expression n'est pas autorisée comme membre droit de `soit rec'"
  | Free_super_var ->
      fprintf ppf
        "Les noms d'ancêtres ne peuvent qu'être utilisés pour sélectionner des méthodes héritées"
  | Unknown_builtin_primitive prim_name ->
      fprintf ppf  "Primitive builtin inconnue \"%s\"" prim_name

soit () =
  Location.register_error_of_exn
    (fonction
      | Error (loc, err) ->
          Some (Location.error_of_printer loc report_error err)
      | _ ->
        None
    )
