(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1998 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* Auxiliaries for type-based optimizations, e.g. array kinds *)

ouvre Path
ouvre Types
ouvre Typedtree
ouvre Lambda

soit scrape env ty =
  (Ctype.repr (Ctype.expand_head_opt env (Ctype.correct_levels ty))).desc

soit has_base_type exp base_ty_path =
  filtre scrape exp.exp_env exp.exp_type avec
  | Tconstr(p, _, _) -> Path.same p base_ty_path
  | _ -> faux

soit maybe_pointer exp =
  filtre scrape exp.exp_env exp.exp_type avec
  | Tconstr(p, args, abbrev) ->
      not (Path.same p Predef.path_int) &&
      not (Path.same p Predef.path_char) &&
      début essaie
        filtre Env.find_type p exp.exp_env avec
        | {type_kind = Type_variant []} -> vrai (* type exn *)
        | {type_kind = Type_variant cstrs} ->
            List.exists (fonc c -> c.Types.cd_args <> []) cstrs
        | _ -> vrai
      avec Not_found -> vrai
        (* This can happen due to e.g. missing -I options,
           causing some .cmi files to be unavailable.
           Maybe we should emit a warning. *)
      fin
  | _ -> vrai

soit array_element_kind env ty =
  filtre scrape env ty avec
  | Tvar _ | Tunivar _ ->
      Pgenarray
  | Tconstr(p, args, abbrev) ->
      si Path.same p Predef.path_int || Path.same p Predef.path_char alors
        Pintarray
      sinon si Path.same p Predef.path_float alors
        Pfloatarray
      sinon si Path.same p Predef.path_string
           || Path.same p Predef.path_array
           || Path.same p Predef.path_nativeint
           || Path.same p Predef.path_int32
           || Path.same p Predef.path_int64 alors
        Paddrarray
      sinon début
        essaie
          filtre Env.find_type p env avec
            {type_kind = Type_abstract} ->
              Pgenarray
          | {type_kind = Type_variant cstrs}
            quand List.for_all (fonc c -> c.Types.cd_args = []) cstrs ->
              Pintarray
          | {type_kind = _} ->
              Paddrarray
        avec Not_found ->
          (* This can happen due to e.g. missing -I options,
             causing some .cmi files to be unavailable.
             Maybe we should emit a warning. *)
          Pgenarray
      fin
  | _ ->
      Paddrarray

soit array_kind_gen ty env =
  filtre scrape env ty avec
  | Tconstr(p, [elt_ty], _) | Tpoly({desc = Tconstr(p, [elt_ty], _)}, _)
    quand Path.same p Predef.path_array ->
      array_element_kind env elt_ty
  | _ ->
      (* This can happen with e.g. Obj.field *)
      Pgenarray

soit array_kind exp = array_kind_gen exp.exp_type exp.exp_env

soit array_pattern_kind pat = array_kind_gen pat.pat_type pat.pat_env

soit bigarray_decode_type env ty tbl dfl =
  filtre scrape env ty avec
  | Tconstr(Pdot(Pident mod_id, type_name, _), [], _)
    quand Ident.name mod_id = "Bigarray" ->
      début essaie List.assoc type_name tbl avec Not_found -> dfl fin
  | _ ->
      dfl

soit kind_table =
  ["float32_elt", Pbigarray_float32;
   "float64_elt", Pbigarray_float64;
   "int8_signed_elt", Pbigarray_sint8;
   "int8_unsigned_elt", Pbigarray_uint8;
   "int16_signed_elt", Pbigarray_sint16;
   "int16_unsigned_elt", Pbigarray_uint16;
   "int32_elt", Pbigarray_int32;
   "int64_elt", Pbigarray_int64;
   "int_elt", Pbigarray_caml_int;
   "nativeint_elt", Pbigarray_native_int;
   "complex32_elt", Pbigarray_complex32;
   "complex64_elt", Pbigarray_complex64]

soit layout_table =
  ["c_layout", Pbigarray_c_layout;
   "fortran_layout", Pbigarray_fortran_layout]

soit bigarray_kind_and_layout exp =
  filtre scrape exp.exp_env exp.exp_type avec
  | Tconstr(p, [caml_type; elt_type; layout_type], abbrev) ->
      (bigarray_decode_type exp.exp_env elt_type kind_table Pbigarray_unknown,
       bigarray_decode_type exp.exp_env layout_type layout_table
                            Pbigarray_unknown_layout)
  | _ ->
      (Pbigarray_unknown, Pbigarray_unknown_layout)
