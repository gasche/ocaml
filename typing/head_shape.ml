(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*   Gabriel Scherer, projet Partout, INRIA Saclay                        *)
(*   Nicolas Chataing, ENS Paris                                          *)
(*                                                                        *)
(*   Copyright 2021 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

open Types
open Data_types
open Head_shape_types

type t = Head_shape_types.t

let any =
  {
    imms = Any;
    blocks = Any;
  }

let any_immediate =
  {
    imms = Any;
    blocks = Those TagSet.empty;
  }

let empty =
  {
    imms = Those ImmSet.empty;
    blocks = Those TagSet.empty;
  }

let union sh1 sh2 =
  let imms = Or_any.mon_map2 ImmSet.union sh1.imms sh2.imms in
  let blocks = Or_any.mon_map2 TagSet.union sh1.blocks sh2.blocks in
  { imms; blocks; }

let imm_list li = Or_any.Those (ImmSet.of_list li)

let tag_list tags : block_set = Or_any.Those (TagSet.of_list tags)

let imm_shape imms =
  { empty with imms = imm_list imms }
let block_shape tags =
  { empty with blocks = tag_list tags }

let rec of_type_expr env ty fuel =
  match Types.get_desc ty with
  | Tvar _ | Tunivar _ ->
      (* FIXME: variables that are universally quantified
         (including type parameters) should get [any], but GADT
         variables that are existentially quantified should get
         [poison] instead -- they are not separated. *)
      any
  | Tconstr (p, args, _abbrev) ->
      (* Both [of_predef_abstract_type] and [of_typedescr] may loop over
         infinite types or recursive expansions; decrease fuel now. *)
      if fuel = 0 then of_unknown_type env p args else
      let fuel = fuel - 1 in
      begin match Predef.find_type_constr p with
      | Some (#Predef.abstract_type_constr as tconstr) ->
          of_predef_abstract_type env tconstr args fuel
      | None | Some #Predef.data_type_constr ->
      match Env.find_type_descrs p env, Env.find_type p env with
      | descr, decl ->
          of_typedescr env p descr decl ~args fuel
      | exception Not_found ->
          of_unknown_type env p args
      end
  | Ttuple _ ->
      block_shape [Tag 0]
  | Tarrow _ ->
      block_shape [Tag Obj.closure_tag; Tag Obj.infix_tag]
  | Tpackage _ ->
      block_shape [Tag 0]
  | Tobject _ ->
      (* TODO refine someday *)
      any
  | Tvariant _ ->
      (* constant polymorphic variants are immediates,
         non-constant variants have tag 0 *)
      union any_immediate (block_shape [Tag 0])
  | Tpoly (ty, _vars) ->
      of_type_expr env ty fuel
  | Tlink _ | Tsubst _ | Tfield _ | Tnil ->
      (* cannot be returned by [get_desc] *)
      assert false

and of_unknown_type env p args =
  (* FIXME: if one of the parameters contains a non-separated variable,
     then this unknown type should be considered non-separated as well.
     (It may be a projection into this parameter.)
     This corresponds to the DeepSep case of the separability analysis. *)
  ignore (env, p, args);
  any

and of_predef_abstract_type env tconstr args fuel =
  match tconstr with
  | `Int | `Char -> any_immediate
  | `Array ->
      block_shape
        ([Tag 0]
         @ if Config.flat_float_array then []
         else [Tag Obj.double_array_tag])
  | `Float ->
      block_shape [Tag Obj.double_tag]
  | `Floatarray ->
      block_shape [Tag Obj.double_array_tag]
  | `Nativeint | `Int32 | `Int64 ->
      block_shape [Tag Obj.custom_tag]
  | `String | `Bytes ->
      block_shape [Tag Obj.string_tag]
  | `Continuation ->
      block_shape [Tag Obj.cont_tag]
  | `Extension_constructor ->
      block_shape [Tag Obj.object_tag]
  | `Lazy_t ->
      (* Once lazy values are forced, their Forward_tag block can be
         'cut short', and then they are represented exactly like the
         underlying type.

         Note that this union may be non-disjoint: it is okay if the
         underlying type can itself have lazy tags, shortcutting will
         be disabled by a runtime check.  *)
      let ty = match args with [ty] -> ty | _ -> assert false in
      union
        (block_shape [Tag Obj.lazy_tag; Tag Obj.forcing_tag; Tag Obj.forward_tag])
        (of_type_expr env ty fuel)

and of_typedescr env p ty_descr ty_decl ~args fuel =
  let of_type_expr_with_params ty =
    (* We instantiate the formal type variables with the
       type expression parameters at use site. *)
    let params = ty_decl.type_params in
    let ty = Ctype.apply env params ty args in
    of_type_expr env ty fuel
  in
  match ty_descr with
  | Type_record (_, Record_regular) ->
      block_shape [Tag 0]
  | Type_record (_, Record_float) ->
      block_shape [Tag Obj.double_array_tag]
  | Type_record (fields, Record_unboxed _) ->
      (* an [@@unboxed] record must have exactly one field *)
      begin match fields with
      | [{lbl_arg = ty; _}] -> of_type_expr_with_params ty
      | _ -> assert false
      end
  | Type_record (_lbls, Record_inlined tag) ->
      block_shape [Tag tag]
  | Type_record (_lbls, Record_extension _) ->
      (* non-constant extension constructors have tag 0 *)
      block_shape [Tag 0]
  | Type_open ->
      (* constant constructors have tag Obj.object_tag,
         non-constant constructors have tag 0 *)
      block_shape [Tag 0; Tag Obj.object_tag]
  | Type_variant (cstrs, Variant_unboxed) ->
      (* an [@@unboxed] variant must have exactly one constructor
         with one parameter *)
      begin match cstrs with
      | [{cstr_args = [ty]; _}] -> of_type_expr_with_params ty
      | _ -> assert false
      end
  | Type_variant ([], Variant_regular) ->
      empty
  | Type_variant (cstr_descrs, Variant_regular) ->
      let of_cstr_descr descr = of_regular_cstr_description env descr fuel in
      List.map of_cstr_descr cstr_descrs
      |> List.fold_left union empty
  | Type_abstract _ ->
      match ty_decl.type_manifest with
      | Some ty -> of_type_expr_with_params ty
      | None ->
          match ty_decl.type_immediate with
          | Always -> any_immediate
          | Always_on_64bits ->
              (* TODO maybe refine? *)
              any
          | Unknown ->
              of_unknown_type env p args

and of_regular_cstr_description env descr fuel =
  ignore (env, fuel);
  match descr.cstr_tag with
  | Cstr_constant n -> imm_shape [Imm n]
  | Cstr_block tag ->
      block_shape [Tag tag]
  | Cstr_unboxed | Cstr_extension _ ->
      (* cannot occur in regular variants *)
      assert false

let initial_fuel =
  (* choice of fuel: see
     {!Typedecl_unboxed.get_unboxed_type_representation} *)
  100

let of_type_path env path =
  let decl = Env.find_type path env in
  let ty = Btype.newgenty (Tconstr (path, decl.type_params, ref Mnil)) in
  of_type_expr env ty initial_fuel
