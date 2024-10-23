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

module Shape = struct
  let intersection sh1 sh2 =
    let inter_any inter any1 any2 =
      match any1, any2 with
      | Any, other | other, Any ->
          other
      | Those a, Those b -> Those (inter a b)
    in
    {
      imms = inter_any ImmSet.inter sh1.imms sh2.imms;
      blocks =
        inter_any (fun tm1 tm2 ->
          TagMap.merge (fun _tag s1 s2 ->
            match s1, s2 with
            | None, _ | _, None -> None
            | Some s1, Some s2 -> Some (inter_any SizeSet.inter s1 s2)
          ) tm1 tm2
        ) sh1.blocks sh2.blocks;
    }

  let is_empty sh =
    let empty_any is_empty = function
      | Any -> false
      | Those s -> is_empty s
    in
    let empty_tag_map =
      TagMap.for_all (fun _tag -> empty_any SizeSet.is_empty)
    in
    empty_any ImmSet.is_empty sh.imms
    && empty_any empty_tag_map sh.blocks

  let union sh1 sh2 =
    let imms = Or_any.mon_map2 ImmSet.union sh1.imms sh2.imms in
    let blocks =
      Or_any.mon_bind2 (fun bs1 bs2 ->
        let any_count = ref 0 in
        let tag_map =
          TagMap.union (fun _tag s1 s2 ->
            let s = Or_any.mon_map2 SizeSet.union s1 s2 in
            (if s = Any then incr any_count);
            Some s
          ) bs1 bs2
        in
        if !any_count = 256 then begin
          assert (
            List.init 256 Fun.id
            |> List.for_all (fun i ->
              TagMap.find_opt (Tag i) tag_map = Some Any)
          );
          Any
        end
        else Those tag_map
      ) sh1.blocks sh2.blocks
    in
    { imms; blocks; }

  let any =
    {
      imms = Any;
      blocks = Any;
    }

  let empty =
    {
      imms = Those ImmSet.empty;
      blocks = Those TagMap.empty;
    }

  let any_immediate =
    { empty with imms = Any }

  let imm li =
    let imms = Or_any.Those (ImmSet.of_list li) in
    { empty with imms }

  let block ?size tags =
    let blocks : block_set =
      let size : size_set = match size with
        | None -> Any
        | Some fixed -> Those (SizeSet.singleton (Size fixed))
      in
      Those (TagMap.of_list (List.map (fun tags -> (tags, size)) tags))
    in
    { empty with blocks }

  let float =
    (* Float values have size 1 or 2 depending
       on the architecture. *)
    union
      (block ~size:1 [Tag Obj.double_tag])
      (block ~size:2 [Tag Obj.double_tag])

  let string =
    block [Tag Obj.string_tag]

  let tuple ~size =
    block ?size [Tag 0]

  let array =
    block
      ([Tag 0]
       @ if Config.flat_float_array then []
       else [Tag Obj.double_array_tag])

  let floatarray =
    block [Tag Obj.double_array_tag]

  let \#function =
    block [Tag Obj.closure_tag; Tag Obj.infix_tag]

  let \#object =
    block [Tag Obj.object_tag]

  let \#lazy arg_shape =
    (* Once lazy values are forced, their Forward_tag block can be 'cut
       short', and then they are represented exactly like the underlying
       type.

       Note that this union may be non-disjoint: it is okay if the
       underlying type can itself have lazy tags, shortcutting will be
       disabled by a runtime check.  *)
    union arg_shape
      (block [Tag Obj.lazy_tag; Tag Obj.forcing_tag; Tag Obj.forward_tag])

  let continuation =
    block [Tag Obj.cont_tag]

  let extensible_variant =
    (* constant extensible constructors have tag Obj.object_tag,
       non-constant constructors have tag 0. *)
    block [Tag 0; Tag Obj.object_tag]

  let polymorphic_variant ~has_consts ~has_nonconsts =
    (* constant polymorphic variants are immediates,
       non-constant variants have tag 0. *)
    union
      (if has_consts then any_immediate else empty)
      (if has_nonconsts then block [Tag 0] else empty)

  let abstract ~size =
    block ?size [Tag Obj.abstract_tag]

  let custom ~size =
    block ?size [Tag Obj.custom_tag]
end

let constructor_tag ~loc n =
  if (n < 0 || n > Obj.last_non_constant_constructor_tag) then
    (* TODO: turn into a proper error with a registered printer. *)
    Location.raise_errorf ~loc
      "The shape (constr ~tag:n) can only be used for regular block \
       constructor, ~tag:%d is outside valid range." n;
  Tag n

let rec of_shape_name loc : Asttypes.shape_name -> shape = function
  | Any -> Shape.any
  | Imm n -> Shape.imm [Imm n]
  | Constructor { tag; size } -> Shape.block ?size [constructor_tag ~loc tag]
  | Int -> Shape.any_immediate
  | Float -> Shape.float
  | String -> Shape.string
  | Tuple { size } -> Shape.tuple ~size
  | Array -> Shape.array
  | Floatarray -> Shape.floatarray
  | Function -> Shape.\#function
  | Object -> Shape.\#object
  | Lazy arg_shape_names ->
      let arg_shape =
        List.fold_left (fun shape name ->
          Shape.union shape (of_shape_name loc name)
        ) Shape.empty arg_shape_names
      in
      Shape.\#lazy arg_shape
  | Continuation -> Shape.continuation
  | Extensible_variant -> Shape.extensible_variant
  | Polymorphic_variant { has_consts; has_nonconsts } ->
      Shape.polymorphic_variant ~has_consts ~has_nonconsts
  | Abstract { size } -> Shape.abstract ~size
  | Custom { size } -> Shape.custom ~size

let rec of_type_expr env ty fuel =
  match Types.get_desc ty with
  | Tvar _ | Tunivar _ ->
      (* FIXME: variables that are universally quantified
         (including type parameters) should get [any], but GADT
         variables that are existentially quantified should get
         [poison] instead -- they are not separated. *)
      Shape.any
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
  | Ttuple li ->
      Shape.tuple ~size:(Some (List.length li))
  | Tarrow _ ->
      Shape.\#function
  | Tpackage _ ->
      Shape.tuple ~size:None
  | Tobject _ ->
      Shape.\#object
  | Tvariant row ->
      let has_consts, has_nonconsts =
        if not (Types.row_closed row) then true, true
        else begin
          (* Note: for closed polymorphic variants, we could refine
             our shape by listing specific immediates for constant
             constructors (the hashes of the name). This would allow
             merging two unboxed constructors containing disjoint
             constant polymorphic variants. *)
          let consts = ref false in
          let nonconsts = ref false in
          let notify (_label, row_field) =
            match Types.row_field_repr row_field with
            | Types.Rpresent None -> consts := true
            | Types.Rpresent (Some _) -> nonconsts := true
            | Types.Rabsent -> ()
            | Types.Reither (is_const, _, _) ->
                (if is_const then consts else nonconsts) := true
          in
          List.iter notify (Types.row_fields row);
          !consts, !nonconsts
        end
      in
      Shape.polymorphic_variant ~has_consts ~has_nonconsts
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
  Shape.any

and of_predef_abstract_type env tconstr args fuel =
  match tconstr with
  | `Int | `Char -> Shape.any_immediate
  | `Array -> Shape.array
  | `Float -> Shape.float
  | `Floatarray -> Shape.floatarray
  | `Nativeint | `Int32 | `Int64 ->
      Shape.custom ~size:(Some 1)
  | `String | `Bytes ->
      Shape.string
  | `Continuation ->
      Shape.continuation
  | `Extension_constructor ->
      Shape.block ~size:1 [Tag Obj.object_tag]
  | `Lazy_t ->
      (* Once lazy values are forced, their Forward_tag block can be
         'cut short', and then they are represented exactly like the
         underlying type.

         Note that this union may be non-disjoint: it is okay if the
         underlying type can itself have lazy tags, shortcutting will
         be disabled by a runtime check.  *)
      let ty = match args with [ty] -> ty | _ -> assert false in
      Shape.\#lazy (of_type_expr env ty fuel)

and of_typedescr env p ty_descr ty_decl ~args fuel =
  let of_type_expr_with_params ty =
    (* We instantiate the formal type variables with the
       type expression parameters at use site. *)
    let params = ty_decl.type_params in
    let ty = Ctype.apply env params ty args in
    of_type_expr env ty fuel
  in
  match ty_descr with
  | Type_record (lbls, Record_regular) ->
      Shape.tuple ~size:(Some (List.length lbls))
  | Type_record (_lbls, Record_float) ->
      Shape.floatarray
  | Type_record (fields, Record_unboxed _) ->
      (* an [@@unboxed] record must have exactly one field *)
      begin match fields with
      | [{lbl_arg = ty; _}] -> of_type_expr_with_params ty
      | _ -> assert false
      end
  | Type_record (lbls, Record_inlined tag) ->
      Shape.block ~size:(List.length lbls) [Tag tag]
  | Type_record (lbls, Record_extension _) ->
      (* non-constant extension constructors have tag 0,
         and one additional argument storing the
         extension constructor dynamic value. *)
      Shape.block ~size:(1 + List.length lbls) [Tag 0]
  | Type_open ->
      Shape.extensible_variant
  | Type_variant (cstrs, Variant_unboxed) ->
      (* an [@@unboxed] variant must have exactly one constructor
         with one parameter *)
      begin match cstrs with
      | [{cstr_args = [ty]; _}] -> of_type_expr_with_params ty
      | _ -> assert false
      end
  | Type_variant ([], Variant_regular) ->
      Shape.empty
  | Type_variant (cstr_descrs, Variant_regular) ->
      (* Here we use the {!union} function to compute the head shape
         of the variant, without trying to enforce that the union is
         disjoint. Indeed, we already know that it must be disjoint,
         otherwise it would have been rejected at declaration time by
         the {!check_typedecl} function below. *)
      let of_cstr_descr descr = of_regular_cstr_description env descr fuel in
      List.map of_cstr_descr cstr_descrs
      |> List.fold_left Shape.union Shape.empty
  | Type_abstract _ ->
      match ty_decl.type_manifest with
      | Some ty -> of_type_expr_with_params ty
      | None ->
      match ty_decl.type_immediate with
      | Always -> Shape.any_immediate
      | Always_on_64bits ->
          (* TODO maybe refine? *)
          Shape.any
      | Unknown ->
          of_unknown_type env p args

and of_regular_cstr_description env descr fuel =
  match descr.cstr_tag with
  | Cstr_constant n -> Shape.imm [Imm n]
  | Cstr_block tag ->
      Shape.block ~size:descr.cstr_arity [Tag tag]
  | Cstr_unboxed descr ->
      of_unboxed_cstr_description env descr fuel
  | Cstr_extension _ ->
      (* cannot occur in regular variants *)
      assert false

and of_unboxed_cstr_description env descr fuel =
  try Misc.Cached.force descr (fun ty -> of_type_expr env ty fuel)
  with Misc.Cached.Forcing_race -> Shape.any

let initial_fuel =
  (* choice of fuel: see
     {!Typedecl_unboxed.get_unboxed_type_representation} *)
  100

let of_type_path env path =
  let decl = Env.find_type path env in
  let ty = Btype.newgenty (Tconstr (path, decl.type_params, ref Mnil)) in
  of_type_expr env ty initial_fuel

let of_regular_cstr_description env descr =
  of_regular_cstr_description env descr initial_fuel

let of_unboxed_cstr_description env descr =
  of_unboxed_cstr_description env descr initial_fuel

let check_typedecl env (path, decl) =
  match Env.find_type_descrs path env with
  | exception Not_found -> assert false
  | Type_open | Type_record _ -> ()
  | Type_abstract _ -> ()
  | Type_variant (_, Variant_unboxed) -> ()
  | Type_variant (cstrs, Variant_regular) ->
      let is_unboxed cstr =
        match cstr.cstr_tag with
        | Cstr_constant _ | Cstr_block _ | Cstr_extension _ -> false
        | Cstr_unboxed _ -> true
      in
      let has_unboxed_cstr = List.exists is_unboxed cstrs in
      if not has_unboxed_cstr then ()
      else begin
        let cstr_shapes =
          Array.of_list @@ List.map (fun descr ->
            of_regular_cstr_description env descr
          ) cstrs
        in
        (* Boxed constructors, by construction, cannot have overlapping representations,
           as they get assigned distinct immediates or tags.

           If an overlap arises, it is necessarily between an unboxed
           constructor an another constructor (boxed or unboxed). We
           check all pairs of an unboxed constructor and another
           constructor. *)
        List.iteri (fun i cstr1 ->
          if is_unboxed cstr1 then
            List.iteri (fun j cstr2 ->
              let sh1, sh2 = cstr_shapes.(i), cstr_shapes.(j) in
              if i <> j && not Shape.(is_empty (intersection sh1 sh2)) then
                (* TODO: define a proper error with an error printer. *)
                Location.raise_errorf ~loc:decl.type_loc
                  "@[Constructors %s and %s have overlapping representations.\
                     @;<1 2>shape of %s: %a\
                     @;<1 2>shape of %s: %a\
                   @]"
                  cstr1.cstr_name cstr2.cstr_name
                  cstr1.cstr_name Print_head_shape.doc sh1
                  cstr2.cstr_name Print_head_shape.doc sh2
            ) cstrs
        ) cstrs
      end
