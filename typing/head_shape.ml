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

type t = shape

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

let of_attributes loc attrs =
  match Builtin_attributes.find_shapes attrs with
  | None -> None
  | Some shapes ->
      Some (
        List.fold_left (fun acc shape ->
          Shape.union acc (of_shape_name loc shape)
        ) Shape.empty shapes
      )

let dbg = false

module TypeSet = Btype.TypeSet
let existentials = ref TypeSet.empty
let is_existential ty =
  TypeSet.mem ty !existentials
let notify_existential ty =
  if dbg then
    Format.eprintf "notify existential: %a@."
      Rawprinttyp.type_expr ty;
  existentials := TypeSet.add ty !existentials

let rec of_type_expr env ty fuel =
  match Types.get_desc ty with
  | Tvar _ | Tunivar _ ->
      if is_existential ty
      then Shape.poison
      else Shape.any
  | Tconstr (p, args, _abbrev) ->
      (* Both [of_predef_abstract_type] and [of_typedescr] may loop over
         infinite types or recursive expansions; decrease fuel now. *)
      if fuel = 0 then Shape.any else
      let fuel = fuel - 1 in
      begin match Predef.find_type_constr p with
      | Some (#Predef.abstract_type_constr as tconstr) ->
          of_predef_abstract_type env tconstr args fuel
      | None | Some #Predef.data_type_constr ->
      match Env.find_type_descrs p env, Env.find_type p env with
      | descr_kind, decl ->
          let descr = { decl with type_kind = descr_kind } in
          of_typedescr env p descr ~args fuel
      | exception Not_found ->
          of_unknown_type env p args fuel
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

and of_unknown_type env _p args fuel =
  let arg_shapes =
    List.map (fun ty -> of_type_expr env ty fuel) args in
  if List.exists (fun sh -> not sh.separated) arg_shapes
  then Shape.poison
  else Shape.any

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

and of_typedescr env p ty_descr ~args fuel =
  let ty_descr = Ctype.instance_description ty_descr in
  if dbg then
    Format.eprintf "args: %a@."
      (Format.pp_print_list ~pp_sep:Format.pp_print_space
         Rawprinttyp.type_expr) args;
  List.iter2 (Ctype.unify env) ty_descr.type_params args;
  match ty_descr.type_kind with
  | Type_record (lbls, Record_regular) ->
      Shape.tuple ~size:(Some (List.length lbls))
  | Type_record (_lbls, Record_float) ->
      Shape.floatarray
  | Type_record (fields, Record_unboxed _) ->
      (* an [@@unboxed] record must have exactly one field *)
      begin match fields with
      | [{lbl_arg = ty; _}] -> of_type_expr env ty fuel
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
      | [{cstr_args = [ty]; _}] -> of_type_expr env ty fuel
      | _ -> assert false
      end
  | Type_variant ([], Variant_regular) ->
      Shape.empty
  | Type_variant (cstrs, Variant_regular) ->
      (* Here we use the {!union} function to compute the head shape
         of the variant, without trying to enforce that the union is
         disjoint. Indeed, we already know that it must be disjoint,
         otherwise it would have been rejected at declaration time by
         the {!check_typedecl} function below. *)
      let of_cstr cstr_descr =
        of_regular_cstr_description env cstr_descr fuel in
      List.map of_cstr cstrs
      |> List.fold_left Shape.union Shape.empty
  | Type_abstract _ ->
      match ty_descr.type_manifest with
      | Some ty -> of_type_expr env ty fuel
      | None ->
      let from_immediacy =
        match ty_descr.type_immediate with
        | Always -> Some Shape.any_immediate
        | Always_on_64bits ->
            (* TODO maybe refine? *)
            None
        | Unknown ->
            None
      in
      let from_attributes =
        of_attributes ty_descr.type_loc ty_descr.type_attributes
      in
      match from_immediacy, from_attributes with
      | Some sh1, Some sh2 -> Shape.inter sh1 sh2
      | Some sh, None | None, Some sh -> sh
      | None, None ->
        of_unknown_type env p args fuel

and of_regular_cstr_description env descr fuel =
  List.iter notify_existential descr.cstr_existentials;
  match descr.cstr_tag with
  | Cstr_constant n -> Shape.imm [Imm n]
  | Cstr_block tag ->
      Shape.block ~size:descr.cstr_arity [Tag tag]
  | Cstr_unboxed (ty, _descr) ->
      of_type_expr env ty fuel
  | Cstr_extension _ ->
      (* cannot occur in regular variants *)
      assert false

let initial_fuel =
  (* choice of fuel: see
     {!Typedecl_unboxed.get_unboxed_type_representation} *)
  100

let of_type_expr env ty =
  of_type_expr env ty initial_fuel

let of_type_path env path =
  let decl = Env.find_type path env in
  let decl = Ctype.instance_declaration decl in
  let ty = Btype.newgenty (Tconstr (path, decl.type_params, ref Mnil)) in
  of_type_expr env ty

let of_regular_cstr_description env descr =
  of_regular_cstr_description env descr initial_fuel

let of_unboxed_cstr_description env descr =
  try Misc.Cached.force descr (fun ty -> of_type_expr env ty)
  with Misc.Cached.Forcing_race ->
    Misc.fatal_error "of_unboxed_cstr_description"

let cstr_is_unboxed cstr =
  match cstr.cstr_tag with
  | Cstr_constant _ | Cstr_block _ | Cstr_extension _ -> false
  | Cstr_unboxed _ -> true

let find_constructors_with_unboxed = function
  | Type_open | Type_record _
  | Type_abstract _
  | Type_variant (_, Variant_unboxed) -> None
  | Type_variant (cstrs, Variant_regular) ->
      let has_unboxed_cstr = List.exists cstr_is_unboxed cstrs in
      if has_unboxed_cstr then Some cstrs
      else None

let check_typedecl_conflicts ~loc env cstrs =
  (* Boxed constructors, by construction, cannot have overlapping representations,
     as they get assigned distinct immediates or tags.

     If an overlap arises, it is necessarily between an unboxed
     constructor an another constructor (boxed or unboxed). We
     check all pairs of an unboxed constructor and another
     constructor. *)
  let cstr_shapes =
    Array.of_list @@ List.map (fun descr ->
      of_regular_cstr_description env descr
    ) cstrs
  in
  List.iteri (fun i cstr1 ->
    match cstr1.cstr_tag with
    | Cstr_constant _ | Cstr_block _ | Cstr_extension _ -> ()
    | Cstr_unboxed (_ty, unboxed_descr) ->
      let sh1 = of_unboxed_cstr_description env unboxed_descr in
      List.iteri (fun j cstr2 ->
        let sh2 = cstr_shapes.(j) in
        if i <> j && not Shape.(is_empty (inter sh1 sh2)) then
          (* TODO: define a proper error with an error printer. *)
          Location.raise_errorf ~loc
            "@[Constructors %s and %s have overlapping representations.\
               @;<1 2>shape of %s: %a\
               @;<1 2>shape of %s: %a\
             @]"
            cstr1.cstr_name cstr2.cstr_name
            cstr1.cstr_name Print_head_shape.doc sh1
            cstr2.cstr_name Print_head_shape.doc sh2
      ) cstrs
  ) cstrs

let check_typedecl_separated ~loc get_shape =
  let shape = get_shape () in
  if not shape.separated then
    Location.raise_errorf ~loc
      "@[This type declaration is non-separated, \
         it contains both float and non-float values.@]"

let check_typedecl_constraint ~loc decl get_shape =
  match of_attributes loc decl.type_attributes with
  | Some expected_shape ->
      let actual_shape = get_shape () in
      if not (Shape.subset actual_shape expected_shape) then
        Location.raise_errorf ~loc
          "@[In this type declaration, the actual head shape does not \
           match the expected type shape.@]"
  | None -> ()

(* We check three soundness properties on head shapes:
   - If unboxed constructors are used, they must not introduce
     representation conflicts (two distinct source terms that
     have the same representation).
   - If unboxed constructors are used, they must not introduce
     non-separated types.
   - If a shape annotation is present, the actual shape of the type
     must be a subset of the annotated shape.

   The implementation tries to be zero-cost: it computes nothing at
   all unless unboxed constructors or shape annotations are used.
*)
let check_typedecl env (path, decl) =
  let loc = decl.type_loc in
  let descr =
    try Env.find_type_descrs path env
    with Not_found -> assert false
  in
  let decl =
    Ctype.instance_description { decl with type_kind = descr } in
  let get_shape () = of_type_path env path in
  begin match find_constructors_with_unboxed decl.type_kind with
  | None -> ()
  | Some cstrs ->
      check_typedecl_conflicts ~loc env cstrs;
      check_typedecl_separated ~loc get_shape;
  end;
  check_typedecl_constraint ~loc decl get_shape;
