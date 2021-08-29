(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*   Gabriel Scherer, projet Parsifal, INRIA Saclay                       *)
(*   Rodolphe Lepigre, projet Deducteam, INRIA Saclay                     *)
(*                                                                        *)
(*   Copyright 2018 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

open Types

type t =
  | Unavailable
  | This of type_expr
  | Only_on_64_bits of type_expr

(* We use the Ctype.expand_head_opt version of expand_head to get access
   to the manifest type of private abbreviations. *)
let rec get_unboxed_type_representation env ty fuel =
  if fuel < 0 then Unavailable else
  let ty = Ctype.expand_head_opt env ty in
  match get_desc ty with
  | Tconstr (p, args, _) ->
    begin match Env.find_type p env with
    | exception Not_found -> This ty
    | {type_immediate = Always; _} ->
        This Predef.type_int
    | {type_immediate = Always_on_64bits; _} ->
        Only_on_64_bits Predef.type_int
    | {type_params; type_kind =
         Type_record ([{ld_type = ty2; _}], Record_unboxed _)
       | Type_variant ([{cd_args = Cstr_tuple [ty2]; _}], Variant_unboxed)
       | Type_variant ([{cd_args = Cstr_record [{ld_type = ty2; _}]; _}],
                       Variant_unboxed)}
      ->
        let ty2 = match get_desc ty2 with Tpoly (t, _) -> t | _ -> ty2 in
        get_unboxed_type_representation env
          (Ctype.apply env type_params ty2 args) (fuel - 1)
    | _ -> This ty
    end
  | _ -> This ty

let get_unboxed_type_representation env ty =
  (* Do not give too much fuel: PR#7424 *)
  get_unboxed_type_representation env ty 100
;;

type primitive_type =
  | Int
  | Float
  | String
  | Bytes
  | Array
  | Floatarray
  | Lazy
  | Custom

let match_primitive_type p =
  let open Predef in
  let tbl = [
    (path_int, Int);
    (path_float, Float);
    (path_string, String);
    (path_bytes, Bytes);
    (path_array, Array);
    (path_floatarray, Floatarray);
    (path_lazy_t, Lazy);
    (path_nativeint, Custom);
    (path_int32, Custom);
    (path_int64, Custom);
  ] in
  List.find_opt (fun (p', _) -> Path.same p p') tbl |> Option.map snd

module Head_shape = struct

  exception Conflict
  (* TODO: add more information to be able to display proper
     error messages. *)

  type t = head_shape

  let pp_shape ppf = function
    | Shape_any -> Format.fprintf ppf "Shape_any"
    | Shape_set l ->
        Format.fprintf ppf "Shape_set [%a]"
          (Format.pp_print_list
            ~pp_sep:(fun ppf () -> Format.fprintf ppf "; ")
            Format.pp_print_int) l

  let pp ppf {head_imm; head_blocks} =
    Format.fprintf ppf "{head_imm = %a; head_blocks = %a}"
      pp_shape head_imm
      pp_shape head_blocks

  let any_shape = { head_imm = Shape_any; head_blocks = Shape_any }

  let empty_shape = { head_imm = Shape_set []; head_blocks = Shape_set [] }

  let block_shape tags =
    { head_imm = Shape_set []; head_blocks = Shape_set tags }

  let cstrs_shape ~num_consts ~num_nonconsts =
    let int_list n = List.init n Fun.id in
    {
      head_imm = Shape_set (int_list num_consts);
      head_blocks = Shape_set (int_list num_nonconsts)
    }

  let disjoint_union hd1 hd2 =
    let union s1 s2 = match s1, s2 with
    | Shape_any, Shape_set [] | Shape_set [], Shape_any -> Shape_any
    | Shape_any, _ | _, Shape_any -> raise Conflict
    | Shape_set l1, Shape_set l2 ->
        (* invariant : l1 and l2 are sorted *)
        let rec merge l1 l2 = match l1, l2 with
        | [], l | l, [] -> l
        | x :: xx, y :: yy ->
            if x = y then raise Conflict
            else if x < y then x :: (merge xx l2)
            else y :: (merge l1 yy)
        in Shape_set (merge l1 l2)
    in
    {
      head_imm = union hd1.head_imm hd2.head_imm;
      head_blocks = union hd1.head_blocks hd2.head_blocks
    }

  module Callstack = struct
    type t = Path.t list

    module TypeMap = Btype.TypeMap
    type map = t TypeMap.t

    let visit p callstack : t =
      p :: callstack

    let visited p callstack =
      List.exists (Path.same p) callstack

    let head (callstack_map : map) ty =
      TypeMap.find ty callstack_map

    let rec extend callstack_map ty new_callstack =
      if TypeMap.mem ty callstack_map then callstack_map
      else
        let callstack_map = TypeMap.add ty new_callstack callstack_map in
        Btype.fold_type_expr (fun callstack_map ty' ->
          extend callstack_map ty' new_callstack
        ) callstack_map ty

    let fill ty callstack = extend TypeMap.empty ty callstack
  end

  (* Useful to interactively debug 'of_type_expr' below. *)
  let _print_annotations ty callstack_map =
    Format.eprintf "@[CALLSTACK(%a): @["
      Printtyp.type_expr ty;
    let pp_sep ppf () = Format.fprintf ppf ",@ " in
    Callstack.TypeMap.to_rev_seq callstack_map |> Seq.iter
      (fun (ty, callstack) ->
        Format.eprintf "@ @[%a@ [%a]@]"
          Printtyp.type_expr (Types.Transient_expr.type_expr ty)
          (Format.pp_print_list ~pp_sep Printtyp.path) callstack
      );
    Format.eprintf "@]@]@.";
    ()

  let check_annotated ty callstack =
    let hash = Btype.TypeHash.create 42 in
    let rec loop ty =
      if Btype.TypeHash.mem hash ty then ()
      else begin
        Btype.TypeHash.add hash ty ();
        assert (Btype.TypeMap.mem ty callstack);
        Btype.iter_type_expr loop ty;
      end
    in loop ty

  let ty_of_poly ty = match get_desc ty with
  | Tpoly (t, _) -> t
  | _ -> ty

  let of_primitive_type = function
    | Int -> { head_imm = Shape_any; head_blocks = Shape_set [] }
    | Float -> block_shape [Obj.double_tag]
    | String
    | Bytes -> block_shape [Obj.string_tag]
    | Array ->
        block_shape
          (if Config.flat_float_array then [0]
           else [0; Obj.double_array_tag])
    | Floatarray -> block_shape [Obj.double_array_tag]
    | Lazy -> any_shape
    (* Lazy values can 'shortcut' the lazy block, and thus have many
       different tags. When Config.flat_float_array, they
       cannot be floats, so we might want to refine that if there
       are strong use-cases. *)
    | Custom -> block_shape [Obj.custom_tag]

  let rec of_type_expr env ty callstack_map =
    (* TODO : try the Ctype.expand_head_opt version here *)
    check_annotated ty callstack_map;
    match get_desc ty with
    | Tvar _ | Tunivar _ -> any_shape
    | Tconstr (p, args, _abbrev) ->
        begin match match_primitive_type p with
        | Some prim_type -> of_primitive_type prim_type
        | None ->
            let head_callstack = Callstack.head callstack_map ty in
            if Callstack.visited p head_callstack then
              let loc =
                match Env.find_type p env with
                | decl -> Some decl.type_loc
                | exception Not_found -> None in
              Location.raise_errorf ?loc
                "Cyclic type expansion during [@unboxed] verification.@ \
                 %a appears unboxed at the head of its own definition."
                Path.print p
            else match Env.find_type_descrs p env, Env.find_type p env with
            | exception Not_found -> any_shape
            | descr, decl ->
                of_typedescr env descr decl ~args callstack_map
                  (Callstack.visit p head_callstack)
        end
    | Ttuple _ -> block_shape [0]
    | Tarrow _ | Tpackage _ | Tobject _ | Tnil | Tvariant _ -> (* XXX *)
        any_shape
    | Tlink _ | Tsubst _ | Tpoly _ | Tfield _ ->
        assert false


  and of_typedescr env ty_descr ty_decl ~args
                   callstack_map new_callstack =
    let of_type_expr_with_params ty =
      (* We instantiate the formal type variables with the
         type expression parameters at use site.

         We build a callstack for this new type by mapping all new
         nodes, corresponding to the spine of 'ty', to the current
         call stack. *)
      let ty = ty_of_poly ty in
      let params = ty_decl.type_params in
      let ty = Ctype.apply env params ty args in
      let callstack_map =
        Callstack.extend callstack_map ty new_callstack in
      of_type_expr env ty callstack_map
    in
    match ty_descr with
    | Type_abstract ->
       begin match ty_decl.type_manifest with
       | None -> any_shape
       | Some ty -> of_type_expr_with_params ty
       end
    | Type_record (_, Record_regular) -> block_shape [0]
    | Type_record (_, Record_float) -> block_shape [Obj.double_array_tag]
    | Type_record (fields, Record_unboxed _) ->
        begin match fields with
        | [{lbl_arg = ty; _}] -> of_type_expr_with_params ty
        | _ -> assert false
        end
    | Type_record (_, Record_inlined _)
    | Type_record (_, Record_extension _) -> failwith "TODO"
    | Type_open -> block_shape [0]
    | Type_variant ([],_) -> empty_shape
    | Type_variant ((fst_descr :: _) as cstr_descrs,_) ->
        (* we compute the shape of all boxed constructors, then the shapes of
           each unboxed constructors *)
        let num_consts = fst_descr.cstr_consts in
        let num_nonconsts = fst_descr.cstr_nonconsts in
        (* the head shape of boxed constructors is equivalent to the nb of
           constant constructors and the nb of non constant constructors *)
        let boxed_shape = cstrs_shape ~num_consts ~num_nonconsts in
        let unboxed_shapes = List.filter_map
          (fun descr ->
            match descr.cstr_tag with
            | Cstr_constant _ | Cstr_block _ | Cstr_extension _ -> None
            | Cstr_unboxed {unboxed_ty; _}->
                Some (of_type_expr_with_params unboxed_ty)
          ) cstr_descrs
        in
        (* now checking that the unboxed constructors are compatible with the
           shape of boxed constructors *)
        List.fold_left disjoint_union boxed_shape unboxed_shapes

  (* Remark on the life cycle of [unboxed_shape] information.

     The [cstr_tag] data that contains [unboxed_shape] is created
     un-initialized by Datarepr, when entering a type declaration
     inside the current typing environment. We cannot compute the
     head-shape at this point: Env depends on Datarepr, so Datarepr
     functions cannot depend on Env.t.

     Type declarations coming from the user code are "checked" after
     being entered in the environment by the Typedecl module; at this
     point the [check_typedecl] function below is called, and the
     [unboxed_shape] information for their unboxed constructors is
     computed and cached at this point. Conflicts are turned into
     proper user-facing errors.

     However, the environment can also be extended by type
     declarations coming from other compilation units (signatures in
     .cmi files), and the head-shape information is not present or
     computed at this point -- we are still within Env, and cannot
     call [of_type] below without creating cyclic dependencies. Note
     that these type-declarations have already been checked when
     compiling their own module, so they must not contain head-shape
     conflicts. In this case a type declaration can leave the
     type-checking phase with its [head_shape] field still
     un-initialized.

     When compiling variant constructors in pattern-matching, we need
     the head-shape information again. It is obtained by calling the
     [get] function below, which will re-compute and cache this
     information if the [unboxed_shape] field is still
     un-initialized. The typing environment used for computation at
     this point is the [pat_env] environment of the pattern-matching,
     which we assume is an extension of the environment used at
     variant constructor declaration time.

     Error handling: [check_typedecl] handles Conflict exceptions by
     showing a proper error to the user -- the error is in the user
     code. On the other hand, [get] and [of_type] must never see
     a shape conflict, as we assume the only un-initialized
     [unboxed_shape] fields come from already-checked imported
     declarations. If a conflict arises in those functions, it is
     a programming error in the compiler codebase: a type declaration
     has somehow been entered in the environment without being
     validated by [check_typedecl] first.
  *)
  let fill_and_get env {unboxed_ty; unboxed_shape} =
    match !unboxed_shape with
    | Some shape -> shape
    | None ->
        let ty = ty_of_poly unboxed_ty in
        let callstacks = Callstack.fill ty [] in
        let shape = of_type_expr env ty callstacks in
        unboxed_shape := Some shape;
        shape

  let fill_cache env unboxed_cache =
    ignore (fill_and_get env unboxed_cache)

  let unboxed_type_data_of_shape shape =
    let bound_of_shape = function
      | Shape_set l -> Some (List.fold_left max 0 l)
      | Shape_any -> None
    in
    let num_of_shape = function
      | Shape_set l -> Some (List.length l)
      | Shape_any -> None
    in
    {
      utd_max_imm_value = bound_of_shape shape.head_imm;
      utd_max_block_tag = bound_of_shape shape.head_blocks;
      utd_unboxed_numconsts = num_of_shape shape.head_imm;
      utd_unboxed_numnonconsts = num_of_shape shape.head_blocks;
    }

  let check_typedecl env (path,decl) =
    match Env.find_type_descrs path env with
    | exception Not_found -> failwith "XXX"
    | Type_variant (cstrs, _repr) -> begin
        try begin
          cstrs |> List.iter (fun {cstr_tag; _} -> match cstr_tag with
            | Cstr_unboxed cache -> fill_cache env cache
            | _ -> ()
          );
          (* now check the whole shape for conflict between variants *)
          let params = decl.type_params in
          let ty = Btype.newgenty (Tconstr (path, params, ref Mnil)) in
          let callstack_map = Callstack.fill ty [] in
          let shape = of_type_expr env ty callstack_map in
          (* Fill the variant data *)
          match cstrs with
            | [] -> ()
            | cstr :: _ ->
                cstr.cstr_unboxed_type_data :=
                  Some (unboxed_type_data_of_shape shape);
          if !Clflags.dump_headshape then
            (* TODO improve the printing to something nicer. *)
            Format.fprintf Format.err_formatter "SHAPE(%a) %a@."
              Path.print path
              pp shape
          end
        with Conflict ->
          (* TODO raise a fatal error with a registered printer,
             instead of what is below. *)
          if !Clflags.dump_headshape then
            Format.fprintf Format.err_formatter "SHAPE(%a) CONFLICT@."
              Path.print path
      end
    | _ -> ()

  let get env unboxed_data =
    match fill_and_get env unboxed_data with
    | exception Conflict ->
        Misc.fatal_error
          "Head_shape.get: check_typedecl should have run first."
    | shape -> shape

  let of_type env path =
    let decl = Env.find_type path env in
    let ty = Btype.newgenty (Tconstr (path, decl.type_params, ref Mnil)) in
    let callstacks = Callstack.fill ty [] in
    try of_type_expr env ty callstacks
    with Conflict ->
        Misc.fatal_error
          "Head_shape.of_type: check_typedecl should have run first."
end
