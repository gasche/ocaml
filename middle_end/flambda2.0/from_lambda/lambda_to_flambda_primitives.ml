(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2019 OCamlPro SAS                                    *)
(*   Copyright 2014--2019 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-30-40-41-42"]

open! Flambda.Import

module C = Lambda_conversions
module H = Lambda_to_flambda_primitives_helpers
module I = Flambda_kind.Standard_int
module I_or_f = Flambda_kind.Standard_int_or_float
module K = Flambda_kind
module L = Lambda
module P = Flambda_primitive

let tag_int (arg : H.expr_primitive) : H.expr_primitive =
  Unary (Box_number Untagged_immediate, Prim arg)
let untag_int (arg : H.simple_or_prim) : H.simple_or_prim =
  Prim (Unary (Unbox_number Untagged_immediate, arg))

let box_float (arg : H.expr_primitive) : H.expr_primitive =
  Unary (Box_number Flambda_kind.Boxable_number.Naked_float, Prim arg)
let unbox_float (arg : H.simple_or_prim) : H.simple_or_prim =
  Prim (Unary (Unbox_number Flambda_kind.Boxable_number.Naked_float, arg))
let box_bint bi (arg : H.expr_primitive) : H.expr_primitive =
  Unary (Box_number (C.boxable_number_of_boxed_integer bi), Prim arg)
let unbox_bint bi (arg : H.simple_or_prim) : H.simple_or_prim =
  Prim (Unary (Unbox_number (C.boxable_number_of_boxed_integer bi), arg))

let tagged_immediate_as_naked_nativeint (arg : H.simple_or_prim)
      : H.simple_or_prim = arg  (* XXX *)

let bint_binary_prim bi prim arg1 arg2 =
  box_bint bi
    (Binary (Int_arith (C.standard_int_of_boxed_integer bi, prim),
             unbox_bint bi arg1, unbox_bint bi arg2))
let bint_shift bi prim arg1 arg2 =
  box_bint bi
    (Binary (Int_shift (C.standard_int_of_boxed_integer bi, prim),
             unbox_bint bi arg1, untag_int arg2))

(* offset to subtract from a string length depending
   on the size of the read/write *)
let length_offset_of_size size =
  let offset =
    match (size : Flambda_primitive.string_accessor_width) with
    | Eight -> 0
    | Sixteen -> 1
    | Thirty_two -> 3
    | Sixty_four -> 7
  in
  Immediate.int (Targetint.OCaml.of_int offset)

(* This computes the maximum of a given value [x] with zero,
   in an optimized way. It takes as named argument the size (in bytes)
   of an integer register on the target architecture.
   It is equivalent to the `max_or_zero` function in `cmm_helpers.ml` *)
let max_with_zero ~size_int x =
  let register_bitsize_minus_one =
    H.Simple (Simple.const (Naked_immediate (
        Immediate.int (Targetint.OCaml.of_int (size_int * 8 - 1)))))
  in
  let sign =
    H.Prim (Binary (Int_shift (Naked_nativeint, Asr),
                    x, register_bitsize_minus_one))
  in
  let minus_one =
    H.Simple (Simple.const (Naked_nativeint (Targetint.of_int (-1))))
  in
  let sign_negation =
    H.Prim (Binary (Int_arith (Naked_nativeint, Xor),
                    sign, minus_one))
  in
  let ret =
    H.Prim (Binary (Int_arith (Naked_nativeint, And),
                    sign_negation, x))
  in
  ret

(* actual (strict) upper bound for an index in a string read/write *)
let actual_max_length ~size_int ~access_size length =
  match (access_size : Flambda_primitive.string_accessor_width) with
  | Eight -> length (* micro-optimization *)
  | Sixteen | Thirty_two | Sixty_four ->
    let offset = length_offset_of_size access_size in
    let reduced_length =
      H.Prim (Binary (Int_arith (Naked_immediate, Sub),
                      length, Simple (Simple.const (Naked_immediate offset))))
    in
    (* We need to convert the length into a naked_nativeint because the optimised
       version of the max_with_zero function needs to be on machine-width integers
       to work (or at least on an integer number of bytes to work). *)
    let reduced_length_nativeint =
      H.Prim (Unary (Num_conv { src = Naked_immediate; dst = Naked_nativeint },
                     reduced_length))
    in
    let nativeint_res = max_with_zero ~size_int reduced_length_nativeint in
    H.Prim (Unary (Num_conv { src = Naked_nativeint; dst = Naked_immediate },
                   nativeint_res))

let string_or_bytes_access_validity_condition
    ~size_int str kind access_size index : H.expr_primitive =
  Binary (Int_comp (I.Naked_immediate, Unsigned, Lt),
          untag_int index,
          actual_max_length ~size_int ~access_size (Prim (Unary (String_length kind, str))))

let string_or_bytes_ref ~size_int kind arg1 arg2 dbg : H.expr_primitive =
  Checked {
    primitive =
      tag_int (Binary (String_or_bigstring_load (kind, Eight), arg1, arg2));
    validity_conditions = [
      string_or_bytes_access_validity_condition ~size_int arg1 String Eight arg2;
    ];
    failure = Index_out_of_bounds;
    dbg;
  }

let bigstring_access_validity_condition ~size_int bstr access_size index : H.expr_primitive =
  Binary (Int_comp (I.Naked_immediate, Unsigned, Lt),
          untag_int index,
          actual_max_length ~size_int ~access_size
            (Prim (Unary (Bigarray_length { dimension = 1; }, bstr))))

(* CR mshinwell: Same problems as previous function *)
let bigstring_ref ~size_int access_size arg1 arg2 dbg : H.expr_primitive =
  let wrap =
    match (access_size : Flambda_primitive.string_accessor_width) with
    | Eight | Sixteen -> tag_int
    | Thirty_two -> box_bint Pint32
    | Sixty_four -> box_bint Pint64
  in
  Checked {
    primitive =
      wrap (Binary (String_or_bigstring_load (Bigstring, access_size), arg1, arg2));
    validity_conditions = [
      bigstring_access_validity_condition ~size_int arg1 access_size arg2;
    ];
    failure = Index_out_of_bounds;
    dbg;
  }

let bigarray_box_raw_value_read kind =
  match P.element_kind_of_bigarray_kind kind with
  | Value -> Fun.id
  | Naked_number k ->
    let bi = K.Boxable_number.of_naked_number_kind k in
    fun arg -> H.Unary (Box_number bi, Prim arg)
  | Fabricated ->
    Misc.fatal_errorf
      "Don't know how to unbox a fabricated expression to \
       store it in a bigarray"

let bigarray_unbox_value_to_store kind =
  match P.element_kind_of_bigarray_kind kind with
  | Value -> Fun.id
  | Naked_number k ->
    let bi = K.Boxable_number.of_naked_number_kind k in
    fun arg -> H.Prim (Unary (Unbox_number bi, arg))
  | Fabricated ->
    Misc.fatal_errorf
      "Don't know how to unbox a fabricated expression to \
       store it in a bigarray"

let convert_lprim ~backend (prim : L.primitive) (args : Simple.t list)
      (dbg : Debuginfo.t) : H.expr_primitive =
  let args = List.map (fun arg : H.simple_or_prim -> Simple arg) args in
  let module B = (val backend : Flambda2_backend_intf.S) in
  let size_int = B.size_int in
  match prim, args with
  | Pmakeblock (tag, flag, shape), _ ->
    let flag = C.convert_mutable_flag flag in
    let shape = C.convert_block_shape shape ~num_fields:(List.length args) in
    Variadic (Make_block (
        Full_of_values (Tag.Scannable.create_exn tag, shape), flag),
      args)
  | Pmakearray (kind, mutability), _ ->
    let flag = C.convert_mutable_flag mutability in
    let kind, args =
      let module S = P.Generic_array_specialisation in
      match kind with
      | Pgenarray -> S.no_specialisation (), args
      | Paddrarray -> S.full_of_arbitrary_values_but_not_floats (), args
      | Pintarray -> S.full_of_immediates (), args
      | Pfloatarray -> S.full_of_naked_floats (), List.map unbox_float args
    in
    Variadic (Make_block (Generic_array kind, flag), args)
  | Popaque, [arg] ->
    Unary (Opaque_identity, arg)
  | Pduprecord (repr, num_fields), [arg] ->
    let kind : P.duplicate_block_kind =
      match repr with
      | Record_regular -> Full_of_values_known_length Tag.Scannable.zero
      | Record_float ->
        Full_of_naked_floats
          { length = Some (Targetint.OCaml.of_int num_fields) }
      | Record_unboxed _ ->
        Misc.fatal_error "Pduprecord of unboxed record"
      | Record_inlined tag ->
        Full_of_values_known_length (Tag.Scannable.create_exn tag)
      | Record_extension _ ->
        Full_of_values_known_length Tag.Scannable.zero
    in
    Unary (Duplicate_block {
      kind;
      source_mutability = Mutable;
      destination_mutability = Mutable;
    }, arg)
  | Pnegint, [arg] ->
    Unary (Int_arith (I.Tagged_immediate, Neg), arg)
  | Paddint, [arg1; arg2] ->
    Binary (Int_arith (I.Tagged_immediate, Add), arg1, arg2)
  | Psubint, [arg1; arg2] ->
    Binary (Int_arith (I.Tagged_immediate, Sub), arg1, arg2)
  | Pmulint, [arg1; arg2] ->
    Binary (Int_arith (I.Tagged_immediate, Mul), arg1, arg2)
  | Pandint, [arg1; arg2] ->
    Binary (Int_arith (I.Tagged_immediate, And), arg1, arg2)
  | Porint, [arg1; arg2] ->
    Binary (Int_arith (I.Tagged_immediate, Or), arg1, arg2)
  | Pxorint, [arg1; arg2] ->
    Binary (Int_arith (I.Tagged_immediate, Xor), arg1, arg2)
  | Plslint, [arg1; arg2] ->
    Binary (Int_shift (I.Tagged_immediate, Lsl), arg1, untag_int arg2)
  | Plsrint, [arg1; arg2] ->
    Binary (Int_shift (I.Tagged_immediate, Lsr), arg1, untag_int arg2)
  | Pasrint, [arg1; arg2] ->
    Binary (Int_shift (I.Tagged_immediate, Asr), arg1, untag_int arg2)
  | Pnot, [arg] ->
    Unary (Boolean_not, arg)
  | Pintcomp comp, [arg1; arg2] ->
    tag_int (Binary (C.convert_integer_comparison_prim comp, arg1, arg2))
  | Pbintcomp (kind, comp), [arg1; arg2] ->
    let arg1 = unbox_bint kind arg1 in
    let arg2 = unbox_bint kind arg2 in
    tag_int (Binary (
      C.convert_boxed_integer_comparison_prim kind comp, arg1, arg2))
  | Pintoffloat, [arg] ->
    let src = K.Standard_int_or_float.Naked_float in
    let dst = K.Standard_int_or_float.Tagged_immediate in
    Unary (Num_conv {src; dst}, unbox_float arg)
  | Pfloatofint, [arg] ->
    let src = K.Standard_int_or_float.Tagged_immediate in
    let dst = K.Standard_int_or_float.Naked_float in
    box_float (Unary (Num_conv {src; dst}, arg))
  | Pnegfloat, [arg] ->
    box_float (Unary (Float_arith Neg, unbox_float arg))
  | Pabsfloat, [arg] ->
    box_float (Unary (Float_arith Abs, unbox_float arg))
  | Paddfloat, [arg1; arg2] ->
    box_float (Binary (Float_arith Add, unbox_float arg1, unbox_float arg2))
  | Psubfloat, [arg1; arg2] ->
    box_float (Binary (Float_arith Sub, unbox_float arg1, unbox_float arg2))
  | Pmulfloat, [arg1; arg2] ->
    box_float (Binary (Float_arith Mul, unbox_float arg1, unbox_float arg2))
  | Pdivfloat, [arg1; arg2] ->
    box_float (Binary (Float_arith Div, unbox_float arg1, unbox_float arg2))
  | Pfloatcomp comp, [arg1; arg2] ->
    tag_int (Binary (Float_comp (C.convert_float_comparison comp),
      unbox_float arg1, unbox_float arg2))
  | Pfield_computed sem, [obj; field] ->
    Binary (Block_load (
      Block (Value Anything), C.convert_field_read_semantics sem), obj, field)
  | Psetfield_computed (imm_or_pointer, init_or_assign), [obj; field; value] ->
    let access_kind =
      C.convert_access_kind imm_or_pointer
    in
    Ternary
      (Block_set
         (Block access_kind, C.convert_init_or_assign init_or_assign),
       obj, field, value)
  | Parraylength kind, [arg] ->
    Unary (Array_length (C.convert_array_kind kind), arg)
  | Pduparray (kind, mutability), [arg] ->
    Unary (Duplicate_block {
      (* CR mshinwell: fix this next function *)
      kind = C.convert_array_kind_to_duplicate_block_kind kind;
      (* CR mshinwell: Check that [Pduparray] is only applied to immutable
         arrays *)
      source_mutability = Immutable;
      (* CR mshinwell: Check that [mutability] is the destination
         mutability *)
      destination_mutability = C.convert_mutable_flag mutability;
    }, arg)
  | Pstringlength, [arg] ->
    (* CR mshinwell: Decide whether things such as String_length should return
       tagged or untagged integers.  Probably easiest to match Cmm_helpers
       for now and change individual cases later for better codegen if
       required. *)
    tag_int (Unary (String_length String, arg))
  | Pbyteslength, [arg] ->
    tag_int (Unary (String_length Bytes, arg))
  | Pstringrefu, [arg1; arg2] ->
    tag_int (Binary (String_or_bigstring_load (String, Eight), arg1, arg2))
  | Pbytesrefu, [arg1; arg2] ->
    tag_int (Binary (String_or_bigstring_load (Bytes, Eight), arg1, arg2))
  | Pbytesrefs, [arg1; arg2] ->
    string_or_bytes_ref ~size_int Bytes arg1 arg2 dbg
  | Pstringrefs, [arg1; arg2] ->
    string_or_bytes_ref ~size_int String arg1 arg2 dbg
  | Pstring_load_16 true (* unsafe *), [arg1; arg2]
  | Pbytes_load_16 true (* unsafe *), [arg1; arg2] ->
    tag_int (Binary (String_or_bigstring_load (String, Sixteen), arg1, arg2))
  | Pstring_load_32 true (* unsafe *), [arg1; arg2]
  | Pbytes_load_32 true (* unsafe *), [arg1; arg2] ->
    Unary (Box_number Naked_int32,
      Prim (Binary (String_or_bigstring_load (String, Thirty_two),
        arg1, arg2)))
  | Pstring_load_64 true (* unsafe *), [arg1; arg2]
  | Pbytes_load_64 true (* unsafe *), [arg1; arg2] ->
    Unary (Box_number Naked_int64,
      Prim (Binary (String_or_bigstring_load (String, Sixty_four),
        arg1, arg2)))
  | Pstring_load_16 false, [str; index] ->
    Checked {
      primitive =
        tag_int
          (Binary (String_or_bigstring_load (String, Sixteen), str, index));
      validity_conditions = [
        string_or_bytes_access_validity_condition ~size_int str String Sixteen index;
      ];
      failure = Index_out_of_bounds;
      dbg;
    }
  | Pstring_load_32 false, [str; index] ->
    Checked {
      primitive =
        Unary (Box_number Naked_int32,
          Prim (Binary (String_or_bigstring_load (String, Thirty_two),
            str, index)));
      validity_conditions = [
        string_or_bytes_access_validity_condition ~size_int str String Thirty_two index;
      ];
      failure = Index_out_of_bounds;
      dbg;
    }
  | Pstring_load_64 false, [str; index] ->
    Checked {
      primitive =
        Unary (Box_number Naked_int64,
          Prim (Binary (String_or_bigstring_load (String, Sixty_four),
            str, index)));
      validity_conditions = [
        string_or_bytes_access_validity_condition ~size_int str String Sixty_four index;
      ];
      failure = Index_out_of_bounds;
      dbg;
    }
  (* CR mshinwell: factor out *)
  | Pbytes_load_16 false, [bytes; index] ->
    Checked {
      primitive =
        tag_int
          (Binary (String_or_bigstring_load (Bytes, Sixteen), bytes, index));
      validity_conditions = [
        string_or_bytes_access_validity_condition ~size_int bytes Bytes Sixteen index;
      ];
      failure = Index_out_of_bounds;
      dbg;
    }
  | Pbytes_load_32 false, [bytes; index] ->
    Checked {
      primitive =
        Unary (Box_number Naked_int32,
          Prim (Binary (String_or_bigstring_load (Bytes, Thirty_two),
            bytes, index)));
      validity_conditions = [
        string_or_bytes_access_validity_condition ~size_int bytes Bytes Thirty_two index;
      ];
      failure = Index_out_of_bounds;
      dbg;
    }
  | Pbytes_load_64 false, [bytes; index] ->
    Checked {
      primitive =
        Unary (Box_number Naked_int64,
          Prim (Binary (String_or_bigstring_load (Bytes, Sixty_four),
            bytes, index)));
      validity_conditions = [
        string_or_bytes_access_validity_condition ~size_int bytes Bytes Sixty_four index;
      ];
      failure = Index_out_of_bounds;
      dbg;
    }
  (* CR mshinwell: Change [Lambda] to have a [Safe] / [Unsafe] variant *)
  | Pbytes_set_16 true, [bytes; index; new_value] ->
    Ternary (Bytes_or_bigstring_set (Bytes, Sixteen),
      bytes, index, untag_int new_value)
  | Pbytes_set_32 true, [bytes; index; new_value] ->
    Ternary (Bytes_or_bigstring_set (Bytes, Thirty_two),
      bytes, index, Prim (Unary (Unbox_number Naked_int32, new_value)))
  | Pbytes_set_64 true, [bytes; index; new_value] ->
    Ternary (Bytes_or_bigstring_set (Bytes, Sixty_four),
      bytes, index, Prim (Unary (Unbox_number Naked_int64, new_value)))
  | Pbytes_set_16 false, [bytes; index; new_value] ->
    Checked {
      primitive =
        Ternary (Bytes_or_bigstring_set (Bytes, Sixteen),
          bytes, index, untag_int new_value);
      validity_conditions = [
        string_or_bytes_access_validity_condition ~size_int bytes Bytes Sixteen index;
      ];
      failure = Index_out_of_bounds;
      dbg;
    }
  | Pbytes_set_32 false, [bytes; index; new_value] ->
    Checked {
      primitive =
        Ternary (Bytes_or_bigstring_set (Bytes, Thirty_two),
          bytes, index, Prim (Unary (Unbox_number Naked_int32, new_value)));
      validity_conditions = [
        string_or_bytes_access_validity_condition ~size_int bytes Bytes Thirty_two index;
      ];
      failure = Index_out_of_bounds;
      dbg;
    }
  | Pbytes_set_64 false, [bytes; index; new_value] ->
    Checked {
      primitive =
        Ternary (Bytes_or_bigstring_set (Bytes, Sixty_four),
          bytes, index, Prim (Unary (Unbox_number Naked_int64, new_value)));
      validity_conditions = [
        string_or_bytes_access_validity_condition ~size_int bytes Bytes Sixty_four index;
      ];
      failure = Index_out_of_bounds;
      dbg;
    }

  (* CR mshinwell: To do: | Pbittest, [arg1; arg2] -> *)
  (*   Binary (Bit_test, arg1, arg2) *)

  | Pflambda_isint, [arg] ->
    tag_int (Unary (Is_int, arg))
  | Pgettag, [arg] ->
    tag_int (Unary (Get_tag, arg))
  | Pisout, [arg1; arg2] ->
    tag_int (
      Binary (Int_comp (I.Tagged_immediate, Unsigned, Lt),
              tagged_immediate_as_naked_nativeint arg1,
              tagged_immediate_as_naked_nativeint arg2))
  | Pbintofint bi, [arg] ->
    let dst = C.standard_int_or_float_of_boxed_integer bi in
    Unary (
      Box_number
        (C.boxable_number_of_boxed_integer bi),
      Prim (Unary (Num_conv { src = I_or_f.Tagged_immediate; dst }, arg)))
  | Pintofbint bi, [arg] ->
    let src = C.standard_int_or_float_of_boxed_integer bi in
    Unary (
      Num_conv { src; dst = I_or_f.Tagged_immediate },
      Prim (Unary (Unbox_number (C.boxable_number_of_boxed_integer bi), arg)))
  | Pcvtbint (source, destination), [arg] ->
    box_bint destination
      (Unary (Num_conv {
        src = C.standard_int_or_float_of_boxed_integer source;
        dst = C.standard_int_or_float_of_boxed_integer destination },
      unbox_bint source arg))
  | Pnegbint bi, [arg] ->
    box_bint bi (Unary (Int_arith (C.standard_int_of_boxed_integer bi, Neg),
      unbox_bint bi arg))
  | Paddbint bi, [arg1; arg2] ->
    bint_binary_prim bi Add arg1 arg2
  | Psubbint bi, [arg1; arg2] ->
    bint_binary_prim bi Sub arg1 arg2
  | Pmulbint bi, [arg1; arg2] ->
    bint_binary_prim bi Mul arg1 arg2
  | Pandbint bi, [arg1; arg2] ->
    bint_binary_prim bi And arg1 arg2
  | Porbint bi, [arg1; arg2] ->
    bint_binary_prim bi Or arg1 arg2
  | Pxorbint bi, [arg1; arg2] ->
    bint_binary_prim bi Xor arg1 arg2
  | Plslbint bi, [arg1; arg2] ->
    bint_shift bi Lsl arg1 arg2
  | Plsrbint bi, [arg1; arg2] ->
    bint_shift bi Lsr arg1 arg2
  | Pasrbint bi, [arg1; arg2] ->
    bint_shift bi Asr arg1 arg2
  | Poffsetint n, [arg] ->
    let const =
      Simple.const
        (Simple.Const.Tagged_immediate
           (Immediate.int (Targetint.OCaml.of_int n)))
    in
    Binary (Int_arith (I.Tagged_immediate, Add), arg, Simple const)
  | Pfield (field, sem), [arg] ->
    (* CR mshinwell: Cause fatal error if the field value is < 0.
       We can't do this once we convert to Flambda *)
    let imm = Immediate.int (Targetint.OCaml.of_int field) in
    let field = Simple.const (Simple.Const.Tagged_immediate imm) in
    let mutability = C.convert_field_read_semantics sem in
    Binary (Block_load (Block (Value Anything), mutability), arg,
      Simple field)
  | Pfloatfield (field, sem), [arg] ->
    let imm = Immediate.int (Targetint.OCaml.of_int field) in
    let field = Simple.const (Simple.Const.Tagged_immediate imm) in
    let mutability = C.convert_field_read_semantics sem in
    box_float
      (Binary (Block_load (Block Naked_float, mutability), arg, Simple field))
  | Psetfield (field, immediate_or_pointer, initialization_or_assignment),
    [block; value] ->
    let access_kind = C.convert_access_kind immediate_or_pointer in
    let imm = Immediate.int (Targetint.OCaml.of_int field) in
    let field = Simple.const (Simple.Const.Tagged_immediate imm) in
    Ternary (Block_set (Block access_kind,
         C.convert_init_or_assign initialization_or_assignment),
       block, Simple field, value)
  | Psetfloatfield (field, init_or_assign), [block; value] ->
    let imm = Immediate.int (Targetint.OCaml.of_int field) in
    let field = Simple.const (Simple.Const.Tagged_immediate imm) in
    Ternary (Block_set (Block Naked_float,
        C.convert_init_or_assign init_or_assign),
      block, Simple field, unbox_float value)
  | Pdivint Unsafe, [arg1; arg2] ->
    Binary (Int_arith (I.Tagged_immediate, Div), arg1, arg2)
  | Pdivint Safe, [arg1; arg2] ->
    Checked {
      primitive =
        Binary (Int_arith (I.Tagged_immediate, Div), arg1, arg2);
      validity_conditions = [
        Binary (Phys_equal (K.value, Neq), arg2,
                Simple
                  (Simple.const
                     (Simple.Const.Tagged_immediate
                        (Immediate.int (Targetint.OCaml.zero)))));
      ];
      failure = Division_by_zero;
      dbg;
    }
  | Pmodint Safe, [arg1; arg2] ->
    Checked {
      primitive =
        Binary (Int_arith (I.Tagged_immediate, Mod), arg1, arg2);
      validity_conditions = [
        Binary (Phys_equal (K.value, Neq), arg2,
                Simple
                  (Simple.const
                     (Simple.Const.Tagged_immediate
                        (Immediate.int (Targetint.OCaml.zero)))));
      ];
      failure = Division_by_zero;
      dbg;
    }
  | Pdivbint { size = Pint32; is_safe = Safe; }, [arg1; arg2] ->
    (* The duplicate unboxing generated in the Pdivbint/Pmodbint cases will
       be removed by the simplifier. *)
    (* CR mshinwell: Factor these cases out *)
    Checked {
      primitive =
        box_bint Pint32
          (Binary (Int_arith (I.Naked_int32, Div),
            unbox_bint Pint32 arg1, unbox_bint Pint32 arg2));
      validity_conditions = [
        Binary (Phys_equal (K.naked_int32, Neq), unbox_bint Pint32 arg2,
                Simple
                  (Simple.const
                     (Simple.Const.Naked_int32 0l)));
      ];
      failure = Division_by_zero;
      dbg;
    }
  | Pmodbint { size = Pint32; is_safe = Safe; }, [arg1; arg2] ->
    Checked {
      primitive =
        box_bint Pint32
          (Binary (Int_arith (I.Naked_int32, Mod),
            unbox_bint Pint32 arg1, unbox_bint Pint32 arg2));
      validity_conditions = [
        Binary (Phys_equal (K.naked_int32, Neq), unbox_bint Pint32 arg2,
                Simple
                  (Simple.const
                     (Simple.Const.Naked_int32 0l)));
      ];
      failure = Division_by_zero;
      dbg;
    }
  | Pdivbint { size = Pint64; is_safe = Safe; }, [arg1; arg2] ->
    Checked {
      primitive =
        box_bint Pint64
          (Binary (Int_arith (I.Naked_int64, Div),
            unbox_bint Pint64 arg1, unbox_bint Pint64 arg2));
      validity_conditions = [
        Binary (Phys_equal (K.naked_int64, Neq), unbox_bint Pint64 arg2,
                Simple
                  (Simple.const
                     (Simple.Const.Naked_int64 0L)));
      ];
      failure = Division_by_zero;
      dbg;
    }
  | Pmodbint { size = Pint64; is_safe = Safe; }, [arg1; arg2] ->
    Checked {
      primitive =
        box_bint Pint64
          (Binary (Int_arith (I.Naked_int64, Mod),
            unbox_bint Pint64 arg1, unbox_bint Pint64 arg2));
      validity_conditions = [
        Binary (Phys_equal (K.naked_int64, Neq), unbox_bint Pint64 arg2,
                Simple
                  (Simple.const
                     (Simple.Const.Naked_int64 0L)));
      ];
      failure = Division_by_zero;
      dbg;
    }
  | Pdivbint { size = Pnativeint; is_safe = Safe; }, [arg1; arg2] ->
    Checked {
      primitive =
        box_bint Pnativeint
          (Binary (Int_arith (I.Naked_nativeint, Div),
            unbox_bint Pnativeint arg1, unbox_bint Pnativeint arg2));
      validity_conditions = [
        Binary (Phys_equal (K.naked_nativeint, Neq), unbox_bint Pnativeint arg2,
                Simple
                  (Simple.const
                     (Simple.Const.Naked_nativeint Targetint.zero)));
      ];
      failure = Division_by_zero;
      dbg;
    }
  | Pmodbint { size = Pnativeint; is_safe = Safe; }, [arg1; arg2] ->
    Checked {
      primitive =
        box_bint Pnativeint
          (Binary (Int_arith (I.Naked_nativeint, Mod),
            unbox_bint Pnativeint arg1, unbox_bint Pnativeint arg2));
      validity_conditions = [
        Binary (Phys_equal (K.naked_nativeint, Neq), unbox_bint Pnativeint arg2,
                Simple
                  (Simple.const
                     (Simple.Const.Naked_nativeint Targetint.zero)));
      ];
      failure = Division_by_zero;
      dbg;
    }
  | Parrayrefu (Pgenarray | Paddrarray | Pintarray), [array; index] ->
    (* CR mshinwell: Review all these cases.  Isn't this supposed to
       produce [Generic_array]? *)
    Binary (Block_load (Array (Value Anything), Mutable), array, index)
  | Parrayrefu Pfloatarray, [array; index] ->
    box_float (Binary (Block_load (Array Naked_float, Mutable), array, index))
  | Parrayrefs (Pgenarray | Paddrarray | Pintarray), [array; index] ->
    Checked {
      primitive =
        Binary (Block_load (Array (Value Anything), Mutable), array, index);
      validity_conditions = [
        Binary (Int_comp (Tagged_immediate, Signed, Ge), index,
          Simple (Simple.const (Simple.Const.Tagged_immediate
            (Immediate.int (Targetint.OCaml.zero)))));
        Binary (Int_comp (Tagged_immediate, Signed, Lt), index,
          Prim (Unary (Array_length (Array (Value Anything)), array)));
      ];
      failure = Index_out_of_bounds;
      dbg;
    }
  | Parrayrefs Pfloatarray, [array; index] ->
    Checked {
      primitive =
       box_float (
         Binary (Block_load (Array Naked_float, Mutable), array, index));
      validity_conditions = [
        Binary (Int_comp (Tagged_immediate, Signed, Ge), index,
          Simple (Simple.const (Simple.Const.Tagged_immediate
            (Immediate.int (Targetint.OCaml.zero)))));
        Binary (Int_comp (Tagged_immediate, Signed, Lt), index,
          Prim (Unary (Array_length (Array Naked_float), array)));
      ];
      failure = Index_out_of_bounds;
      dbg;
    }
  | Parraysetu (Pgenarray | Paddrarray | Pintarray),
      [array; index; new_value] ->
    Ternary (Block_set (Array (Value Anything), Assignment),
      array, index, new_value)
  | Parraysetu Pfloatarray, [array; index; new_value] ->
    Ternary (Block_set (Array Naked_float, Assignment),
      array, index, unbox_float new_value)
  | Parraysets (Pgenarray | Paddrarray | Pintarray),
      [array; index; new_value] ->
    Checked {
      primitive =
        Ternary (Block_set (Array (Value Anything), Assignment),
          array, index, new_value);
      validity_conditions = [
        Binary (Int_comp (Tagged_immediate, Signed, Ge), index,
          Simple (Simple.const (Simple.Const.Tagged_immediate
            (Immediate.int (Targetint.OCaml.zero)))));
        Binary (Int_comp (Tagged_immediate, Signed, Lt), index,
          Prim (Unary (Array_length (Array (Value Anything)), array)));
      ];
      failure = Index_out_of_bounds;
      dbg;
    }
  | Parraysets Pfloatarray, [array; index; new_value] ->
    Checked {
      primitive =
        Ternary (Block_set (Array Naked_float, Assignment),
          array, index, unbox_float new_value);
      validity_conditions = [
        Binary (Int_comp (Tagged_immediate, Signed, Ge), index,
          Simple (Simple.const (Simple.Const.Tagged_immediate
            (Immediate.int (Targetint.OCaml.zero)))));
        Binary (Int_comp (Tagged_immediate, Signed, Lt), index,
          Prim (Unary (Array_length (Array Naked_float), array)));
      ];
      failure = Index_out_of_bounds;
      dbg;
    }
  | Pbytessetu, [bytes; index; new_value] ->
    Ternary (Bytes_or_bigstring_set (Bytes, Eight), bytes, index,
             untag_int new_value)
  | Pbytessets, [bytes; index; new_value] ->
    Checked {
      primitive =
        Ternary (Bytes_or_bigstring_set (Bytes, Eight),
          bytes, index, untag_int new_value);
      validity_conditions = [
        string_or_bytes_access_validity_condition ~size_int bytes Bytes Eight index;
      ];
      failure = Index_out_of_bounds;
      dbg;
    }
  | Poffsetref n, [block] ->
    Ternary (Block_set (Block (Value Definitely_immediate), Assignment),
      block,
      Simple Simple.const_zero,
      Prim (Binary (Int_arith (Tagged_immediate, Add),
        Simple (Simple.const_int (Targetint.OCaml.of_int n)),
        Prim (Binary (Block_load (Block (Value Definitely_immediate), Mutable),
          block,
          Simple Simple.const_zero)))))
  | Pctconst const, _ ->
    (* CR mshinwell: This doesn't seem to be zero-arity like it should be *)
    (* CR pchambart: It's not obvious when this one should be converted.
       mshinwell: Have put an implementation here for now. *)
    begin match const with
    | Big_endian -> Simple (Simple.const_bool B.big_endian)
    | Word_size ->
      Simple (Simple.const_int (Targetint.OCaml.of_int (8*size_int)))
    | Int_size ->
      Simple (Simple.const_int (Targetint.OCaml.of_int (8*size_int - 1)))
    | Max_wosize ->
      (* CR mshinwell: This depends on the number of bits in the header
         reserved for profinfo, no?  If this computation is wrong then
         the one in [Closure] (and maybe Flambda 1) is wrong. *)
      Simple (Simple.const_int (Targetint.OCaml.of_int
        ((1 lsl ((8*size_int) - 10)) - 1)))
    | Ostype_unix -> Simple (Simple.const_bool (Sys.os_type = "Unix"))
    | Ostype_win32 -> Simple (Simple.const_bool (Sys.os_type = "Win32"))
    | Ostype_cygwin -> Simple (Simple.const_bool (Sys.os_type = "Cygwin"))
    | Backend_type ->
      Simple (Simple.const_zero) (* constructor 0 is the same as Native here *)
    end
  | Pbswap16, [arg] ->
    Unary (Int_arith (Tagged_immediate, Swap_byte_endianness), arg)
  | Pbbswap Pint32, [arg] ->
    Unary (Box_number Naked_int32,
      Prim (Unary (Int_arith (Naked_int32, Swap_byte_endianness),
        Prim (Unary (Unbox_number Naked_int32, arg)))))
  | Pbbswap Pint64, [arg] ->
    Unary (Box_number Naked_int64,
      Prim (Unary (Int_arith (Naked_int64, Swap_byte_endianness),
        Prim (Unary (Unbox_number Naked_int64, arg)))))
  | Pbbswap Pnativeint, [arg] ->
    Unary (Box_number Naked_nativeint,
      Prim (Unary (Int_arith (Naked_nativeint, Swap_byte_endianness),
        Prim (Unary (Unbox_number Naked_nativeint, arg)))))
  | Pint_as_pointer, [arg] -> Unary (Int_as_pointer, arg)
  | Pbigarrayref (unsafe, num_dimensions, kind, layout), args ->
    (* CR mshinwell: When num_dimensions = 1 then we could actually
       put the bounds check in Flambda. *)
    let is_safe : P.is_safe = if unsafe then Unsafe else Safe in
    let kind = C.convert_bigarray_kind kind in
    let layout = C.convert_bigarray_layout layout in
    let box = bigarray_box_raw_value_read kind in
    box (Variadic (Bigarray_load (is_safe, num_dimensions, kind, layout), args))
  | Pbigarrayset (unsafe, num_dimensions, kind, layout), args ->
    let is_safe : P.is_safe = if unsafe then Unsafe else Safe in
    let kind = C.convert_bigarray_kind kind in
    let layout = C.convert_bigarray_layout layout in
    let unbox = bigarray_unbox_value_to_store kind in
    let indexes, value_to_store = Misc.split_last args in
    Variadic (Bigarray_set (is_safe, num_dimensions, kind, layout),
              indexes @ [unbox value_to_store])
  | Pbigarraydim dimension, [arg] ->
    tag_int (Unary (Bigarray_length { dimension; }, arg))
  | Pbigstring_load_16 true, [arg1; arg2] ->
    Binary (String_or_bigstring_load (Bigstring, Sixteen), arg1, arg2)
  | Pbigstring_load_16 false, [arg1; arg2] ->
    bigstring_ref ~size_int Sixteen arg1 arg2 dbg
  | Pbigstring_load_32 true, [arg1; arg2] ->
    Binary (String_or_bigstring_load (Bigstring, Thirty_two), arg1, arg2)
  | Pbigstring_load_32 false, [arg1; arg2] ->
    bigstring_ref ~size_int Thirty_two arg1 arg2 dbg
  | Pbigstring_load_64 true, [arg1; arg2] ->
    Binary (String_or_bigstring_load (Bigstring, Sixty_four), arg1, arg2)
  | Pbigstring_load_64 false, [arg1; arg2] ->
    bigstring_ref ~size_int Sixty_four arg1 arg2 dbg
  | Pbigstring_set_16 true, [bigstring; index; new_value] ->
    Ternary (Bytes_or_bigstring_set (Bigstring, Sixteen),
      bigstring, index, untag_int new_value)
  | Pbigstring_set_32 true, [bigstring; index; new_value] ->
    Ternary (Bytes_or_bigstring_set (Bigstring, Thirty_two),
      bigstring, index, Prim (Unary (Unbox_number Naked_int32, new_value)))
  | Pbigstring_set_64 true, [bigstring; index; new_value] ->
    Ternary (Bytes_or_bigstring_set (Bigstring, Sixty_four),
      bigstring, index, Prim (Unary (Unbox_number Naked_int64, new_value)))
  | Pbigstring_set_16 false, [bigstring; index; new_value] ->
    Checked {
      primitive =
        Ternary (Bytes_or_bigstring_set (Bigstring, Sixteen),
          bigstring, index, untag_int new_value);
      validity_conditions = [
        bigstring_access_validity_condition ~size_int bigstring Sixteen index;
      ];
      failure = Index_out_of_bounds;
      dbg;
    }
  | Pbigstring_set_32 false, [bigstring; index; new_value] ->
    Checked {
      primitive =
        Ternary (Bytes_or_bigstring_set (Bigstring, Thirty_two),
          bigstring, index, Prim (Unary (Unbox_number Naked_int32, new_value)));
      validity_conditions = [
        bigstring_access_validity_condition ~size_int bigstring Thirty_two index;
      ];
      failure = Index_out_of_bounds;
      dbg;
    }
  | Pbigstring_set_64 false, [bigstring; index; new_value] ->
    Checked {
      primitive =
        Ternary (Bytes_or_bigstring_set (Bigstring, Sixty_four),
          bigstring, index, Prim (Unary (Unbox_number Naked_int64, new_value)));
      validity_conditions = [
        bigstring_access_validity_condition ~size_int bigstring Sixty_four index;
      ];
      failure = Index_out_of_bounds;
      dbg;
    }
  | ( Pmodint Unsafe
    | Pdivbint { is_safe = Unsafe; size = _; }
    | Pmodbint { is_safe = Unsafe; size = _; }
    | Psetglobal _ | Praise _ | Pccall _
    ), _ ->
    Misc.fatal_errorf "Closure_conversion.convert_primitive: \
        Primitive %a (%a) shouldn't be here, either a bug in [Prepare_lambda] \
        or [Closure_conversion] or the wrong number of arguments"
      Printlambda.primitive prim
      H.print_list_of_simple_or_prim args
  | ( Pfield _ | Pnegint | Pnot | Poffsetint _ | Pintoffloat | Pfloatofint
    | Pnegfloat | Pabsfloat | Pstringlength | Pbyteslength | Pgettag
    | Pbintofint _ | Pintofbint _ | Pnegbint _ | Popaque | Pduprecord _
    | Parraylength _ | Pduparray _ | Pfloatfield _ | Pcvtbint _ | Poffsetref _
    | Pbswap16 | Pbbswap _ | Pisint | Pflambda_isint | Pint_as_pointer
    | Pbigarraydim _
    ),
    ([] |  _ :: _ :: _) ->
    Misc.fatal_errorf "Closure_conversion.convert_primitive: \
        Wrong arity for unary primitive %a (%a)"
      Printlambda.primitive prim
      H.print_list_of_simple_or_prim args
  | ( Paddint | Psubint | Pmulint | Pandint | Porint | Pxorint | Plslint
    | Plsrint | Pasrint | Pdivint _ | Pmodint _ | Psetfield _ | Pintcomp _
    | Paddfloat | Psubfloat | Pmulfloat | Pdivfloat | Pfloatcomp _
    | Pstringrefu | Pbytesrefu | Pstringrefs | Pbytesrefs
    | Pstring_load_16 _ | Pstring_load_32 _ | Pstring_load_64 _
    | Pbytes_load_16 _ | Pbytes_load_32 _ | Pbytes_load_64 _
    | Pisout | Paddbint _ | Psubbint _ | Pmulbint _ | Pandbint _ | Porbint _
    | Pxorbint _ | Plslbint _ | Plsrbint _ | Pasrbint _ | Pfield_computed _
    | Pdivbint _ | Pmodbint _ | Psetfloatfield _ | Pbintcomp _
    | Pbigstring_load_16 _ | Pbigstring_load_32 _ | Pbigstring_load_64 _
    | Parrayrefu (Pgenarray | Paddrarray | Pintarray | Pfloatarray)
    | Parrayrefs (Pgenarray | Paddrarray | Pintarray | Pfloatarray)
    ),
    ([] | [_] | _ :: _ :: _ :: _) ->
    Misc.fatal_errorf "Closure_conversion.convert_primitive: \
        Wrong arity for binary primitive %a (%a)"
      Printlambda.primitive prim
      H.print_list_of_simple_or_prim args
  | ( Psetfield_computed _ | Pbytessetu | Pbytessets
    | Parraysetu (Pgenarray | Paddrarray | Pintarray | Pfloatarray)
    | Parraysets (Pgenarray | Paddrarray | Pintarray | Pfloatarray)
    | Pbytes_set_16 _ | Pbytes_set_32 _ | Pbytes_set_64 _
    | Pbigstring_set_16 _ | Pbigstring_set_32 _ | Pbigstring_set_64 _
    ),
    ([] | [_] | [_;_] | _ :: _ :: _ :: _ :: _) ->
    Misc.fatal_errorf "Closure_conversion.convert_primitive: \
        Wrong arity for ternary primitive %a (%a)"
      Printlambda.primitive prim
      H.print_list_of_simple_or_prim args
  | ( Pidentity | Pignore | Prevapply | Pdirapply | Psequand | Psequor
    | Pbytes_of_string | Pbytes_to_string | Pisint
    ), _ ->
    Misc.fatal_errorf "[%a] should have been removed by \
      [Prepare_lambda.prepare]"
      Printlambda.primitive prim
  | Pgetglobal _, _ ->
    Misc.fatal_errorf "[%a] should have been handled by \
      [Closure_conversion.close_primitive]"
      Printlambda.primitive prim

let convert_and_bind ~backend exn_cont ~register_const_string
      (prim : L.primitive) ~(args : Simple.t list) (dbg : Debuginfo.t)
      (cont : Named.t option -> Expr.t) : Expr.t =
  let expr = convert_lprim ~backend prim args dbg in
  H.bind_rec ~backend exn_cont ~register_const_string expr dbg
    (fun named -> cont (Some named))