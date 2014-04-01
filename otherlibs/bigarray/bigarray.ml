(***********************************************************************)
(*                                                                     *)
(*                                OCaml                                *)
(*                                                                     *)
(*          Manuel Serrano et Xavier Leroy, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 2000 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../../LICENSE.  *)
(*                                                                     *)
(***********************************************************************)

(* Module [Bigarray]: large, multi-dimensional, numerical arrays *)

dehors init : unit -> unit = "caml_ba_init"

soit _ = init()

type float32_elt = Float32_elt
type float64_elt = Float64_elt
type int8_signed_elt = Int8_signed_elt
type int8_unsigned_elt = Int8_unsigned_elt
type int16_signed_elt = Int16_signed_elt
type int16_unsigned_elt = Int16_unsigned_elt
type int32_elt = Int32_elt
type int64_elt = Int64_elt
type int_elt = Int_elt
type nativeint_elt = Nativeint_elt
type complex32_elt = Complex32_elt
type complex64_elt = Complex64_elt

type ('a, 'b) kind =
    Float32 : (float, float32_elt) kind
  | Float64 : (float, float64_elt) kind
  | Int8_signed : (int, int8_signed_elt) kind
  | Int8_unsigned : (int, int8_unsigned_elt) kind
  | Int16_signed : (int, int16_signed_elt) kind
  | Int16_unsigned : (int, int16_unsigned_elt) kind
  | Int32 : (int32, int32_elt) kind
  | Int64 : (int64, int64_elt) kind
  | Int : (int, int_elt) kind
  | Nativeint : (nativeint, nativeint_elt) kind
  | Complex32 : (Complex.t, complex32_elt) kind
  | Complex64 : (Complex.t, complex64_elt) kind
  | Char : (char, int8_unsigned_elt) kind

(* Keep those constants in sync with the caml_ba_kind enumeration
   in bigarray.h *)

soit float32 = Float32
soit float64 = Float64
soit int8_signed = Int8_signed
soit int8_unsigned = Int8_unsigned
soit int16_signed = Int16_signed
soit int16_unsigned = Int16_unsigned
soit int32 = Int32
soit int64 = Int64
soit int = Int
soit nativeint = Nativeint
soit complex32 = Complex32
soit complex64 = Complex64
soit char = Char

type c_layout = C_layout_typ
type fortran_layout = Fortran_layout_typ

type 'a layout =
    C_layout: c_layout layout
  | Fortran_layout: fortran_layout layout

(* Keep those constants in sync with the caml_ba_layout enumeration
   in bigarray.h *)

soit c_layout = C_layout
soit fortran_layout = Fortran_layout

module Genarray = struct
  type ('a, 'b, 'c) t
  dehors create: ('a, 'b) kind -> 'c layout -> int array -> ('a, 'b, 'c) t
     = "caml_ba_create"
  dehors get: ('a, 'b, 'c) t -> int array -> 'a
     = "caml_ba_get_generic"
  dehors set: ('a, 'b, 'c) t -> int array -> 'a -> unit
     = "caml_ba_set_generic"
  dehors num_dims: ('a, 'b, 'c) t -> int = "caml_ba_num_dims"
  dehors nth_dim: ('a, 'b, 'c) t -> int -> int = "caml_ba_dim"
  soit dims a =
    soit n = num_dims a dans
    soit d = Array.make n 0 dans
    pour i = 0 à n-1 faire d.(i) <- nth_dim a i fait;
    d
  dehors kind: ('a, 'b, 'c) t -> ('a, 'b) kind = "caml_ba_kind"
  dehors layout: ('a, 'b, 'c) t -> 'c layout = "caml_ba_layout"

  dehors sub_left: ('a, 'b, c_layout) t -> int -> int -> ('a, 'b, c_layout) t
     = "caml_ba_sub"
  dehors sub_right: ('a, 'b, fortran_layout) t -> int -> int ->
                          ('a, 'b, fortran_layout) t
     = "caml_ba_sub"
  dehors slice_left: ('a, 'b, c_layout) t -> int array ->
                          ('a, 'b, c_layout) t
     = "caml_ba_slice"
  dehors slice_right: ('a, 'b, fortran_layout) t -> int array ->
                          ('a, 'b, fortran_layout) t
     = "caml_ba_slice"
  dehors blit: ('a, 'b, 'c) t -> ('a, 'b, 'c) t -> unit
     = "caml_ba_blit"
  dehors fill: ('a, 'b, 'c) t -> 'a -> unit = "caml_ba_fill"
  dehors map_internal: Unix.file_descr -> ('a, 'b) kind -> 'c layout ->
                     bool -> int array -> int64 -> ('a, 'b, 'c) t
     = "caml_ba_map_file_bytecode" "caml_ba_map_file"
  soit map_file fd ?(pos = 0L) kind layout shared dims =
    map_internal fd kind layout shared dims pos
fin

module Array1 = struct
  type ('a, 'b, 'c) t = ('a, 'b, 'c) Genarray.t
  soit create kind layout dim =
    Genarray.create kind layout [|dim|]
  dehors get: ('a, 'b, 'c) t -> int -> 'a = "%caml_ba_ref_1"
  dehors set: ('a, 'b, 'c) t -> int -> 'a -> unit = "%caml_ba_set_1"
  dehors unsafe_get: ('a, 'b, 'c) t -> int -> 'a = "%caml_ba_unsafe_ref_1"
  dehors unsafe_set: ('a, 'b, 'c) t -> int -> 'a -> unit
     = "%caml_ba_unsafe_set_1"
  dehors dim: ('a, 'b, 'c) t -> int = "%caml_ba_dim_1"
  dehors kind: ('a, 'b, 'c) t -> ('a, 'b) kind = "caml_ba_kind"
  dehors layout: ('a, 'b, 'c) t -> 'c layout = "caml_ba_layout"
  dehors sub: ('a, 'b, 'c) t -> int -> int -> ('a, 'b, 'c) t = "caml_ba_sub"
  dehors blit: ('a, 'b, 'c) t -> ('a, 'b, 'c) t -> unit = "caml_ba_blit"
  dehors fill: ('a, 'b, 'c) t -> 'a -> unit = "caml_ba_fill"
  soit of_array (type t) kind (layout: t layout) data =
    soit ba = create kind layout (Array.length data) dans
    soit ofs =
      filtre layout avec
        C_layout -> 0
      | Fortran_layout -> 1
    dans
    pour i = 0 à Array.length data - 1 faire unsafe_set ba (i + ofs) data.(i) fait;
    ba
  soit map_file fd ?pos kind layout shared dim =
    Genarray.map_file fd ?pos kind layout shared [|dim|]
fin

module Array2 = struct
  type ('a, 'b, 'c) t = ('a, 'b, 'c) Genarray.t
  soit create kind layout dim1 dim2 =
    Genarray.create kind layout [|dim1; dim2|]
  dehors get: ('a, 'b, 'c) t -> int -> int -> 'a = "%caml_ba_ref_2"
  dehors set: ('a, 'b, 'c) t -> int -> int -> 'a -> unit = "%caml_ba_set_2"
  dehors unsafe_get: ('a, 'b, 'c) t -> int -> int -> 'a
     = "%caml_ba_unsafe_ref_2"
  dehors unsafe_set: ('a, 'b, 'c) t -> int -> int -> 'a -> unit
     = "%caml_ba_unsafe_set_2"
  dehors dim1: ('a, 'b, 'c) t -> int = "%caml_ba_dim_1"
  dehors dim2: ('a, 'b, 'c) t -> int = "%caml_ba_dim_2"
  dehors kind: ('a, 'b, 'c) t -> ('a, 'b) kind = "caml_ba_kind"
  dehors layout: ('a, 'b, 'c) t -> 'c layout = "caml_ba_layout"
  dehors sub_left: ('a, 'b, c_layout) t -> int -> int -> ('a, 'b, c_layout) t
     = "caml_ba_sub"
  dehors sub_right:
    ('a, 'b, fortran_layout) t -> int -> int -> ('a, 'b, fortran_layout) t
     = "caml_ba_sub"
  soit slice_left a n = Genarray.slice_left a [|n|]
  soit slice_right a n = Genarray.slice_right a [|n|]
  dehors blit: ('a, 'b, 'c) t -> ('a, 'b, 'c) t -> unit = "caml_ba_blit"
  dehors fill: ('a, 'b, 'c) t -> 'a -> unit = "caml_ba_fill"
  soit of_array (type t) kind (layout: t layout) data =
    soit dim1 = Array.length data dans
    soit dim2 = si dim1 = 0 alors 0 sinon Array.length data.(0) dans
    soit ba = create kind layout dim1 dim2 dans
    soit ofs =
      filtre layout avec
        C_layout -> 0
      | Fortran_layout -> 1
    dans
    pour i = 0 à dim1 - 1 faire
      soit row = data.(i) dans
      si Array.length row <> dim2 alors
        invalid_arg("Bigarray.Array2.of_array: non-rectangular data");
      pour j = 0 à dim2 - 1 faire
        unsafe_set ba (i + ofs) (j + ofs) row.(j)
      fait
    fait;
    ba
  soit map_file fd ?pos kind layout shared dim1 dim2 =
    Genarray.map_file fd ?pos kind layout shared [|dim1;dim2|]
fin

module Array3 = struct
  type ('a, 'b, 'c) t = ('a, 'b, 'c) Genarray.t
  soit create kind layout dim1 dim2 dim3 =
    Genarray.create kind layout [|dim1; dim2; dim3|]
  dehors get: ('a, 'b, 'c) t -> int -> int -> int -> 'a = "%caml_ba_ref_3"
  dehors set: ('a, 'b, 'c) t -> int -> int -> int -> 'a -> unit
     = "%caml_ba_set_3"
  dehors unsafe_get: ('a, 'b, 'c) t -> int -> int -> int -> 'a
     = "%caml_ba_unsafe_ref_3"
  dehors unsafe_set: ('a, 'b, 'c) t -> int -> int -> int -> 'a -> unit
     = "%caml_ba_unsafe_set_3"
  dehors dim1: ('a, 'b, 'c) t -> int = "%caml_ba_dim_1"
  dehors dim2: ('a, 'b, 'c) t -> int = "%caml_ba_dim_2"
  dehors dim3: ('a, 'b, 'c) t -> int = "%caml_ba_dim_3"
  dehors kind: ('a, 'b, 'c) t -> ('a, 'b) kind = "caml_ba_kind"
  dehors layout: ('a, 'b, 'c) t -> 'c layout = "caml_ba_layout"
  dehors sub_left: ('a, 'b, c_layout) t -> int -> int -> ('a, 'b, c_layout) t
     = "caml_ba_sub"
  dehors sub_right:
     ('a, 'b, fortran_layout) t -> int -> int -> ('a, 'b, fortran_layout) t
     = "caml_ba_sub"
  soit slice_left_1 a n m = Genarray.slice_left a [|n; m|]
  soit slice_right_1 a n m = Genarray.slice_right a [|n; m|]
  soit slice_left_2 a n = Genarray.slice_left a [|n|]
  soit slice_right_2 a n = Genarray.slice_right a [|n|]
  dehors blit: ('a, 'b, 'c) t -> ('a, 'b, 'c) t -> unit = "caml_ba_blit"
  dehors fill: ('a, 'b, 'c) t -> 'a -> unit = "caml_ba_fill"
  soit of_array (type t) kind (layout: t layout) data =
    soit dim1 = Array.length data dans
    soit dim2 = si dim1 = 0 alors 0 sinon Array.length data.(0) dans
    soit dim3 = si dim2 = 0 alors 0 sinon Array.length data.(0).(0) dans
    soit ba = create kind layout dim1 dim2 dim3 dans
    soit ofs =
      filtre layout avec
        C_layout -> 0
      | Fortran_layout -> 1
    dans
    pour i = 0 à dim1 - 1 faire
      soit row = data.(i) dans
      si Array.length row <> dim2 alors
        invalid_arg("Bigarray.Array3.of_array: non-cubic data");
      pour j = 0 à dim2 - 1 faire
        soit col = row.(j) dans
        si Array.length col <> dim3 alors
          invalid_arg("Bigarray.Array3.of_array: non-cubic data");
        pour k = 0 à dim3 - 1 faire
          unsafe_set ba (i + ofs) (j + ofs) (k + ofs) col.(k)
        fait
      fait
    fait;
    ba
  soit map_file fd ?pos kind layout shared dim1 dim2 dim3 =
    Genarray.map_file fd ?pos kind layout shared [|dim1;dim2;dim3|]
fin

dehors genarray_of_array1: ('a, 'b, 'c) Array1.t -> ('a, 'b, 'c) Genarray.t
   = "%identity"
dehors genarray_of_array2: ('a, 'b, 'c) Array2.t -> ('a, 'b, 'c) Genarray.t
   = "%identity"
dehors genarray_of_array3: ('a, 'b, 'c) Array3.t -> ('a, 'b, 'c) Genarray.t
   = "%identity"
soit array1_of_genarray a =
  si Genarray.num_dims a = 1 alors a
  sinon invalid_arg "Bigarray.array1_of_genarray"
soit array2_of_genarray a =
  si Genarray.num_dims a = 2 alors a
  sinon invalid_arg "Bigarray.array2_of_genarray"
soit array3_of_genarray a =
  si Genarray.num_dims a = 3 alors a
  sinon invalid_arg "Bigarray.array3_of_genarray"

dehors reshape:
   ('a, 'b, 'c) Genarray.t -> int array -> ('a, 'b, 'c) Genarray.t
   = "caml_ba_reshape"
soit reshape_1 a dim1 = reshape a [|dim1|]
soit reshape_2 a dim1 dim2 = reshape a [|dim1;dim2|]
soit reshape_3 a dim1 dim2 dim3 = reshape a [|dim1;dim2;dim3|]

(* Force caml_ba_get_{1,2,3,N} to be linked in, since we don't refer
   to those primitives directly in this file *)

soit _ =
  soit _ = Genarray.get dans
  soit _ = Array1.get dans
  soit _ = Array2.get dans
  soit _ = Array3.get dans
  ()

dehors get1: unit -> unit = "caml_ba_get_1"
dehors get2: unit -> unit = "caml_ba_get_2"
dehors get3: unit -> unit = "caml_ba_get_3"
dehors set1: unit -> unit = "caml_ba_set_1"
dehors set2: unit -> unit = "caml_ba_set_2"
dehors set3: unit -> unit = "caml_ba_set_3"
