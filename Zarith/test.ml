(* See 'Makefile' for building and running instructions *)
type test =
  | Wrong_int
  | Zarith
  | Boxed
  | Unboxed
  | Unboxed_both

let impls = [
  "wrong-int", Wrong_int;
  "zarith", Zarith;
  "boxed", Boxed;
  "unboxed", Unboxed;
  "unboxed_both", Unboxed_both;
]

let usage () =
  Printf.eprintf
    "Usage: %s [%s] <input : int> <n_iters: int >\n%!"
    (String.concat "|" (List.map fst impls))
    Sys.argv.(0)

let impl_choice = match List.assoc Sys.argv.(1) impls with
  | v -> v
  | exception _ -> usage (); exit 2

let factorial_input =
  try int_of_string Sys.argv.(2)
  with _ -> usage (); exit 3

let n_iters =
  try int_of_string Sys.argv.(3)
  with _ -> usage (); exit 4

(* Our benchmark computes (factorial n) in a silly way,
   using the repeated-addition definition of multiplication:

   !3 is computed as
     let !0 = 1 in
     let !1 = !0 in
     let !2 = !1 + !1 in
     let !3 = !2 + !2 + !2 in
     !3

   The number of additions is quadratic in the input n.

   The result of (factorial n) exceeds OCaml's 63-bit integers for n=21.
*)
let factorial of_int ( +! ) n =
  let rec ( *! ) a b =
    if b = 0 then of_int 0
    else a *! (b - 1) +! a
  in
  let rec fac n =
    if n = 0 then of_int 1
    else fac (n - 1) *! n
  in
  fac n

module Wrong_int = struct
  (* This a *wrong* implementation of bignums using integers that will overflow and wraparound.
     It is informative to compare the benchmark performance of this implementation
     with the correct implementations. *)
  let of_int n = n
  let add x y = x + y
  let fac = factorial of_int add
  let to_string = string_of_int
end

module Zarith = struct
  (* This is taken verbatim from Zarith's z.ml:
       https://github.com/ocaml/Zarith/blob/39df015/z.ml#L41-L49
  *)
  type t

  external is_small_int: t -> bool = "%obj_is_int"
  external unsafe_to_int: t -> int = "%identity"
  external of_int: int -> t = "%identity"

  external c_add: t -> t -> t = "ml_z_add"
  let add_zarith x y =
    if is_small_int x && is_small_int y then begin
      let z = unsafe_to_int x + unsafe_to_int y in
      (* Overflow check -- Hacker's Delight, section 2.12 *)
      if (z lxor unsafe_to_int x) land (z lxor unsafe_to_int y) >= 0
      then of_int z
      else c_add x y
    end else
      c_add x y

  (* new code *)
  let fac n = factorial of_int add_zarith n

  external c_format: string -> t -> string = "ml_z_format"
  let to_string n = c_format "%d" n
end

module Boxed = struct
  (* This is a naive, safe implementation of Zarith's fast-path logic,
     using an algebraic datatype to distinguish short from long integers. *)
  type gmp_t

  external c_add: gmp_t -> gmp_t -> gmp_t = "ml_z_add"
  external long_int : int -> gmp_t = "ml_z_of_int"

  type t =
    | Short of int
    | Long of gmp_t

  let of_int n = Short n

  let to_long = function
    | Short x -> long_int x
    | Long x -> x

  let add_boxed a b =
    match a, b with
    | Short x, Short y ->
        let z = x + y in
        (* Overflow check -- Hacker's Delight, section 2.12 *)
        if (z lxor x) land (z lxor y) >= 0
        then Short z
        else
          (* Note: in the general case of additions, in some cases the
             result of c_add may be a "short" integer again, and
             should be turned back into a Short if we wanted to mimick
             Zarith' representation invariants. The current approach
             is correct, simpler, and strictly equivalent for this
             benchmark as we only manipulate non-negative numbers. *)
          Long (c_add (long_int x) (long_int y))
    | _, _ -> Long (c_add (to_long a) (to_long b))

  let fac n = factorial of_int add_boxed n

  external c_format: string -> gmp_t -> string = "ml_z_format"
  let to_string = function
    | Short n -> string_of_int n
    | Long n -> c_format "%d" n
end

module Unboxed = struct
  (* This is a safe implementation of Zarith's fast-path logic,
     using an algebraic to distinguish short from long integers,
     unboxing the "short" constructor to get something close to Zarith's internal representation.

     The only different compared to the Boxed implementation above is the [@unboxed] annotation.
  *)
  type gmp_t

  type t =
    | Short of int [@unboxed]
    | Long of gmp_t

  external c_add: t -> t -> t = "ml_z_add_boxcustom"

  let of_int n = Short n

  let add_unboxed a b =
    match a, b with
    | Short x, Short y ->
        let z = x + y in
        (* Overflow check -- Hacker's Delight, section 2.12 *)
        if (z lxor x) land (z lxor y) >= 0
        then Short z
        else c_add a b
    | _, _ -> c_add a b

  let fac n = factorial of_int add_unboxed n

  external c_format: string -> gmp_t -> string = "ml_z_format"
  let to_string = function
    | Short n -> string_of_int n
    | Long n -> c_format "%d" n
end

module Unboxed_both = struct
  (* This is a safe implementation of Zarith's fast-path logic,
     using an algebraic to distinguish short from long integers,
     unboxing both constructors to recover Zarith's internal representation.
  *)
  type gmp_t [@@shape [custom]]

  type t =
    | Short of int [@unboxed]
    | Long of gmp_t [@unboxed]

  external c_add: t -> t -> t = "ml_z_add_unboxcustom"

  let of_int n = Short n

  let add_unboxed a b =
    match a, b with
    | Short x, Short y ->
        let z = x + y in
        (* Overflow check -- Hacker's Delight, section 2.12 *)
        if (z lxor x) land (z lxor y) >= 0
        then Short z
        else c_add a b
    | _, _ -> c_add a b

  let fac n = factorial of_int add_unboxed n

  external c_format: string -> gmp_t -> string = "ml_z_format"
  let to_string = function
    | Short n -> string_of_int n
    | Long n -> c_format "%d" n
end


let test to_string fac =
  for _i = 1 to n_iters - 1 do
    ignore (fac factorial_input);
  done;
  print_endline (to_string (fac factorial_input))

let () =
  match impl_choice with
  | Wrong_int ->
      test Wrong_int.to_string Wrong_int.fac
  | Zarith ->
      test Zarith.to_string Zarith.fac
  | Boxed ->
      test Boxed.to_string Boxed.fac
  | Unboxed ->
      test Unboxed.to_string Unboxed.fac
  | Unboxed_both ->
      test Unboxed_both.to_string Unboxed_both.fac
