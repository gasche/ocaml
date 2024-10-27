(* TEST
   expect;
*)

type t = Float of float [@unboxed] | Foo
[%%expect {|
Line 1, characters 0-40:
1 | type t = Float of float [@unboxed] | Foo
    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: This type declaration is non-separated, it contains both float and non-float values.
|}]

type custom [@@shape [custom]]
type t = Float of float [@unboxed] | Custom of custom [@unboxed]
[%%expect {|
type custom
Line 2, characters 0-64:
2 | type t = Float of float [@unboxed] | Custom of custom [@unboxed]
    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: This type declaration is non-separated, it contains both float and non-float values.
|}]

(* We need such GADTs to be rejected
   as they also break separability. *)
type t = Any : 'a -> t [@unboxed]
[%%expect {|
Line 1, characters 0-33:
1 | type t = Any : 'a -> t [@unboxed]
    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: This type declaration is non-separated, it contains both float and non-float values.
|}]

