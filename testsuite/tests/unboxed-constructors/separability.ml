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

type t = Float of float [@unboxed] | Abstract of abstract [@unboxed]
[%%expect {|
Line 1, characters 49-57:
1 | type t = Float of float [@unboxed] | Abstract of abstract [@unboxed]
                                                     ^^^^^^^^
Error: Unbound type constructor "abstract"
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

