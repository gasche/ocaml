(* TEST

files = "missing_original.ml missing_middle.ml"
* setup-ocamlc.byte-build-env
** ocamlc.byte
module = "missing_original.ml"
*** ocamlc.byte
module = "missing_middle.ml"
**** script
script = "rm -f missing_original.cmi"
***** expect
*)


#directory "ocamlc.byte";;
#load "missing_middle.cmo"

type should_fail =
  | Abs : 'a Missing_middle.sep -> should_fail [@@unboxed]
[%%expect{|
Lines 1-2, characters 0-58:
1 | type should_fail =
2 |   | Abs : 'a Missing_middle.sep -> should_fail [@@unboxed]
Error: This type cannot be unboxed because
       it might contain both float and non-float values,
       depending on the instantiation of the existential variable 'a.
       You should annotate it with [@@ocaml.boxed].
|}]

type also_fail =
  | Abs : ('a * int) Missing_middle.deepsep -> also_fail [@@unboxed]
[%%expect{|
Lines 1-2, characters 0-68:
1 | type also_fail =
2 |   | Abs : ('a * int) Missing_middle.deepsep -> also_fail [@@unboxed]
Error: This type cannot be unboxed because
       it might contain both float and non-float values,
       depending on the instantiation of the existential variable 'a.
       You should annotate it with [@@ocaml.boxed].
|}]

type should_pass =
  | Abs : 'a Missing_middle.ind -> should_pass [@@unboxed]
[%%expect{|
type should_pass = Abs : 'a Missing_middle.ind -> should_pass [@@unboxed]
|}]
