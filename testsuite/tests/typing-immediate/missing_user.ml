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

type should_fail_without_crashing = Missing_middle.abstract [@@immediate]
[%%expect{|
Line 1, characters 0-73:
1 | type should_fail_without_crashing = Missing_middle.abstract [@@immediate]
    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: Types marked with the immediate attribute must be non-pointer types
       like int or bool.
|}]

type should_pass = Missing_middle.immediate [@@immediate]
[%%expect{|
type should_pass = Missing_middle.immediate [@@immediate]
|}]
