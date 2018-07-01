(* TEST
files = "myppx.ml"
include ocamlcommon

* skip
** setup-ocamlc.byte-build-env
*** ocamlc.byte
program = "${test_build_directory}/myppx.exe"
all_modules = "myppx.ml"
**** ocamlc.byte
module = "test.ml"
flags = "-thread -ppx ${program}"
***** ocamlc.byte
module = "test.ml"
flags = "-vmthread -ppx ${program}"
****** check-ocamlc.byte-output
*)

(* empty *)

(* we skip this test in the menhir-wip branch: incompatible with
   yacc+menhir double parser runs *)
