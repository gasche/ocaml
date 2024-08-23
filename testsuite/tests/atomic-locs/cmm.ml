(* TEST_BELOW *)

type 'a atomic = { filler : unit; mutable x : 'a [@atomic] }

let get (v : 'a atomic) : 'a =
  Atomic.Loc.get [%atomic.loc v.x]

let get_immediate (v : int atomic) : int =
  Atomic.Loc.get [%atomic.loc v.x]

let compare_and_set (v : 'a atomic) old_ new_ : bool =
  Atomic.Loc.compare_and_set [%atomic.loc v.x] old_ new_

(* Compare with standard atomics *)
let standard_atomic_get (v : 'a Atomic.t) = Atomic.get v

let standard_atomic_get_immediate (v : int Atomic.t) = Atomic.get v

(* TEST
   no-flambda; (* the output will be slightly different under flambda, meh. *)
   setup-ocamlopt.byte-build-env;
   flags = "-c -dcmm -dno-locations -dno-unique-ids";
   ocamlopt.byte;
   check-ocamlopt.byte-output;
*)
