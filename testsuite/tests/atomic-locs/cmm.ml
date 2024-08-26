(* TEST_BELOW *)

(* standard atomics *)

let standard_atomic_get (r : 'a Atomic.t) =
  Atomic.get r

let standard_atomic_cas (r : 'a Atomic.t) oldv newv =
  Atomic.compare_and_set r oldv newv


(* atomic record fields *)

type 'a atomic = { filler : unit; mutable x : 'a [@atomic] }

let get (r : 'a atomic) : 'a =
  r.x

let set (r : 'a atomic) v =
  r.x <- v

let cas (r : 'a atomic) oldv newv =
  Atomic.Loc.compare_and_set [%atomic.loc r.x] oldv newv

(* TEST
   not-windows; (* MSVC uses a different symbol separator *)
   no-flambda; (* the output will be slightly different under Flambda *)
   no-tsan; (* TSan modifies the generated code *)
   setup-ocamlopt.byte-build-env;
   flags = "-c -dcmm -dno-locations -dno-unique-ids";
   ocamlopt.byte;
   check-ocamlopt.byte-output;
*)
