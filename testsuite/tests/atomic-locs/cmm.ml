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

(* TEST
   no-flambda; (* the output will be slightly different under flambda, meh. *)
   setup-ocamlopt.byte-build-env;
   flags = "-c -dcmm -dno-locations -dno-unique-ids";
   ocamlopt.byte;
   check-ocamlopt.byte-output;
*)
