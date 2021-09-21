(* TEST
   * setup-ocamlc.byte-build-env
   ** ocamlc.byte
   *** check-ocamlc.byte-output
   **** run
   ***** check-program-output
*)

module A = struct
  type t = A of int | B of string [@unboxed]

  let f = function A _ -> 0 | B _ -> 1

  let test () =
    assert (f (A 0) = 0);
    assert (f (B "0") = 1)
end

let () = A.test ()

module B = struct
  type t = A of int | B of float
  type tt = A' of t [@unboxed] | B'

  let f = function A' _ -> 0 | B' -> 1

  let test () =
    assert (f (A' (A 0)) = 0);
    assert (f (A' (B 0.)) = 0);
    assert (f B' = 1)
end

let () = B.test ()

module C = struct
  type t = I of int [@unboxed] | C1 of unit | C2 of unit

  let f = function I i -> i | C1 () -> 0 | C2 () -> 1
end
