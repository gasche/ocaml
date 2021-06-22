(* TEST
*)

module A = struct
  type t = A of int | B of float [@unboxed]

  let f = function A _ -> 0 | B _ -> 1

  let test () =
    assert (f (A 0) = 0);
    assert (f (B 0.) = 1)
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
