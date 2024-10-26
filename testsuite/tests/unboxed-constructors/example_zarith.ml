(* TEST
   setup-ocamlc.byte-build-env;
   compile_only = "true";
   flags = "-dsource -dlambda -stop-after lambda -dno-locations -dno-unique-ids";
   ocamlc.byte;
   check-ocamlc.byte-output;
*)
module Gmp = struct
  type t [@@shape [custom]]

  (* imaginary externals, for the sake of the example *)
  external of_int : (int[@untagged]) -> t = "gmp_of_int" "gmp_of_int_tagged"
  external add : t -> t -> t = "gmp_add"
  external add_int : t -> (int[@untagged]) -> t = "gmp_add_int" "gmp_add_int_tagged"
end

(* imaginary external, for the sake of the example *)
external add_would_overflow : int -> int -> bool = "int_add_would_overflow"

type zarith =
  | Small of int [@unboxed]
  | Big of Gmp.t [@unboxed]

let add z1 z2 =
  match z1, z2 with
  | Big gmp1, Big gmp2 ->
      Big (Gmp.add gmp1 gmp2)
  | Big gmp, Small n | Small n, Big gmp ->
      Big (Gmp.add_int gmp n)
  | Small n1, Small n2 ->
      if add_would_overflow n1 n2 then
        Big (Gmp.add_int (Gmp.of_int n1) n2)
      else
        Small (n1 + n2)

