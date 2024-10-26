(* TEST
   flags="-dheadshape";
   expect;
*)

type 'a unboxed = Unboxed of 'a [@unboxed]
[%%expect{|
shape of _ unboxed: {imm = Any; blocks = Any;}
type 'a unboxed = Unboxed of 'a [@unboxed]
|}]

type t = int unboxed
[%%expect{|
shape of t: {imm = Any; blocks = [];}
type t = int unboxed
|}]

type valid = Nonconst of unit | Int of t [@unboxed]
[%%expect{|
shape of valid: {imm = Any; blocks = [0: [1]];}
type valid = Nonconst of unit | Int of t [@unboxed]
|}]
