(* TEST
   flags="-dheadshape";
   expect;
*)

type t = int
[%%expect{|
shape of t: {imm = Any; blocks = [];}
type t = int
|}]

type u =
  | Block of bool
  | Constant
  | Int of t [@unboxed]
[%%expect{|
Lines 1-4, characters 0-23:
1 | type u =
2 |   | Block of bool
3 |   | Constant
4 |   | Int of t [@unboxed]
Error: Constructors Int and Constant have overlapping representations.
         shape of Int: {imm = Any; blocks = [];}
         shape of Constant: {imm = [0]; blocks = [];}
|}]


type v =
  | Bool of bool
  | Maybe_int of int option [@unboxed]
[%%expect{|
Lines 1-3, characters 0-38:
1 | type v =
2 |   | Bool of bool
3 |   | Maybe_int of int option [@unboxed]
Error: Constructors Maybe_int and Bool have overlapping representations.
         shape of Maybe_int: {imm = [0]; blocks = [0: [1];];}
         shape of Bool: {imm = []; blocks = [0: [1];];}
|}]


(* There is *no* conflict between Single and Double,
   thanks to our tracking of size/arity *)
type 'a solution =
  | Zero
  | Single of 'a
  | Double of 'a pair [@unboxed]
and 'a pair = 'a * 'a
[%%expect{|
shape of _ solution: {imm = [0]; blocks = [0: [1; 2];];}
shape of _ pair: {imm = []; blocks = [0: [2];];}
type 'a solution = Zero | Single of 'a | Double of 'a pair
and 'a pair = 'a * 'a
|}]


type benign_cycle =
  | Cycle of benign_cycle [@unboxed]
[%%expect{|
shape of benign_cycle: {imm = Any; blocks = Any;}
type benign_cycle = Cycle of benign_cycle
|}]


type bad_cycle =
  | Case
  | Cycle of bad_cycle [@unboxed]
[%%expect{|
Lines 1-3, characters 0-33:
1 | type bad_cycle =
2 |   | Case
3 |   | Cycle of bad_cycle [@unboxed]
Error: Constructors Cycle and Case have overlapping representations.
         shape of Cycle: {imm = Any; blocks = Any;}
         shape of Case: {imm = [0]; blocks = [];}
|}]
