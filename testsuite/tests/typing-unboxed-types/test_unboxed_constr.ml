(* TEST
   flags = "-dheadshape"
   * expect
*)

(* Check the unboxing of constructors *)
type t = A of int | B;;
[%%expect{|
SHAPE(t/88[1]) {head_imm = Shape_set [0]; head_blocks = Shape_set [0]}
type t = A of int | B
|}];;

type t = A of int | B of float | C | D;;
[%%expect{|
SHAPE(t/91[2]) {head_imm = Shape_set [0; 1]; head_blocks = Shape_set [0; 1]}
type t = A of int | B of float | C | D
|}];;

type t = A of int [@unboxed] | B;;
[%%expect{|
SHAPE(t/96[3]) CONFLICT
type t = A of int | B
|}];;

type t = A of float [@unboxed] | B;;
[%%expect{|
SHAPE(t/99[4]) {head_imm = Shape_set [0]; head_blocks = Shape_set [253]}
type t = A of float | B
|}];;

type t = A of float [@unboxed] | B of string [@unboxed] | C | D of int;;
[%%expect{|
SHAPE(t/102[5]) {head_imm = Shape_set [0]; head_blocks = Shape_set [0; 252; 253]}
type t = A of float | B of string | C | D of int
|}];;

type t = K of int u u [@unboxed]
and 'a u = 'a id
and 'a id = Id of 'a [@unboxed];;
[%%expect{|
SHAPE(t/107[6]) {head_imm = Shape_any; head_blocks = Shape_set []}
SHAPE(id/109[6]) {head_imm = Shape_any; head_blocks = Shape_any}
type t = K of int u u
and 'a u = 'a id
and 'a id = Id of 'a
|}];;

type t = { a : int } [@@unboxed]
and tt = A of t [@unboxed];;
[%%expect{|
SHAPE(tt/113[7]) {head_imm = Shape_any; head_blocks = Shape_set []}
type t = { a : int; } [@@unboxed]
and tt = A of t
|}];;

type t = A of { a : int } [@unboxed];;
[%%expect{|
SHAPE(t/116[8]) {head_imm = Shape_any; head_blocks = Shape_set []}
type t = A of { a : int; }
|}];;

type ('a, 'r) u = 'r
and 'a t = A of { body : 'r. ('a, 'r) u } [@unboxed];;
[%%expect{|
SHAPE(t/120[9]) {head_imm = Shape_any; head_blocks = Shape_any}
type ('a, 'r) u = 'r
and 'a t = A of { body : 'r. ('a, 'r) u; }
|}];;
