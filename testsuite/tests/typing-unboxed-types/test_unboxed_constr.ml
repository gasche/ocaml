(* TEST
   flags = "-dheadshape"
   * expect
*)

(* Check the unboxing of constructors *)
type t = A of int | B;;
[%%expect{|
SHAPE(t/88[1]) {head_imm = Shape_set [0]; head_blocks = Shape_set [0]; head_separated = true}
type t = A of int | B
|}];;

type t = A of int | B of float | C | D;;
[%%expect{|
SHAPE(t/91[2]) {head_imm = Shape_set [0; 1]; head_blocks = Shape_set [0; 1]; head_separated = true}
type t = A of int | B of float | C | D
|}];;

type t = A of int [@unboxed] | B;;
[%%expect{|
SHAPE(t/96[3]) CONFLICT
type t = A of int [@unboxed] | B
|}];;

type t = A of float [@unboxed] | B;;
[%%expect{|
t/99[4] IS NOT SEPARABLE
SHAPE(t/99[4]) {head_imm = Shape_set [0]; head_blocks = Shape_set [253]; head_separated = false}
type t = A of float [@unboxed] | B
|}];;

type t = A of float [@unboxed] | B of string [@unboxed] | C | D of int;;
[%%expect{|
t/102[5] IS NOT SEPARABLE
SHAPE(t/102[5]) {head_imm = Shape_set [0]; head_blocks = Shape_set [0; 252; 253]; head_separated = false}
type t = A of float [@unboxed] | B of string [@unboxed] | C | D of int
|}];;

type t = K of int u u [@unboxed]
and 'a u = 'a id
and 'a id = Id of 'a [@unboxed];;
[%%expect{|
SHAPE(t/107[6]) {head_imm = Shape_any; head_blocks = Shape_set []; head_separated = true}
id/109[6] IS NOT SEPARABLE
SHAPE(id/109[6]) {head_imm = Shape_any; head_blocks = Shape_any; head_separated = false}
type t = K of int u u [@unboxed]
and 'a u = 'a id
and 'a id = Id of 'a [@unboxed]
|}];;

type t = { a : int } [@@unboxed]
and tt = A of t [@unboxed];;
[%%expect{|
SHAPE(tt/113[7]) {head_imm = Shape_any; head_blocks = Shape_set []; head_separated = true}
type t = { a : int; } [@@unboxed]
and tt = A of t [@unboxed]
|}];;

type t = A of { a : int } [@unboxed];;
[%%expect{|
SHAPE(t/116[8]) {head_imm = Shape_any; head_blocks = Shape_set []; head_separated = true}
type t = A of { a : int; } [@unboxed]
|}];;

type ('a, 'r) u = 'r
and 'a t = A of { body : 'r. ('a, 'r) u } [@unboxed];;
[%%expect{|
t/120[9] IS NOT SEPARABLE
SHAPE(t/120[9]) {head_imm = Shape_any; head_blocks = Shape_any; head_separated = false}
type ('a, 'r) u = 'r
and 'a t = A of { body : 'r. ('a, 'r) u; } [@unboxed]
|}];;
