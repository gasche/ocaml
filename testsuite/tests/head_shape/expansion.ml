(* TEST
   flags="-dheadshape";
   expect;
*)

type 'a id1 = 'a
type foo = int id1 id1 id1
[%%expect {|
shape of _ id1: {imm = Any; blocks = Any;}
type 'a id1 = 'a
shape of foo: {imm = Any; blocks = [];}
type foo = int id1 id1 id1
|}]

type 'a id2 = { id : 'a } [@@unboxed]
type foo = int id2 id2 id2
[%%expect {|
shape of _ id2: {imm = Any; blocks = Any;}
type 'a id2 = { id : 'a; } [@@unboxed]
shape of foo: {imm = Any; blocks = [];}
type foo = int id2 id2 id2
|}]

type 'a id3 = Id of 'a [@unboxed]
type foo = int id3 id3 id3
[%%expect {|
shape of _ id3: {imm = Any; blocks = Any;}
type 'a id3 = Id of 'a [@unboxed]
shape of foo: {imm = Any; blocks = [];}
type foo = int id3 id3 id3
|}]
