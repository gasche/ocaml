(* TEST
   flags = "-dlambda -dno-locations -dno-unique-ids"; (* TODO: use -dcanonical-ids *)
   expect;
*)

module NoImmSingleTag = struct
  type t = C of string [@unboxed]

  let f = function
    | C s -> String.length s

  let () =
    assert (f (C "foo") = 3);
end
[%%expect {|
(apply (field_mut 1 (global Toploop!)) "NoImmSingleTag/353"
  (let
    (f = (function param : int (string.length param))
     *match* =
       (if (== (apply f "foo") 3) 0
         (raise (makeblock 0 (global Assert_failure!) [0: "" 8 4]))))
    (makeblock 0 f)))
module NoImmSingleTag :
  sig type t = C of string [@unboxed] val f : t -> int end
|}]

module NoImmDenseTags = struct
  type t = A of int | B of int * int | C of string

  let f = function
    | A i -> i
    | B (a, b) -> a + b
    | C s -> String.length s

  let () =
    assert (f (A 12) = 12);
    assert (f (B (4, 3)) = 7);
    assert (f (C "foo") = 3);
end
[%%expect {|
(apply (field_mut 1 (global Toploop!)) "NoImmDenseTags/367"
  (let
    (f =
       (function param : int
         (switch* param
          case tag 0: (field_imm 0 param)
          case tag 1: (+ (field_imm 0 param) (field_imm 1 param))
          case tag 2: (string.length (field_imm 0 param))))
     *match* =
       (seq
         (if (== (apply f [0: 12]) 12) 0
           (raise (makeblock 0 (global Assert_failure!) [0: "" 10 4])))
         (if (== (apply f [1: 4 3]) 7) 0
           (raise (makeblock 0 (global Assert_failure!) [0: "" 11 4])))
         (if (== (apply f [2: "foo"]) 3) 0
           (raise (makeblock 0 (global Assert_failure!) [0: "" 12 4])))))
    (makeblock 0 f)))
module NoImmDenseTags :
  sig type t = A of int | B of int * int | C of string val f : t -> int end
|}]

module NoImmSparseTags = struct
  type t = A of int | B of int * int | C of string [@unboxed]

  let f = function
    | A i -> i
    | B (a, b) -> a + b
    | C s -> String.length s

  let () =
    assert (f (A 12) = 12);
    assert (f (B (4, 3)) = 7);
    assert (f (C "foo") = 3);
end
[%%expect {|
(apply (field_mut 1 (global Toploop!)) "NoImmSparseTags/381"
  (let
    (f =
       (function param : int
         (if (!= (caml_obj_tag param) 1)
           (if (>= (caml_obj_tag param) 252) (string.length param)
             (field_imm 0 param))
           (+ (field_imm 0 param) (field_imm 1 param))))
     *match* =
       (seq
         (if (== (apply f [0: 12]) 12) 0
           (raise (makeblock 0 (global Assert_failure!) [0: "" 10 4])))
         (if (== (apply f [1: 4 3]) 7) 0
           (raise (makeblock 0 (global Assert_failure!) [0: "" 11 4])))
         (if (== (apply f "foo") 3) 0
           (raise (makeblock 0 (global Assert_failure!) [0: "" 12 4])))))
    (makeblock 0 f)))
module NoImmSparseTags :
  sig
    type t = A of int | B of int * int | C of string [@unboxed]
    val f : t -> int
  end
|}]

module AnyImmSingleTag = struct
  type t = A of int [@unboxed] | B of string [@unboxed]

  let f = function
    | A i -> i
    | B s -> String.length s

  let () =
    assert (f (A 12) = 12);
    assert (f (B "foo") = 3);
end
[%%expect {|
(apply (field_mut 1 (global Toploop!)) "AnyImmSingleTag/392"
  (let
    (f =
       (function param : int (if (isint param) param (string.length param)))
     *match* =
       (seq
         (if (== (apply f 12) 12) 0
           (raise (makeblock 0 (global Assert_failure!) [0: "" 9 4])))
         (if (== (apply f "foo") 3) 0
           (raise (makeblock 0 (global Assert_failure!) [0: "" 10 4])))))
    (makeblock 0 f)))
module AnyImmSingleTag :
  sig
    type t = A of int [@unboxed] | B of string [@unboxed]
    val f : t -> int
  end
|}]

module AnyImmDenseTags = struct
  type t = A of int [@unboxed] | B of int * int | C of string

  let f = function
    | A i -> i
    | B (a, b) -> a + b
    | C s -> String.length s

  let () =
    assert (f (A 12) = 12);
    assert (f (B (4, 3)) = 7);
    assert (f (C "foo") = 3);
end
[%%expect {|
(apply (field_mut 1 (global Toploop!)) "AnyImmDenseTags/406"
  (let
    (f =
       (function param : int
         (if (isint param) param
           (switch* param
            case tag 0: (+ (field_imm 0 param) (field_imm 1 param))
            case tag 1: (string.length (field_imm 0 param)))))
     *match* =
       (seq
         (if (== (apply f 12) 12) 0
           (raise (makeblock 0 (global Assert_failure!) [0: "" 10 4])))
         (if (== (apply f [0: 4 3]) 7) 0
           (raise (makeblock 0 (global Assert_failure!) [0: "" 11 4])))
         (if (== (apply f [1: "foo"]) 3) 0
           (raise (makeblock 0 (global Assert_failure!) [0: "" 12 4])))))
    (makeblock 0 f)))
module AnyImmDenseTags :
  sig
    type t = A of int [@unboxed] | B of int * int | C of string
    val f : t -> int
  end
|}]

module AnyImmSparseTags = struct
  type t = A of int [@unboxed] | B of int * int | C of string [@unboxed]

  let f = function
    | A i -> i
    | B (a, b) -> a + b
    | C s -> String.length s

  let () =
    assert (f (A 12) = 12);
    assert (f (B (4, 3)) = 7);
    assert (f (C "foo") = 3);
end
[%%expect {|
(apply (field_mut 1 (global Toploop!)) "AnyImmSparseTags/420"
  (let
    (f =
       (function param : int
         (if (isint param) param
           (if (>= (caml_obj_tag param) 252) (string.length param)
             (+ (field_imm 0 param) (field_imm 1 param)))))
     *match* =
       (seq
         (if (== (apply f 12) 12) 0
           (raise (makeblock 0 (global Assert_failure!) [0: "" 10 4])))
         (if (== (apply f [0: 4 3]) 7) 0
           (raise (makeblock 0 (global Assert_failure!) [0: "" 11 4])))
         (if (== (apply f "foo") 3) 0
           (raise (makeblock 0 (global Assert_failure!) [0: "" 12 4])))))
    (makeblock 0 f)))
module AnyImmSparseTags :
  sig
    type t = A of int [@unboxed] | B of int * int | C of string [@unboxed]
    val f : t -> int
  end
|}]

module SingleImmNoTag = struct
  type u = Foo
  type t = A of u [@unboxed]

  let f = function
    | A Foo -> 12

  let () =
    assert (f (A Foo) = 12);
end
[%%expect {|
(apply (field_mut 1 (global Toploop!)) "SingleImmNoTag/430"
  (let
    (f = (function param : int 12)
     *match* =
       (if (== (apply f 0) 12) 0
         (raise (makeblock 0 (global Assert_failure!) [0: "" 9 4]))))
    (makeblock 0 f)))
module SingleImmNoTag :
  sig type u = Foo type t = A of u [@unboxed] val f : t -> int end
|}]

module SingleImmSingleTag = struct
  type u = Foo
  type t = A of u [@unboxed] | B of string

  let f = function
    | A Foo -> 12
    | B s -> String.length s

  let () =
    assert (f (A Foo) = 12);
    assert (f (B "foo") = 3);
end
[%%expect {|
(apply (field_mut 1 (global Toploop!)) "SingleImmSingleTag/442"
  (let
    (f =
       (function param : int
         (if param (string.length (field_imm 0 param)) 12))
     *match* =
       (seq
         (if (== (apply f 0) 12) 0
           (raise (makeblock 0 (global Assert_failure!) [0: "" 10 4])))
         (if (== (apply f [0: "foo"]) 3) 0
           (raise (makeblock 0 (global Assert_failure!) [0: "" 11 4])))))
    (makeblock 0 f)))
module SingleImmSingleTag :
  sig
    type u = Foo
    type t = A of u [@unboxed] | B of string
    val f : t -> int
  end
|}]

module SingleImmDenseTags = struct
  type u = Foo
  type t = A of u [@unboxed] | B of int * int | C of string

  let f = function
    | A Foo -> 12
    | B (a, b) -> a + b
    | C s -> String.length s

  let () =
    assert (f (A Foo) = 12);
    assert (f (B (4, 3)) = 7);
    assert (f (C "foo") = 3);
end
[%%expect {|
(apply (field_mut 1 (global Toploop!)) "SingleImmDenseTags/457"
  (let
    (f =
       (function param : int
         (switch* param
          case int 0: 12
          case tag 0: (+ (field_imm 0 param) (field_imm 1 param))
          case tag 1: (string.length (field_imm 0 param))))
     *match* =
       (seq
         (if (== (apply f 0) 12) 0
           (raise (makeblock 0 (global Assert_failure!) [0: "" 11 4])))
         (if (== (apply f [0: 4 3]) 7) 0
           (raise (makeblock 0 (global Assert_failure!) [0: "" 12 4])))
         (if (== (apply f [1: "foo"]) 3) 0
           (raise (makeblock 0 (global Assert_failure!) [0: "" 13 4])))))
    (makeblock 0 f)))
module SingleImmDenseTags :
  sig
    type u = Foo
    type t = A of u [@unboxed] | B of int * int | C of string
    val f : t -> int
  end
|}]

module SingleImmSparseTags = struct
  type u = Foo
  type t = A of u [@unboxed] | B of int * int | C of string [@unboxed]

  let f = function
    | A Foo -> 12
    | B (a, b) -> a + b
    | C s -> String.length s

  let () =
    assert (f (A Foo) = 12);
    assert (f (B (4, 3)) = 7);
    assert (f (C "foo") = 3);
end
[%%expect {|
(apply (field_mut 1 (global Toploop!)) "SingleImmSparseTags/472"
  (let
    (f =
       (function param : int
         (if (isint param) 12
           (if (>= (caml_obj_tag param) 252) (string.length param)
             (+ (field_imm 0 param) (field_imm 1 param)))))
     *match* =
       (seq
         (if (== (apply f 0) 12) 0
           (raise (makeblock 0 (global Assert_failure!) [0: "" 11 4])))
         (if (== (apply f [0: 4 3]) 7) 0
           (raise (makeblock 0 (global Assert_failure!) [0: "" 12 4])))
         (if (== (apply f "foo") 3) 0
           (raise (makeblock 0 (global Assert_failure!) [0: "" 13 4])))))
    (makeblock 0 f)))
module SingleImmSparseTags :
  sig
    type u = Foo
    type t = A of u [@unboxed] | B of int * int | C of string [@unboxed]
    val f : t -> int
  end
|}]

module DenseImmNoTags = struct
  type u = Foo | Bar
  type t = A of u [@unboxed]

  let f = function
    | A Foo -> 12
    | A Bar -> 24

  let () =
    assert (f (A Foo) = 12);
    assert (f (A Bar) = 24);
end
[%%expect {|
(apply (field_mut 1 (global Toploop!)) "DenseImmNoTags/483"
  (let
    (f = (function param : int (if param 24 12))
     *match* =
       (seq
         (if (== (apply f 0) 12) 0
           (raise (makeblock 0 (global Assert_failure!) [0: "" 10 4])))
         (if (== (apply f 1) 24) 0
           (raise (makeblock 0 (global Assert_failure!) [0: "" 11 4])))))
    (makeblock 0 f)))
module DenseImmNoTags :
  sig type u = Foo | Bar type t = A of u [@unboxed] val f : t -> int end
|}]

module DenseImmSingleTag = struct
  type t = Foo | Bar | C of string [@unboxed]

  let f = function
    | Foo -> 12
    | Bar -> 24
    | C s -> String.length s

  let () =
    assert (f Foo = 12);
    assert (f Bar = 24);
    assert (f (C "baz") = 3);
end
[%%expect {|
(apply (field_mut 1 (global Toploop!)) "DenseImmSingleTag/494"
  (let
    (f =
       (function param : int
         (if (isint param) (if param 24 12) (string.length param)))
     *match* =
       (seq
         (if (== (apply f 0) 12) 0
           (raise (makeblock 0 (global Assert_failure!) [0: "" 10 4])))
         (if (== (apply f 1) 24) 0
           (raise (makeblock 0 (global Assert_failure!) [0: "" 11 4])))
         (if (== (apply f "baz") 3) 0
           (raise (makeblock 0 (global Assert_failure!) [0: "" 12 4])))))
    (makeblock 0 f)))
module DenseImmSingleTag :
  sig type t = Foo | Bar | C of string [@unboxed] val f : t -> int end
|}]

module DenseImmSparseTags = struct
  type t = Foo | Bar | B of int * int | C of string [@unboxed]

  let f = function
    | Foo -> 12
    | Bar -> 24
    | B (a, b) -> a + b
    | C s -> String.length s

  let () =
    assert (f Foo = 12);
    assert (f Bar = 24);
    assert (f (B (4, 3)) = 7);
    assert (f (C "baz") = 3);
end
[%%expect {|
(apply (field_mut 1 (global Toploop!)) "DenseImmSparseTags/508"
  (let
    (f =
       (function param : int
         (if (isint param) (if param 24 12)
           (if (>= (caml_obj_tag param) 252) (string.length param)
             (+ (field_imm 0 param) (field_imm 1 param)))))
     *match* =
       (seq
         (if (== (apply f 0) 12) 0
           (raise (makeblock 0 (global Assert_failure!) [0: "" 11 4])))
         (if (== (apply f 1) 24) 0
           (raise (makeblock 0 (global Assert_failure!) [0: "" 12 4])))
         (if (== (apply f [0: 4 3]) 7) 0
           (raise (makeblock 0 (global Assert_failure!) [0: "" 13 4])))
         (if (== (apply f "baz") 3) 0
           (raise (makeblock 0 (global Assert_failure!) [0: "" 14 4])))))
    (makeblock 0 f)))
module DenseImmSparseTags :
  sig
    type t = Foo | Bar | B of int * int | C of string [@unboxed]
    val f : t -> int
  end
|}]

module SizeDiscrimination = struct
  type 'a pair = 'a * 'a
  type 'a triple = 'a * 'a * 'a
  type t = A | B of int pair [@unboxed] | C of int triple [@unboxed]

  let f = function
    | A -> 0
    | B (a, b) -> a + b
    | C (a, b, c) -> a + b + c

  let () =
    assert (f A = 0);
    assert (f (B(3, 4)) = 7);
    assert (f (C(3, 4, 5)) = 12);
end
[%%expect {|
(apply (field_mut 1 (global Toploop!)) "SizeDiscrimination/525"
  (let
    (f =
       (function param : int
         (switch* param
          case int 0: 0
          case tag 0:
           (if (>= (array.length[addr] param) 3)
             (+ (+ (field_imm 0 param) (field_imm 1 param))
               (field_imm 2 param))
             (+ (field_imm 0 param) (field_imm 1 param)))))
     *match* =
       (seq
         (if (== (apply f 0) 0) 0
           (raise (makeblock 0 (global Assert_failure!) [0: "" 12 4])))
         (if (== (apply f [0: 3 4]) 7) 0
           (raise (makeblock 0 (global Assert_failure!) [0: "" 13 4])))
         (if (== (apply f [0: 3 4 5]) 12) 0
           (raise (makeblock 0 (global Assert_failure!) [0: "" 14 4])))))
    (makeblock 0 f)))
module SizeDiscrimination :
  sig
    type 'a pair = 'a * 'a
    type 'a triple = 'a * 'a * 'a
    type t = A | B of int pair [@unboxed] | C of int triple [@unboxed]
    val f : t -> int
  end
|}]
