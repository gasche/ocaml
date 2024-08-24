(* TEST
   flags = "-dlambda -dno-locations -dno-unique-ids";
   expect;
*)

(* Basic usage: redefine atomics. *)

module Basic = struct
  type 'a atomic = { mutable filler: unit; mutable x : 'a [@atomic] }

  let get (type a) (v : a atomic) : a = v.x

  let compare_and_set (type a) (v : a atomic) (old_ : a) (new_ : a) : bool =
    Atomic.Loc.compare_and_set [%atomic.loc v.x] old_ new_

  (* it is also possible to use the location as a first-class field *)
  let[@inline never] get_loc (type a) (v : a atomic) : a Atomic.Loc.t =
    [%atomic.loc v.x]

  let less_efficient_set (type a) (v : a atomic) (new_ : a) =
    Atomic.Loc.set (get_loc v) new_
end
[%%expect{|
(apply (field_mut 1 (global Toploop!)) "Basic/329"
  (let
    (get = (function v (atomic_load_field v 1))
     compare_and_set =
       (function v old_ new_ : int (atomic_cas_field v 1 old_ new_))
     get_loc = (function v never_inline (makeblock 0 (*,int) v 1))
     less_efficient_set =
       (function v new_ : int
         (apply (field_imm 0 (field_imm 0 (global Stdlib__Atomic!)))
           (apply get_loc v) new_)))
    (makeblock 0 get compare_and_set get_loc less_efficient_set)))
module Basic :
  sig
    type 'a atomic = { mutable filler : unit; mutable x : 'a [@atomic]; }
    val get : 'a atomic -> 'a
    val compare_and_set : 'a atomic -> 'a -> 'a -> bool
    val get_loc : 'a atomic -> 'a Atomic.Loc.t
    val less_efficient_set : 'a atomic -> 'a -> unit
  end
|}];;


(* If you mark a non-mutable field as atomic,
   taking its location is an error. *)
module Weird = struct
  type t = { x : int [@atomic] }

  let this_is_an_error (w : t) =
    [%ocaml.atomic.loc w.x]

  (* TODO: we should forbid this,
     only support [@atomic] on mutable fields. *)
end
[%%expect{|
Line 5, characters 23-26:
5 |     [%ocaml.atomic.loc w.x]
                           ^^^
Error: The record field "x" is not mutable
|}];;


(* Check module interface checking: it is not allowed to remove or add
   atomic attributes. *)

module Wrong1 = (struct
  type t = { mutable x : int }
end : sig
  (* adding an 'atomic' attribute missing in the implementation: invalid. *)
  type t = { mutable x : int [@atomic] }
end)
[%%expect{|
Lines 1-3, characters 17-3:
1 | .................struct
2 |   type t = { mutable x : int }
3 | end......
Error: Signature mismatch:
       Modules do not match:
         sig type t = { mutable x : int; } end
       is not included in
         sig type t = { mutable x : int [@atomic]; } end
       Type declarations do not match:
         type t = { mutable x : int; }
       is not included in
         type t = { mutable x : int [@atomic]; }
       Fields do not match:
         "mutable x : int;"
       is not the same as:
         "mutable x : int [@atomic];"
       The second is atomic and the first is not.
|}];;

module Wrong2 = (struct
  type t = { mutable x : int [@atomic] }
end : sig
  (* removing an 'atomic' attribute present in the implementation: invalid. *)
  type t = { mutable x : int }
end)
[%%expect{|
Lines 1-3, characters 17-3:
1 | .................struct
2 |   type t = { mutable x : int [@atomic] }
3 | end......
Error: Signature mismatch:
       Modules do not match:
         sig type t = { mutable x : int [@atomic]; } end
       is not included in
         sig type t = { mutable x : int; } end
       Type declarations do not match:
         type t = { mutable x : int [@atomic]; }
       is not included in
         type t = { mutable x : int; }
       Fields do not match:
         "mutable x : int [@atomic];"
       is not the same as:
         "mutable x : int;"
       The first is atomic and the second is not.
|}];;

module Ok = (struct
  type t = { mutable x : int [@atomic] }
end : sig
  type t = { mutable x : int [@atomic] }
end)
[%%expect{|
(apply (field_mut 1 (global Toploop!)) "Ok/349" (makeblock 0))
module Ok : sig type t = { mutable x : int [@atomic]; } end
|}];;



(* Inline records are supported, including in extensions. *)

module Inline_record = struct
  type t = A of { mutable x : int [@atomic] }

  let test : t -> int = fun (A r) -> r.x
end
[%%expect{|
(apply (field_mut 1 (global Toploop!)) "Inline_record/357"
  (let (test = (function param : int (atomic_load_field param 0)))
    (makeblock 0 test)))
module Inline_record :
  sig type t = A of { mutable x : int [@atomic]; } val test : t -> int end
|}];;

module Extension_with_inline_record = struct
  type t = ..
  type t += A of { mutable x : int [@atomic] }

  (* one should see in the -dlambda output below that the field offset is not 0
     as one could expect, but 1, due to an extra argument in extensible variants. *)
  let test : t -> int = function
    | A r -> r.x
    | _ -> 0
end
[%%expect{|
(apply (field_mut 1 (global Toploop!)) "Extension_with_inline_record/365"
  (let
    (A =
       (makeblock 248 "Extension_with_inline_record.A" (caml_fresh_oo_id 0))
     test =
       (function param : int
         (if (== (field_imm 0 param) A) (atomic_load_field param 1) 0)))
    (makeblock 0 A test)))
module Extension_with_inline_record :
  sig
    type t = ..
    type t += A of { mutable x : int [@atomic]; }
    val test : t -> int
  end
|}];;


(* Marking a field [@atomic] in a float-only record disables the unboxing optimization. *)
module Float_records = struct
  type t = { x : float; mutable y : float [@atomic] }

  (* one should see in the -dlambda output below that this creates a block of tag 0. *)
  let mk_t x y : t = { x; y }
  let get v = v.y
end
[%%expect{|
(apply (field_mut 1 (global Toploop!)) "Float_records/377"
  (let
    (mk_t = (function x[float] y[float] (makemutable 0 (float,float) x y))
     get = (function v : float (atomic_load_field v 1)))
    (makeblock 0 mk_t get)))
module Float_records :
  sig
    type t = { x : float; mutable y : float [@atomic]; }
    val mk_t : float -> float -> t
    val get : t -> float
  end
|}];;


