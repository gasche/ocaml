(* TEST
 readonly_files = "example_1.ml example_2.ml";
 flags = "-drawlambda -dlambda";
 expect;
*)

(* See the head comment of [basic/patmatch_for_multiple.ml] for a discussion
   of why we enable both -drawlambda and -dlambda. *)

#use "example_1.ml";;
[%%expect {|
0
0
type u = { a : bool; mutable b : (bool, int) Either.t; }
(let
  (f_input/309 = (function param/311[int] (makemutable 0 (int,*) 1 [0: 1])))
  (apply (field_mut 1 (global Toploop!)) "f_input" f_input/309))
(let
  (f_input/309 = (function param/311[int] (makemutable 0 (int,*) 1 [0: 1])))
  (apply (field_mut 1 (global Toploop!)) "f_input" f_input/309))
val f_input : unit -> u = <fun>
(let
  (f/313 =
     (function x/315
       (let (x'1/337 =o (field_mut 1 x/315) x'0/338 =a (field_int 0 x/315))
         (catch
           (catch
             (catch (if x'0/338 (exit 4) [1: 1]) with (4)
               (switch* x'1/337
                case tag 0: (exit 3)
                case tag 1: (let (x'1'0/339 =a (field_imm 0 x'1/337)) [1: 2])))
            with (3)
             (if (seq (setfield_ptr 1 x/315 [1: 3]) 0) [1: 3] (exit 2)))
          with (2)
           (let (y/316 =a (field_imm 0 x'1/337)) (makeblock 0 (int) y/316))))))
  (apply (field_mut 1 (global Toploop!)) "f" f/313))
(let
  (f/313 =
     (function x/315
       (let (x'1/337 =o (field_mut 1 x/315))
         (if (field_int 0 x/315)
           (switch* x'1/337
            case tag 0:
             (if (seq (setfield_ptr 1 x/315 [1: 3]) 0) [1: 3]
               (makeblock 0 (int) (field_imm 0 x'1/337)))
            case tag 1: [1: 2])
           [1: 1]))))
  (apply (field_mut 1 (global Toploop!)) "f" f/313))
val f : u -> (bool, int) Result.t = <fun>
|}]

#use "example_2.ml";;
[%%expect {|
0
0
type 'a myref = { mutable mut : 'a; }
0
0
type u = { a : bool; b : (bool, int) Either.t myref; }
(let
  (f_input/345 =
     (function param/346[int] (makeblock 0 (int,*) 1 (makemutable 0 [0: 1]))))
  (apply (field_mut 1 (global Toploop!)) "f_input" f_input/345))
(let
  (f_input/345 =
     (function param/346[int] (makeblock 0 (int,*) 1 (makemutable 0 [0: 1]))))
  (apply (field_mut 1 (global Toploop!)) "f_input" f_input/345))
val f_input : unit -> u = <fun>
(let
  (f/349 =
     (function x/350
       (let (x'0/352 =a (field_int 0 x/350))
         (catch
           (catch
             (if x'0/352 (exit 6)
               (let (x'1/353 =a (field_imm 1 x/350)) [1: 1]))
            with (6)
             (let (x'1/354 =a (field_imm 1 x/350))
               (catch
                 (let (x'1'0/355 =o (field_mut 0 x'1/354))
                   (switch* x'1'0/355
                    case tag 0: (exit 7)
                    case tag 1:
                     (let (x'1'0'0/356 =a (field_imm 0 x'1'0/355)) [1: 2])))
                with (7)
                 (if (seq (setfield_ptr 0 (field_imm 1 x/350) [1: 3]) 0)
                   [1: 3] (exit 5)))))
          with (5)
           (let
             (x'1/357 =a (field_imm 1 x/350)
              x'1'0/358 =o (field_mut 0 x'1/357)
              y/351 =a (field_imm 0 x'1'0/358))
             (makeblock 0 (int) y/351))))))
  (apply (field_mut 1 (global Toploop!)) "f" f/349))
(let
  (f/349 =
     (function x/350
       (if (field_int 0 x/350)
         (let (x'1'0/355 =o (field_mut 0 (field_imm 1 x/350)))
           (switch* x'1'0/355
            case tag 0:
             (if (seq (setfield_ptr 0 (field_imm 1 x/350) [1: 3]) 0)
               [1: 3]
               (let (x'1'0/358 =o (field_mut 0 (field_imm 1 x/350)))
                 (makeblock 0 (int) (field_imm 0 x'1'0/358))))
            case tag 1: [1: 2]))
         [1: 1])))
  (apply (field_mut 1 (global Toploop!)) "f" f/349))
val f : u -> (bool, int) Result.t = <fun>
|}]

