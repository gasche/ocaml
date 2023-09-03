(* TEST
 readonly_files = "example_1.ml example_2.ml";
 expect;
*)

#use "example_1.ml";;
[%%expect {|
type u = { a : bool; mutable b : (bool, int) Either.t; }
val f_input : unit -> u = <fun>
val f : u -> (bool, int) Result.t = <fun>
|}]

let _ =
  match f (f_input ()) with
  | Result.Error n ->
      Printf.ksprintf failwith "Error %d" n
  | Result.Ok (b : bool) ->
      (* on non-fixed systems, this returns the integer '3'
         unsoundly cast as a boolean *)
      b
;;
[%%expect {|
- : bool = true
|}]

#use "example_2.ml";;
[%%expect {|
type 'a myref = { mutable mut : 'a; }
type u = { a : bool; b : (bool, int) Either.t myref; }
val f_input : unit -> u = <fun>
val f : u -> (bool, int) Result.t = <fun>
|}];;

let _ =
  match f (f_input ()) with
  | Result.Error n ->
      Printf.ksprintf failwith "Error %d" n
  | Result.Ok (b : bool) ->
      (* on non-fixed systems, this returns the integer '3'
         unsoundly cast as a boolean *)
      b
;;
[%%expect {|
- : bool = <unknown constructor>
|}]
(* oops, there is still a bug here! *)
