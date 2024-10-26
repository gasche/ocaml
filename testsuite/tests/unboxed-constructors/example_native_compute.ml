(* TEST
   flags = "-dlambda -dno-unique-ids";
   expect;
*)

type t =
  | Var of int [@unboxed]
  | App of t * t
  | Lam of (t -> t) [@unboxed]
[%%expect {|
0
type t = Var of int [@unboxed] | App of t * t | Lam of (t -> t) [@unboxed]
|}]

let app t v =
  match t with
  | Lam f -> f v
  | ne -> App (ne, v)
[%%expect {|
(let
  (app =
     (function t v
       (catch
         (if (isint t) (exit 2)
           (if (>= (caml_obj_tag t) 247) (apply t v) (exit 2)))
        with (2) (makeblock 0 t v))))
  (apply (field_mut 1 (global Toploop!)) "app" app))
val app : t -> t -> t = <fun>
|}]
