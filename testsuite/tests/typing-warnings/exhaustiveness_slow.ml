(* TEST
   * setup-ocamlc.opt-build-env
   ** ocamlc.opt
   flags = " -w A -strict-sequence "
   *** check-ocamlc.opt-output
*)

(* Exhaustiveness check is very slow *)
type _ t =
  A : int t | B : bool t | C : char t | D : float t
type (_,_,_,_) u = U : (int, int, int, int) u
type v = E | F | G
;;

let f : type a b c d e f g.
      a t * b t * c t * d t * e t * f t * g t * v
       * (a,b,c,d) u * (e,f,g,g) u -> int =
 function A, A, A, A, A, A, A, _, U, U -> 1
   | _, _, _, _, _, _, _, G, _, _ -> 1
   (*| _ -> _ *)
;;
