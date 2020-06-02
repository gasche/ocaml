(* TEST
   * expect *)

module type Sig = sig
  type t
  type u = t
end
[%%expect{|
module type Sig = sig type t type u = t end
|}]

(* This type error is intentional:
   with-constraints "with <lhs> = <rhs>"
   have their <rhs> evaluated in the current
   typing environment, no within the signature
   that they are constraining. [t] is unbound 
   in the current environment, so [with u = t]
   must be rejected. *)
module type Problem = Sig
   with type u = t
[%%expect{|
Line 2, characters 17-18:
2 |    with type u = t
                     ^
Error: Unbound type constructor t
|}]
