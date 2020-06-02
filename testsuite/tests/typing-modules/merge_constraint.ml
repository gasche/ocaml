(* TEST
   * expect *)

module RhsScopeCheck = struct
  module type Sig1 = sig
    type t
    type u = t
  end

  (* A scoping error is intentional:
     with-constraints "with <lhs> = <rhs>"
     have their <rhs> evaluated in the current
     typing environment, no within the signature
     that they are constraining. [t] is unbound
     in the current environment, so [with u = t]
     must be rejected. *)
  module type Check1 = Sig1
    with type u = t
end
[%%expect{|
Line 15, characters 18-19:
15 |     with type u = t
                       ^
Error: Unbound type constructor t
|}]


module VarianceEnv = struct
  module type Sig = sig
    type +'a abstract
    type +'a user = Foo of 'a abstract
  end

  module type Problem = sig
    include Sig
    module M : Sig
      with type 'a abstract = 'a abstract
       and type 'a user = 'a user

    (* the variance annotation of [+'a foo] should be accepted, which
       would not be the case if the with-constraint [and type 'a
       user = 'a user] had its variance type-checked in the wrong typing
       environment: see #9624 *)
    type +'a foo = 'a M.user
  end
end
[%%expect{|
module VarianceEnv :
  sig
    module type Sig =
      sig type +'a abstract type 'a user = Foo of 'a abstract end
    module type Problem =
      sig
        type +'a abstract
        type 'a user = Foo of 'a abstract
        module M :
          sig
            type 'a abstract = 'a abstract
            type 'a user = 'a user = Foo of 'a abstract
          end
        type 'a foo = 'a M.user
      end
  end
|}]

module UnboxedEnv = struct
  module type Sig = sig
    type 'a ind = 'a * int
    type t = T : 'e ind -> t [@@unboxed]
  end

  module type Problem = sig
    include Sig
    module type ReboundSig = Sig
      with type 'a ind = 'a ind
       and type t = t
    (* the with-definition [and type t = t] above should be accepted,
       which would not be the case if its definition had separability
       checked in the wrong typing environment: see #9624 *)
  end
end
[%%expect{|
module UnboxedEnv :
  sig
    module type Sig =
      sig type 'a ind = 'a * int type t = T : 'e ind -> t [@@unboxed] end
    module type Problem =
      sig
        type 'a ind = 'a * int
        type t = T : 'e ind -> t [@@unboxed]
        module type ReboundSig =
          sig
            type 'a ind = 'a ind
            type t = t/2 = T : 'a ind -> t/1 [@@unboxed]
          end
      end
  end
|}]
