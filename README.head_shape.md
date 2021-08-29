# Constructor unboxing

This PR implements a variant of the "constructor unboxing" feature proposed by Jeremy Yallop in [RFC #14](https://github.com/ocaml/RFCs/pull/14), which extends the current `[@@unboxed]` annotation for single-constructor variant types (or single-field record types). The PR was implemented by @nchataing during an internship supervised by @gasche.

## Short example

The following is now accepted:

```
type bignum =
  | Short of int [@unboxed] (* represented directly by an integer *)
  | Long of Gmp.t           (* Block of tag 0 (first non-unboxed constructor) *)
```

In a [small benchmark](https://github.com/gasche/ocaml/pull/10), we tested that this representation provides the same performances as the current Zarith implementation when computations remain in the "short integer" range -- Zarith uses [dirty unsafe tricks](https://github.com/ocaml/Zarith/blob/2be3c25/z.ml#L28-L37) to avoid boxing short integers, which we can replace with [natural OCaml code](https://github.com/gasche/ocaml/blob/head_shape_zarith/Zarith/test.ml#L110-L125).

(Note: Zarith does not box the Long case either, checking for a Custom tag instead. We do not support this yet, but it would be a natural extension of this PR.)

The intent of the currently presented work is to do the simplest possible step in the direction of more unboxing. Most advanced aspects were left to future work. We believe that it would be reasonable to integrate the PR with its current feature scope: it provides values for users, and should not hamper further extensions.


## Precise specification

We define the *head* of an OCaml value as follows:
- the head of an immediate value `v` is the pair `(Imm, v)`
- the head of a heap block with tag `t` is the pair `(Block, t)`.

(In other words, the head tracks whether a value is immediate or a block, and for blocks only keeps the tag.)

The "head shape" of a type is a (slight over-approximation of) the set of heads of all possible values of this type.

Now consider a variant type declaration containing one or several constructors annotated with `[@unboxed]`:

```ocaml
type ('a, 'b, ...) t =
  | Const0 (* some constant constructors *)
  | Const1
  | ...
  | Const{m}
  | NonConst0 of t00 * t01 * ...
  | Nonconst1 of t10 * t11 * ...
  | ...
  | NonConst{n} of t{n}0 * t{n}1 * ...
  | Unboxed1 of u0 [@unboxed]
  | Unboxed2 of u1 [@unboxed]
  | ...
  | Unboxed{l} of u{l} [@unboxed]
```

(For simplicity we wrote above all constant constructors first, then all non-constant constructors then all unboxed constructors. But in fact we support arbitrary interleaving of these categories, and the representation is exactly the same as long as the ordering within constant constructors and within non-constant constructors is preserved.)

The compiled representation of this type is as follows:
- as before, constant constructors `Const{k}` are represented by the immediate number `k`
- as before, non-constant constructors `Nonconst{k} of ...` are represented by a heap block with tag `k`
- unboxed constructors `Unboxed{k} of u{k}` are represented directly by the value of type `u{k}`, without
  any boxing

This definition is *rejected* statically if the unboxed constructors overlap with the other values of the type, in the following precise sense:

1. We compute the "boxed head shape" `BS` of this type *without* the unboxed constructors; by definition of the head shape, this is the set `{(Imm, 0), (Imm, 1), ..., (Imm, m)} ∪ {(Block, 0), (Block, 1), ,.., (Block, n)}`.

2. Then we compute the "unboxed shapes" `US{k}` of each unboxed constructor, that is the head shape of `u{k}`.

3. The type is accepted if and only if the shapes `BS, US0, US1, ..., US{l}` are disjoint from each other. The head shape of the whole shape is then the disjoint union `BS ⊎ US0 ⊎ US1 ⊎ ... ⊎ US{l}`.

Unknown/abstract types are assumed to have a "top" shape with containing potentially all heads. (This should be refined when the abstract type is used to represent an FFI type with a precise shape implemented in C; supporting head shape assertions on abstract types is future work.)

### Examples

```ocaml
(* rejected *)
type t =
  | Int of int [@unboxed] (* shape: (Imm, _) *)
  | Unit                  (* shape: (Imm, 0), conflicts with Int above *)

(* accepted *)
type t =
  | Int of int [@unboxed]  (* shape: (Imm, _) *)
  | Box of t               (* shape: (Block, 0), as the first non-constant non-unboxed constructor *)
  (* shape(t): (Imm, _) ∪ {(Block, 0)} *)

(* accepted *)
type prod = t * t
and t =
  | Int of int [@unboxed]        (* shape: (Imm, _): any immediate *)
  | String of string [@unboxed]  (* shape: (Block, Obj.string_tag)    (Obj.string_tag is 252) *)
  | Prod of prod [@unboxed]      (* shape: (Block, 0) *)
  (* shape(t): (Imm, _) ∪ {(Block, 0), (Block, Obj.string_tag)} *)


(** With abstract types *)

type abstract

(* accepted *)
type t =
  | Int of int [@unboxed] (* shape: (Imm, _) *)
  | Abs of abstract       (* shape: (Block, 0) *)
  (* shape(t): (Imm, _) ∪ {(Block, 0)} *)

(* rejected *)
type t =
  | Int of int                 (* shape: (Block, 0) *)
  | Abs of abstract [@unboxed] (* any shape, conflicts with Int *)


(** Nested unboxing *)

type t1 =
  | Int of int [@unboxed]
  | Block of unit
  (* shape(t1): (Imm, _) ∪ {(Block, 0)} *)

(* rejected *)
type t2 =
  | T1 of t1 [@unboxed] (* shape: (Imm, _) ∪ {(Block, 0)} *)
  | S of string         (* shape: (Block, 0), conflicts with T1 *)

(* accepted *)
type t3 =
  | T1 of t1 [@unboxed]    (* shape: {(Imm, _), (Block, 0)} *)
  | S of string [@unboxed] (* shape: (Block, Obj.stringₜag) *)
  (* shape(t3): (Imm, _) ∪ {(Block, 0)} ∪ {(Block, Obj.string_tag)} *)
```


### Comparison with Yallop's proposal [RFC#14](https://github.com/ocaml/RFCs/pull/14)

Jeremy Yallop's proposal uses a global annotation `[@@unboxed]` on all constructors at once, we use a per-constructor annotation `[@unboxed]`. (The RFC mentions this as a possible extension in "Extension: partial unboxing".) It would be easy to interpret `[@@unboxed]` as just "[@unboxed] on all constructors", but we have not implemented this yet.

A major difference is that the RFC#14 specification suggests renumbering constructors in some cases, where the representation of `C of foo [@unboxed]` is taken to be different from the representation of `foo`, in order to avoid conflicts with other constructors at this type. We do not support any such renumbering:
- the representation of `Unboxed of foo [@unboxed]` is always the representation of `foo`
- the representation of `Boxed of foo` always uses the block tag consecutive/next/succedent to the previous boxed-constructor tag in the declaration (filtering out unboxed constructors).

(Note: @stedolan calls this aspect of RFC#14 "[conflating inlining and disjointness](https://github.com/ocaml/RFCs/pull/14#issuecomment-603867960)". We only deal with disjointness.)

### Leftover question: how close to the compiler-distribution runtime should the specification be?

We define static accept/reject decisions for partially-unboxed types using "head shapes", which are defined in terms of the value-representation strategy of the main OCaml implementation. Should we have a more abstract definition, that leaves more room to other representations in alternative implementations?

We have not studied this question yet and we believe it is a pressing question. In particular, any choice that would end up being merged in the language probably MUST support the js_of_ocaml value representation. (Do you know of a reference document that describes the js_of_ocaml value representation? Pointers are welcome are we are not jsoo experts ourselves. cc @hhugo.)

Our intuition is that we could fine a "weakening" of our current specification that distinguishes less different sort of shapes -- thus rejects more definitions -- and gives good flexibility for alternative implementations. Here are some things we could do:

- We could stop making assumptions about the shape of function closures (currently: {Closure_tag, Infix_tag}), preventing the unboxing of closure-holding constructors.
- We could also weaken our assumptions about built-in containers (string/byte, arrays, double-arrays, etc.)
- We could stop distinguishing "float" from immediates (ouch!) if jsoo does this. What about Int32, Int64, should they be known as custom values?

In other words: what amount of runtime type information should we require from OCaml implementations?

At the limit, one extreme choice would be to only reason on the tag of variant constructors (constant or not), which are distinguishable from each other in any OCaml implementation, and not make any other assumption about head shapes (map all types except variants to the "top" shape). This would reject most unboxing definitions, leave maximal freedom for langauge implementations. Unfortunately this would also prevent the actually-interesting uses of the feature we know about, which mostly resolve around unboxing an `int`-carrying constructor.

This is an aspect of our design on which we need external feedback from people with a good taste for these matters. (cc @xavierleroy, @damiendoligez, @stedolan, @lpw25, @let-def, etc.).


## Implementation strategy

The main components required for this feature are:
1. We need to compute head shape information for unboxed constructors, which in turn requires computing head shape information for whole type.
2. At type-declaration time, we need to check disjointness of head shapes and reject invalid declarations.
3. We need to compile unboxed constructors in expressions.
4. We need to compile unboxed constructors in patterns.

(3) is in fact very easy: unboxed constructors in expressions are implemented by doing [nothing at all](https://github.com/gasche/ocaml/blob/head_shape/lambda/translcore.ml#L336-L337).

(1) and (2) proved fairly difficult to implement cleanly due in large part to accidental complexity.

### Head shapes

Representing head shapes by their set of possible values is not practical, as `(Imm, _)` (the shape of all immediate values) would be too large a set. Instead we use a representation with an explicit "any" value in either domains (for immediates or for tags):

```
(* Over-approximation of the possible values of a type,
   used to verify and compile unboxed head constructors.

   We represent the "head" of the values: their value if
   it is an immediate, or their tag if is a block.
   A head "shape" is a set of possible heads.
*)
and head_shape =
  { head_imm : imm shape;               (* set of immediates the head can be *)
    head_blocks : tag shape;            (* set of tags the head can have *)
  }

(* A description of a set of ['a] elements. *)
and 'a shape =
  | Shape_set of 'a list                (* An element among a finite list. *)
  | Shape_any                           (* Any element (Top/Unknown). *)

and imm = int
and tag = int
```

This definition is found in typing/types.mli: https://github.com/gasche/ocaml/blob/head_shape/typing/types.mli#L624-L642

Remark: we tried turning `imm` and `tag` into single-constructor variants for more safety, but this proved very cumbersome as many auxiliary functions happily process either sorts of tags to compute numeric aggregates.

Remark: in practice we don't know of any use type in OCaml that contains the `(Block, _)` shape without also allowing `(Imm, _)`. (So we could do without `(Block, _)` and have two tops, "any immediate" or "any value whatsoever") No type describes "any block but not immediates". Allowing it in the compiler implementation makes the code more regular, and it could come handy in the future (if we wanted, say, to assign shapes to Cmm-level types) or for weird FFI projects.

### Compiling unboxed constructors in pattern-matching

Pattern-matching compilation is done in [lambda/matching.ml](https://github.com/gasche/ocaml/blob/head_shape/lambda/matching.ml).

Remark: The other pattern-matching-heavy module, [typing/parmatch.ml](https://github.com/gasche/ocaml/blob/head_shape/typing/parmatch.ml), is in charge of checking for exhaustiveness and other type-checking-time warnings; it required basically no change, given that unboxing a constructor does not change the observable behavior of pattern-matching, unboxed constructors are handled just like usual constructors for exhaustiveness and all other static-analysis purpose.

The pattern-matching compiler works by decomposing pattern-matching clauses into a lower-level representation built from "switches", a lower-level control-flow construct that just dispatches on the value of immediates and tags of a head block. Those switches are then lowered further to Lambda constructs (`Lifthenelse` + tag accesses, or a native `Lswitch` instruction used for the bytecode compiler).

A switch is a list of switch clauses, which are of the form `(cstr_tag, action)`, where `cstr_tag` is either an immediate value or a block tag, and actions are pieces of lambda-code. Our implementation adds a new sort of `cstr_tag`, morally `Cstr_unboxed of head_shape` (representation details in the next section); these "unboxed tags" are "expanded away" by replacing clauses witch unboxed tags by clauses for the underlying elements of the head shape.

For example, consider the following type declarations:

```ocaml
type internal = Foo | Bar of string [@unboxed]        (* head shape: {(Imm, 0); (Block, 252)} *)
type t = First of int | Second of internal [@unboxed]
```

An exhaustive switch on a value of type `t` may look like

```ocaml
| Cstr_block 0 -> act1
| Cstr_unboxed [{(Imm, 0); (Block, 252)}] -> act2)
```

and we expand it to a switch without unboxed constructors, to be compiled by the existing machinery:

```ocaml
| Cstr_block 0 -> act1
| Cstr_constant 0 -> act2
| Cstr_block 252 -> act2
```

This is the general idea, but in fact we need slightly more sophistication to deal with `(Imm, _)` or `(Block, _)` shapes. Instead of a list of clauses, we represent a switch as a product structure which may contain:
- an action for all immediates (the `any_const` action)
- or a list of specific actions for some immediates
- an action for all blocks (the `any_nonconst` action)
- or a list of specific actions for some block tags

TODO: writing this explanation, I really have the impression that we should try again to use a sum type to clarify that we either have `any` or some immediates. This makes `split_cases` harder to write, but the consumer easier to read, and the consumer is more important here -- it is the subtle piece of code that does the pattern-matching compilation of those switches.

The code that lowers switches into `Lifthenelse` or `Lswitch` has to be adapted to deal with this new structure. If We changed the code in such a way that it should be easy to check that, in absence of unboxed constructors, the code generated is the same as it was previously. (The cost of this approach is that sometimes the code is more verbose / less regular than it could be if written from scratch, accepting some changes in compilation.)

Remark: To emit `Lswitch` instructions, the compiler needs to know of the range of possible immediate values and tags (when we don't have `any_{const,nonconst}` actions). More precisely, we want the maximal possible immediate constructor and block tag at this type (minimal values are always assumed to be 0).

This new representation of switches with "any immediate" or "any block tag" cases is in a new `Cases` submodule:
https://github.com/gasche/ocaml/blob/head_shape/lambda/matching.ml#L2738-L2790

The expansion of unboxed constructors in switches is performed in the `split_cases` function:
https://github.com/gasche/ocaml/blob/head_shape/lambda/matching.ml#L2792-L2827

Finally, the lowering of those switches to Lambda code is done in the `combine_constructor` function:
https://github.com/gasche/ocaml/blob/head_shape/lambda/matching.ml#L2914-L3080


### General approach to computing head shapes

We use the "on-demand" approach advertised by @lpw25 and @stedolan to compute type properties on-demand, at each type declaration with unboxed constructors, instead of trying to compute the property modularly for all type definitions (which may or may not occur in the type of an unboxed constructor later).

Here "demand" is defined as either:
- a type declaration using some unboxed constructors is processed by the type-checker
  (this "demands" computing the shape of each unboxed constructor)
- the pattern-matching compiler encounters an unboxed constructor

In particular, it can happen that an unboxed-constructor is compiled *without* the type-checker having processed its declaration first! This is the case where the type declaration comes from a .cmi – it has been checked by a previous run of the compiler, and is then imported as-is into the environment without being re-checked.

The head shape computed for an unboxed constructor is cached on first demand, and will not be recomputed several times. The computation requires a typing environment -- which must be an extension of the environment in which the constructor was defined -- to unfold the definition of typing constructors used in the unboxed constructor parameter type, and further constructions reachable from them.

The details of how we perform repeated expansion of type constructors while ensuring termination are tricky, they are discussed in [this ML Workshop extended abstract](http://gallium.inria.fr/~scherer/research/constructor-unboxing/constructor-unboxing-ml-workshop-2021.pdf) and [PR #10479](https://github.com/ocaml/ocaml/pull/10479).

The computation of the head shape is done in the functions `of_type_expr` and `of_typedescr` in a new `Head_shape` module of [typing/typedecl_unboxed.ml](https://github.com/gasche/ocaml/blob/head_shape/typing/typedecl_unboxed.ml).

In particular, the definition of head shape on "base types" relies on a [`match_primitive`](https://github.com/gasche/ocaml/blob/head_shape/typing/typedecl_unboxed.ml#L65) function recognized a set of builtin type paths (we borrowed the logic from [Typeopt.classify](https://github.com/gasche/ocaml/blob/head_shape/typing/typeopt.ml#L75)).

TODO: there is no special support for `Tarrow` for now, it returns `any_shape` instead of {Closure,Infix}. (Is it by explicit choice?)


### Storing unboxing information in type descriptions

This, surprisingly, turned out to be the most difficult part of the PR to get right.

As discussed above, we need to store two different kind of information for compilation:
- per-unboxed-constructor information: what is the shape of the unboxed constructor argument
- per-sum-type information: how many unboxed constructors are there,
  what is the maximal value of the immediates and block tags they contain

The existing codebase already computes per-constructor information (imm/tag values) and per-sum-type information (the number of constant and non-constant constructors) in [typing/datarepr.ml : constructor_descrs](https://github.com/gasche/ocaml/blob/head_shape_base/typing/datarepr.ml#L95). This function is called (through `Datarepr.constructors_of_type`) from the `Env` module, which is in the business of converting type *declarations* (as provided by the user) into type *descriptions* (with extra information for compilation) as stored in the typing environment.

Unfortunately, this scheme cannot be extended for our unboxing-related information. Computing the head shape of an unboxed constructor requires unfolding type constructors from the typing environment, so in particular the function doing the computation needs an Env.t argument and depends on the Env module. It cannot be put in the module Datarepr that itself is called from Env, as this would be create a circular dependency.

We tried many ways to avoid this cyclic dependency (for example we went half-way through large refactorings trying to compute type descriptions in Typedecl, and pass it to Env-extending functions, instead of computing them within Env).

In the end we settled on a very simple approach: the per-unboxed-constructor information has type `head_shape option ref`, and the per-sum-type information has type `unboxed_type_data option ref`, they are initialized to `ref None` by the Datarepr module, and then filled on-demand -- from a module that *can* depend on Env. Caching the on-demand computation is hidden under accessor-style functions (that fills the cache if the value was not computed yet):
- per-unboxed-constructor information are accessed using [Typedecl_unboxed.Head_shape.get](https://github.com/gasche/ocaml/blob/head_shape/typing/typedecl_unboxed.ml#L398); it is also computed and cached for all unboxed constructors of a given type by [Typedecl_unboxed.Head_shape.check_typedecl].
- per-sum-type information is placed in an `unboxed_type_data option ref` [field](https://github.com/gasche/ocaml/blob/head_shape/typing/types.mli#L592) of the `Types.constructor_description` type -- we sheepishly extended the dubious existing approach of storing per-sum-type information in each of its constructors. It is computed by [Typedecl_unboxed.unboxed_type_data_of_shape](https://github.com/gasche/ocaml/blob/head_shape/typing/typedecl_unboxed.ml#L347).

Note: the `unboxed_type_data option ref` field is not meant to be accessed directly, but through helper functions in Typedecl, that export its content as fields:

```ocaml
cstr_max_block_tag : Env.t -> constructor_description -> Types.tag option
cstr_max_imm_value : Env.t -> constructor_description -> Types.imm option
cstr_unboxed_numconsts : Env.t -> constructor_description -> int option
cstr_unboxed_numnonconsts : Env.t -> constructor_description -> int option
```

Morally those are fields of a constructor description; the main difference is that, unlike other fields, they can only be computed "later than Datarepr", when a typing environment is available. We first tried having each of them be a mutable field, but this made it difficult to give a type to a function computing all of them at once, as [unboxed_type_data_of_shape] does.

## Testing

TODO: describe our testing approach and testsuite

## In scope for this PR, but not yet implemented

We are submitting this PR in the interest of gathering feedback, and getting the review train rolling. (We know it takes a while from people reading about the work to actually reviewing it. Please start right now!) There are still a few things *we* want to changes before we consider it mergeable -- and surely other suggestions from the reviewers.


### Handle cyclic types in the termination checker

The termination-checking algorithm currently does not take cyclic
types into account, and may non-terminate on those. This should be
fixed easily by keeping track of the set of type nodes we have already
encountered in head position during reduction.


### Distinguish "good" from "bad" cycles

Our cycle-detection algorithm will sometimes reject definitions that indeed are cyclic, but do admit a valid fixpoint:

```
(* this bad declaration should be rejected *)
type t = Loop of t [@unboxed] | Other
(* because `Other` and `Loop Other` would have the same representation *)

(* this weird declaration could be accepted
type t = Loop of t [@unboxed]
(* because it is just an empty type *)
```

"Good cycle" types have no value of their own and they can go to hell as far as we are concerned. However, Stephen Dolan (@stedolan) pointed out that they can be introduced by revealing the definition of an abstract type: `type t = Loop of abstract [@unboxed]` (accepted, even though we could have `abstract = t`). This introduces a case where revealing type abstractions makes a definition rejected, breaking some reasonable properties of the type system.

It would be nice to put in the work to distinguish "good cycles" from "bad cycles" to avoid this small defect of the current strategy of rejecting *all* cycles.


### TODO enforce "separability" of resulting types

It is unsound in presence of the flat-float-array optimization to have types that contain both floating-point values and non-floating-point values. Our current approach does not enforce this, so it will allow this unsound definition:

```ocaml
type t = Float of float [@unboxed] | Other
```

The simplest possible idea to solve this is to give `float` the "top" shape (instead of Double_tag), which should reject all such definitions. (But the error message will be disappointing.)

A more elaborate fix to this issue is to add to the head shape a boolean flag, "separated". A "separated" shape guarantees that it is the over-approximation of a separable type, while a non-separated shape may be the shape of a non-separated type. So for example we have a "Separated Top" value (which can be inhabited by any value, but either contains float and nothing else or no floats) and a "Non-separated top" value (any value, possibly floats and other stuff at the same time). It may be possible to compute this bit simply by giving existential variables in GADTs the "non-separated top" shape, and then to reject all non-separated type declarations. This would allow removing the current separability-computation machinery, which could bring a substantial simplification of this corner of the type-checker.



## Future work

We know about some improvements that we are interested in working on eventually, but we believe are out of scope for this PR.

### Nice shape-conflict error messages

If a type definition is rejected due to shape conflict, it would be nice to give a clear explanation to the user, with the location of the two constructors (possibly both in different variant declarations than the one being checked) that introduce the incompatibility. One way to do this is to track, for each part of the shape, the location of the constructor that introduced it in the shape.

### GADTs

Finer-grained shape computations for GADTs: to compute the shape of a type `foo t` when `t` is a GADT, instead of taking the disjoint union of the shape of all constructors, we can filter only the constructors that are "compatible" with `foo` (we cannot prove that the types are disjoint). This is simple enough and gives good, interesting results in practice, but it also requires refining the termination-checking strategy for GADTs (in addition to the head type constructor, we need to track the set of compatible constructors for the particular expansion that was done). For now we punt on this by not doing any special handling of GADTs, even though it is less precise.

### Shape annotations on abstract types

If an abstract type is meant to be defined through the FFI, the OCaml-side could come with an annotation restricting its shape from the pessimal default "{ (Imm, _); (Block, _) }" to the actual shape of FFI-produced values for this type. This requires blindly trusting the programmer, but this blind trust is the foundation of our FFI model already.

Having shape annotations on abstract types means that shape-inclusion has to be checked when verifying that a type definition in a module matches a type declaration in its interface. (Currently we don't have any work there, because means of abstractions always either preserve the head shape or turn it into "top".)

### Compilation strategy

The pattern-matching compilation strategy could be improved in some cases, at the cost of substantial changes to our current implementation. Consider `type t = Int of int [@unboxed] | String of string [@unboxed] and u = T of t [@unboxed] | Float of float [@unboxed]`. A matching of the form

```ocaml
match arg with
| Float _ -> 0
| T (Int _) -> 1
| T (String _) -> 2
```

will generate two nested switches:

```
match-shape arg with
| (Block, Obj.double_tag) -> 0
| (Imm, _) | (Block, Obj.string_tag) ->
  match-shape arg with
  | (Imm, _) -> 1
  | (Block, Obj.string_tag) -> 2
```

(This is the exact same generated-code shape that we would have without unboxing, except that one dereference is gone, but the first switch is now more expensive as the now-unboxed input values are not in a small consecutive interval of tags.)

It would of course be better to generate a single switch instead. We see two approaches to do this:

1. We could "merge" some switches after the fact.
2. We could remove unboxed constructors much earlier in the pattern-matching compiler, before matrix decomposition, so that morally `T (Int _)` is handled as having a single head constructor `T ∘ Int`.

We are not considering either of those ambitious changes a priority, because:
1. We expect the performance wins from unboxing (if any) to come from tighter memory representations;
   the pattern-matching branches are comparatively unexpansive
2. In practice most examples of unboxed constructors we have in mind do *not* hit this bad situation.

In particular, if you unboxed a constructor with only immediate
values, then the generated code will split the query space by checking
`Obj.is_int`, which is the optimal strategy in any case (what the
native compiler will do for the merged switch as well). For example,
these produce exactly the same native code:

```ocaml
(* what we get today *)
match-shape arg with
| (Imm, _) -> -1
| (Block, 0) | (Block, 1) ->
  match-shape arg with
  | (Block, 0) -> 0
  | (Block, 1) -> 1

(* what switch-merging would give *)
match-shape arg with
| (Imm, _) -> -1
| (Block, 0) -> 0
| (Block, 1) -> 1
```

The two forms get compiled to the following

```ocaml
if Obj.is_int arg then -1
else match Obj.tag arg with
     | 0 -> 0
     | 1 -> 1
```