/-
  # Universes

  Digging deeper into type universes and universe polymorphism -/

import Course.CourseLib

topic::UNIVERSES
/-
  Every Lean type lives in some _universe_. Somewhat confusingly, every universe
  is also a type: the type of the universe below it. `Prop` has type `Type`,
  which is shorthand for `Type 0`; `Type 0` has type `Type 1`, which has type
  `Type 2`, etc. The universes are `Prop < Type < Type 1 < ⋯`. -/
#check Prop
#check Type 0
#check Type 1
#check Type 2

/-
  You may also see `Sort` mentioned; this is a convenient way to talk about all
  universes including `Prop` and `Type n`. `Sort 0 = Prop`, `Sort 1 = Type`,
  `Sort 2 = Type 1`, etc. -/
#check Sort 0
#check Sort 1
#check Sort 2

/-
  We have confined ourselves up to this point to be in `Prop` or `Type`, where
  propositions we want to prove live in universe `Prop` and the standard types
  that you are familiar with live in universe `Type 0`. Why do we need infinite
  univeres instead of just using these two? -/
#check 2 + 2 = 4
#check Bool
#check ℕ
#check ℤ
#check String
#check List ℕ

/-
  - The key reason for type universes is _logical consistency_

    + Recall _Russell's Paradox_: let U = { S | S ∉ S }; is U ∈ U?

    + There is a similar paradox called _Girard's Paradox_ for type theory, that hinges on a type being its own type, i.e., `Type : Type`

    + Universes are a way to avoid that paradox...in fact, it's the method used by Russell and Whitehead in Principia Mathematica. By establishing a hierarchy of type universes and restricting types in a particular way, we guarantee that these paradoxes are avoided.

  - Note that universes are not cumulative, that is, every type universe is an element of the next larger universe _but_ is not an element of even larger universes: every type inhabits exactly one universe
-/

#check (Type 3 : Type 4)
#check_failure (Type 3 : Type 5)

/-
  - A type system is called _predicative_ if types in a given universe may only quantify over types in smaller universes. Recall that type `∀ (a : T), P a` is another way of saying `(a : T) → P a`, so predicativity is talking about dependent function types. A predicative system avoids circularity that leads to paradox, and Lean's type system for `Type 0` and above is predicative.

  - The universe of a function type is the least upper-bound of the universes of its argument and result types. That is, it is the maximum universe over its argument types and result type.
-/

/- A function that "quantifies" over `Type` -/
def f : Type → ℕ := fun _ => 42

/-
  - `Type` is in universe 1
  - `ℕ` is in universe 0
  - therefore `Type → ℕ` is in universe `Type 1`
-/
#check Type
#check ℕ
#check Type → ℕ

/-
  If we try to pass `ℕ → Type` as an argument to `f` we get an error, because
  `f` can only accept arguments that are in a _lower_ universe than `f`s type -/
#check_failure f (Type → ℕ)

/-
  We won't get into the type theory behind all this, just be aware that
  universes serve an important purpose if you want a consistent logic. You as a
  user of Lean need to be aware of universes because sometimes you may try to
  define things in a way that violates predicativity and you need to understand
  what's happening. -/
end_topic UNIVERSES


topic::PROP
/-
  - Let's focus in on `Prop` for a moment. `Prop` stands for _proposition_, and for Lean we define propositions as "meaningful statements that admit proof".

  - We emphasized before that "types are propositions and programs are proofs", which applies to any program and any type. For pragmatic reasons, however, we will distinguish between:

    + Types and programs intended for computation, which are things of `Type 0` or above

    + Types and programs that are intended to express and prove logical statements, which are things that belong to `Prop`

  - By segregating logical theorems and proofs into `Prop` we can treat them differently from "regular" types and programs

    + _Proof irrelevance_: any two proofs of the same proposition are completely interchangeable. That is, if we have a proof of a proposition then the exact form of the proof itself is irrelevant; any proof will do as well.

    + _Runtime irrelevance_: propositions are erased from compiled code. That is, anything of type `Prop` will be removed by the compiler and has no affect on runtime performance.

    + _Propositional extensionality_: `(A ↔ B) ↔ (A = B)`. i.e., two propositions are logically equivalent iff they are equal

    + _Restricted elimination_: (with one exception that we'll talk about later) propositions cannot be used to derive non-propositions, e.g., we cannot take something of type `Prop` and use it to derive a `ℕ`.

    + _Impredicativity_, i.e., `Prop` violates predicativity: propositions may quantify over any universe at all (but the result is always in `Prop`). Things in Lean are defined carefully so that this fact does not cause unsoundness (e.g., the restricted elimination described above). Impredicativity is useful because we want propositions to be able to make statements about other propositions.
-/

/-
  Concretely demonstrating proof irrelevance by showing two different proofs of
  the same proposition and then showing that they are considered equal. -/

theorem proof1 : 1 ∈ [1, 1] := .head _
theorem proof2 : 1 ∈ [1, 1] := .tail _ (.head _)

example : proof1 = proof2 := rfl

/-
  This next example shows the importance of the difference between `Type` and
  `Prop`: the type `Notℕ` is exactly like the definition of `ℕ` except that it
  lives in `Prop` instead of `Type` -/
inductive Notℕ : Prop where
  | zero : Notℕ
  | succ : Notℕ → Notℕ

/-
  Because `Notℕ` lives in `Prop` it is subject to proof irrelevance, hence the
  following example is correct (both sides of the equality are proofs of `Notℕ`,
  and to Lean are indistinguishable) -/
example : Notℕ.zero = Notℕ.succ Notℕ.zero := rfl

/-
  Demonstrating runtime irrelevance using lists. All functions must be total, so
  to take the head of a list we have to provide proof that the list is not
  empty. Note that the `h :` in the condition allows us to refer to the value of
  the condition in each branch. This proof is erased during compilation and has
  no affect on the computation. (In reality we would use `List.head?` instead of
  the function below.) -/
example (ℓ : List ℕ) : Option ℕ :=
  if h : ℓ = [] then .none
  else ℓ.head h

/- Propositional extensionality -/
#check eq_iff_iff

/-
  Demonstrating proof irrelevance _and_ impredicativity. The following
  proposition and proof shows that for any two proofs of some proposition `P`,
  the two proofs are considered equal to each other. -/
example : ∀ (P : Prop) (proof1 proof2 : P), proof1 = proof2 := by
  intro P p1 p2
  rfl

/-
  Propositions, being impredicative, can range over any universe not just
  propositions -/
example : Prop := ∀ (α : Type), ∀ (x : α), x = x
example : Prop := ∀ (α : Type 5), ∀ (x : α), x = x

end_topic PROP


topic::DECIDABLE
/-
  - We said that `Prop` is, in general, undecidable (since it can express arbitrary logical propositions including, e.g., the halting problem) and it doesn't participate in computation. There is an exception: given `P : Prop` we can _prove_ that `P` is decidable, which we do by providing an algorithm for deciding it. Lean can now compute `P` by using the provided algorithm.

  - The `Decidable` type class is for exactly this purpose (and `DecidableEq` is a wrapper around `Decidable` specifically for saying that equality is decidable)
-/

/- A predicate describing even integers -/
def even_prop (n : ℤ) := ∃ (k : ℤ), 2*k = n
#check even_prop

/-
  We cannot evaluate `even_prop` because Lean does not know it is decidable -/
/--
  error: failed to synthesize Decidable (even_prop 42) -/
#guard_error
#eval even_prop 42

/- A function for determining whether an integer is even -/
def even_fun (n : ℤ) := n % 2 == 0

#check even_fun
#eval even_fun 42
#eval even_fun 43

/-
  We need to prove that `even_fun` agrees with `even_prop` (I'm cheating a
  bit by using `grind`, which we haven't covered yet) -/
theorem even_fun_correct {n : ℤ} : even_fun n ↔ even_prop n := by
  grind [even_fun, even_prop]

/- Now we can show Lean that `even_prop` is decidable -/
instance {n : ℤ} : Decidable (even_prop n) :=
  decidable_of_decidable_of_iff even_fun_correct

/-
  - There are two useful consequences of showing that a proposition is decidable (besides proving that fact itself, which would be of interest, e.g., in computability theory)

  - The first is that we can make use of decidability in a proof, e.g., if part of our proof requires showing that a specific integer is even then we can have Lean use the algorithm to decide whether it is true automatically
-/

/-
  We have told Lean that `even_fun` is equivalent to `even_prop`, so the
  `decide` tactic just uses `even_fun` to compute the answer -/
example : even_prop 42 := by decide

/-
  - We can also use the proposition in computable code. While propositions are erased during compilation, Lean recognizes that because the proposition is decidable, it can replace the proposition with its corresponding algorithm (which returns a `Bool` and hence is _not_ erased)

    + That's why I've been able to use `x = y` in conditional guards in my code instead of `x == y`. The former is a proposition (living in `Prop`) while the latter is computable (living in `Bool`), but if `=` is decidable for the type being compared then Lean can automatically promote the `Prop` to `Bool`
-/
#eval even_prop 42
#eval even_prop 43

end_topic DECIDABLE


topic::UNIVERSE_POLYMORPHISM
/-
  - We have discussed what universes are and why we need them, but so far we have been able to mostly ignore them. All of our examples have been in either `Prop` or `Type`, so it may seem like we can just use those two universes and forget the rest. Unfortunately this isn't true.

  - Recall that universes enforce logical consistency by ensuring that a type in universe `u` can only "quantify over" (i.e., take as an argument) types of a universe strictly less than `u`; this requirement guarantees that a type cannot quantify over itself

  - Here we will see examples where universes start mattering, and we will also see how to use _universe polymorphism_ to address the problem
-/

subtopic::UNIVERSE_RULES
/-
  - First we'll establish some terminology to help make the discussion more clear. To illustrate, we'll use the following example.
-/

/- We'll use this example to illustrate the terminology -/
inductive T (α : Type) : ℕ → Type
  | c1 (n : ℕ) : α → T α n
  | c2 (n : ℕ) : α → T α (n + 1)

/-
    + _type parameter_ means the things after the type name and before the `:` in the signature. In the example `T`, the `(α : Type)` is a type parameter. Remember that type parameters must be consistently given the same argument for any mention of the inductive type in the constructors. For `T` this means that the result of constructors `c1` and `c2` must both be `T α _` and we can't use anything other than `α` there.

      - There is a caveat that we'll discuss in more detail in a bit: Lean will try to promote things that syntactically come after the `:` into type parameters when it can. So something that comes after the `:` might count as a parameter if this happens.

    + _final universe_ means the universe of the inductive type being defined, and it is the very last thing in the signature. In the example `T` the very last `Type` after the `ℕ` in the signature is the final universe, so the universe of `T` is `Type`. When we apply a constructor to create an object of this inductive type, the final universe is the universe of that object (see the example immediately below).
-/

/-
  When we apply the constructor we get an object whose type is `T α n` for some
  type `α` and number `n` (`String` and `42` for the object below)  -/
#check T.c1 42 "hello"

/-
  The universe of the object is the type of `T α β`, which our inductive type
  declaration for `T` says is `Type` -/
#check T String 42

/-
    + _index_ means the things after the `:` in the declaration of the inductive type but before the final universe. In the example `ℕ` is an index. Remember that indices can vary for different recursive mentions of the inductive type in the constructors. For `T` this means that the results of constructors `c1` and `c2` can differ in what number they use to create `T` (`c1` uses `n` while `c2` uses `n+1`.

      - As mentioned before Lean can promote some indices into being type parameters, so something that syntactically comes after the `:` is not necessarily an index per se. We'll discuss this more later.

    + _constructor parameter_ means the parameters of a particular constructor. Remember that constructors are functions and there is no difference between parameters that come before the `:` and those that come after. In the example `T` both `(n : ℕ)` and `α` are constructor parameters for constructors `c1` and `c2`.

      - If we look at the type of a constructor itself, we see that all type parameters are made into implicit parameters of the constructor; we will not consider these to be constructor parameters for the purposes of this discussion (see the example immediately below)
-/

/-
  Both `c1` and `c2` have `{α : Type}` as an implicit parameter, which comes
  from the `(α : Type)` type parameter -/
#check T.c1
#check T.c2

/-
  - Now we can state the universe rules for inductive types whose final universe is not `Prop` (Lean ignores the universe rules for inductive types in `Prop` because `Prop` is impredicative and so universes don't really matter):

    1. The universe of any type parameter must be no greater than the final universe

    2. The universe of any constructor parameter or index must be strictly less than the final universe

  - We will illustrate these rules with a series of examples
-/

/-
  Here is a baseline inductive type with a type parameter. The final universe is
  `Type` and the type parameter is in `Type`, therefore everything is fine. -/
inductive T1₁ (α : Type) : Type
  | c : α → T1₁ α

/-
  If we increase the universe of the type parameter then we violate rule #1 -/
/--
  error: Invalid universe level in constructor -/
#guard_error
inductive T1₂ (α : Type 1) : Type
  | c : α → T1₂ α

/-
  We can fix the error by increasing the final universe to match -/
inductive T1₃ (α : Type 1) : Type 1
  | c : α → T1₃ α

/-
  As a caveat, we can violate this rule with no error if the type parameter is
  never mentioned except in the constructor result type -/
inductive T1₄ (α : Type 5) : Type
  | c : T1₄ α

/-
  Let's return to the baseline `T1₁` and add a constructor parameter in universe
  `Type`, which violates rule #2 -/
/--
  error: Invalid universe level in constructor -/
#guard_error
inductive T2₁ (α : Type) : Type where
  | c : α → (β : Type) → β → T2₁ α

/-
  Again we can fix the error by increasing the final universe -/
inductive T2₂ (α : Type) : Type 1 where
  | c : α → (β : Type) → β → T2₂ α

/-
  Now consider a baseline inductive type with a (syntactic) index. It seems like
  it violates rule #2 because we have a constructor parameter `(α : Type)` used
  as an index in `T3₁ α` that matches the final universe, but rule #2 says it
  must be smaller than the final universe. -/
inductive T3₁ : Type → Type
  | c (α : Type) : α → T3₁ α

/-
  I qualified it as a "syntactic" index because if we look at the result of
  `#print` we see that it has been promoted to a type parameter, making the
  example valid. This happened because Lean saw that every mention of `T3₁`
  (which is just the result type of `c`) used the same argument for `n`, making
  it eligible to be promoted. -/
#print T3₁

/-
  Let's try to make it a real index by adding another constructor that uses the
  index in an inconsistent way. Apparently it didn't work, which we can confirm
  using `#print`: Lean recognizes that `α` and `β` are just variable names and
  so calling them different things doesn't make a real difference. -/
inductive T3₂ : Type → Type
  | c (α : Type) : α → T3₂ α
  | d (β : Type) : β → T3₂ β

#print T3₂

/-
  Here is a version that treats the index inconsistently, prohibiting it from
  being promoted to a type parameter, and now we really do violate rule #2 -/
/--
  error: Invalid universe level in constructor -/
#guard_error
inductive T3₃ : Type → Type
  | c (α : Type) : α → T3₃ α
  | d (β : Type) : β → T3₃ (β × β)

/-
  Again we can fix the error by increasing the final universe -/
inductive T3₄ : Type → Type 1
  | c (α : Type) : α → T3₄ α
  | d (β : Type) : β → T3₄ (β × β)

/-
  Note that all parameters must come before all indices, which can inhibit
  promotion even if otherwise an index is eligible. In this example `ℕ` must be
  an index, therefore everything after it must be an index even though the
  `Type` index is otherwise eligible for being promoted -/
/--
  error: Invalid universe level in constructor -/
#guard_error
inductive T3₅ : ℕ → Type → Type
  | c (α : Type) : α → T3₅ 1 α
  | d (α : Type) : α → T3₅ 2 α

end_subtopic UNIVERSE_RULES


subtopic::POLYMORPHISM
/-
  - Our fixes for the above examples were concrete, requiring specific universe levels to work. We would prefer that our definitions be more general, working with any universe levels. That is where universe polymorphism comes into play.

  - We can describe universes using _universe expressions_ `e ∈ Expressions` s.t. `e` is one of the following forms:

    + `0, 1, 2, ... ∈ Constants`: universe constants
    + `u, v, w, ... ∈ Variables`: universe variables
    + `u + k` for `u ∈ Variables`, `k ∈ Constants`
    + `max e₁ e₂` for `e₁, e₂ ∈ Expressions`
    + `imax e₁ e₂` for `e₁, e₂ ∈ Expressions`

  - The meanings should be obvious except for `imax`, which is just like `max` except that it is 0 when its second argument is 0 (`imax` is from "impredicative max" and is used when a type could be from `Prop` or something from `Type u`).

  - We can introduce universe variables either directly in a definition by appending `.{u, v, ...}` to its name, or using the `universe` command which acts like the `variable` command except for universes: that is, it makes the declared universe variables available as a parameter for any definition that uses them

    + We make the universe parameters explicit in the examples below, but we could remove all of the `.{u}` and `.{u,v}` below by adding the following command somewhere before the definitions: `universe u v`
-/

/-
  Here is the erroneous `T1` example -/
/--
  error: Invalid universe level in constructor -/
#guard_error
inductive T1₂ (α : Type 1) : Type
  | c : α → T1₂ α

/-
  Here is the concrete fix -/
inductive T1₃ (α : Type 1) : Type 1
  | c : α → T1₃ α

/-
  Here is the polymorphic fix, ensuring that the final universe is at the same
  level as the type parameter universe, whatever it is -/
inductive T1₅.{u} (α : Type u) : Type u
  | c : α → T1₅ α

/-
  Here is the erroneous `T2` example -/
/--
  error: Invalid universe level in constructor -/
#guard_error
inductive T2₁ (α : Type) : Type where
  | c : α → (β : Type) → β → T2₁ α

/-
  Here is the concrete fix -/
inductive T2₂ (α : Type) : Type 1 where
  | c : α → (β : Type) → β → T2₂ α

/-
  Here is the polymorphic fix, ensuring that the final universe is one greater
  than the constructor parameter's universe, whatever it is -/
inductive T2₃.{u} (α : Type) : Type (u + 1) where
  | c : α → (β : Type u) → β → T2₃ α

/-
  But if we want it to be fully polymorphic then we should make the type
  parameter polymorphic as well. Now we need to make sure that the final
  universe it at least as large as the type parameter universe _and_ at least
  one greater than the constructor parameter universe. -/
inductive T2₄.{u,v} (α : Type v) : Type (max v (u + 1)) where
  | c : α → (β : Type u) → β → T2₄ α

/-
  Here is the erroneous `T3` example -/
/--
  error: Invalid universe level in constructor -/
#guard_error
inductive T3₃ : Type → Type
  | c (α : Type) : α → T3₃ α
  | d (β : Type) : β → T3₃ (β × β)

/-
  Here is the concrete fix -/
inductive T3₄ : Type → Type 1
  | c (α : Type) : α → T3₄ α
  | d (β : Type) : β → T3₄ (β × β)

/-
  Here is the polymorphic fix, ensuring that the final universe is one greater
  than the index universe-/
inductive T3₆.{u} : Type u → Type (u + 1)
  | c (α : Type u) : α → T3₆ α
  | d (β : Type u) : β → T3₆ (β × β)

end_subtopic POLYMORPHISM


subtopic::UNIVERSE_LIFTING
/-
  - Remember that universe are not cumulative, e.g., a member of universe `Type 0` is _not_ a member of universe `Type 1`

  - We usually describe the universe hierarchy as `Prop` < `Type` < `Type 1` < ⋯, but remember that to keep things uniform under the hood, these are all `Sort u` for `u ≥ 0`. So in reality we have `Sort 0` < `Sort 1` < `Sort 2` < ⋯, where `Sort 0` is `Prop` and `Sort u` for `u > 0` is `Type u-1`.

  - Sometimes we need an object to be in universe `u` but it occupies a universe `v` s.t. `v < u` (e.g., if a definition was defined with concrete universe levels instead of polymorphically). When this happens we can _lift_ the object to a higher universe.

  - There are two mechanisms for doing so; both are basically wrapper types around the object in question:

    + `PLift` can lift a proposition or type (i.e., `Sort 0` or above) one level higher

    + `ULift` can lift a type (i.e., `Sort 1` or above) an arbitrary number of levels higher
-/

/-
  - `PLift` takes an object in universe `u` and creates a wrapper object in universe `u + 1`. Its constructor is `PLift.up` and its getter is `PLift.down`.

  - The constructor `PLift.up.{u}` takes something that lives in `Sort u` and returns something that lives in `Type u` (i.e., `Sort u+1` per the explanation above). `u` can be omitted if Lean can infer it automatically.
-/

#check PLift

/- With explicit level -/
#check PLift.{0} True
#check PLift.{1} Prop
#check PLift.{1} ℕ
#check PLift.{2} Type

/- With inferred level -/
#check PLift True
#check PLift Prop
#check PLift ℕ
#check PLift Type

/- Using the constructor -/
#check PLift.up True
#check PLift.up 42
#check PLift.up ℕ

/- Using the getter -/
#check (PLift.up True).down
#check (PLift.up 42).down
#check (PLift.up ℕ).down

/-
  As an example, notice that `List` is defined over `Type u` which doesn't
  include `Prop`, therefore we cannot make lists of proofs (which live in
  `Prop`) -/
#check List
#check_failure List (∀ x, x = x)

/-
  We can use `PLift` to make a list of proofs -/
def ℓ : List (PLift (∀ (x : Type), x = x)) := [.up (by simp), .up (by intro x; rfl)]
#check ℓ

/-
  And then extract them again -/
example : ∀ (x : Type), x = x := (ℓ.head (by simp [ℓ])).down

/-
  - `ULift` takes an object in universe `Sort u` where `u ≥ 1` (i.e., `Type 0`, `Type 1`, etc) and creates a wrapper object in universe `u + k` for any non-negative `k`. Its constructor is `ULift.up` and its getter is `ULift.down`.

  - The constructor `ULift.up.{u, v}` takes two universes: `u` is the desired universe and `v` is the original universe. `v` can be omitted if Lean can infer it automatically.
-/

#check ULift

/- With explicit original universe -/
#check ULift.{10, 0} ℕ
#check ULift.up.{10, 0} 42

/- With inferred original universe -/
#check ULift.{10} ℕ
#check ULift.up.{10} 42

/-
  Here is a function that requires a type living in `Type 10` -/
def foo (α : Type 10) (x : α) : List α := [x]

/-
  We cannot call it with `ℕ` unless we use `ULift` -/
#check_failure foo ℕ 42
#check foo (ULift.{10} ℕ) (ULift.up.{10} 42)

/-
  Lean will automatically coerce the argument if it can (hover over the `42` to
  see that its type has been coerced) -/
#check foo (ULift.{10} ℕ) 42

end_subtopic UNIVERSE_LIFTING


subtopic::WRAPUP
/-
  - As a general rule when defining inductive types, try to make things type parameters instead of indices if you can. Indices increase the universe level and make things more complicated.

  - Style-wise, it's nice to be as general as possible, i.e., defining things universe polymorphically (not just inductive type, but functions as well)

    + However, this is more important for libraries that will be used by thord-parties than it is for personal projects, so if you don't want to deal with the extra complexity don't worry abou it too much (unless your definitions _require_ polymorphism)
-/
end_subtopic WRAPUP
end_topic UNIVERSE_POLYMORPHISM
