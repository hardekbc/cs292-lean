/-
  # Proof Advice

  We cover some advice about writing proofs and specific tips about solving
  various problems that might crop up while proving or otherwise -/

import Course.CourseLib

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

topic::PROOF_STRATEGY
subtopic::GENERAL_ADVICE
/-
  - Probably the most important thing before starting a proof is to already have an argument for why the theorem is correct

    + Don't just blindly apply tactics based on the current goal, or blindly use givens just because they are there. Doing so may work for simple proofs, but for non-trivial proofs it can lead you down a blind alley and leave you stuck.

    + Having an argument in mind will guide your proof, letting you know what kind of proof to use and what subgoals you'll need to prove along the way

  - When defining functions and data structures, define them in as clear and simple a way as possible---don't try to optimize. The simpler the definitions, the easier the proofs.

    + For example, when defining a map it is often easier to prove things about a function or an associative list than a hashmap. Don't necessarily implement things the way that you would in a normal programming language; think about provability as an important metric for how good a design actually is.

    + Consider whether you even need to define them in a computable way: is a description using (inductive) predicates sufficient, or do you need it to be executable?

    + If you do need an optimized executable version, one way to approach the problem is to implement the unoptimized version, prove things about it, implement the optimized version, then prove that the unoptimized and optimized versions are equivalent

      - `Functional Programming in Lean` has a good example of this approach in Chapter 8.2, where we implement a recursive program in a clear, naive way, then implement a more efficient version and prove that they are equivalent

  - There are pros and cons to defining things in terms of (inductive) predicates vs computable functions; it is useful to consider which approach is best for your needs

    + Function pros: you are immediately guaranteed that the definition is total and deterministic, without having to prove anything; you have something that you can execute (e.g., for tests)

    + Function cons: you have to define it in a way that guarantees termination; more complex functions can make proofs more difficult

    + Predicate pros: you are describing _what_ the definition is supposed to do, not the details of _how_ to do it, which can make it simpler to define and prove things about; you don't have to worry about termination or totality issues

    + Predicate cons: you don't have anything executable; if you care about properties like being deterministic then you need to prove them yourself

    + A hybrid approach is to define the same thing both ways and then prove the equivalence between them; then you can use whichever definition is most convenient for whatever various things you are trying to do

  - Finally, proofs are like essays: the first draft is unlikely to be pretty and elegant and it's usually a waste of time to try. First make it work, then make it pretty.
-/
end_subtopic GENERAL_ADVICE


subtopic::LEMMAS
/-
  - Think of organizing a proof the way that you would a program

    + Don't try to create one huge "spaghetti proof" that tries to do everything at once; instead decompose the proof into smaller, simpler pieces (i.e., lemmas) the same way that you would decompose a program into smaller, simpler functions

      - A benefit of this approach is that, like with functions, we can now reuse lemmas across multiple proofs

      - As a rule of thumb, try for many small proofs instead of a few big proofs

    + One way to think about lemmas is as guarding an abstraction layer over a data structure and/or set of functions (i.e., the "API")

      - If a third-party proof involving the API needs to keep worrying about the internal details behind the API (e.g., doing lots of `unfold`) then that signals there are missing lemmas that could be used to hide those details

      - We don't want third-party proofs involving the API to depend in internal details because if those details change (even if those changes don't affect the behavior of the API itself) then all the proofs depending on those details are now broken

      - Mathlib is designed with this idea in mind, and can be used as a good example

  - Recall that if you define something as an inductive predicate there is no inherent guarantee that the predicate is deterministic or total, even if what you're describing is something you know has function-like behavior. Use lemmas to establish these properties (and any other useful properties) if they are relevant.

    + For example, if in a proof you have `P a b` and `P a c`, you cannot conclude that `b = c` unless you've established that `P` acts like a function, using a lemma. We show an example below.
-/

/-
  A predicate that inductively describes a particular sequence of numbers based
  on a given binary function. `Sequence f n₁ w n₂` states that using function
  `f` and starting from initial value `n₁`, `w` is a correct sequence of numbers
  that results in value `n₂`. -/
inductive Sequence (f : ℕ → ℕ → ℕ) : ℕ → List ℕ → ℕ → Prop
  | empty n₁ : Sequence f n₁ [] n₁
  | step {n₁ n₂ n₃ w} a :
    Sequence f n₁ w n₂ → f n₂ a = n₃ → Sequence f n₁ (w ++ [a]) n₃

/-
  A lemma that states the `Sequence` relation is deterministic. Note that
  `lemma` is a macro defined in Mathlib as an alias for `theorem`, i.e., to Lean
  the two keywords are indistinguishable. -/
lemma sequence_deterministic
  (f : ℕ → ℕ → ℕ) (a b c: ℕ) (ℓ : List ℕ)
  : Sequence f a ℓ b → Sequence f a ℓ c → b = c
:= by sorry -- proof is irrelevant to the point we're making

/-
  When defining a predicate (inductive or otherwise), one particular kind of
  lemma is often worth proving: _inversion lemmas_. An inversion lemma states
  what must be true in order for the predicate to be true, i.e., they are of the
  form `∀ x, P(x) → Q(x)` where `P` is the predicate in question and `Q` gives
  the necessary conditions for `P` to be true. Inversion lemmas allow us to take
  a given and infer what else must be true based on the fact that the given is
  true. We show an example below. -/

inductive Even : ℕ → Prop
  | zero : Even 0
  | add2 n : Even n → Even (n+2)

/-
  Here is an inversion lemma for `Even`. Given that `Even n`, there are two
  possible ways it could be true: either `n` is 0 (via `zero`) or `n = m + 2`
  for some `Even m` (via `add2`). We actually prove `↔` instead of `→` for
  reasons that will become apparent when we talk about proof automation tactics
  below. -/
theorem even_inv (n : ℕ) : Even n ↔ n = 0 ∨ ∃ m, n = m + 2 ∧ Even m := by
  sorry -- proof is irrelevant to the point we're making

/-
  In general there may be several inversion lemmas for a single predicate,
  depending on how many forms the predicate could take. Here is an example where
  we want to establish determinism and provide several inversion lemmas. -/

/-
  An abstract syntax tree for the language of arithmetic expressions -/
inductive AExp
  | num : ℤ → AExp
  | var : String → AExp
  | add : AExp → AExp → AExp
  | mul : AExp → AExp → AExp

/-
  An environment mapping variables to values -/
def Env := String → ℤ

/-
  A bigstep semantics describing how expressions should be evaluated -/
inductive BigstepAE : AExp → Env → ℤ → Prop
  | num (i env) : BigstepAE (.num i) env i
  | var (x env) : BigstepAE (.var x) env (env x)
  | add (e1 e2 n1 n2 env) (h1 : BigstepAE e1 env n1) (h2 : BigstepAE e2 env n2) :
    BigstepAE (.add e1 e2) env (n1 + n2)
  | mul (e1 e2 n1 n2 env) (h1 : BigstepAE e1 env n1) (h2 : BigstepAE e2 env n2) :
    BigstepAE (.mul e1 e2) env (n1 * n2)

variable {n₁ n₂ n₃ n : ℕ} {env : Env} {e e1 e2 : AExp} {x : String}

theorem ae_deterministic
  : BigstepAE e env n₁ → BigstepAE e env n₂ → n₁ = n₂
:= by sorry

theorem ae_num_inv
  : BigstepAE (.num n₁) env n₂ ↔ n₁ = n₂
:= by sorry

theorem ae_var_inv
  : BigstepAE (.var x) env n ↔ env x = n
:= by sorry

theorem ae_add_inv
  : BigstepAE (.add e1 e2) env n₃ ↔
      BigstepAE e1 env n₁ ∧
      BigstepAE e2 env n₂ ∧
      n₃ = n₁ + n₂
:= by sorry

theorem ae_mul_inv
  : BigstepAE (.mul e1 e2) env n₃ ↔
      BigstepAE e1 env n₁ ∧
      BigstepAE e2 env n₂ ∧
      n₃ = n₁ * n₂
:= by sorry

/-
  These lemmas will make some proofs involving `BigstepAE` much easier because
  they will allow us to infer useful information simply from having some
  `BigstepAE` given(s). Whether they are useful or not in a specific proof will
  depend on what exactly we're trying to prove, but if we're defining lemmas to
  use as an interface over our definition then these lemmas are a good place to
  start. -/

end_subtopic LEMMAS


subtopic::STUBS
/-
  - The same way that you could start designing a program by writing stub functions (i.e., with a particular signature but with empty bodies) you can design a proof using stub lemmas (with a particular signature but using `sorry` as the body)

    + For example, the lemmas given in the subtopic above which currently are all proved using `sorry`

    + However, you have to be careful when doing this: using `sorry` tells Lean "forget about checking this, just assume that it is correct". If you create an inconsistent lemma using `sorry` then you have made the entire logical system inconsistent, and hence any proofs are worthless.

  - You can also use `sorry` inside a proof to temporarily stand for missing terms (e.g., create a `have` statement whose proof is `sorry`), with the same caution
-/

/- Simple example of stubbing with `sorry` -/
example
  (n : ℕ) (P Q : ℕ → Prop) (h : ∀ (x : ℕ), P x ∧ Q x)
  : ∃ y, P y ∧ Q y
:= by
  have hn : P n ∧ Q n := sorry
  exists n

/- The danger of `sorry` -/
example : False := by
  have h : ∀ (P : Prop), P := sorry
  exact h False

/-
  - Taking the idea of stubbing even further, we may be in a situation where our current proof relies on some known result (e.g., from a published paper), but proving the result requires a lot of work and is outside the scope of what we're trying to accomplish

    + We can address this problem by adding the known result as an _axiom_, i.e., something that Lean takes as a given

    + This strategy has the same drawbacks as using `sorry` (in fact, using `sorry` essentially adds whatever it is as an axiom)
-/

/-
  `opaque` specifies the existence of a definition without actually defining it;
  since it isn't defined it also can't be evaluated. I'm using here for
  convenience so I don't have to actually define what a right-sided triangle is.
-/
opaque right_sided_triangle : ℕ → ℕ → ℕ → Prop

/-
  Stating the Pythagorean Theorem as an axiom instead of proving it -/
axiom pythagorean : ∀ (a b c : ℕ),
  right_sided_triangle a b c → a^2 + b^2 = c^2

end_subtopic STUBS
end_topic PROOF_STRATEGY


topic::TROUBLESHOOTING
/-
  I have endeavoured to explain Lean and its concepts in a way that removes some
  of the pain points that I encountered while learning Lean. There are a few
  miscellaneous tips left to impart for specific problems that we haven't seen
  yet. -/

subtopic::DEPENDENT_PERILS
/-
  - Recall that _dependent pattern matching_ means that we are "destructing" an inductive type with indices (i.e., using `cases`, `induction`, `match`, etc to split it into its separate cases). Doing so is more complicated than destructing non-dependent inductive types because each case can have a different type.

  - We will go into some more examples of what can go wrong and why, and some possible fixes.
-/

/-
  Lean has very limited ability to reason about type equality, as the `#eval`
  below shows: it isn't even able to determine that `ℕ` is not the same as
  `String` (why it has this difficulty goes beyond the scope of this class) -/
/--
  error: failed to synthesize Decidable (ℕ = String) -/
#guard_error
#eval ℕ = String

/-
  Consider `T₁`, with one index that is `Type` and whose two constructors
  instantiate that index with `ℕ` and `String` respectively. This is a
  simplified version of the inductive type we used in the `L12_DExpLang` example
  for inherently-typed expressions. -/
inductive T₁ : Type → Type
  | one : ℕ → T₁ ℕ
  | two : String → T₁ String

/-
  Now we try to do a proof by cases using `T₁ ℕ` and get the error below. When
  we destruct a dependent inductive type (which is what "dependent elimination"
  means) using `cases` or `match`, Lean automatically employs an equation solver
  to figure out what is true or false for each case based on the different
  constructors of the type being destructed. Here, this entails solving the
  equations `ℕ = ℕ` (for constructor `one`) and `ℕ = String` (for constructor
  `two`). What we would like to happen is for Lean to realize that the first
  equation is true (and hence case `one` is valid) and the second equation is
  false (and hence case `two` is not valid and can be ignored). But since Lean
  cannot decide type equality, it cannot solve these equations...and thus we get
  the error below. -/
/--
  error: Dependent elimination failed: Failed to solve equation ℕ = String -/
#guard_error
example (h : T₁ ℕ) : True := by
  cases h

/-
  If we abstract the concrete type as a variable then everything is fine,
  because Lean generates the two equations `α = ℕ` and `α = String` for each
  case respectively, which doesn't require deciding type equality (but also
  means that we can't rule out a case based on the actual type, we have to
  handle both cases). -/
example {α : Type} (h : T₁ α) : True := by
  cases h
  all_goals simp

/-
  We get the same problem when pattern-matching -/
/--
  error: Tactic `cases` failed with a nested error:
    Dependent elimination failed: Failed to solve equation
      ℕ = String
    at case `T₁.two` after processing _

  the dependent pattern matcher can solve the following kinds of equations
  - <var> = <term> and <term> = <var>
  - <term> = <term> where the terms are definitionally equal
  - <constructor> = <constructor>, examples: List.cons x xs = List.cons y ys, and List.cons x xs = List.nil
-/
#guard_error
example : T₁ ℕ → ℕ
  | .one n => n

/-
  And again we can solve it by abstracting the concrete type into a variable
  (but now cannot rule out returning a `String`) -/
example {α : Type} : T₁ α → α
  | .one n => n
  | .two s => s

/-
  We can try to be clever by abstracting the type into a variable but also
  adding a given equating that variable with the concrete type, which allows the
  `cases` to go through...but it is ultimately futile: we need to be able to
  rule out case `two` because there is no number to return, but the
  contradiction in the givens that would rule the case out is `String = ℕ` which
  Lean cannot decide. -/
example {α : Type} (h₁ : α = ℕ) (h₂ : T₁ α) : ℕ := by
  cases h₂ with
  | one n => exact n
  | two s => sorry -- problem here: need to decide `String = ℕ`

/-
  - In summary, Lean has problems destructing dependent inductive types whose indices are concrete types (either directly or via equations), because it can't decide type equality. We can solve the problem by not using concrete types (using variables instead), but then we lose the ability to reason about the dependent inductive type based on what the actual concrete type of an index might be (e.g., we can't say that because the index is `ℕ` we will be able to return a `ℕ` as in the example above).

  - However, all is not lost...there is a workaround. We can create a inductive type (named, say, `Ty`) that has a constructor for each type we want to allow as an index. Then we define our  inductive type `T₂` using `Ty` as the index instead of `Type`. The idea here is that when we destruct `T₂`, the equation solver will be comparing `Ty`s constructors for equality instead of the concrete `Type`s that they map to, and therefore can detect inconsistent types with no problem. We've effectively replaced deciding type equality with deciding constructor equality.

    + The drawback (or benefit, depending on your use-case) is that we have to explicitly list ahead-of-time all the types that we want to allow as an index, so we lose flexibility (or gain precision, again depending on your perspective)
-/

/-
  Here is our list of desired types -/
inductive Ty
  | nat
  | string

/-
  We create the actual inductive type we care about, using `Ty` instead of `ℕ`
  and `String` -/
inductive T₂ : Ty → Type
  | one : ℕ → T₂ Ty.nat
  | two : String → T₂ Ty.string

/-
  Now we destruct a `T₂` that has the concrete index `Ty.nat` and Lean can rule
  out the case `T₂.two` as we would hope, allowing us to return a `ℕ` -/
example : T₂ Ty.nat → ℕ
  | .one n => n

/-
  One issue is that we don't have any explicit connection between `Ty`s
  constructors and the types they are supposed to stand for. We can fix this by
  using a function that maps `Ty`s constructors to the appropriate types. -/

/-
  We map each constructor to the `Type` it stands for -/
def Ty.to_type : Ty → Type
  | .nat => ℕ
  | .string => String

/-
  We create the actual inductive type we care about, using `Ty` instead of `ℕ`
  and `String` and using `Ty.to_type` to automatically use the correct concrete
  `Type` for the constructor arguments -/
inductive T₃ : Ty → Type
  | one : Ty.nat.to_type → T₃ Ty.nat
  | two : Ty.string.to_type → T₃ Ty.string

/-
  If we want to be fancy about it we can use an implicit coercion between `Ty`s
  constructors and their corresponding `Type`s via a type class -/
instance : CoeSort Ty Type where
  coe := Ty.to_type

/-
  Note that we're using `Ty`s constructors as types directly; the coercion we
  defined above automatically uses `Ty.to_type` to translate them into actual
  `Type`s wherever a `Type` is expected -/
inductive T₄ : Ty → Type
  | one : Ty.nat → T₄ Ty.nat
  | two : Ty.string → T₄ Ty.string

/-
  We can create `T₄` as expected, though we need to explicitly cast the argument
  to `one` because there are many possible implicit casts and Lean gets confused
-/
#check T₄.one (42 : ℕ)
#check T₄.two "hello"

/-
  And our previous example now works -/
example : T₄ Ty.nat → Ty.nat
  | .one n => n

/-
  - See `L18_Ex_DExp` for a more in-depth examples of how to apply the advice given above

  - The same sort of issue can happen when doing a proof, e.g., when doing rule induction the `induction` tactic requires that any indices of the inductive predicate we're doing induction on must be variables. However, sometimes we need to do rule induction when this is not true. The `generalize` tactic can help, by replacing an expression with a variable. This was discussed (with examples) in `L13_ComprehensiveRecap`.
-/

end_subtopic DEPENDENT_PERILS


subtopic::TERMINATION_PROOFS
/-
  Here I discuss a couple of strategies for helping with termination proofs -/

/-
  Here is an example where the argument to a recursive call is, itself, a
  recursive call. The function `silly₁` is a terribly inefficient identity
  function, i.e, `∀ n, silly₁ n = n`. Lean is unable to determine that the
  function terminates, and if we look inside the `decreasing_by` proof we can
  see why. -/
def silly₁ : ℕ → ℕ
  | 0 => 0
  | n + 1 => 1 + (silly₁ (silly₁ n))
decreasing_by
  · lia -- `n < n + 1` is trivially true
  · rename_i inner_silly₁
    /-
      In the proof state we see an odd function, which I have renamed to
      `inner_silly₁` to help with intuition. This is the function that we're
      calling to make the inner recursive call that is the argument to the outer
      recursive call. It is a function with two arguments: `y` is the natural
      number argument we expect; the second argument is a proof (created by Lean
      to show that the inner recursive call is decreasing) that `y < n + 1`; the
      result is another natural number. However, there is no information given
      about the relation between the result (which is passed to the outer
      recursive call) and `n`, so it is impossible to prove the goal (i.e., that
      the result is less than `n + 1`, hence the outer call is also decreasing).
    -/
    sorry

/-
  We can address this issue using subtypes: instead of just returning a natural
  number, we return a subtype proving that the result is identical to the
  argument. We need to change the return values to turn them into subtypes with
  the appropriate proofs (in this case `grind` can prove the claim by itself;
  you might think we need an inductive argument, but we already have the
  "inductive hypotheses" in the form of the return values of the two recursive
  calls). If we look inside the `decreasing_by` clause, we now have exactly the
  information that we need to prove the goal, i.e., that the result of the inner
  recursive call is less than `n + 1`. -/
def silly₂ : (n : ℕ) → {m // m = n}
  | 0 => ⟨0, rfl⟩
  | n + 1 =>
    ⟨1 + (silly₂ (silly₂ n)), by grind⟩
decreasing_by all_goals grind

/-
  Here is an example showing an issue with nested inductive types. Recall that
  this means that one of the constructors (`kids` in this case) has an argument
  that is a different inductive type that itself takes the current inductive
  type as an argument (so `List T1` in this example: `List` is taking `T1` as an
  argument). -/
structure T1 where
  val : ℕ
  kids : List T1

/-
  Lean can't figure out the termination argument, so we need to provide one. In
  this example all we need to do is used `cases` to expose the underlying
  definition of `t`, which is enough for the default tactic to take it from
  there. Note that `T1` is a structure so it may seem odd to use `cases` on it,
  but recall that a structure is just syntactic sugar for a inductive type.
  Think of `cases` as "peer inside the definition of this structure/inductive
  type to see what it's made of". -/
def T1.num_nodes (t : T1) : ℕ :=
  1 + (t.kids.map (·.num_nodes)).sum
decreasing_by
  cases t
  decreasing_tactic

/-
  Here is a more complicated example using nested inductive types -/
inductive T2
  | nat : ℕ → T2
  | kids : List (ℕ × T2) → T2

/-
  Again Lean automatically generates a `sizeOf` implementation for `T2`; it
  recursively counts the sizes of the subexpressions (using the default `sizeOf`
  for `ℕ` and `List`) plus the number of subexpressions -/
#print T2._sizeOf_1

/-
  Now we try to write a function that traverses a `T2` and sums up the values of
  its nodes (for a node `(n, t)` the value is `n * (sumT₁ t)`). Lean is using
  the default `sizeOf` as the measure, which is fine, but it is not able to
  determine that the function terminates (check the goal of the `decreasing_by`
  clause): it is confused by the nested inductive types. -/
def sumT₁ : T2 → ℕ
  | .nat n => n
  | .kids tns => tns.foldl (fun acc (n, t) => acc + n * (sumT₁ t)) 0
decreasing_by sorry

/-
  We can prove the termination condition as a lemma -/
lemma sizeOf_T2_lt_mem_T2
  {ts : List (ℕ × T2)} {n t} (h : (n, t) ∈ ts)
  : sizeOf t < sizeOf (T2.kids ts)
:= by induction h with grind

/-
  However, this is not sufficient. If we look at the proof state for the
  termination proof, we're missing the fact that `t = x.2`, that is, there is no
  connection given between `t` and `tns`, so we don't have the necessary fact
  `(x.1, t) ∈ tns`, which we need for the lemma to apply. _We_ know that `x.2`
  and `t` are the same, but Lean doesn't (try swapping `x.2` for `t` in the
  lemma arguments to see what happens). -/
def sumT₂ : T2 → ℕ
  | .nat n => n
  | .kids tns => tns.foldl (fun acc (n, t) => acc + n * (sumT₂ t)) 0
decreasing_by
  expose_names
  exact @sizeOf_T2_lt_mem_T2 tns x.1 t (by sorry)

/-
  Fortunately subtypes can come to the rescue again, this time in the form of
  the `List.attach` function. `ℓ.attach` takes a list `ℓ` of type `List α` and
  produces a new list of type `List {x:α // x ∈ ℓ}`, i.e., the elements are
  subtypes asserting the fact that the element is a member of the original list.
  This is exactly the information that we need to know for our termination
  proof. The `property` given in the proof state is coming from `List.attach`.
  Other container datatypes besides `List` also usually have an `attach`
  function for exactly this purpose. -/
def sumT₃ : T2 → ℕ
  | .nat n => n
  | .kids tns => tns.attach.foldl (fun acc ⟨(n, t), _⟩ => acc + n * (sumT₃ t)) 0
decreasing_by grind [→ sizeOf_T2_lt_mem_T2]

end_subtopic TERMINATION_PROOFS


subtopic::INSTANCES_ARE_NOT_UNIQUE
/-
  - Instance inference takes a type class and a type and searches for an instance of that typeclass for that type

    + Inference can be triggered via an implicit parameter (e.g, `[DecidableEq α]`) or explicitly using `inferInstance` or `inferInstanceAs` or the tactic `infer_instance`

  - An important point to keep in mind is that two different instance inferences for the same type class and type can result in two different instances. Different instances are not guaranteed to be equivalent, and may behave differently from one another.
-/

/-
  Here is an example of a potential bug resulting from the possibility of
  multiple instances -/
namespace Example1

/- We define a structure `T` -/
structure T where
  f1 : ℤ
  f2 : ℤ
deriving Repr

/- And some objects of type `T` -/
def t1 : T := { f1 := 2, f2 := 4 }
def t2 : T := { f1 := 6, f2 := 8 }
def t3 : T := { f1 := 3, f2 := 5 }

/-
  We define another structure `MyList` that is a container around elements of an
  arbitrary type -/
structure MyList (α : Type) where
  list : List α

/-
  And some objects of type `MyList` that contain the `T` objects that we defined
  above -/
def ℓ1 : MyList T := { list := [t1, t2] }
def ℓ2 : MyList T := { list := [t2, t3] }

/-
  And a function on `MyList` that requires that the contents have an instance of
  the `Add` type class -/
def MyList.sum {α : Type} [Add α] (ℓ₁ ℓ₂ : MyList α) : MyList α :=
  { list := (ℓ₁.list.zip ℓ₂.list).map (fun (a, b) => a + b) }

/-
  To call the `MyList.sum` function on `ℓ1` and `ℓ2` we have to give `T` an
  instance of the `Add` class -/
instance : Add T where
  add := fun t₁ t₂ => { f1 := t₁.f1 + t₂.f1, f2 := t₁.f2 + t₂.f2 }

/- And the result is as we expect -/
#eval (ℓ1.sum ℓ2).list

/-
  Now we define a _new_ instance of the `Add` type class for `T` that behaves
  differently from the first instance -/
instance : Add T where
  add := fun t₁ t₂ => { f1 := t₁.f1 - t₂.f1, f2 := t₁.f2 - t₂.f2 }

/-
  When we call `MyList.sum` again we get a different answer because the instance
  inference chooses the latest `Add` instance registered for `T` -/
#eval (ℓ1.sum ℓ2).list

/-
  The issue is that we have decoupled the `MyList` objects from the instances of
  `Add` used to manipulate those objects, leaving open the possibility that we
  can manipulate the same objects with the same functions and get different
  results. This is especially bad if these functions are an API around a data
  structure that is supposed to maintain a particular invariant (e.g., being
  sorted), because the different instances being mixed together on the same data
  structure can break the invariant. -/

end Example1

/-
  Here is one way to fix the problem, by coupling the instance of `Add` being
  used for `α` with the `MyList` inductive type itself. -/
namespace Example2

/- We define `T` -/
structure T where
  f1 : ℤ
  f2 : ℤ
deriving Repr

/- And some objects of type `T` -/
def t1 : T := { f1 := 2, f2 := 4 }
def t2 : T := { f1 := 6, f2 := 8 }
def t3 : T := { f1 := 3, f2 := 5 }

/-
  We define `MyList`, now requiring an instance of `Add` for `α` at the point we
  create an object of type `MyList` -/
structure MyList (α : Type) [Add α] where
  list : List α

#check MyList

/-
  To create `ℓ1` and `ℓ2` we have to give `T` an instance of the `Add` class -/
instance : Add T where
  add := fun t₁ t₂ => { f1 := t₁.f1 + t₂.f1, f2 := t₁.f2 + t₂.f2 }

/-
  Now we can define `ℓ₁` and `ℓ₂` -/
def ℓ1 : MyList T := { list := [t1, t2] }
def ℓ2 : MyList T := { list := [t2, t3] }

/-
  And `MyList.sum`. Notice that we still need to require an instance of `Add`
  for `α`, but the `MyList` parameters constrain it to be the same instance that
  was used to create `ℓ₁` and `ℓ₂` (see the `#check MyList` above) -/
def MyList.sum {α : Type} [Add α] (ℓ₁ ℓ₂ : MyList α) : MyList α :=
  { list := (ℓ₁.list.zip ℓ₂.list).map (fun (a, b) => a + b) }

/- The result is again as we expect -/
#eval (ℓ1.sum ℓ2).list

/-
  Now we again define a new instance of the `Add` type class for `T` -/
instance : Add T where
  add := fun t₁ t₂ => { f1 := t₁.f1 - t₂.f1, f2 := t₁.f2 - t₂.f2 }

/-
  When we call `MyList.sum` again we get the error below because it synthesized
  (i.e., found via instance inference) a different instance of `Add` for `T`
  than the one required by `ℓ₁` and `ℓ₂`. Note that Lean does not continue
  looking for other instances that might work, it stops at the first one that it
  finds. This error is a _good_ thing because it prevents the code from silently
  using inconsistent instances. -/
/--
  error: synthesized type class instance is not definitionally equal to
  expression inferred by typing rules, synthesized instAddT_1 inferred instAddT
-/
#guard_error
#eval (ℓ1.sum ℓ2).list

end Example2

/-
  The issue can also show up via inductive type constructors, as shown below -/
namespace Example3
/-
  We define `T₁` to have one parameter `α` and one index (a value of type `α`);
  note that `α` looks like an index but has been promoted to a parameter. Its
  constructor takes a type `β`, a proof `[Add β]` that `β` implements the `Add`
  type class, and a value `b : β`, and returns an object of type `T₁ β (b + b)`
-/
inductive T₁ : (α : Type) → α → Prop
  | mk {β : Type} [Add β] (b : β) : T₁ β (b + b)

/-
  We then try to prove that for `T₁ ℕ n`, `n` must be even, which should be true
  because we construct all `T₁` by doubling the given value. However, we quickly
  run into a problem as shown in the error below. -/
/--
  error: Tactic `rfl` failed: The left-hand side
    @HAdd.hAdd ℕ ℕ ℕ (@instHAdd ℕ inst✝) a a
  is not definitionally equal to the right-hand side
    @HAdd.hAdd ℕ ℕ ℕ (@instHAdd ℕ instAddNat) a a
-/
#guard_error
example {n: ℕ} (h : T₁ ℕ n) : Even n := by
  cases h with
  | mk a =>
    unfold Even
    exists a
    /-
      The goal at this point is `⊢ a + a = a + a`, which seems like it should be
      easy to prove: both sides are the same, so we just use `rfl`. However,
      `rfl` gives the error described above. Notice that the pretty printer
      shows us `a + a` in the infoview, but the error is showing the actual,
      non-pretty printed version...and the two sides are _not_ actually the
      same. The left side is using the `Add ℕ` instance inferred for the `T₁.mk`
      constructor, while the right side is using the `Add ℕ` instance inferred
      right now when we expanded `Even x` into its definition. Lean has no way
      of knowing whether these two instances are the same or if they behave the
      same, and so cannot determine whether the goal is true. -/
    rfl

/-
  One other lesson from this example is that you can't always trust what you
  see. The pretty-printer tries to make things more human-readable, but in doing
  so it can omit information that turns out to be important. If you are in a
  situation where things look identical but don't behave the same, this is
  probably the reason why. -/

/-
  Again, inferring instances as inductive type _parameters_ works fine, as in
  the following example -/
inductive T₂ (α : Type) [Add α] : α → Prop
  | one (a : α) : T₂ α (a + a)

/-
  Notice immediately before the `rfl` that we have a goal that looks the same as
  before, but now `rfl` works because under the hood Lean knows they are using
  the same inferred instance -/
example {n: ℕ} (h : T₂ ℕ n) : Even n := by
  cases h with
  | one a =>
    unfold Even
    apply Exists.intro a
    rfl

end Example3

/-
  See `L18_Ex_Dfa` for a practical example of how this problem might arise and
  how to fix it -/

end_subtopic INSTANCES_ARE_NOT_UNIQUE


subtopic::TYPECLASS_INSTANCE_FOR_NESTED_TYPES
/-
  - One issue that I struggled with for a while is figuring out how to define a type class instance for a nested inductive type. Recall that a nested inductive type is when a constructor gives the inductive type being defined as an argument to another inductive type, e.g., if we are defining the type `Foo` and a constructor parameter is `List Foo`.

  - Here I will demonstrate how to do so, using the `DecidableEq` type class. Recall that this type class means that determining whether two objects of that type are equal is a decidable problem, i.e., there is an algorithm that can compute the answer.
-/

/-
  Here is a non-nested inductive type, demonstrating that creating an instance
  of `DecidableEq` is trivial enough that Lean can do it automatically -/
inductive T1
  | one
  | two : T1 → T1
deriving DecidableEq

/-
  Here we have a nested inductive type, and Lean _cannot_ automatically make it
  an instance of `DecidableEq` (uncomment the `deriving` line to see the error).
  Therefore we have to create the instance manually.
-/
inductive T2
  | one
  | two : List T2 → T2
-- deriving DecidableEq

/-
  Here is what we're trying to define: a function that takes two objects `a` and
  `b` of type `T2` and returns an instance of `Decidable (a = b)` -/
#print DecidableEq

/-
  And here is `Decidable`, the thing we want the function to return. It has two
  cases: `isTrue` takes a proof that the proposition (`a = b` in this case) is
  true and `isFalse` takes a proof that the proposition is false. -/
#print Decidable

/-
  Here is a naive attempt to define the required function. The `noConfusion` is
  the canonical term-based way to say that constructors are injective, i.e., if
  two objects were created by different constructors then they cannot be equal.
-/
/--
  error: failed to synthesize instance of type class DecidableEq T2 -/
#guard_error
instance T2.decEq1 : DecidableEq T2 := fun (t₁ t₂ : T2) =>
  match t₁, t₂ with
  | .one, .one => .isTrue rfl
  | .one, .two _ | .two _, .one => .isFalse T2.noConfusion
  | .two ts1, .two ts2 =>
    /-
      And this is the fundamental problem: we rely on `DecidableEq` for `List`
      to determine whether `ts1` and `ts2` are equal, but because it is a list
      of `T2`, _that_ depends on `DecidableEq` for `T2`...which is exactly what
      we're trying to define now. -/
    match instDecidableEqList ts1 ts2 with
      | .isFalse h => .isFalse (by grind)
      | .isTrue h => .isTrue (by grind)

/-
  Here is the working version. There are two changes: (1) the `let _ ...` in the
  final case is a trick that allows the instance inference algorithm to find
  `DecidableEq T2` while we're defining it recursively; and (2) because it's
  recursive we get a complaint about proving termination, which we fix by making
  the function `partial` (this is fine because we aren't reasoning about the
  decidability algorithm; if we were then we would need to prove termination) -/
partial instance T2.decEq2 : DecidableEq T2 := fun (t₁ t₂ : T2) =>
  match t₁, t₂ with
  | .one, .one => .isTrue rfl
  | .one, .two _ | .two _, .one => .isFalse T2.noConfusion
  | .two ts1, .two ts2 =>
    let _ : DecidableEq T2 := T2.decEq2
    match instDecidableEqList ts1 ts2 with
      | .isFalse h => .isFalse (by grind)
      | .isTrue h => .isTrue (by grind)

/-
  `inferInstance` will attempt to synthesize the requested type class for the
  given type; this shows that `T2` does have an instance for `DecidableEq` -/
#check (inferInstance : DecidableEq T2)

def t2_1 := T2.two [T2.one, T2.two [T2.one], T2.one]
def t2_2 := T2.two [T2.one, T2.one, T2.two [T2.one]]

#eval t2_1 = t2_1
#eval t2_1 = t2_2

end_subtopic TYPECLASS_INSTANCE_FOR_NESTED_TYPES
end_topic TROUBLESHOOTING
