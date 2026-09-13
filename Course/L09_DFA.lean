/-
  # Deterministic finite automata

  We will define and verify certain properties of DFA.
-/

import Course.CourseLib

/-
  -----------------------------------------------------------
  IMPLEMENTATION
  -----------------------------------------------------------
-/

/-
  First we need to define a data structure for the DFA. Rather than an inductive
  type we will use a _structure_, as explained further below. We use `ℕ` for
  states; the issue with this choice is that there is nothing stopping the user
  from creating an _infinite_ automata, and thus we will encounter difficulties
  in defining and proving certain things. We will see how to fix this problem
  elegantly using dependent types later. -/
structure Dfa
  -- `α` is the alphabet, it must be finite and non-empty
  (α : Type) [Fintype α] [Nonempty α]
where
  size : ℕ              -- number of states
  δ : ℕ → α → ℕ         -- transition function
  start : ℕ             -- starting state
  accepting : ℕ → Bool  -- accepting states

/-
  - Structure types are another kind of user-defined data structure. They are basically "records" or "structs", i.e., they have multiple fields that can be accessed independently. Behind the scenes they are actually implemented as inductive types with a single constructor whose parameters are the fields of the structure.

  - `Fintype` and `Nonempty` are type classes, similar to the ones we've seen before (e.g., `DecidableEq` and `ToString`). `Fintype` provides evidence that a type is finite, i.e., there are only a finite number of values of that type. `Nonempty` provides evidence that there is at least one value of that type.

  - The `[...]` are another kind of _implicit parameter_, like `{}` except intended specifically for type classes. So the `Dfa` parameters are saying that `α` (the alphabet type) can be any type, as long as that type has been registered to have instances for `Fintype` and `Nonempty`.
-/

/-
  We'll be defining lots of things that require an alphabet type, and it can be
  annoying to have to constantly include it (and its associated type classes) as
  parameters in everything. Lean provides a shortcut with `variable` (which we
  have seen before but not really talked about). `variable` does _not_ declare
  something as a "global variable", rather if any definition mentions `α`
  without declaring it explicitly then Lean will automatically include it (and
  the associated type classes) as parameters of that definition. Since we
  declare `α` here inside `{}` it will be an implicit parameter; if we had used
  `()` it would be an explicit parameter. -/
variable {α : Type} [Fintype α] [Nonempty α]

/-
  Now we will define various operations on a `Dfa` -/
namespace Dfa

/-
  Return the resulting state after running `M` on input `w` starting in state
  `σ`. The `w.foldl` is applying the transition function `M.δ` to each element
  of the input in turn to get a new state, starting from `σ`. -/
def runsto (M : Dfa α) (σ : ℕ) (w : List α) : ℕ :=
  w.foldl M.δ σ

/-
  Return whether Dfa `M` accepts input word `w`. We use `runsto` starting from
  `M.start` to determine what state we end up in, and then call `M.accepting` to
  see if that state is accepting. -/
def accepts (M : Dfa α) (w : List α) : Bool :=
  M.accepting (M.runsto M.start w)

/-
  Return the complement of `M`, which is the same as `M` except that for
  `accepting` we do the opposite of whatever `M.accepting` does. We use the
  notation for copying the values of another structure except replacing certain
  fields: `{SomeStruct with field := <replacement>}`. -/
def compl (M : Dfa α) : Dfa α :=
  { M with accepting := fun s => !(M.accepting s) }

/-
  Return the union of `M1` and `M2`. The classic construction is to have DFA
  states that are pairs of states from `M1` and `M2`, but our `Dfa` only uses
  `ℕ` for states. We solve this using Cantor's pairing function that uniquely
  transforms pairs of numbers to a single number and back again. We use the
  notation for creating a structure: `{field1 := ..., field2 := ..., ...}` -/
def union (M1 M2 : Dfa α) : Dfa α :=
  { size :=
      /-
        An upper bound on the number of states in the new `Dfa` -/
      3 * M1.size * M2.size
    δ :=
      /-
        Translate the input state into a pair of states from `M1` and `M2`, run
        `M1.δ` and `M2.δ` on them, then translate the resulting pair of states
        back to a single number.-/
      fun s a =>
        let (s1, s2) := nat_to_pair s
        pair_to_nat ((M1.δ s1 a), (M2.δ s2 a))
    start :=
      /-
        Use the pairing function to map the pair of starting states to a new
        starting state -/
      pair_to_nat (M1.start, M2.start)
    accepting :=
      /-
        Translate the input state into a pair of states from `M1` and `M2` and
        accept if either of them are accepting states in the original DFAs -/
      fun s =>
        let (s1, s2) := nat_to_pair s
        M1.accepting s1 || M2.accepting s2 }
where
  /- Cantor's pairing function and its inverse -/
  pair_to_nat (xy : ℕ × ℕ) : ℕ :=
    let (x, y) := xy
    ((x + y) * (x + y + 1)) / 2 + y
  nat_to_pair (z : ℕ) : ℕ × ℕ :=
    let w : ℕ := Nat.floor (((Rat.sqrt (8 * (z : ℚ) + 1)) - 1) / 2)
    let t : ℕ := (w^2 + w) / 2
    let y : ℕ := z - t
    let x : ℕ := w - y
    (x, y)

/-
  Return the intersection of `M1` and `M2`. We use the identity that `A ∩ B` is
  the same as `¬(¬A ∪ ¬B)`. -/
def intersect (M1 M2 : Dfa α) : Dfa α :=
  Dfa.compl (Dfa.union (Dfa.compl M1) (Dfa.compl M2))

/-
  Return whether `M` recognizes the empty language. The strategy is to determine
  if any accepting state is reachable from the start state; if so then the
  language is not empty, otherwise it is empty. -/
def empty (M : Dfa α) : Bool :=
  !(reaches_accepting {M.start} M.size)
where
  /-
    Figure out whether the starting state can reach some accepting state. We use
    the clocked recursion strategy to show Lean this terminates. We need to
    check at most the number of states contained in `M`, so as long as we give
    it that much fuel we're guaranteed to not prematurely run out of fuel. This
    strategy depends on the assumption that `size` is accurate. We cannot prove
    termination without clocked recursion because nothing restricts the `Dfa` to
    finite states; we'll see how to do better using dependent types later. -/
  reaches_accepting (states : Finset ℕ) : ℕ → Bool
    | 0 => false
    | n + 1 =>
      /-
        We can learn that `Finset` operations like `fold`, `sup`, `univ`, and
        `image` exist using the Mathlib API. Hover over them in VS Code to see
        what they do. Note that `Finset` is not really intended as an efficient
        set-like data structure for regular programming (there are other data
        structures for that). -/
      if states.fold Bool.or false (M.accepting ·) then true
      else
        let next := states.sup (fun s => Finset.univ.image (M.δ s ·))
        reaches_accepting next n

/-
  Return whether the languages of `M1` and `M2` are the same, which is true iff
  `L(M1) \ L(M2) = ∅ ∧ L(M2) \ L(M1) = ∅` -/
def equals (M1 M2 : Dfa α) : Bool :=
  (M1.intersect M2.compl).empty &&
  (M2.intersect M1.compl).empty

end Dfa

/-
  -----------------------------------------------------------
  FORMALIZATION
  -----------------------------------------------------------
-/

/-
  First we define a formal language. A language over an alphabet `α` is a set of
  words, where a word is a list of elements from the alphabet. `α` is the type
  of the alphabet, and it must be finite and nonempty. -/
abbrev Language (α : Type) [Fintype α] [Nonempty α] :=
  Set (List α)

/-
  `Mul` is a type class that gives access to `*` notation that we use here for
  language concatenation. Any type with an instance registered for `Mul` can use
  the `*` binary operator and it will translate to whatever function we use for
  that instance. Lean uses type classes for a lot of notation, which we can use
  for our own types by registering instances as shown here. -/
instance : Mul (Language α) := ⟨Set.image2 (· ++ ·)⟩

/-
  The Kleene star of a language. `w` is in `L⋆` if we can split it into
  substrings s.t. each substring is in `L`. We use Lean's set comprehension
  syntax to define this new set: `{ <var> : <type> | <proposition>}`. -/
def kleene_star (L : Language α) : Language α :=
  { w : List α | ∃ ℓ : List (List α), w = ℓ.flatten ∧ ∀ w' ∈ ℓ, w' ≠ [] ∧ w' ∈ L }

/-
  Now we formalize things about `Dfa` specifically -/
namespace Dfa

/-
  While ultimately we are interested in a DFA running on an input from the
  starting state and seeing whether it ends in an accepting state, this is too
  weak to be useful when doing inductive proofs on DFA. Per the common strategy
  when this happens, we need to strengthen the inductive hypothesis by making a
  stronger statement. Here we define DFA behavior in terms of starting from some
  given state, running on some input, and ending in some state: the inductive
  predicate `RunsTo M σ₁ w σ₂` means `M` starting in state `σ₁` on input `w`
  ends in state `σ₂`. -/
inductive RunsTo (M : Dfa α) : ℕ → List α → ℕ → Prop where
  | empty σ : RunsTo M σ [] σ
  | step {σ₁ σ₂ σ₃ w a} : RunsTo M σ₁ w σ₂ → M.δ σ₂ a = σ₃ → RunsTo M σ₁ (w ++ [a]) σ₃

/-
  We define acceptance in terms of the `RunsTo` predicate: `M` accepts `w` if
  there is some accepting state `σ` s.t. running `M` on `w` from `M.start` ends
  in state `σ`. -/
def accepts_prop (M : Dfa α) (w : List α) : Prop :=
  ∃ σ, M.RunsTo M.start w σ ∧ M.accepting σ

/- The language of a DFA -/
def L (M : Dfa α) : Language α :=
  { w : List α | M.accepts_prop w }

/-
  -----------------------------------------------------------
  PROOFS
  -----------------------------------------------------------
-/

/-
  It will be useful to annotate various definitions with `simp` -/
attribute [simp] compl
attribute [simp] union
attribute [simp] intersect
attribute [simp] empty
attribute [simp] empty.reaches_accepting
attribute [simp] equals
attribute [simp] kleene_star
attribute [simp] RunsTo.empty
attribute [simp] RunsTo.step
attribute [simp] accepts_prop
attribute [simp] L
attribute [simp] runsto
attribute [simp] accepts

/-
  We will need some helper lemmas about `RunsTo`, leading up to the fact that
  `runsto` agrees with `RunsTo` -/
namespace RunsTo

/-
  Note the `with simp_all`; this means to apply the `simp_all` tactic to all
  cases of the induction. In this case, that is enough to close all the cases by
  itself. -/
lemma runsto_equiv₁
  {M : Dfa α} {σ₁ σ₂ : ℕ} {w : List α}
  : M.RunsTo σ₁ w σ₂ → M.runsto σ₁ w = σ₂
:= by
  intro h
  induction h with simp_all

/-
  Here we can't do induction on `RunsTo` (because that's our goal), and `runsto`
  isn't recursive so we can't use `fun_induction`, so the only thing that makes
  sense is to do induction on the input word `w`. However, there is a problem:
  the `List` induction principle, when trying to prove predicate `P`, says
  something like "if `P []`, and if `P as → P (a :: as)`, then `P ℓ`". However,
  `RunsTo.step` is defined by saying "if `P as` then `P (as ++ [a])`". In other
  words, the induction principle assumes that we're prepending `a` but `RunsTo`
  assumes that we're appending `a`. Fortunately the `induction` tactic allows us
  to use different induction principles as needed, and there is one for `List`
  that is exactly what we need. We'll discuss alternate induction principles in
  detail (and how to write our own induction principles) later. -/
lemma runsto_equiv₂
  {M : Dfa α} {σ₁ σ₂ : ℕ} {w : List α}
  : M.runsto σ₁ w = σ₂ → M.RunsTo σ₁ w σ₂
:= by
  induction w using List.reverseRecOn generalizing σ₂ with
  | nil => simp_all
  | append_singleton as a ih =>
    intro h
    simp_all
    exact RunsTo.step ih h

lemma runsto_equiv
  {M : Dfa α} {σ₁ σ₂ : ℕ} {w : List α}
  : M.RunsTo σ₁ w σ₂ ↔ M.runsto σ₁ w = σ₂
:= ⟨runsto_equiv₁, runsto_equiv₂⟩

end RunsTo

/- ----- accepts_is_correct ----- -/

lemma accepts_of_accepts_prop
  {M : Dfa α} {w : List α}
  : M.accepts_prop w → M.accepts w
:= by simp_all [RunsTo.runsto_equiv]

/-
  We need to explicitly invoke `RunsTo.runsto_equiv` because we don't have a
  given in the proper form (i.e., `σ = σ`). Notice that (1) we don't have to
  give the `have` a name; and (2) we do need to give `σ` explicitly to `simp` so
  that it will know what its definition is. -/
lemma accepts_prop_of_accepts
  {M : Dfa α} {w : List α}
  : M.accepts w → M.accepts_prop w
:= by
  intro h
  let σ := M.runsto M.start w
  exists σ
  have : M.RunsTo M.start w σ := RunsTo.runsto_equiv.2 (by simp [σ])
  simp_all [σ]

/-
  We verify that our implementation of acceptance is correct -/
theorem accepts_is_correct
  {M : Dfa α} {w : List α}
  : M.accepts_prop w ↔ M.accepts w
:= ⟨accepts_of_accepts_prop, accepts_prop_of_accepts⟩

/- ----- compl_is_correct ----- -/

/-
  We verify that our implementation of complement is correct -/
theorem compl_is_correct {M : Dfa α} : M.compl.L = M.Lᶜ := by
  ext
  simp [RunsTo.runsto_equiv]

/- ----- union_is_correct ----- -/

/-
  Rather than re-prove that Cantor's pairing function is a bijection, we'll make
  it an axiom. This is _dangerous_, because if I made a mistake then this axiom
  could make Lean's logic inconsistent, and anything derived using it would be
  worthless. Be very careful when declaring an axiom (and prefer not doing at
  all), and if you _do_ make an axiom try to make it the simplest statement that
  you can in order to help prevent mistakes. -/
axiom pairing_axiom : union.nat_to_pair ∘ union.pair_to_nat = id

/-
  Now we can prove that `union`s strategy for its transition function `δ` is
  identical to running on both machines simultaneously. The `omit` clause is
  there because the linter complained; try removing it to see what it says. -/
omit [Fintype α] [Nonempty α] in
lemma fold_pairing
  {σ₁ σ₂ : ℕ} {δ₁ δ₂ : ℕ → α → ℕ} {w : List α}
  : let paired := union.nat_to_pair
      (w.foldl
        (fun σ a => union.pair_to_nat
          (δ₁ (union.nat_to_pair σ).1 a,
          δ₂ (union.nat_to_pair σ).2 a))
        (union.pair_to_nat (σ₁, σ₂)))
    paired.1 = w.foldl δ₁ σ₁ ∧ paired.2 = w.foldl δ₂ σ₂
:= by
  induction w using List.reverseRecOn with
  | nil =>
    simp_all
    have h : union.nat_to_pair (union.pair_to_nat (σ₁, σ₂)) =
      (union.nat_to_pair ∘ union.pair_to_nat) (σ₁, σ₂) := by simp
    rw [h, pairing_axiom]
    simp
  | append_singleton as a ih =>
    simp_all
    /-
      The `generalize` tactic replaces an expression with a variable. Here I use
      it just to make things more convenient. Later we'll see examples where
      it's very useful for making a proof even possible. -/
    generalize (List.foldl δ₁ σ₁ as) = σ₃
    generalize (List.foldl δ₂ σ₂ as) = σ₄
    have h : union.nat_to_pair (union.pair_to_nat (δ₁ σ₃ a, δ₂ σ₄ a)) =
      (union.nat_to_pair ∘ union.pair_to_nat) (δ₁ σ₃ a, δ₂ σ₄ a) := by simp
    rw [h, pairing_axiom]
    simp

/-
  We verify that our implementation of union is correct -/
theorem union_is_correct
  {M1 M2 : Dfa α}
  : (M1.union M2).L = M1.L ∪ M2.L
:= by
  ext
  simp [RunsTo.runsto_equiv]
  rw [fold_pairing.1, fold_pairing.2]

/- ----- intersect_is_correct ----- -/

/-
  We verify that our implementation of intersection is correct. Notice that if
  we want to rewrite multiple occurences of something then we need to specify it
  multiple times; also that the rewrites happen in the order they are listed. As
  a more interesting point, notice that I didn't use `simp_all` until after I
  unfolded and rewrote the goal; this is because `simp_all` would simplify _too_
  much, making the theorems used here inapplicable. -/
theorem intersect_is_correct
  {M1 M2 : Dfa α}
  : M1.L ∩ M2.L = (M1.intersect M2).L
:= by
  unfold intersect
  rw [compl_is_correct, union_is_correct, compl_is_correct, compl_is_correct]
  simp_all

/- ----- empty_is_correct ----- -/

/-
  We cannot prove that `empty` is correct because it actually is not: we wrote
  it assuming that the `Dfa` is actually a fixed size bounded by `Dfa.size` but
  nothing prevents the user from creating an infinite-state `Dfa`, or just a
  `Dfa` that ignores `Dfa.size`, either of which breaks `empty`. In order to
  prove it correct we need to use dependent techniques to define `Dfa` so that
  it is guaranteed to be finite. -/

/- ----- equals_is_correct ----- -/

/-
  Since `equals` depends on `empty` we cannot prove it correct either, for the
  same reason. -/

end Dfa
