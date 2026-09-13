/-
  # Term-Style Proofs

  - We said at the beginning of the course that "types are propositions and programs are proofs"; now we will see exactly what that means in Lean:

    + Types of type `Prop` are logical propositions (distinguished from non-`Prop` types for efficiency and computability reasons). To prove something of type `P` where `P : Prop`, we construct a value of type `P`.

    + Values of some type whose type is `Prop` (e.g., values of type `P` if `P : Prop`) are called _proof objects_.

    + We'll give examples for `→`, `∧`, `∨`, `¬`, and `↔`, but leave `∀` and `∃` for later (they will require dependent types, which we haven't really covered yet). Conceptually they are the same though: `∀` is a function type and `∃` is a data structure.

  - Recall that a _term_ is a syntactic construct in the language; a _term-style proof_ means that we directly use Lean terms to construct a proof object
-/

import Course.CourseLib

topic::FUNCTIONS
/-
  The logical connective `→` is just a Lean function on proof objects -/

/- This is a tactic-based proof -/
theorem impl_prop₁ : 1 ≤ 2 → 1 ≤ 3 := by
  intro h
  exact NeZero.one_le

#print impl_prop₁

/-
  This is a term-based proof. Note that `impl_prop` has a normal function type
  where the domain and codomain are both propositions in `Prop`. -/
theorem impl_prop₂ : 1 ≤ 2 → 1 ≤ 3 :=
  fun _h => NeZero.one_le

/-
  - To do a term-based proof of a `→` we create a function whose parameter is the type of the antecedent and whose body is the type of the consequent

  - To use a proof object whose type is `→` we just apply it as a function to an argument whose type matches the function's domain
-/
end_topic FUNCTIONS


topic::DATA_STRUCTURES
/-
  - The logical connectives `∧`, `∨`, `¬`, and `↔` are data structures on proof objects, defined using `inductive` and given special notation

  - We could define our own special notation for data structures that we define ourselves if we wanted to, using Lean's extensible syntax
-/

/- ---- `∧` -----/

/-
  `And` is actually a _structure_, which we haven't covered yet, but structures
  are just syntactic sugar for inductive types -/
#print And

/- Our own version -/
inductive And' (P Q : Prop) : Prop
  | intro (left : P) (right : Q)

/- A tactic-based proof -/
theorem and_prop (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  obtain ⟨hP, hQ⟩ := h
  constructor
  · exact hQ
  · exact hP

/-
  A term-based proof (and now we can see where the name `constructor` comes from
  for the tactic: it is splitting the goal into the separate pieces of the
  inductive type constructor) -/
theorem and_prop₁ (P Q : Prop) (h : P ∧ Q) : Q ∧ P :=
  let ⟨h1, h2⟩ := h
  And.intro h2 h1

/-
  An alternate term-based proof. If there is only a single constructor, Lean
  lets us use `⟨...⟩` to compose the constructor arguments instead of having to
  name the constructor explicitly. -/
theorem and_prop₂ (P Q : Prop) (h : P ∧ Q) : Q ∧ P :=
  let ⟨h1, h2⟩ := h
  ⟨h2, h1⟩


/- ---- `∨` -----/
#print Or

/- Our own version -/
inductive Or' (P Q : Prop) where
  | inl : P → Or' P Q
  | inr : Q → Or' P Q

/- A tactic-based proof -/
theorem or_prop (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hL => right; exact hL
  | inr hR => left; exact hR

/- A term-based proof -/
theorem or_prop₁ (P Q : Prop) (h : P ∨ Q) : Q ∨ P :=
  match h with
  | .inl hL => Or.inr hL
  | .inr hR => Or.inl hR


/- ---- `¬` -----/
#print Not

/- Our own version -/
def Not' := fun (P : Prop) => P → False

/-
  Negation is just an implication to Lean, and is treated the same way (i.e., as
  a function type) -/


/- ---- `↔` -----/
#print Iff

/- Our own version -/
inductive Iff' (P Q : Prop)
  | intro (mp : P → Q) (mpr : Q → P)

/- A tactic-based proof -/
theorem iff_prop (P Q : Prop) (h : P ↔ Q) : Q ↔ P := by
  obtain ⟨mp, mpr⟩ := h
  constructor
  · exact mpr
  · exact mp

/- A term-based proof -/
theorem iff_prop₁ (P Q : Prop) (h : P ↔ Q) : Q ↔ P :=
  let ⟨mp, mpr⟩ := h
  Iff.intro mpr mp

/- An alternate term-based proof -/
theorem iff_prop₂ (P Q : Prop) (h : P ↔ Q) : Q ↔ P :=
  let ⟨mp, mpr⟩ := h
  ⟨mpr, mp⟩

end_topic DATA_STRUCTURES


topic::INDUCTION
/-
  - A theorem is a function, so conceptually induction is just a recursive call to the theorem being proved (using "smaller" arguments to guarantee termination)

    + This approach works fine for some proofs, but can get complicated when dealing with more complicated structures and definitions

    + Lean has machinery under the hood to implement induction and recursion, but we will only introduce it briefly here and save a more in-depth discussion for later
-/

/- Here is the tactic-based inductive proof we saw before -/
theorem tactic_example : ∀ (n : ℕ), 2 ∣ n^2 + n := by
  intro n
  induction n with
  | zero => lia
  | succ m ih =>
    have ⟨k, hk⟩ := ih
    exists (k + m + 1)
    nlinarith

/-
  Notice that (1) the proof doesn't use recursion directly, and (2) the tactics
  inflate the size of the proof dramatically -/
#print tactic_example

/-
  Here is a term-based version (mostly, except for the arithmetic parts) using
  recursion -/
theorem term_example : ∀ (n : ℕ), 2 ∣ n^2 + n :=
  fun n => match n with
    | 0 => by lia
    | m + 1 =>
      let ⟨k, hk⟩ := term_example m -- recursive call for induction
      Exists.intro (k + m + 1) (by nlinarith)

/-
  Notice that even though we defined the proof using recursion directly, the
  actual proof doesn't reflect that because of Lean's behind-the-scenes
  manipulations -/
#print term_example
#print term_example._f

/-
  Induction and recursion are actually implemented using a _recursor_ that was
  automatically generated when the inductive type being inducted/recursed on was
  defined. Here is an example of the recursor for natural numbers (note that the
  details of the type will be different depending on the inductive type being
  defined) -/
#check Nat.recOn

/-
  - Here is a more readable version of the recursor's type:

  Nat.recOn.{u}
    {motive : ℕ → Sort u}
    (t : ℕ)
    (zero : motive Nat.zero)
    (succ : (n : ℕ) → motive n → motive n.succ) : motive t

  - The `motive` is what we're trying to accomplish, the thing we're using the recursor to get; it is parameterized over possible type universes (read `Sort u` as "any of `Prop` or `Type n` for any value of `n`")

    + If we're doing an inductive proof then `Sort u` will be `Prop` and so `motive : ℕ → Prop`, i.e., the motive is the predicate over natural numbers that we're trying to proven

  - `t` is a member of the type being recursed/inducted over; think of `Nat.recOn` as saying `∀t, motive t`

  - `zero` is a proof of the motive specialized to 0

  - `succ` is a proof that, given an arbitrary `n` and a proof that the motive is true for `n`, the motive is true for `n + 1`

  - The return value is of type `motive t`, i.e., that the motive is true for `t`

  - Put it all together and we get the standard principle of induction for natural numbers: to prove that a predicate `P` is true for all natural numbers: (1) prove `P 0` and (2) prove that for arbitrary `n`, `P n → P (n+1)`
 -/

/-
  Here is the "real" way to write a term-based inductive proof. I have used
  named arguments to make it more clear. -/
theorem term_example_recursor : ∀ (n : ℕ), 2 ∣ n^2 + n :=
  fun n => @Nat.recOn
    (motive := fun n => 2 ∣ n^2 + n)
    (t := n)
    (zero := by grind)
    (succ := fun m (h : 2 ∣ m^2 + m) =>
      let ⟨k, hk⟩ := h
      Exists.intro (k + m + 1) (by nlinarith))

/-
  Tactics create terms, so all proofs under the hood are "term-mode" proofs.
  When we use `intro h`, for example, that means to create an anonymous function
  with parameter `h` whose type is the thing we're assuming as a given; all
  parts of the proof after the `intro` make up the function's body. -/

end_topic INDUCTION


topic::TERM_VS_TACTIC
/-
  - Using term-based vs tactic-based proof isn't a binary choice, we can mix them together in the same proof (and in fact, we already have)

  - In a tactic-based proof:

    + When using `have` we can do the subproof using terms or tactics depending on whether we use `:=` or `:= by`

    + `apply` and `exact` switch into term mode

  - In a term-based proof:

    + Whenever we need to supply a proof (e.g., as an argument to a function), we can switch into tactic-mode using `by`

  - We used both of these strategies back in `02_BasicProofs.lean`
-/
end_topic TERM_VS_TACTIC


topic::TERM_BASED_EXAMPLES
open Classical

/-
  Here are some of the examples from `L02_BasicProofs` redone using term-mode
  (except for the arithmetic tactic like `lia`). You might want to go back to
  those examples to compare the tactic-mode proofs with the term-mode proofs. -/

/- ---- SETS AND LOGIC -----/

example
    (P Q R : Prop)
    (h : P → (Q → R))
    : ¬R → (P → ¬Q)
:=
  fun h1 h2 h3 =>
    have h4 := h h2 h3 -- `have` is a term as well as a tactic
    False.elim (h1 h4)

example
    (U : Type) (A B C : Set U) (a : U)
    (h1 : a ∈ A)
    (h2 : a ∉ A \ B)
    (h3 : a ∈ B → a ∈ C)
    : a ∈ C
:=
  have h4 : a ∈ B :=
    byContradiction fun h4 : a ∉ B =>
      have h5 : a ∈ A \ B := ⟨h1, h4⟩
      False.elim (h2 h5)
  h3 h4

example
    (U : Type) (A B C : Set U)
    (h1 : A ⊆ B ∪ C)
    (h2 : ∀ (x : U), x ∈ A → x ∉ B)
    : A ⊆ C
:=
  fun a hA =>
    have h3 := h1 hA
    Or.casesOn h3
      (fun h =>
        have h4 := h2 a hA
        False.elim (h4 h))
      (fun h => h)

example
    (U : Type) (A B C D : Set U)
    (h1 : A ⊆ B)
    (h2 : ¬∃ (c : U), c ∈ C ∩ D)
    : A ∩ C ⊆ B \ D
:=
  have h2 := not_exists.mp h2
  fun a hA =>
    And.intro
      (h1 hA.left)
      (fun h3 =>
        have h4 := h2 a
        have h5 : a ∈ C ∩ D := ⟨hA.right, h3⟩
        False.elim (h4 h5))

example
    (U : Type) (A B C : Set U)
    : A \ (B \ C) ⊆ (A \ B) ∪ C
:=
  fun a hA =>
    And.casesOn hA fun h1 h2 =>
      if h3 : a ∈ C then Or.inr h3
      else
        Or.inl (
          have h4 := fun h4 =>
            have h5 := ⟨h4, h3⟩
            False.elim (h2 h5)
          ⟨h1, h4⟩)

example
    (U : Type) (A B C : Set U)
    (h1 : A ⊆ B ∪ C)
    (h2 : ¬∃ (x : U), x ∈ A ∩ B)
    : A ⊆ C
:=
  have h2 := not_exists.mp h2
  fun a hA =>
    have h3 := h1 hA
    have h4 := h2 a
    Or.casesOn h3
      (fun h =>
        have h5 : a ∈ A ∩ B := ⟨hA, h⟩
        False.elim (h4 h5))
      (fun h => h)

/- ---- FUNCTIONS -----/

variable {α β : Type}

def inj (f : α → β) :=
  ∀ (x y : α), f x = f y → x = y

def surj (f : α → β) :=
  ∀ (y : β), ∃ (x : α), f x = y

def bijection (f : α → β) :=
  inj f ∧ surj f

example
    {A B C : Type}
    (f : A → B) (g : B → C)
    : inj f → inj g → inj (g ∘ f)
:=
  fun h1 h2 x y h3 =>
    have h4 := h1 x y
    have h5 := h2 (f x) (f y)
    have h6 := h5 h3
    h4 h6

/- ---- INDUCTION -----/

def even (n : ℕ) :=
  ∃ (k : ℕ), n = 2 * k

def odd (n : ℕ) :=
  ∃ (k : ℕ), n = 2 * k + 1

theorem ind3 : ∀ n, ¬(even n ∧ odd n)
:=
  let rec ind3' (n : ℕ) : ¬ even n ∨ ¬ odd n :=
    match n with
      | 0 => Or.inr (
          have h1 : odd 0 = ∃ k, 0 = 2*k + 1 := rfl
          Eq.subst h1.symm (not_exists.mpr (fun k => by lia)))
      | m + 1 => match (ind3' m) with
        | .inl h => Or.inr (
          have h1 : even m = ∃ k, m = 2*k := rfl
          have h2 : odd (m + 1) = ∃ k, (m + 1) = 2*k + 1 := rfl
          have h := not_exists.mp (Eq.subst h1 h)
          Eq.subst h2.symm (not_exists.mpr (fun k =>
            have h3 := h k
            by lia)))
        | .inr h => Or.inl (
          have h1 : odd m = ∃ k, m = 2*k + 1 := rfl
          have h2 : even (m + 1) = ∃ k, (m + 1) = 2*k := rfl
          have h := not_exists.mp (Eq.subst h1 h)
          Eq.subst h2.symm (not_exists.mpr (fun k =>
            have h3 := h (k - 1)
            by lia)))
  fun n => not_and.mpr (imp_iff_not_or.mpr (ind3' n))

end_topic TERM_BASED_EXAMPLES


topic::EQUALITY
/-
  - An important question Lean needs to answer when proving things is: When are two terms equal? I.e., if we are trying to prove `<exp₁>` is "the same as" `<exp₂>`, what does "same as" mean exactly?

  - Normally we think fairly loosely about what equality means, but in Lean we need to draw a distinction between three different kinds of equality: _syntactic_, _definitional_, and _propositional_
-/

variable (n a b c : ℕ)

/-
  _Syntactic equality_ (almost) means that two terms are textually the same
  string. The following are examples of syntactic equality.  -/
example : n = n := rfl
example : n + 0 = n + 0 := rfl

/-
  - We say "almost" because there are a couple of exceptions

  - First, the names of bound variables can be different (this is because Lean uses de Bruijn indices under the hood which replaces bound names with numeric indices):

    + `fun (x : ℕ) => x` is syntactically equal to `fun (y : ℕ) => y`
    + `∀x, ∃y, x + y = 0` is syntactically equal to `∀y, ∃x, y + x = 0`

  - Second, notation (i.e., extended syntax) can be unfolded without breaking syntactic equality. For example, `=` is notation for the `Eq` function, so `x = y` is syntactically equal to `Eq x y`.
-/

example : (fun (x : ℕ) => x) = (fun (y : ℕ) => y) := rfl
example : (∀x, ∃y, x + y = 0) = (∀y, ∃x, y + x = 0) := rfl
example (x y : ℕ) : (x = y) = (Eq x y) := rfl

/-
  Syntactic equality is relevant to tactics like `rw` and some others. In the
  following example we can use `rw` to replace the `a` in the goal because `rw`
  sees that the `a` in `h1` and the `a` in the goal are syntactically identical.
-/
example (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1]
  exact h2

/-
  However, in the following example `rw` fails because `n + 0` and `n` are _not_
  syntactically equal -/
/--
  error: Tactic `rewrite` failed: Did not find an occurrence of the pattern n +
  0 in the target expression n = a -/
#guard_error
example (h : n + 0 = a) : n = a := by
  rw [h]

/-
  _Definitional equality_ means that two (possibly syntactically different)
  terms _reduce_ to the same normal form. Think of "reduce" as meaning "evaluate
  by instantiating the definition". The following are examples of definitional
  equality.
-/
example : 2 + 2 = 4 := rfl
example : n = n + 0 := rfl

#reduce 2 + 2
#reduce n + 0

/-
  `rfl`, `exact`, `intro` and some other tactics care about definitional
  equality. `rfl` says that two terms are equal if they are definitionally
  equal; `exact` allows a proof that is definitionally equal to the current
  goal; `intro` introduces a given for any goal that is definitionally equal to
  a function; etc. We have seen the use of `rfl` above, here are examples for
  `exact` and `intro`. -/

example (h : n = 42) : n + 0 = 42 := by
  exact h

example (P : Prop) (h : P → False) : ¬P := by
  intro hP
  contradiction

/-
  An important note: for Lean to determine definitional equality it needs to be
  able to "see" inside the definitions, i.e., unfold the name into its content.
  However, if we allowed Lean to _always_ unfold definitions then we would have
  horrible performance and, in some cases, nontermination of Lean itself.
  Therefore Lean supports different levels of "transparency" that dictate when
  and where it is allowed to unfold definitions. The default level, when we use
  `def`, is "semi-reducible": Lean will sometimes unfold the definition
  automatically but sometimes you need to tell it to explicitly. Using `abbrev`
  instead of `def` makes the definition "reducible", i.e., Lean will _always_
  unfold it. There is also an "irreducible" level that Lean will _never_ unfold. See
  the Lean Reference Manual for more details. -/

/-
  Perhaps surprisingly, the following is _not_ a definitional
  equality -/
/--
  error: Type mismatch rfl has type ?m.9 = ?m.9 but is expected to have type n =
  0 + n -/
#guard_error
example : n = 0 + n := rfl

/-
  We can see that `n` and `0 + n` do not reduce to the same term -/
#reduce n
#reduce 0 + n

/-
  The definition of `+` on natural numbers is defined using recursion (we show a
  simplified version here for readability). Notice that we are recursing on the
  second argument, and by definition `a + 0` = `a` for any value `a`. However,
  if the second argument is a variable then we don't know how to evaluate any
  further and have to stop. The value of the first argument is irrelevant
  according to the definition. -/
def nat_plus : ℕ → ℕ → ℕ
  | a, 0 => a
  | a, m + 1 => .succ (nat_plus a m)

/-
  This example shows that definitional equality is in some sense just an
  implementation artifact: if we define the same concepts in different ways then
  different things will be definitionally equal. We could easily define addition
  to recurse on the first parameter instead of the second, in which case the
  equality `n = 0 + n` would be definitionally equal and `n = n + 0` would not.
-/

/-
  Of course, it is true that `n = 0 + n` and fortunately we can prove it. We
  prove it here for our simplified definition `nat_plus`, but the idea is the
  same for the normal `+`. -/
example : n = nat_plus 0 n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    unfold nat_plus
    rw [← ih]

/-
  _Propositional equality_ is provable equality, and it is what we normally
  think of as "mathematical equality". `simp`, for example, applies
  propositional equalities. -/

end_topic EQUALITY
