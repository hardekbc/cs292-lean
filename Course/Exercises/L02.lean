/-
  # EXERCISES FOR `L02`

  - Propositional and predicate logic
  - Sets, relations, and functions
  - Induction

  Some exercises adapted from "Theorem Proving in Lean" and Velleman's "How to Prove It"

  ## INSTRUCTIONS

  Replace the `sorry` in each exercise with a proof of the given proposition.
-/

import Course.CourseLib
import AutograderLib

topic::PROBLEM_SET_1

variable (P Q R : Prop)

@[autogradedProof 1]
theorem ex1_1 : (P ∧ Q) ∧ R ↔ P ∧ (Q ∧ R) := by
  sorry

@[autogradedProof 1]
theorem ex1_2 : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) := by
  sorry

@[autogradedProof 1]
theorem ex1_3 : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  sorry

@[autogradedProof 1]
theorem ex1_4 : P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := by
  sorry

@[autogradedProof 1]
theorem ex1_5 : (P → (Q → R)) ↔ (P ∧ Q → R) := by
  sorry

@[autogradedProof 1]
theorem ex1_6 : ((P ∨ Q) → R) ↔ (P → R) ∧ (Q → R) := by
  sorry

@[autogradedProof 1]
theorem ex1_7 : ¬P ∨ ¬Q → ¬(P ∧ Q) := by
  sorry

@[autogradedProof 1]
theorem ex1_8 : ¬(P ∧ ¬P) := by
  sorry

@[autogradedProof 1]
theorem ex1_9 : P ∧ ¬Q → ¬(P → Q) := by
  sorry

@[autogradedProof 1]
theorem ex1_10 : ¬P → (P → Q) := by
  sorry

end_topic PROBLEM_SET_1


topic::PROBLEM_SET_2

variable {α : Type} (A B C : Set α) (x : α)

@[autogradedProof 1]
theorem ex2_1 : x ∈ A \ (A ∩ B) ↔ x ∈ A \ B := by
  sorry

@[autogradedProof 1]
theorem ex2_2 : x ∈ A ∪ (B ∩ C) ↔ x ∈ (A ∪ B) ∩ (A ∪ C) := by
  sorry

@[autogradedProof 1]
theorem ex2_3 : x ∈ (A ∪ B) \ C ↔ x ∈ (A \ C) ∪ (B \ C) := by
  sorry

@[autogradedProof 1]
theorem ex2_4 : x ∈ A ∪ (B \ C) ↔ x ∈ (A ∪ B) \ (C \ A) := by
  sorry

end_topic PROBLEM_SET_2


topic::PROBLEM_SET_3

variable {α : Type} (P Q : α → Prop) (A B C : Set α)

@[autogradedProof 1]
theorem ex3_1 : (∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x) := by
  sorry

@[autogradedProof 1]
theorem ex3_2 : (∀ x, P x → Q x) → (∀ x, P x) → (∀ x, Q x) := by
  sorry

@[autogradedProof 1]
theorem ex3_3 : (∀ x, P x) ∨ (∀ x, Q x) → ∀ x, P x ∨ Q x := by
  sorry

@[autogradedProof 1]
theorem ex3_4 : (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by
  sorry

@[autogradedProof 1]
theorem ex3_5 : (∀ x, P x) ↔ ¬ (∃ x, ¬ P x) := by
  sorry

@[autogradedProof 1]
theorem ex3_6 : (∃ x, P x) ↔ ¬ (∀ x, ¬ P x) := by
  sorry

@[autogradedProof 1]
theorem ex3_7 : (¬ ∃ x, P x) ↔ (∀ x, ¬ P x) := by
  sorry

@[autogradedProof 1]
theorem ex3_8 : (¬ ∀ x, P x) ↔ (∃ x, ¬ P x) := by
  sorry

@[autogradedProof 1]
theorem ex3_9 : A ⊆ B ↔ A \ B = ∅ := by
  sorry

@[autogradedProof 1]
theorem ex3_10 : C ⊆ A ∪ B ↔ C \ A ⊆ B := by
  sorry

end_topic PROBLEM_SET_3


topic::PROBLEM_SET_4
/-
  HINT: In both exercises below you can replace `R` with its definition using
  `rw` on the goal and/or other givens; then `whnf` can simplify things -/

variable {α β : Type}

def is_refl  (R : SetRel α α) := ∀ (a : α), (a, a) ∈ R
def is_symm  (R : SetRel α α) := ∀ (a b : α), (a, b) ∈ R ↔ (b, a) ∈ R
def is_trans (R : SetRel α α) := ∀ (a b c : α), (a, b) ∈ R → (b, c) ∈ R → (a, c) ∈ R
def eqrel    (R : SetRel α α) := is_refl R ∧ is_symm R ∧ is_trans R

@[autogradedProof 1]
theorem ex4_1
  (m : ℕ) (R : SetRel ℕ ℕ)
  (h1 : 0 < m) (h2 : R = { xy | let (x, y) := xy; x % m = y % m })
  : eqrel R
:= by
  sorry

@[autogradedProof 1]
theorem ex4_2
  (f : α → β) (R : SetRel α α)
  (h1 : R = { xy | let (x, y) := xy; f x = f y })
  : eqrel R
:= by
  sorry

end_topic PROBLEM_SET_4


topic::PROBLEM_SET_5

variable {α β γ : Type} (f : α → β)

def inj       (f : α → β) := ∀ (x y : α), f x = f y → x = y
def surj      (f : α → β) := ∀ (y : β), ∃ (x : α), f x = y
def bijection (f : α → β) := inj f ∧ surj f

@[autogradedProof 1]
theorem ex5_1
  (f : α → β) (g : β → γ)
  : surj f → surj g → surj (g ∘ f)
:= by
  sorry

@[autogradedProof 1]
theorem ex5_2
  (f : α → β) (g : β → α)
  (h : g ∘ f = id)
  : inj f
:= by
  sorry

/-
  HINT: the following theorems may be useful for `ex5_3`. Don't forget that
  `nlinarith` can solve some (not all) non-linear arithmetic goals. Ignore the
  `@` when using the theorem, it's only there to make the `#check` output look
  nicer. -/
#check @mul_eq_mul_left_iff
#check @mul_div_cancel₀

@[autogradedProof 1]
theorem ex5_3
  (a b : ℝ) (f : ℝ → ℝ)
  (h1 : f = fun z => a*z + b) (h2 : a ≠ 0)
  : bijection f
:= by
  sorry

end_topic PROBLEM_SET_5


topic::PROBLEM_SET_6

abbrev even (n : ℕ) :=
  ∃ (k : ℕ), n = 2 * k

abbrev odd (n : ℕ) :=
  ∃ (k : ℕ), n = 2 * k + 1

@[autogradedProof 1]
theorem ex6_1 : ∀ n, even n ∨ odd n := by
  sorry

/-
  HINT: you may find the following two theorems useful for `ex6_2`. Given a
  proof that a proposition is true or false, they can be used to reduce an `if`
  expression into the true or false branches. Ignore the `@` when using the
  theorem, it's only there to make the `#check` output look nicer. -/
#check @if_pos
#check @if_neg

/- Factorial function -/
def fact (n : ℕ) :=
  if n = 0 then 1
  else n * fact (n-1)

@[autogradedProof 1]
theorem ex6_2 : ∀ (n : Nat), fact n ≥ 1 := by
  sorry

end_topic PROBLEM_SET_6
