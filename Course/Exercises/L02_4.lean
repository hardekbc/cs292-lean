/-
  # EXERCISES FOR `L02`

  Some of the exercises are adapted from "Theorem Proving in Lean" and Velleman's "How to Prove It"

  ## INSTRUCTIONS

  Replace the `sorry` in each exercise with a proof of the given proposition.
-/

import Course.CourseLib

/-
  HINT: In both exercises below you can replace `R` with its definition using
  `rw` on the goal and/or other givens; then `whnf` can simplify things -/

/-
  HINT: remember that `rw` can also be used to rewrite things based on givens in
  the current proof state, e.g., `rw [h1]` would rewrite the goal based on some
  given named `h1` that is an equality or biimplication -/

variable {α β : Type}

def is_refl  (R : SetRel α α) := ∀ (a : α), (a, a) ∈ R
def is_symm  (R : SetRel α α) := ∀ (a b : α), (a, b) ∈ R ↔ (b, a) ∈ R
def is_trans (R : SetRel α α) := ∀ (a b c : α), (a, b) ∈ R → (b, c) ∈ R → (a, c) ∈ R
def eqrel    (R : SetRel α α) := is_refl R ∧ is_symm R ∧ is_trans R

theorem ex4_1
  (m : ℕ) (R : SetRel ℕ ℕ)
  (h1 : 0 < m) (h2 : R = { xy | let (x, y) := xy; x % m = y % m })
  : eqrel R
:= by
  sorry

theorem ex4_2
  (f : α → β) (R : SetRel α α)
  (h1 : R = { xy | let (x, y) := xy; f x = f y })
  : eqrel R
:= by
  sorry
