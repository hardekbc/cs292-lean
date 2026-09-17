/-
  # EXERCISES FOR `L02`

  Some of the exercises are adapted from "Theorem Proving in Lean" and Velleman's "How to Prove It"

  ## INSTRUCTIONS

  Replace the `sorry` in each exercise with a proof of the given proposition.
-/

import Course.CourseLib

variable (P Q R : Prop)

theorem ex1_1 : (P ∧ Q) ∧ R ↔ P ∧ (Q ∧ R) := by
  sorry

theorem ex1_2 : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) := by
  sorry

theorem ex1_3 : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  sorry

theorem ex1_4 : P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := by
  sorry

theorem ex1_5 : (P → (Q → R)) ↔ (P ∧ Q → R) := by
  sorry

theorem ex1_6 : ((P ∨ Q) → R) ↔ (P → R) ∧ (Q → R) := by
  sorry

theorem ex1_7 : ¬P ∨ ¬Q → ¬(P ∧ Q) := by
  sorry

theorem ex1_8 : ¬(P ∧ ¬P) := by
  sorry

theorem ex1_9 : P ∧ ¬Q → ¬(P → Q) := by
  sorry

theorem ex1_10 : ¬P → (P → Q) := by
  sorry
