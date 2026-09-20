/-
  # EXERCISES FOR `L02`

  Some of the exercises are adapted from "Theorem Proving in Lean" and Velleman's "How to Prove It"

  ## INSTRUCTIONS

  Replace the `sorry` in each exercise with a proof of the given proposition.
-/

import Course.CourseLib

variable {α : Type} (P Q : α → Prop) (A B C : Set α)

theorem ex3_1 : (∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x) := by
  sorry

theorem ex3_2 : (∀ x, P x) ∨ (∀ x, Q x) → ∀ x, P x ∨ Q x := by
  sorry

theorem ex3_3 : (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by
  sorry

theorem ex3_4 : A ⊆ B ↔ A \ B = ∅ := by
  sorry

theorem ex3_5 : C ⊆ A ∪ B ↔ C \ A ⊆ B := by
  sorry
