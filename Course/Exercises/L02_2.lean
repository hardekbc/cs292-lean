/-
  # EXERCISES FOR `L02`

  Some of the exercises are adapted from "Theorem Proving in Lean" and Velleman's "How to Prove It"

  ## INSTRUCTIONS

  Replace the `sorry` in each exercise with a proof of the given proposition.
-/

import Course.CourseLib

variable {α : Type} (A B C : Set α) (x : α)

theorem ex2_1 : x ∈ A \ (A ∩ B) ↔ x ∈ A \ B := by
  sorry

theorem ex2_2 : x ∈ A ∪ (B ∩ C) ↔ x ∈ (A ∪ B) ∩ (A ∪ C) := by
  sorry

theorem ex2_3 : x ∈ (A ∪ B) \ C ↔ x ∈ (A \ C) ∪ (B \ C) := by
  sorry

theorem ex2_4 : x ∈ A ∪ (B \ C) ↔ x ∈ (A ∪ B) \ (C \ A) := by
  sorry
