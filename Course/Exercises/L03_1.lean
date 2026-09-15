/-
  # EXERCISES FOR `L03`

  Reasoning about lists and sorting.

  ## INSTRUCTIONS

  Replace the `sorry` in each theorem below with a proof of the given
  proposition.
-/

import Course.CourseLib
import AutograderLib

variable {α : Type}

/-
  -----------------------------------------------------------
  REASONING ABOUT LISTS
  -----------------------------------------------------------
-/

/-
  Append an element to the end of a list -/
def snoc : List α → α → List α
  | [], a => [a]
  | x :: xs, a => x :: snoc xs a

/-
  Sum a list of numbers -/
def sum : List ℕ → ℕ
  | [] => 0
  | x :: xs => x + sum xs

@[autogradedProof 1]
theorem ex3_1
  (ℓ : List ℕ) (n : ℕ)
  : sum (snoc ℓ n) = n + sum ℓ
:= by
  sorry

@[autogradedProof 1]
theorem ex3_2
  (ℓ₁ ℓ₂ : List ℕ)
  : sum (ℓ₁ ++ ℓ₂) = sum ℓ₁ + sum ℓ₂
:= by
  sorry

@[autogradedProof 1]
theorem ex3_3
  (ℓ : List ℕ)
  : sum ℓ.reverse = sum ℓ
:= by
  sorry
