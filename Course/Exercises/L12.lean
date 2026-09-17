/-
  # EXERCISES FOR `L12`

  In `L08` we extended our expression language to include statements; here we
  modify that extension to use dependent types.
-/

import Course.CourseLib
import Course.L12_DExpLang

inductive DStmt where
/-
  ## INSTRUCTIONS
  Define the constructors of `DStmt` so that it uses `DExp` instead of `Exp` and
  guarantees that (1) for assignments, the type of the variable is the same as
  the type of the right-hand side; and (2) the types of the guards for
  conditionals and loops is guaranteed to be `Bool`.
-/

inductive BigstepS : DState → DStmt → DState → Prop
/-
  ## INSTRUCTIONS
  Define the constructors of `BigstepS` on `DStmt` (it will be very much like
  the original given in `L08`, except that `DExp` cannot evaluate to `error`)
-/

/-
  ## INSTRUCTIONS
  Fill in the `sorry` for the definition of `clocked_eval` and the theorems
  below. Feel free to add lemmas if you find them helpful.
-/

/-
  We can no longer get errors during execution, so we use an `Option` to
  indicate whether we ran out of fuel or not -/
def clocked_eval (σ : DState) (fuel : ℕ) (s : DStmt) : Option DState :=
  sorry

lemma clocked_eval.monotone
  {σ₁ σ₂ : DState} {s : DStmt} {n₁ : ℕ} (n₂ : ℕ)
  : clocked_eval σ₁ n₁ s = .some σ₂ → n₁ ≤ n₂ → clocked_eval σ₁ n₂ s = .some σ₂
:= by
  sorry

theorem stmt_eval_matches_semantics
  {σ₁ σ₂ : DState} {s : DStmt}
  : BigstepS σ₁ s σ₂ → ∃ n, clocked_eval σ₁ n s = (.some σ₂)
:= by
  sorry

theorem stmt_semantics_matches_eval
  {σ₁ σ₂ : DState} {s : DStmt}
  : (∃ n, clocked_eval σ₁ n s = (.some σ₂)) → BigstepS σ₁ s σ₂
:= by
  sorry
