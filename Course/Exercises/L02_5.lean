/-
  # EXERCISES FOR `L02`

  Some of the exercises are adapted from "Theorem Proving in Lean" and Velleman's "How to Prove It"

  ## INSTRUCTIONS

  Replace the `sorry` in each exercise with a proof of the given proposition.
-/

import Course.CourseLib

variable {α β γ : Type} (f : α → β)

def inj       (f : α → β) := ∀ (x y : α), f x = f y → x = y
def surj      (f : α → β) := ∀ (y : β), ∃ (x : α), f x = y
def bijection (f : α → β) := inj f ∧ surj f

theorem ex5_1
  (f : α → β) (g : β → γ)
  : surj f → surj g → surj (g ∘ f)
:= by
  sorry

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

theorem ex5_3
  (a b : ℝ) (f : ℝ → ℝ)
  (h1 : f = fun z => a*z + b) (h2 : a ≠ 0)
  : bijection f
:= by
  sorry
