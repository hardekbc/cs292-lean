/-
  # EXERCISES FOR `L05`
-/

import Course.CourseLib

/-
  ## INSTRUCTIONS

  Prove that `qsort` terminates. You may add a `termination_by` clause if you
  think it makes sense to do so.
-/

def qsort : List ℕ → List ℕ
  | [] => []
  | x :: xs =>
    let ℓs := xs.partition (· ≤ x)
    qsort ℓs.1 ++ [x] ++ qsort ℓs.2
decreasing_by
  sorry
  sorry
