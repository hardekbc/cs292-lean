/-
  # EXERCISES FOR `L14`

  We revisit `L04_2` so that we can redo the proofs using `grind` and `aesop`.
  Annotate as you see fit, and see how much of the proofs you can automate.
  Remember that you can annotate things in other files (e.g., `sorted` and the
  various `sorted` lemmas) using `attribute`.
-/

import Course.CourseLib
import Course.L03_Sorting
import Course.L04_SortingDeux
import AutograderLib

/-
  Make available the `sorted` predicate and various useful lemmas about the
  `sorted` predicate -/
open INSERTION_SORT_P2 (sorted empty_sorted singleton_sorted head_sorted
  tail_sorted cons_sorted cons_sorted')

/-
  -----------------------------------------------------------
  SELECTION SORT
  -----------------------------------------------------------
-/

def select_min (n : ℕ) (ℓ : List ℕ) : ℕ × (List ℕ) :=
  let min := (n :: ℓ).minimum_of_length_pos (by simp)
  (min, (n :: ℓ).erase min)

@[autogradedProof 1]
lemma select_min_size
  (n : ℕ) (ℓ : List ℕ)
  : let (_, ℓ₁) := select_min n ℓ
    ℓ₁.length = ℓ.length
:= by
  sorry

def selection_sort : List ℕ → List ℕ
  | [] => []
  | x :: xs =>
    let mr := select_min x xs
    mr.1 :: (selection_sort mr.2)
termination_by ℓ => ℓ.length
decreasing_by
  sorry

@[autogradedProof 1]
lemma select_min_perm
  (n : ℕ) (ℓ : List ℕ)
  : let (n₁, ℓ₁) := select_min n ℓ
    (n₁ :: ℓ₁).Perm (n :: ℓ)
:= by
  sorry

@[autogradedProof 1]
lemma select_min_smallest
  (n : ℕ) (ℓ : List ℕ)
  : let (n₁, _) := select_min n ℓ
    (∀ m ∈ (n :: ℓ), n₁ ≤ m)
:= by
  sorry

@[autogradedProof 1]
lemma selection_sort_perm
  (ℓ : List ℕ)
  : (selection_sort ℓ).Perm ℓ
:= by
  sorry

@[autogradedProof 1]
lemma selection_sort_sorted
  (ℓ : List ℕ)
  : sorted (selection_sort ℓ)
:= by
  sorry
