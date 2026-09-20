/-
  # EXERCISES FOR `L04`

  Mergesort and selection sort.

  ## INSTRUCTIONS

  Fill in the `sorry` for the theorems below, as well as the `decreasing_by`
  clause for `selection_sort`.
-/

import Course.CourseLib
import Course.L03_Sorting
import Course.L04_SortingDeux

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

/-
  Given `n` and `ℓ` returns `n₁` and `ℓ₁` where `n₁` is the smallest element in
  `n :: ℓ` and `ℓ₁` is all of `n :: ℓ` _except_ the smallest element. We can see
  what `List.minimum_of_length_pos` does by hovering over it in VS Code. It
  requires a proof that the list is nonempty, which we provide using `simp`. -/
def select_min (n : ℕ) (ℓ : List ℕ) : ℕ × (List ℕ) :=
  let min := (n :: ℓ).minimum_of_length_pos (by simp)
  (min, (n :: ℓ).erase min)

/-
  HINT: A useful theorem for proving `select_min_size` -/
#check List.minimum_of_length_pos_mem

/-
  A useful lemma for helping to prove termination of `selection_sort` below -/
lemma select_min_size
  (n : ℕ) (ℓ : List ℕ)
  : let (_, ℓ₁) := select_min n ℓ
    ℓ₁.length = ℓ.length
:= by
  sorry

/-
  The selection sort algorithm -/
def selection_sort : List ℕ → List ℕ
  | [] => []
  | x :: xs =>
    let mr := select_min x xs
    mr.1 :: (selection_sort mr.2)
termination_by ℓ => ℓ.length
decreasing_by
  sorry

/-
  HINT: Some useful theorems for the lemmas below (along with the theorems
  already suggested in the `L04_1` exercises) -/
#check List.minimum_of_length_pos_mem
#check List.minimum_of_length_pos_le_of_mem
#check List.perm_cons_erase

/-
  HINT: sometimes `simp` will simplify things _too_ much, applying too many
  rewrites that transform the target into something that our theorems don't
  apply to. Remember that we can use `simp only [...]` to apply only the
  theorems we want, and in particular we can use `simp only` to apply no
  theorems at all, only the built-in `simp` simplications. -/

lemma select_min_perm
  (n : ℕ) (ℓ : List ℕ)
  : let (n₁, ℓ₁) := select_min n ℓ
    (n₁ :: ℓ₁).Perm (n :: ℓ)
:= by
  sorry

lemma select_min_smallest
  (n : ℕ) (ℓ : List ℕ)
  : let (n₁, _) := select_min n ℓ
    (∀ m ∈ (n :: ℓ), n₁ ≤ m)
:= by
  sorry

lemma selection_sort_perm
  (ℓ : List ℕ)
  : (selection_sort ℓ).Perm ℓ
:= by
  sorry

lemma selection_sort_sorted
  (ℓ : List ℕ)
  : sorted (selection_sort ℓ)
:= by
  sorry
