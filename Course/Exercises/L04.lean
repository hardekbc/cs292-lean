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
import AutograderLib

/-
  Make available the `sorted` predicate and various useful lemmas about the
  `sorted` predicate -/
open INSERTION_SORT_P2 (sorted empty_sorted singleton_sorted head_sorted
  tail_sorted cons_sorted cons_sorted')

/-
  -----------------------------------------------------------
  MERGE SORT
  -----------------------------------------------------------
-/

@[autogradedProof 1]
theorem split_correct
  (ℓ : List ℕ)
  : let (ℓ₁, ℓ₂) := split ℓ
    (ℓ₁ ++ ℓ₂).Perm ℓ
:= by
  sorry

@[autogradedProof 1]
lemma merge_perm
  (ℓ₁ ℓ₂ : List ℕ)
  : (merge ℓ₁ ℓ₂).Perm (ℓ₁ ++ ℓ₂)
:= by
  sorry

@[autogradedProof 1]
lemma merge_sorted
  {ℓ₁ ℓ₂ : List ℕ}
  : sorted ℓ₁ → sorted ℓ₂ → sorted (merge ℓ₁ ℓ₂)
:= by
  sorry

theorem merge_correct
  (ℓ₁ ℓ₂ : List ℕ)
  : let ℓ := merge ℓ₁ ℓ₂
    ℓ.Perm (ℓ₁ ++ ℓ₂) ∧ (sorted ℓ₁ → sorted ℓ₂ → sorted ℓ)
:=
  ⟨merge_perm ℓ₁ ℓ₂,
  fun (h₁ : sorted ℓ₁) (h₂ : sorted ℓ₂) => merge_sorted h₁ h₂⟩

@[autogradedProof 1]
lemma merge_sort_perm
  (ℓ : List ℕ)
  : (merge_sort ℓ).Perm ℓ
:= by
  sorry

@[autogradedProof 1]
lemma merge_sort_sorted
  (ℓ : List ℕ)
  : sorted (merge_sort ℓ)
:= by
  sorry

theorem merge_sort_correct
  (ℓ : List ℕ)
  : let ℓ' := merge_sort ℓ
    sorted ℓ' ∧ ℓ'.Perm ℓ
:= ⟨merge_sort_sorted ℓ, merge_sort_perm ℓ⟩

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
  A useful theorem for proving `select_min_size` -/
#check List.minimum_of_length_pos_mem

/-
  A useful lemma for helping to prove termination of `selection_sort` below -/
@[autogradedProof 1]
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
  Some useful theorems for the lemmas below -/
#check List.minimum_of_length_pos_mem
#check List.minimum_of_length_pos_le_of_mem

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

theorem select_min_correct
  (n : ℕ) (ℓ : List ℕ)
  : let (n₁, ℓ₁) := select_min n ℓ
    (∀ m ∈ (n :: ℓ), n₁ ≤ m) ∧ (n₁ :: ℓ₁).Perm (n :: ℓ)
:= ⟨select_min_smallest n ℓ, select_min_perm n ℓ⟩

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

theorem selection_sort_correct
  (ℓ : List ℕ)
  : let ℓ' := selection_sort ℓ
    sorted ℓ' ∧ ℓ'.Perm ℓ
:= ⟨selection_sort_sorted ℓ, selection_sort_perm ℓ⟩
