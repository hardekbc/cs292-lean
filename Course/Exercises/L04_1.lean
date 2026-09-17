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
  MERGE SORT
  -----------------------------------------------------------
-/

theorem split_correct
  (ℓ : List ℕ)
  : let (ℓ₁, ℓ₂) := split ℓ
    (ℓ₁ ++ ℓ₂).Perm ℓ
:= by
  sorry

lemma merge_perm
  (ℓ₁ ℓ₂ : List ℕ)
  : (merge ℓ₁ ℓ₂).Perm (ℓ₁ ++ ℓ₂)
:= by
  sorry

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

lemma merge_sort_perm
  (ℓ : List ℕ)
  : (merge_sort ℓ).Perm ℓ
:= by
  sorry

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
