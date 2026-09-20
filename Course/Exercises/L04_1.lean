/-
  # EXERCISES FOR `L04`

  Mergesort and selection sort.

  ## INSTRUCTIONS

  Fill in the `sorry` for the theorems below.
-/

import Course.CourseLib
import Course.L03_Sorting
import Course.L04_SortingDeux

/-
  HINT: don't forget about the `sorted` lemmas we proved in the lecure notes;
  you will need them in the following exercises -/

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

/-
  HINT: recall the following theorems, used in `L03_Sorting` -/
#check if_pos
#check if_neg
#check List.Perm.nil
#check List.Perm.refl
#check List.Perm.trans
#check List.Perm.cons
#check List.Perm.swap
#check List.Perm.mem_iff
#check List.mem_cons
#check List.pairwise_cons

/-
  HINT: you may also find the following theorems helpful -/
#check List.Perm.append
#check List.perm_comm
#check List.perm_middle

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
