/-
  # # Example for `L14`: Revisiting Verified Sorting with `grind`
-/

import Course.CourseLib
namespace L14_Sorting

@[grind, simp]
def insertion_sort (ℓ : List ℕ) : List ℕ :=
  match ℓ with
  | [] => []
  | x :: xs => insert x (insertion_sort xs)
where
  @[grind, simp]
  insert (n : ℕ) (ℓ : List ℕ) : List ℕ :=
    match ℓ with
    | [] => [n]
    | x :: xs =>
      if n ≤ x then n :: x :: xs
      else x :: insert n xs

@[grind, simp]
def sorted (ℓ : List ℕ) : Prop :=
  ℓ.Pairwise (· ≤ ·)

@[grind .]
lemma empty_sorted : sorted [] := by grind

@[grind .]
lemma singleton_sorted {n : ℕ} : sorted [n] := by grind

@[grind →]
lemma head_sorted
  {n : ℕ} {ℓ : List ℕ}
  : sorted (n :: ℓ) → ∀ m ∈ ℓ, n ≤ m
:= by grind [List.pairwise_cons]

@[grind →]
lemma tail_sorted
  {n : ℕ} {ℓ : List ℕ}
  : sorted (n :: ℓ) → sorted ℓ
:= by grind

@[grind .]
lemma cons_sorted
  {n : ℕ} {ℓ : List ℕ}
  : sorted ℓ → (∀ m ∈ ℓ, n ≤ m) → sorted (n :: ℓ)
:= by grind [List.Pairwise.cons]

@[grind →]
lemma cons_sorted'
  {n m : ℕ} {ℓ : List ℕ}
  : sorted (m :: ℓ) → n ≤ m → sorted (n :: m :: ℓ)
:= by grind

@[grind! .]
lemma insert_perm
  {n : ℕ} {ℓ : List ℕ}
  : (insertion_sort.insert n ℓ).Perm (n :: ℓ)
:= by induction ℓ with grind

@[grind! .]
lemma insert_sorted
  {n : ℕ} {ℓ : List ℕ}
  : sorted ℓ → sorted (insertion_sort.insert n ℓ)
:= by fun_induction insertion_sort.insert with grind

theorem insert_correct {n : ℕ} {ℓ : List ℕ} :
    let ℓ' := insertion_sort.insert n ℓ
    (sorted ℓ → sorted ℓ') ∧ ℓ'.Perm (n :: ℓ)
:= ⟨insert_sorted, insert_perm⟩

lemma insertion_sort_sorted {ℓ : List ℕ} : sorted (insertion_sort ℓ) := by
  fun_induction insertion_sort with grind

lemma insertion_sort_perm {ℓ : List ℕ} : (insertion_sort ℓ).Perm ℓ := by
  fun_induction insertion_sort with grind

theorem insertion_sort_correct
  (ℓ : List ℕ)
  : let ℓ' := insertion_sort ℓ
    sorted ℓ' ∧ List.Perm ℓ' ℓ
:= ⟨insertion_sort_sorted, insertion_sort_perm⟩
