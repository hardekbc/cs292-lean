/-
  # EXERCISES FOR `L14`

  We revisit `L04` and `L08` so that we can redo the proofs using `grind` and
  `aesop`. Annotate as you see fit, and see how much of the proofs you can
  automate. Remember that you can annotate things in other files (e.g., `sorted`
  and the various `sorted` lemmas) using `attribute`.
-/

import Course.CourseLib
import Course.L03_Sorting
import Course.L04_SortingDeux
import Course.L08_ExpLang
import AutograderLib

topic::L04

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

end_topic L04


topic::L08

@[autogradedProof 1]
theorem HasType.deterministic
  {Γ : Env} {e : Exp} {τ₁ τ₂ : Ty}
  : HasType Γ e τ₁ → HasType Γ e τ₂ → τ₁ = τ₂
:= by
  sorry

@[autogradedProof 1]
theorem BigstepE.deterministic
  {σ : State} {e : Exp} {v₁ v₂ : Value}
  : BigstepE σ e v₁ → BigstepE σ e v₂ → v₁ = v₂
:= by
  sorry

inductive Stmt
  | skip    : Stmt
  | assign  : Var → Exp → Stmt
  | seq     : Stmt → Stmt → Stmt
  | ifelse  : Exp → Stmt → Stmt → Stmt
  | whiledo : Exp → Stmt → Stmt

inductive BigstepS : State → Stmt → State → Prop
  | skip σ : BigstepS σ .skip σ
  | assign {σ₁ σ₂ x rhs v}:
      BigstepE σ₁ rhs v → v ≠ .error → σ₂ = σ₁.insert x v →
      BigstepS σ₁ (.assign x rhs) σ₂
  | seq {σ₁ σ₂ σ₃ s₁ s₂}:
      BigstepS σ₁ s₁ σ₂ → BigstepS σ₂ s₂ σ₃ →
      BigstepS σ₁ (.seq s₁ s₂) σ₃
  | ifelse_tt {σ₁ σ₂ g tt ff} :
      BigstepE σ₁ g (.bool true) → BigstepS σ₁ tt σ₂ →
      BigstepS σ₁ (.ifelse g tt ff) σ₂
  | ifelse_ff {σ₁ σ₂ g tt ff} :
      BigstepE σ₁ g (.bool false) → BigstepS σ₁ ff σ₂ →
      BigstepS σ₁ (.ifelse g tt ff) σ₂
  | whiledo_tt {σ₁ σ₂ σ₃ g body} :
      BigstepE σ₁ g (.bool true) → BigstepS σ₁ body σ₂ →
      BigstepS σ₂ (.whiledo g body) σ₃ → BigstepS σ₁ (.whiledo g body) σ₃
  | whiledo_ff {σ g body} :
      BigstepE σ g (.bool false) → BigstepS σ (.whiledo g body) σ

@[autogradedProof 1]
theorem BigstepS.deterministic
  {σ₁ σ₂ σ₃ : State} {s : Stmt}
  : BigstepS σ₁ s σ₂ → BigstepS σ₁ s σ₃ → σ₂ = σ₃
:= by
  sorry

inductive Result
  | normal (σ : State)
  | error
  | timeout

def clocked_eval (σ : State) (fuel : ℕ) (s : Stmt) : Result :=
  sorry -- FILL IN FROM `L08`

@[autogradedProof 1]
lemma clocked_eval.monotone
  {σ₁ σ₂ : State} {s : Stmt} {n₁ : ℕ} (n₂ : ℕ)
  : clocked_eval σ₁ n₁ s = .normal σ₂ → n₁ ≤ n₂ → clocked_eval σ₁ n₂ s = .normal σ₂
:= by
  sorry

@[autogradedProof 1]
theorem stmt_eval_matches_semantics
  {σ₁ σ₂ : State} {s : Stmt}
  : BigstepS σ₁ s σ₂ → ∃ n, clocked_eval σ₁ n s = (.normal σ₂)
:= by
  sorry

@[autogradedProof 1]
theorem stmt_semantics_matches_eval
  {σ₁ σ₂ : State} {s : Stmt}
  : (∃ n, clocked_eval σ₁ n s = (.normal σ₂)) → BigstepS σ₁ s σ₂
:= by
  sorry

end_topic L08
