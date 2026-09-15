/-
  # EXERCISES FOR `L14`

  We revisit `L08` so that we can redo the proofs using `grind` and `aesop`.
  Annotate as you see fit, and see how much of the proofs you can automate.
  Remember that you can annotate things in other files using `attribute`.
-/

import Course.CourseLib
import Course.L08_ExpLang
import AutograderLib

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
