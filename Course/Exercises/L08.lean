/-
  # EXERCISES FOR `L08`

  Fill in the `sorry` in the theorems and definitions below. Feel free to create
  additional lemmas as you find them helpful.
-/

import Course.CourseLib
import Course.L08_ExpLang
import AutograderLib

/-
  Determinism is a generally useful property to have; we can prove that both
  `HasType` and `BigstepE` are deterministic -/

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

/-
  We extend `ExpLang` to include statements, turning it into a simple imperative
  programming language. `skip` does nothing; `assign` update a variable's value;
  `seq` sequences two statements; `ifelse` is a conditional branch; `whiledo` is
  a while loop. -/
inductive Stmt
  | skip    : Stmt
  | assign  : Var → Exp → Stmt
  | seq     : Stmt → Stmt → Stmt
  | ifelse  : Exp → Stmt → Stmt → Stmt
  | whiledo : Exp → Stmt → Stmt

/-
  The semantics of evaluating statements. `BigstepS σ₁ s σ₂` means that under
  state `σ₁` evaluating statement `s` results in state `σ₂`. Notice that because
  we're defining an inductive predicate there is no issue with the fact that a
  while loop may never terminate: if `s` is nonterminating when starting from
  `σ₁`, then there just doesn't exist any `σ₂` s.t. `BigstepS σ₁ s σ₂`. Again
  importantly, note that type-incorrect statements (e.g., when the conditional
  guard doesn't evaluate to a boolean) do not have any defined transitions. -/
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

/-
  We will write an interpreter for statements. Because while loops may not
  terminate we will have to use clocked recursion. We'll want to distinguish
  between executions that fail due to running out the clock vs those that fail
  due to actual errors. -/
inductive Result
  | normal (σ : State)
  | error
  | timeout

/-
  Fill in the implementation to match the semantics described above. If the fuel
  runs out return `Result.timeout`; if there is no valid result according to the
  semantics then return `Result.error`. -/
def clocked_eval (σ : State) (fuel : ℕ) (s : Stmt) : Result :=
  sorry

/-
  This lemma will be useful for proving the interpreter is correct -/
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
