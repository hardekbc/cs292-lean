/-
  # # Example for `L14`: Revisiting the Expression Language with `grind` and `aesop`
-/

import Course.CourseLib

@[grind cases, aesop safe cases]
inductive Ty
  | int
  | bool
deriving DecidableEq

abbrev Var := String

@[grind cases, aesop safe cases]
inductive BinOp
  | add
  | mul
  | le
  | and
  | or

@[grind cases, aesop safe cases]
inductive UnOp
  | neg
  | not

@[grind cases, aesop unsafe 10% cases]
inductive Exp
  | int   : ℤ → Exp
  | bool  : Bool → Exp
  | var   : Var → Exp
  | binop : BinOp → Exp → Exp → Exp
  | unop  : UnOp → Exp → Exp

abbrev Env := AList (fun (_ : Var) => Ty)

@[grind, simp]
def Exp.check (Γ : Env) : Exp → Option Ty
  | .int _ => .some .int
  | .bool _ => .some .bool
  | .var x => Γ.lookup x
  | .binop op left right =>
    match op with
    | .add | .mul => match left.check Γ, right.check Γ with
      | .some .int, .some .int => .some .int
      | _, _ => .none
    | .le =>  match left.check Γ, right.check Γ with
      | .some .int, .some .int => .some .bool
      | _, _ => .none
    | .and | .or => match left.check Γ, right.check Γ with
      | .some .bool, .some .bool => .some .bool
      | _, _ => .none
  | .unop op e => match op with
    | .neg => match e.check Γ with
      | .some .int => .some .int
      | _ => .none
    | .not => match e.check Γ with
      | .some .bool => .some .bool
      | _ => .none

@[grind cases, aesop safe cases]
inductive Value
  | int  : ℤ → Value
  | bool : Bool → Value
  | error

namespace Value

@[grind, simp]
def add : Value → Value → Value
  | .int z₁, .int z₂ => .int (z₁ + z₂)
  | _, _ => .error

@[grind, simp]
def mul : Value → Value → Value
  | .int z₁, .int z₂ => .int (z₁ * z₂)
  | _, _ => .error

@[grind, simp]
def le : Value → Value → Value
  | .int z₁, .int z₂ => .bool (z₁ ≤ z₂)
  | _, _ => .error

@[grind, simp]
def and : Value → Value → Value
  | .bool b₁, .bool b₂ => .bool (b₁ && b₂)
  | _, _ => .error

@[grind, simp]
def or : Value → Value → Value
  | .bool b₁, .bool b₂ => .bool (b₁ || b₂)
  | _, _ => .error

@[grind, simp]
def neg : Value → Value
  | .int z => .int (-z)
  | _ => .error

@[grind, simp]
def not : Value → Value
  | .bool b => .bool ¬b
  | _ => .error

end Value

abbrev State := AList (fun (_ : Var) => Value)

@[grind, simp]
def Exp.eval (σ : State) : Exp → Value
  | .int z => .int z
  | .bool b => .bool b
  | .var x => match σ.lookup x with
    | .some v => v
    | .none => .error
  | .binop .add left right => (left.eval σ).add (right.eval σ)
  | .binop .mul left right => (left.eval σ).mul (right.eval σ)
  | .binop .le left right  => (left.eval σ).le  (right.eval σ)
  | .binop .and left right => (left.eval σ).and (right.eval σ)
  | .binop .or left right  => (left.eval σ).or  (right.eval σ)
  | .unop .neg e => (e.eval σ).neg
  | .unop .not e => (e.eval σ).not

@[grind cases, grind intro, aesop [safe constructors, unsafe 10% cases]]
inductive HasType (Γ : Env) : Exp → Ty → Prop
  | int  : HasType Γ (.int _) .int
  | bool : HasType Γ (.bool _) .bool
  | var {x τ} : Γ.lookup x = .some τ → HasType Γ (.var x) τ
  | add_mul {op left right} :
      (op = .add ∨ op = .mul) → HasType Γ left .int → HasType Γ right .int →
      HasType Γ (.binop op left right) .int
  | le {left right} :
      HasType Γ left .int → HasType Γ right .int →
      HasType Γ (.binop .le left right) .bool
  | and_or {op left right} :
      (op = .and ∨ op = .or) → HasType Γ left .bool → HasType Γ right .bool →
      HasType Γ (.binop op left right) .bool
  | neg {e} : HasType Γ e .int → HasType Γ (.unop .neg e) .int
  | not {e} : HasType Γ e .bool → HasType Γ (.unop .not e) .bool

lemma exp_check₁
  {Γ : Env} {e : Exp} {τ : Ty}
  : HasType Γ e τ → e.check Γ == .some τ
:= by
  intro h
  induction h with grind

lemma exp_check₂
  {Γ : Env} {e : Exp} {τ : Ty}
  : e.check Γ == .some τ → HasType Γ e τ
:= by fun_induction Exp.check generalizing τ with grind

theorem exp_check_is_correct
  {Γ : Env} {e : Exp} {τ : Ty}
  : HasType Γ e τ ↔ e.check Γ == .some τ
:= ⟨exp_check₁, exp_check₂⟩

@[grind cases, grind intro, aesop [safe constructors, unsafe 10% cases]]
inductive BigstepE (σ : State) : Exp → Value → Prop
  | int z : BigstepE σ (.int z) (.int z)
  | bool b : BigstepE σ (.bool b) (.bool b)
  | var {x v} : σ.lookup x = .some v → BigstepE σ (.var x) v
  | add {z1 z2 left right} :
      BigstepE σ left (.int z1) → BigstepE σ right (.int z2) →
      BigstepE σ (.binop .add left right) (.int (z1 + z2))
  | mul {z1 z2 left right} :
      BigstepE σ left (.int z1) → BigstepE σ right (.int z2) →
      BigstepE σ (.binop .mul left right) (.int (z1 * z2))
  | le {z1 z2 left right} :
      BigstepE σ left (.int z1) → BigstepE σ right (.int z2) →
      BigstepE σ (.binop .le left right) (.bool (z1 ≤ z2))
  | and {b1 b2 left right} :
      BigstepE σ left (.bool b1) → BigstepE σ right (.bool b2) →
      BigstepE σ (.binop .and left right) (.bool (b1 && b2))
  | or {b1 b2 left right} :
      BigstepE σ left (.bool b1) → BigstepE σ right (.bool b2) →
      BigstepE σ (.binop .or left right) (.bool (b1 || b2))
  | neg {e z} : BigstepE σ e (.int z) → BigstepE σ (.unop .neg e) (.int (-z))
  | not {e b} : BigstepE σ e (.bool b) → BigstepE σ (.unop .not e) (.bool !b)

abbrev value_matches_type : Ty → Value → Prop
  | .bool, v => ∃ b, v = .bool b
  | .int, v => ∃ z, v = .int z

@[grind, simp]
def compatible (Γ : Env) (σ : State) : Prop :=
  ∀ {x τ}, Γ.lookup x = some τ →
    ∃ v, σ.lookup x = .some v ∧ value_matches_type τ v

attribute [simp] BigstepE.int
attribute [simp] BigstepE.bool
attribute [simp] BigstepE.var
attribute [simp] BigstepE.add
attribute [simp] BigstepE.mul
attribute [simp] BigstepE.le
attribute [simp] BigstepE.and
attribute [simp] BigstepE.or
attribute [simp] BigstepE.neg
attribute [simp] BigstepE.not

theorem exp_is_sound
  {Γ : Env} {σ : State} {e : Exp} {τ : Ty}
  : compatible Γ σ → HasType Γ e τ →
      ∃ v, BigstepE σ e v ∧ value_matches_type τ v
:= by
  intro h1 h2
  induction h2 with
  | int | bool | neg | not => aesop
  | var => grind
  | add_mul | le => aesop (add safe (by grind))
  | and_or h3 _ _ ih₁ ih₂ =>
    /-
      For some reason `aesop` times out for this case so we have to do it mostly
      manually -/
    obtain ⟨v₁, hl, hv₁⟩ := ih₁; obtain ⟨b₁, hb₁⟩ := hv₁
    obtain ⟨v₂, hr, hv₂⟩ := ih₂; obtain ⟨b₂, hb₂⟩ := hv₂
    cases h3 with
    | inl h => exists (.bool (b₁ && b₂)); grind
    | inr h => exists (.bool (b₁ || b₂)); grind

lemma exp_eval_matches_semantics
  {σ : State} {e : Exp} {v : Value}
  : BigstepE σ e v → e.eval σ = v
:= by
  intro h
  induction h with simp_all

namespace Value

/-
  The lemmas below cannot be annotated for `grind`; the documentation isn't
  clear why, but I think it has to do with some combination of the `≠` and `∃`.
  Instead we'll turn to `aesop`. -/

@[aesop safe forward]
lemma not_error
  {v : Value}
  : v ≠ .error → (∃ z, v = .int z) ∨ (∃ b, v = .bool b)
:= by grind

@[aesop safe forward]
lemma binop_not_bool
  {v₁ v₂ v : Value}
  : (v₁.add v₂ = v → ∀ b, v ≠ .bool b) ∧
    (v₁.mul v₂ = v → ∀ b, v ≠ .bool b)
:= by grind

@[aesop safe forward]
lemma binop_not_int
  {v₁ v₂ v : Value}
  : (v₁.le v₂ = v → ∀ z, v ≠ .int z) ∧
    (v₁.and v₂ = v → ∀ z, v ≠ .int z) ∧
    (v₁.or v₂ = v → ∀ z, v ≠ .int z)
:= by grind

@[aesop safe forward]
lemma unop_not_bool
  {v₁ v₂ : Value}
  : v₁.neg = v₂ → ∀ b, v₂ ≠ .bool b
:= by grind

@[aesop safe forward]
lemma unop_not_int
  {v₁ v₂ : Value}
  : v₁.not = v₂ → ∀ z, v₂ ≠ .int z
:= by grind

@[aesop safe forward]
lemma add_not_error
  {v₁ v₂ v : Value}
  : v₁.add v₂ = v → v ≠ .error →
      ∃ z₁ z₂, v₁ = .int z₁ ∧ v₂ = .int z₂ ∧ v = .int (z₁ + z₂)
:= by aesop

@[aesop safe forward]
lemma mul_not_error
  {v₁ v₂ v : Value}
  : v₁.mul v₂ = v → v ≠ .error →
      ∃ z₁ z₂, v₁ = .int z₁ ∧ v₂ = .int z₂ ∧ v = .int (z₁ * z₂)
:= by aesop

@[aesop safe forward]
lemma le_not_error
  {v₁ v₂ v : Value}
  : v₁.le v₂ = v → v ≠ .error →
      ∃ z₁ z₂, v₁ = .int z₁ ∧ v₂ = .int z₂ ∧ v = .bool (z₁ ≤ z₂)
:= by aesop

@[aesop safe forward]
lemma and_not_error
  {v₁ v₂ v : Value}
  : v₁.and v₂ = v → v ≠ .error →
      ∃ b₁ b₂, v₁ = .bool b₁ ∧ v₂ = .bool b₂ ∧ v = .bool (b₁ && b₂)
:= by aesop (add safe (by grind))

@[aesop safe forward]
lemma or_not_error
  {v₁ v₂ v : Value}
  : v₁.or v₂ = v → v ≠ .error →
      ∃ b₁ b₂, v₁ = .bool b₁ ∧ v₂ = .bool b₂ ∧ v = .bool (b₁ || b₂)
:= by aesop (add safe (by grind))

@[aesop safe forward]
lemma neg_not_error
  {v₁ v₂ : Value}
  : v₁.neg = v₂ → v₂ ≠ .error →
      ∃ z, v₁ = .int z ∧ v₂ = .int (-z)
:= by aesop

@[aesop safe forward]
lemma not_not_error
  {v₁ v₂ : Value}
  : v₁.not = v₂ → v₂ ≠ .error →
      ∃ b, v₁ = .bool b ∧ v₂ = .bool !b
:= by aesop

end Value

/-
  Wee see that no one proof automation tactic is best; different ones work in
  different cicumstances. Also, even when theoretically they should work
  pragmatically they may fail, as in cases7 and case11 where `aesop` times out
  unless we give some help. -/
lemma exp_semantics_matches_eval
  {σ : State} {e : Exp} {v : Value}
  : v = e.eval σ → v ≠ .error → BigstepE σ e v
:= by
  fun_induction Exp.eval generalizing v with
  | case1 | case2 | case3 | case4 => simp_all
  | case5 | case6 | case10 => aesop
  | case7 _ _ ih₁ ih₂ =>
    intro h1 h2
    obtain ⟨z₁, z₂, h3, h4, h5⟩ := Value.le_not_error h1.symm h2
    aesop
  | case8 | case9 => aesop (add safe (by grind))
  | case11 _ ih =>
    intro h1 h2
    obtain ⟨z, h3, h4⟩ := Value.not_not_error h1.symm h2
    aesop

theorem exp_eval_is_correct
  {σ : State} {e : Exp} {v : Value}
  : (BigstepE σ e v → e.eval σ = v) ∧
    (v = e.eval σ → v ≠ .error → BigstepE σ e v)
:= ⟨exp_eval_matches_semantics, exp_semantics_matches_eval⟩
