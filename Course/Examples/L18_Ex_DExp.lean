/-
  # Example for `L18`

  We revisit `DExp` to show where we might get dependency elimination errors and
  how we would have to redefine things to get rid of them
-/

import Course.CourseLib

topic::BEFORE
/-
  Here is the implementation copied from `L12_DExpLang`. See the end for an
  explanation of the problem we face. -/

abbrev Var := String

inductive BinOp
  | add
  | mul
  | le
  | and
  | or

inductive UnOp
  | neg
  | not

abbrev Var.type_of (x : Var) : Type :=
  if x.endsWith "?" then Bool else ℤ

abbrev BinOp.type_of : BinOp → Type × Type
  | .add | .mul => (ℤ, ℤ)
  | .le => (ℤ, Bool)
  | .and | .or => (Bool, Bool)

abbrev UnOp.type_of : UnOp → Type × Type
  | .neg => (ℤ, ℤ)
  | .not => (Bool, Bool)

inductive DExp : Type → Type
  | int   : ℤ → DExp ℤ
  | bool  : Bool → DExp Bool
  | var   : (x : Var) → DExp x.type_of
  | binop : (op : BinOp) → DExp op.type_of.1 → DExp op.type_of.1 →
            DExp op.type_of.2
  | unop  : (op : UnOp) → DExp op.type_of.1 → DExp op.type_of.2

def DState := AList (fun (x : Var) => x.type_of)

def Var.default (x : Var) : x.type_of := by
  unfold type_of
  split
  · exact false
  · exact 0

def DState.get (x : Var) (σ : DState) : x.type_of :=
  match σ.lookup x with
  | .none => x.default
  | .some v => v

def DExp.eval {τ : Type} (σ : DState) : DExp τ → τ
  | .int z => z
  | .bool b => b
  | .var x => σ.get x
  | .binop op left right => match op with
    | .add => left.eval σ + right.eval σ
    | .mul => left.eval σ * right.eval σ
    | .le => left.eval σ ≤ right.eval σ
    | .and => left.eval σ && right.eval σ
    | .or => left.eval σ || right.eval σ
  | .unop op e => match op with
    | .neg => -(e.eval σ)
    | .not => !(e.eval σ)

inductive BigstepE (σ : DState) : {τ : Type} → DExp τ → τ → Prop
  | int z : BigstepE σ (.int z) z
  | bool b : BigstepE σ (.bool b) b
  | var {x v} : σ.get x = v → BigstepE σ (.var x) v
  | add {z1 z2 left right} :
      BigstepE σ left z1 → BigstepE σ right z2 →
      BigstepE σ (.binop .add left right) (z1 + z2)
  | mul {z1 z2 left right} :
      BigstepE σ left z1 → BigstepE σ right z2 →
      BigstepE σ (.binop .mul left right) (z1 * z2)
  | le {z1 z2 left right} :
      BigstepE σ left z1 → BigstepE σ right z2 →
      BigstepE σ (.binop .le left right) (z1 ≤ z2)
  | and {b1 b2 left right} :
      BigstepE σ left b1 → BigstepE σ right b2 →
      BigstepE σ (.binop .and left right) (b1 && b2)
  | or {b1 b2 left right} :
      BigstepE σ left b1 → BigstepE σ right b2 →
      BigstepE σ (.binop .or left right) (b1 || b2)
  | neg {e z} : BigstepE σ e z → BigstepE σ (.unop .neg e) (-z)
  | not {e b} : BigstepE σ e b → BigstepE σ (.unop .not e) !b

/-
  **NEW MATERIAL**

  Suppose that we want to prove some inversion lemmas about `BigstepE`. We
  didn't need to do so for the correctness proof, but they may come in handy for
  other proofs. For each proof we must proceed by doing `cases` on a given of
  type `BigstepE`, but `cases` gives us a dependent elimination error. This
  error is exactly because of the reasons discussed in `L18_ProofAdvice`. -/

/--
  error: Dependent elimination failed: Failed to solve equation Decidable.rec
  (fun h ↦ (fun x ↦ ℤ) h) (fun h ↦ (fun x ↦ Bool) h) (instDecidableEqBool
  (String.endsWith x "?") true) = ℤ -/
#guard_error
lemma var_inv
  {σ : DState} {x : Var} {v : x.type_of}
  : BigstepE σ (.var x) v → σ.get x = v
:= by
  intro h
  cases h

/--
  error: Dependent elimination failed: Failed to solve equation ℤ = Bool -/
#guard_error
lemma add_inv
  {σ : DState} {left right : DExp BinOp.add.type_of.1} {v : ℤ}
  : BigstepE σ (.binop .add left right) v → ∃ n₁ n₂,
      BigstepE σ left n₁ ∧ BigstepE σ right n₂ ∧
      v = n₁ + n₂
:= by
  intro h
  cases h

/--
  error: Dependent elimination failed: Failed to solve equation ℤ = Bool -/
#guard_error
lemma mul_inv
  {σ : DState} {left right : DExp BinOp.mul.type_of.1} {v : ℤ}
  : BigstepE σ (.binop .mul left right) v → ∃ n₁ n₂,
      BigstepE σ left n₁ ∧ BigstepE σ right n₂ ∧
      v = n₁ * n₂
:= by
  intro h
  cases h

/--
  error: Dependent elimination failed: Failed to solve equation Bool = ℤ -/
#guard_error
lemma le_inv
  {σ : DState} {left right : DExp BinOp.le.type_of.1} {v : Bool}
  : BigstepE σ (.binop .le left right) v → ∃ n₁ n₂,
      BigstepE σ left n₁ ∧ BigstepE σ right n₂ ∧
      v = (n₁ ≤ n₂)
:= by
  intro h
  cases h

/--
  error: Dependent elimination failed: Failed to solve equation Bool = ℤ -/
#guard_error
lemma and_inv
  {σ : DState} {left right : DExp BinOp.and.type_of.1} {v : Bool}
  : BigstepE σ (.binop .and left right) v → ∃ b₁ b₂,
      BigstepE σ left b₁ ∧ BigstepE σ right b₂ ∧
      v = (b₁ && b₂)
:= by
  intro h
  cases h

/--
  error: Dependent elimination failed: Failed to solve equation Bool = ℤ -/
#guard_error
lemma or_inv
  {σ : DState} {left right : DExp BinOp.or.type_of.1} {v : Bool}
  : BigstepE σ (.binop .or left right) v → ∃ b₁ b₂,
      BigstepE σ left b₁ ∧ BigstepE σ right b₂ ∧
      v = (b₁ || b₂)
:= by
  intro h
  cases h

/--
  error: Dependent elimination failed: Failed to solve equation ℤ = Bool -/
#guard_error
lemma neg_inv
  {σ : DState} {e : DExp UnOp.neg.type_of.1} {v : ℤ}
  : BigstepE σ (.unop .neg e) v → ∃ n,
      BigstepE σ e n ∧ v = -n
:= by
  intro h
  cases h

/--
  error: Dependent elimination failed: Failed to solve equation Bool = ℤ -/
#guard_error
lemma not_inv
  {σ : DState} {e : DExp UnOp.not.type_of.1} {v : Bool}
  : BigstepE σ (.unop .not e) v → ∃ b,
      BigstepE σ e b ∧ v = !b
:= by
  intro h
  cases h

end_topic BEFORE


topic::AFTER
/-
  Here is the revised version of `DExp` et al, with fixes so that we can
  destruct terms for the required proofs. We applied the advice given in
  `L18_ProofAdvice` to avoid situations where the equation solver would get
  stuck. -/

inductive Ty
  | int
  | bool

abbrev Var := String

/-
  We map each `Ty` constructor to the `Type` it stands for. We'll use `Ty`
  constructors for expression types, but we'll mean these mapped types. -/
abbrev Ty.to_type : Ty → Type
  | .int => ℤ
  | .bool => Bool

/-
  As a convenience, we'll have Lean implicitly coerce every use of a `Ty`
  constructor where Lean expects a `Type` into an actual `Type` using
  `Ty.to_type`. The `Coe` in `CoeSort` stands for "coercion". This coercion just
  means that we don't have to keep putting `Ty.int.to_type`, `τ.to_type`, etc
  everywhere. -/
instance : CoeSort Ty Type where
  coe := Ty.to_type

abbrev Var.type_of (x : Var) : Ty :=
  if x.endsWith "?" then .bool else .int

/-
  Here's the big change: `DExp` is now indexed by `Ty` instead of `Type`, so
  whenever we destruct it the equations will be about constructors instead of
  types. We've changed the `var` case so that the index is a variable instead of
  the expression `x.type_of`. Just to show that this isn't the only solution, we
  removed the `binop` and `unop` cases and replaced them with a case per
  operator so the index is a constructor instead of an expression. This wasn't
  an option for `var` though (and we could have fixed `binop` and `unop` the
  same way we did `var` if we wanted). -/
inductive DExp : Ty → Type
  | int     : Ty.int → DExp .int
  | bool    : Ty.bool → DExp .bool
  | var {τ} : (x : Var) → (h : τ = x.type_of) → DExp τ
  | add     : DExp .int → DExp .int → DExp .int
  | le      : DExp .int → DExp .int → DExp .bool
  | mul     : DExp .int → DExp .int → DExp .int
  | and     : DExp .bool → DExp .bool → DExp .bool
  | or      : DExp .bool → DExp .bool → DExp .bool
  | neg     : DExp .int → DExp .int
  | not     : DExp .bool → DExp .bool


def DState := AList (fun (x : Var) => x.type_of)

def Var.default (x : Var) : x.type_of := by
  unfold type_of
  split
  · exact false
  · exact 0

def DState.get (x : Var) (σ : DState) : x.type_of :=
  match σ.lookup x with
  | .none => x.default
  | .some v => v

/-
  Now we have `τ : Ty` instead of `τ : Type`, but because of the implicit
  coercion we defined earlier Lean translates the different constructors to
  actual types. Notice that, e.g., the values for the `int` and `bool` cases are
  type `ℤ` and `Bool` respectively. Also note in `var` that the type of the
  result `σ.get x` is `x.type_of` but we need it to be `τ`, so we use the `▸`
  macro to rewrite the type to the correct version. -/
def DExp.eval {τ : Ty} (σ : DState) : DExp τ → τ
  | .int z => z
  | .bool b => b
  | .var x h => h ▸ σ.get x
  | .add left right => (left.eval σ) + (right.eval σ)
  | .mul left right => (left.eval σ) * (right.eval σ)
  | .le left right  => (left.eval σ) ≤ (right.eval σ)
  | .and left right => (left.eval σ) && (right.eval σ)
  | .or left right  => (left.eval σ) ||  (right.eval σ)
  | .neg e => -(e.eval σ)
  | .not e => !(e.eval σ)

/-
  Here we modified `var` so that we could change the type of `v` in the final
  index to the variable `τ` instead of the expression `x.type_of`, and we also
  modified the binary and unary operators so the final indices are variables
  instead of expressions -/
inductive BigstepE (σ : DState) : {τ : Ty} → DExp τ → τ → Prop
  | int z : BigstepE σ (.int z) z
  | bool b : BigstepE σ (.bool b) b
  | var {x v τ} : σ.get x = v → (h : τ = x.type_of) →
      BigstepE σ (@.var τ x h) (h ▸ v)
  | add {z1 z2 left right v} :
      BigstepE σ left z1 → BigstepE σ right z2 →
      v = (z1 + z2) → BigstepE σ (.add left right) v
  | mul {z1 z2 left right v} :
      BigstepE σ left z1 → BigstepE σ right z2 →
      v = (z1 * z2) → BigstepE σ (.mul left right) v
  | le {z1 z2 left right v} :
      BigstepE σ left z1 → BigstepE σ right z2 →
      v = ((z1 ≤ z2) : Bool) → BigstepE σ (.le left right) v
  | and {b1 b2 left right v} :
      BigstepE σ left b1 → BigstepE σ right b2 →
      v = (b1 && b2) → BigstepE σ (.and left right) v
  | or {b1 b2 left right v} :
      BigstepE σ left b1 → BigstepE σ right b2 →
      v = (b1 || b2) → BigstepE σ (.or left right) v
  | neg {e z v} : BigstepE σ e z → v = -z → BigstepE σ (.neg e) v
  | not {e b v} : BigstepE σ e b → v = !b → BigstepE σ (.not e) v

/-
  Now the inversion lemmas can be proved without any issues -/
namespace BigstepE

variable {τ : Ty}

lemma var_inv
  {σ : DState} {x : Var} {v : τ} (h : τ = x.type_of)
  : BigstepE σ (@.var τ x h) v → σ.get x = (h ▸ v)
:= by
  intro h
  cases h with
  | var => grind

lemma add_inv
  {σ : DState} {left right : DExp .int} {v : τ}
  (h : τ = Ty.int)
  : BigstepE σ (.add left right) (h ▸ v) → ∃ n₁ n₂,
    BigstepE σ left n₁ ∧ BigstepE σ right n₂ ∧
    v = h ▸ (n₁ + n₂)
:= by
  intro h
  cases h with
  | add h1 h2 =>
    rename_i n₁ n₂ h3
    exists n₁, n₂
    rw [← h3] -- `grind` gives an error without this, I'm not sure why
    grind

lemma mul_inv
  {σ : DState} {left right : DExp .int} {v : τ}
  (h : τ = Ty.int)
  : BigstepE σ (.mul left right) (h ▸ v) → ∃ n₁ n₂,
    BigstepE σ left n₁ ∧ BigstepE σ right n₂ ∧
    v = h ▸ (n₁ * n₂)
:= by
  intro h
  cases h with grind

lemma le_inv
  {σ : DState} {left right : DExp .int} {v : τ}
  (h : τ = Ty.bool)
  : BigstepE σ (.le left right) (h ▸ v) → ∃ n₁ n₂,
    BigstepE σ left n₁ ∧ BigstepE σ right n₂ ∧
    v = h ▸ (n₁ ≤ n₂)
:= by
  intro h
  cases h with grind

lemma and_inv
  {σ : DState} {left right : DExp .bool} {v : τ}
  (h : τ = Ty.bool)
  : BigstepE σ (.and left right) (h ▸ v) → ∃ b₁ b₂,
    BigstepE σ left b₁ ∧ BigstepE σ right b₂ ∧
    v = h ▸ (b₁ && b₂)
:= by
  intro h
  cases h with grind

lemma or_inv
  {σ : DState} {left right : DExp .bool} {v : τ}
  (h : τ = Ty.bool)
  : BigstepE σ (.or left right) (h ▸ v) → ∃ b₁ b₂,
    BigstepE σ left b₁ ∧ BigstepE σ right b₂ ∧
    v = h ▸ (b₁ || b₂)
:= by
  intro h
  cases h with grind

lemma neg_inv
  {σ : DState} {e : DExp .int} {v : τ} (h : τ = Ty.int)
  : BigstepE σ (.neg e) (h ▸ v) → ∃ n,
    BigstepE σ e n ∧ v = h ▸ -n
:= by
  intro h
  cases h with
  | neg h1 h2 =>
    rename_i n
    exists n
    rw [← h2] -- `grind` gives an error without this, I'm not sure why
    grind

lemma not_inv
  {σ : DState} {e : DExp .bool} {v : τ} (h : τ = Ty.bool)
  : BigstepE σ (.not e) (h ▸ v) → ∃ b,
    BigstepE σ e b ∧ v = h ▸ !b
:= by
  intro h
  cases h with grind

end BigstepE
end_topic AFTER
