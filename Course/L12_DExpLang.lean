/-
  # Revisiting the Expression Language

  - Revisiting the expression language `Exp` from `L08_ExpLang.lean`, this time with an intrinsically-typed description and interpreter: no type checker needed, because the type system prevents ill-typed programs from being created in the first place. We'll use the name `DExp`, for "dependently-typed Exp".

  - Using dependent types can start to blur the distinction between programming and proving, because sometimes we need to explain to Lean why something should pass the type checker. There are several places in this example where we show that we can actually use tactics in "normal" programming as well as proving.
-/

import Course.CourseLib

/-
  -----------------------------------------------------------
  OLD DATA STRUCTURES (`Var`, `BinOp`, `UnOp`)
  -----------------------------------------------------------
-/

/- Variables -/
abbrev Var := String

/- Binary operations -/
inductive BinOp
  | add
  | mul
  | le
  | and
  | or

/- Unary operations -/
inductive UnOp
  | neg
  | not

/-
  -----------------------------------------------------------
  NEW DATA STRUCTURES AND ASSOCIATED FUNCTIONS
  -----------------------------------------------------------
-/

/-
  We'll use the convention that a boolean-valued variable must end with "?",
  i.e., we can determine the type of a variable by looking at its name. This
  isn't necessary, we could use `Env` as we did in `L08_ExpLang.lean`, but this
  convention means that we can remove a level of indirection instead of carrying
  around a type environment everywhere. -/
abbrev Var.type_of (x : Var) : Type :=
  if x.endsWith "?" then Bool else ℤ

/-
  We have to explain to Lean how to convert something of type `x.type_of` into a
  String, which amounts to saying "if it's `Bool` use Bool.toString, if it's `ℤ`
  use Int.toString". We use tactics to specify this behavior, even though we're
  creating an actual function not a proof. -/
instance {x : Var} : ToString x.type_of where
  toString e := by
    unfold Var.type_of at e
    split at e
    · exact (toString e)
    · exact (toString e)

/-
  Mapping binary operations to their operand and result types (the first element
  is the type of both operands, the second element is the result type). Uses
  `abbrev` so that Lean can typecheck `DExp.eval` below. -/
abbrev BinOp.type_of : BinOp → Type × Type
  | .add | .mul => (ℤ, ℤ)
  | .le => (ℤ, Bool)
  | .and | .or => (Bool, Bool)

/-
  Mapping unary operations to their operand and result types (the first element
  is the type of the operand, the second element is the result type). Uses
  `abbrev` so that Lean can typecheck `DExp.eval` below. -/
abbrev UnOp.type_of : UnOp → Type × Type
  | .neg => (ℤ, ℤ)
  | .not => (Bool, Bool)

/-
  Expressions using dependent types. Note that the result-type of an expression
  is explicitly given in its type: an expression of type `DExp ℤ` must evaluate
  to an integer and an expression of type `DExp Bool` must evaluate to a
  boolean. In other words, the IMP type system is embedded in the definition of
  `DExp`. -/
inductive DExp : Type → Type
  | int   : ℤ → DExp ℤ
  | bool  : Bool → DExp Bool
  | var   : (x : Var) → DExp x.type_of
  | binop : (op : BinOp) → DExp op.type_of.1 → DExp op.type_of.1 →
            DExp op.type_of.2
  | unop  : (op : UnOp) → DExp op.type_of.1 → DExp op.type_of.2

/-
  -----------------------------------------------------------
  INTERPRETER
  -----------------------------------------------------------
-/

/-
  An evaluation state is a map from variables to their values. Note that we're
  now taking advantage of `AList` being dependently-typed: variables of integer
  type map to integers and variables of boolean type map to booleans. We don't
  need the `Value` type as a wrapper any more. -/
def DState := AList (fun (x : Var) => x.type_of)

/- Ability to output `DState` as a string -/
instance : ToString DState where
  toString σ := (σ.entries.map (fun ⟨x, v⟩ => s!"{x} ↦ {v}")).toString

/-
  Our change to the variable name convention means that we don't have an
  explicit list of declared variables, so we aren't declaring variables before
  they are used. This means that we need to provide a default value for
  variables in case they are used before being defined. Again we use tactics to
  specify this behavior. -/
def Var.default (x : Var) : x.type_of := by
  unfold type_of
  split
  · exact false -- default value of `Bool` variables
  · exact 0     -- default value of `ℤ` variables

/-
  We add our own state lookup function that returns a default value if the
  variable is not already present -/
def DState.get (x : Var) (σ : DState) : x.type_of :=
  match σ.lookup x with
  | .none => x.default
  | .some v => v

/-
  Evaluating expressions. Note that the type signature guarantees if we're
  evaluating an expression of type `τ` that we get back a value of type `τ`;
  there is no possibility of an error. -/
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

/-
  -----------------------------------------------------------
  UTILITY THEOREMS
  -----------------------------------------------------------
-/

/-
  Using dependent types can make things more complicated, because we have to
  help Lean prove that certain things are type-correct. Specifically for us,
  Lean needs help dealing with things of type `x.type_of` because the value of
  `x.type_of` depends on an external fact, i.e., whether `x` ends in a "?" or
  not. Here are some utility theorems to make that more convenient. I only
  created the ones needed by the examples below, ideally we would have
  corresponding theorems for the other binary and unary operators. -/

/-
  If the given variable does not end in "?" then its type is `ℤ`. If we provide
  a concrete string for `x` then Lean can automatically decide whether `h` is
  true using the `decide` tactic (which needs the additional `+kernel` option in
  this case due to transparency issues with the definition of `endsWith`). -/
theorem int_type
  (x : Var) (h : ¬x.endsWith "?" := by decide +kernel)
  : x.type_of = ℤ
:= by
  unfold Var.type_of
  split
  · contradiction
  · rfl

/-
  If the given variable does not end in "?" then it has the same type as a `mul`
  operand -/
theorem mul_op
  (x : Var) (h : ¬x.endsWith "?" := by decide +kernel)
  : x.type_of = BinOp.mul.type_of.1
:= by rw [int_type x h]

/-
  If the given variable does not end in "?" then it has the same type as a `le`
  operand -/
theorem le_op
  (x : Var) (h : ¬x.endsWith "?" := by decide +kernel)
  : x.type_of = BinOp.le.type_of.1
:= by rw [int_type x h]

/-
  -----------------------------------------------------------
  EXAMPLES
  -----------------------------------------------------------
-/
namespace Examples
/-
  - We use the `▸` macro to apply the utility theorems

    + `h ▸ P a` where `h : a = b` yields `P b` (or the reverse: `h ▸ P b` yields `P a`, i.e., `▸` will try both directions of the equality)

    + Here `h` will be one of the utility theorems and `P a` will be a type involving `x.type_of`, where `▸` will rewrite the type to be the one Lean is expecting as per the utility theorem being used

  - Remove the `... ▸` parts to see the type errors we are fixing
-/


-- The expression `(-2 * x) + 1`
def de1 : DExp ℤ :=
  .binop
    .add
    (.int 1)
    (.binop
      .mul
      (.unop .neg (.int 2))
      (mul_op "x" ▸ .var "x"))

#eval de1.eval [⟨"x", int_type "x" ▸ 0⟩].toAList
#eval de1.eval [⟨"x", int_type "x" ▸ 4⟩].toAList


-- The expression `¬true ∨ (-20 ≤ x ∧ x ≤ 100)`
def de2 : DExp Bool :=
  .binop
    .or
    (.unop .not (.bool true))
    (.binop
      .and
      (.binop .le (.int (-20)) (le_op "x" ▸ .var "x"))
      (.binop .le (le_op "x" ▸ .var "x") (.int 100)))

#eval de2.eval [⟨"x", int_type "x" ▸ (-1)⟩].toAList
#eval de2.eval [⟨"x", int_type "x" ▸ (-50)⟩].toAList
#eval de2.eval [⟨"x", int_type "x" ▸ 200⟩].toAList

end Examples

/-
  -----------------------------------------------------------
  INTERPRETER CORRECT

  By the fact that we wrote a well-typed interpreter, we are already guaranteed
  that the type system embedded in `DExp` is sound because we are guaranteed the
  interpreter cannot make a type-related error. However, we still need to prove
  that the interpreter respects the language semantics. The strategy follows
  that from `L08_ExpLang`.
  -----------------------------------------------------------
-/

/-
  We need to define a bigstep semantics for `DExp`. Note that the implicit
  parameter `τ` _must_ be an index, since the type is different for different
  constructors. -/
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

lemma exp_eval_matches_semantics
  {σ : DState} {τ : Type} {e : DExp τ} {v : τ}
  : BigstepE σ e v → e.eval σ = v
:= by
  intro h
  induction h with simp_all [DExp.eval]

attribute [simp] BigstepE.int
attribute [simp] BigstepE.bool
attribute [simp] BigstepE.var

lemma exp_semantics_matches_eval
  {σ : DState} {τ : Type} {e : DExp τ} {v : τ}
  : v = e.eval σ → BigstepE σ e v
:= by
  fun_induction DExp.eval with
  | case1 | case2 | case3 => simp_all
  | case4 left right ih₁ ih₂ =>
    replace ih₁ := @ih₁ (left.eval σ) rfl
    replace ih₂ := @ih₂ (right.eval σ) rfl
    intro h
    rw [h]
    exact BigstepE.add ih₁ ih₂
  | case5 left right ih₁ ih₂ =>
    replace ih₁ := @ih₁ (left.eval σ) rfl
    replace ih₂ := @ih₂ (right.eval σ) rfl
    intro h
    rw [h]
    exact BigstepE.mul ih₁ ih₂
  | case6 left right ih₁ ih₂ =>
    replace ih₁ := @ih₁ (left.eval σ) rfl
    replace ih₂ := @ih₂ (right.eval σ) rfl
    intro h
    rw [h]
    exact BigstepE.le ih₁ ih₂
  | case7 left right ih₁ ih₂ =>
    replace ih₁ := @ih₁ (left.eval σ) rfl
    replace ih₂ := @ih₂ (right.eval σ) rfl
    intro h
    rw [h]
    exact BigstepE.and ih₁ ih₂
  | case8 left right ih₁ ih₂ =>
    replace ih₁ := @ih₁ (left.eval σ) rfl
    replace ih₂ := @ih₂ (right.eval σ) rfl
    intro h
    rw [h]
    exact BigstepE.or ih₁ ih₂
  | case9 e ih =>
    replace ih := @ih (e.eval σ) rfl
    intro h
    rw [h]
    exact BigstepE.neg ih
  | case10 e ih =>
    replace ih := @ih (e.eval σ) rfl
    intro h
    rw [h]
    exact BigstepE.not ih

theorem exp_eval_is_correct
  {σ : DState} {τ : Type} {e : DExp τ} {v : τ}
  : (BigstepE σ e v → e.eval σ = v) ∧
    (v = e.eval σ → BigstepE σ e v)
:= ⟨exp_eval_matches_semantics, exp_semantics_matches_eval⟩
