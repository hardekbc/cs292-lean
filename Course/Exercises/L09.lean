/-
  # EXERCISES FOR `L09`

  Fill in the `sorry` in the theorems below. Feel free to create additional
  lemmas as you find them helpful.
-/

import Course.CourseLib
import Course.L09_DFA
import AutograderLib

/-
  -----------------------------------------------------------
  REGULAR EXPRESSIONS
  -----------------------------------------------------------
-/

/-
  Regular expressions. The alphabet `α` can be any type as long as it is finite
  and nonempty. A regular expression is empty (`Φ`), the empty string (`ε`), a
  character from the alphabet (`char`), the union of two regular expressions
  (`union`), the concatenation of two regular expressions (`concat`), or the
  kleene star of a regular expression (`star`). -/
inductive Re
  (α : Type) [Fintype α] [Nonempty α]
where
  | Φ
  | ε
  | char   : α → Re α
  | union  : Re α → Re α → Re α
  | concat : Re α → Re α → Re α
  | star   : Re α → Re α

namespace Re

/-
  Some operations on `Re` require that the alphabet has decidable equality -/
variable {α : Type} [Fintype α] [Nonempty α] [DecidableEq α]

/-
  Nullability of a regular expression, i.e., can the expression generate the
  empty string -/
def nullable : Re α → Bool
  | .Φ => false
  | .ε => true
  | .char _ => false
  | .union r1 r2 => r1.nullable || r2.nullable
  | .concat r1 r2 => r1.nullable && r2.nullable
  | .star _ => true

/-
  Derivative of a regular expression: `deriv R a = { w | a::w ∈ L(R) }` -/
def deriv : Re α → α → Re α
  | .Φ, _ => .Φ
  | .ε, _ => .Φ
  | .char c, a => if a = c then .ε else .Φ
  | .union r1 r2, a => .union (r1.deriv a) (r2.deriv a)
  | .concat r1 r2, a =>
    if r1.nullable then .union (.concat (r1.deriv a) r2) (r2.deriv a)
    else .concat (r1.deriv a) r2
  | .star r, a => .concat (r.deriv a) r.star

/-
  Return whether `R` accepts input `w`, which is true iff, after successively
  taking the derivative of `R` wrt the elements of the input string, the
  resulting expression is nullable. -/
def accepts (R : Re α) (w : List α) : Bool :=
  (w.foldl Re.deriv R).nullable

/- The language of a regular expression -/
def L : Re α → Language α
  | .Φ => {}
  | .ε => {[]}
  | .char c => {[c]}
  | .union r1 r2 => r1.L ∪ r2.L
  | .concat r1 r2 => r1.L * r2.L
  | .star r => kleene_star r.L

end Re

variable {α : Type} [Fintype α] [Nonempty α]

/-
  `simp` can't see "underneath" our `*` notation for `Language` concatenation.
  The standard way to handle this is to prove a lemma by `rfl`, and make the
  lemma available to `simp` via annotation. -/
@[simp]
lemma mul_eq_append {L₁ L₂ : Language α} {w : List α}
  : w ∈ L₁ * L₂ ↔ w ∈ Set.image2 (· ++ ·) L₁ L₂
:= by rfl

@[autogradedProof 1]
theorem nullable_is_correct {R : Re α} : R.nullable ↔ [] ∈ R.L := by
  sorry

@[autogradedProof 1]
theorem deriv_is_correct
  {R : Re α} {a : α} [DecidableEq α]
  : (R.deriv a).L = { w | a :: w ∈ R.L }
:= by
  sorry

@[autogradedProof 1]
theorem accepts_is_correct
  {R : Re α} {w : List α} [DecidableEq α]
  : w ∈ R.L ↔ R.accepts w
:= by
  sorry
