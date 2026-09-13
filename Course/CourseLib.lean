import Aesop -- `aesop` tactic
import Batteries.CodeAction.Match -- code completion for `match` expressions
import Mathlib.Data.List.AList
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic -- ℕ notation for Nat
import Mathlib.Data.Rel
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

open Lean Elab Command Tactic Expr MVarId

/-
  Alias for `#guard_msgs` that includes common configurations -/

macro
  doc?:(docComment)? tk:"#guard_error" c:command : command =>
  `(command|$[$doc?]? #guard_msgs%$tk (whitespace := lax, substring := true) in $c)

/-
  Define aliases for `namespace` and `end` that allow for selective color-coding
  in VS Code -/

syntax "topic::" ident : command
syntax "end_topic" ident : command
syntax "subtopic::" ident : command
syntax "end_subtopic" ident : command

macro_rules
  | `(topic:: $title:ident) => `(namespace $title)
  | `(end_topic $title:ident) => `(end $title)
  | `(subtopic:: $title:ident) => `(namespace $title)
  | `(end_subtopic $title:ident) => `(end $title)

/-
  A helpful theorem. This has to already exist somewhere, but I can't find it
  and it's simple enough to prove my own version. -/
theorem imp_iff_or (A B : Prop) : A ∨ B ↔ ¬A → B := by
  constructor
  case mp =>
    intro h
    exact Or.resolve_left h
  case mpr =>
    intro h1
    by_cases h2 : A
    · left; exact h2
    · right; exact h1 h2
