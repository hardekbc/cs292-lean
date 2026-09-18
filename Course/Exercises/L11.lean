/-
  # EXERCISES FOR `L11`

  We define NFA and various operations on NFA and prove their correctness. Fill
  in the `sorry` in the termination proof for `accepts.ε_closure`, in the
  definitions of `union`, `concat`, and `star`, and in the theorems below. Feel
  free to add lemmas if you think they will be helpful.
-/

import Course.CourseLib
import Course.L11_DFA_Redux

open Dfa_Redux

/-
  Nondeterministic finite automata. The alphabet can be any type `α` as long as
  it is finite and nonempty. The states can be any type `σ` as long as it is
  finite and has decidable equality (`σ` is also necessarily nonempty because
  `start : σ`). We require decidable equality on states because we're using
  `Finset` to hold sets of states. We handle `ε` transitions by using `Option`
  for labels, where `none` means `ε`; we handle nondeterminism by making the
  final codomain of the transition function a (finite) set of states. -/
structure Nfa
  (α : Type) [Fintype α] [Nonempty α]
where
  σ : Type
  σ_deq_fin : DecidableEq σ × Fintype σ
  δ : σ → Option α → Finset σ
  start : σ
  accepting : σ → Bool

namespace Nfa

variable {α : Type} [Fintype α] [Nonempty α]

/-
  Does the NFA accept a given string -/
def accepts (M : Nfa α) (w : List α) : Bool :=
  /-
    We accept an input if the final set of states contains an accepting state -/
  (runsto {M.start}).fold Bool.or false (M.accepting ·)
where
  /-
    Given an initial set of states, compute the set of states reached after
    processing the input `w` -/
  runsto (init_states : Finset M.σ) : Finset M.σ :=
    have (_, _) := M.σ_deq_fin
    w.foldl
      (fun states a => ε_closure (states.sup (M.δ · a)))
      (ε_closure init_states)
  /-
    The ε-closure of a set of states is all states reachable via an ε-transition
    from those states -/
  ε_closure (states : Finset M.σ) : Finset M.σ :=
    have := M.σ_deq_fin.1
    let next := states.sup (M.δ · none)
    let acc := next ∪ states
    if acc.card ≤ states.card then states else ε_closure (states ∪ next)
  termination_by
    have := M.σ_deq_fin.2
    (Fintype.card M.σ) - states.card
  decreasing_by
    sorry

/-
  Construct the union of two NFA. We use a type that directly describes the
  algorithm for computing the union of two NFAs: we add a new start state that
  has ε-transitions to the original start states of `M1` and `M2`; then for a
  state from `M1` we use `M1.δ` and for a state from `M2` we use `M2.δ`. So the
  type of states in the new machine is the disjoint union of a new state and the
  states of `M1` and the states of `M2`. -/
def union (M1 M2 : Nfa α) : Nfa α :=
  /-
    We need to bring these facts into the local context so that Lean can infer
    them where they are needed -/
  have (_, _) := M1.σ_deq_fin
  have (_, _) := M2.σ_deq_fin

  { σ := (Fin 1) ⊕ M1.σ ⊕ M2.σ
    /- `inferInstance` infers instances for type classes -/
    σ_deq_fin := (inferInstance, inferInstance)
    /-
      The transition function determines whether the input state is the new
      start state or from `M1` or from `M2` and applies the appropriate
      transition. The new start state is connected by `ε` transitions to the
      start states of `M1` and `M2`. Remember that the final codomain is a set
      of states, and we need to lift their elements from `M1.σ` or `M2.σ` to be
      in the new state type `(Fin 1) ⊕ M1.σ ⊕ M2.σ`. `Finset.image` is a useful
      function here. -/
    δ := sorry
    /- The start state is the new state we just created -/
    start := .inl 0
    /- Similar to `δ`, but for `accepting` -/
    accepting := sorry
  }
where
  /- Lift states from their original type to the new state type -/
  liftM1 (s : M1.σ) : (Fin 1) ⊕ M1.σ ⊕ M2.σ := .inr (.inl s)
  liftM2 (s : M2.σ) : (Fin 1) ⊕ M1.σ ⊕ M2.σ:= .inr (.inr s)

/-
  Construct the concatenation of two NFA. To concatenate `M1` and `M2` our new
  set of states is the disjoint union of `M1.δ` and `M2.δ`, and our transition
  function steps through `M1` until it reaches an accepting state and then makes
  an ε-transition to `M2.start` and starts stepping through `M2` -/
def concat (M1 M2 : Nfa α) : Nfa α :=
  /-
    We need to bring these facts into the local context so that Lean can infer
    them where they are needed -/
  have (_, _) := M1.σ_deq_fin
  have (_, _) := M2.σ_deq_fin

  { σ := M1.σ ⊕ M2.σ
    σ_deq_fin := (inferInstance, inferInstance)
    /-
      If the state is from `M1` use `M1.δ`, but add that if the state is
      accepting then also make an `ε` transition to `M2.start` -/
    δ := sorry
    start := liftM1 M1.start
    accepting := sorry
  }
where
  /- Lift states from their original type to the new state type -/
  liftM1 (s : M1.σ) : M1.σ ⊕ M2.σ := .inl s
  liftM2 (s : M2.σ) : M1.σ ⊕ M2.σ := .inr s

/-
  Construct the Kleene star of an NFA. To take the Kleene star of `M` our new
  set of states is the disjoint union of one new starting state and `M.σ`, and
  our transition function has an `ε` transition from the new start state to
  `M.start`, steps through `M.δ`, then for an accepting state has an
  `ε` transition back to the new start state -/
def star (M : Nfa α) : Nfa α :=
  /-
    We need to bring these facts into the local context so that Lean can infer
    them where they are needed -/
  have (_, _) := M.σ_deq_fin

  { σ := (Fin 1) ⊕ M.σ
    σ_deq_fin := (inferInstance, inferInstance)
    δ := sorry
    start := .inl 0
    accepting := sorry
  }
where
  /- Lift states from their original type to the new state type -/
  liftM (s : M.σ) : (Fin 1) ⊕ M.σ := .inr s

/-
  To prove correctness we go through a similar process as for DFA -/

inductive RunsTo (M : Nfa α) : M.σ → List α → M.σ → Prop where
  | refl σ₁ : RunsTo M σ₁ [] σ₁
  | eps {σ₂ σ₁} : σ₂ ∈ M.δ σ₁ none → RunsTo M σ₁ [] σ₂
  | step {σ₁ σ₂ σ₃ w a} : RunsTo M σ₁ w σ₂ → σ₃ ∈ M.δ σ₂ (.some a) →
      RunsTo M σ₁ (w ++ [a]) σ₃

def accepts_prop (M : Nfa α) (w : List α) : Prop :=
  ∃ σ, M.RunsTo M.start w σ ∧ M.accepting σ

def L (M : Nfa α) : Language α :=
  { w | M.accepts_prop w }

/- ----- accepts_is_correct ----- -/

theorem accepts_is_correct
  {M : Nfa α} {w : List α}
  : M.accepts_prop w ↔ M.accepts w
:= by
  sorry

/- ----- union_is_correct ----- -/

theorem union_is_correct
  {M1 M2 : Nfa α}
  : M1.L ∪ M2.L = (M1.union M2).L
:= by
  sorry

/- ----- concat_is_correct ----- -/

theorem concat_is_correct
  {M1 M2 : Nfa α}
  : M1.L * M2.L = (M1.concat M2).L
:= by
  sorry

/- ----- star_is_correct ----- -/

theorem star_is_correct
  {M : Nfa α}
  : kleene_star M.L = M.star.L
:= by
  sorry

end Nfa
