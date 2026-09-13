/-
  # Example for `L18`

  We demonstrate one possible implication of the fact that instances are not
  unique. Specifically the example is in the termination proof of
  `empty.reaches_accepting` for `Dfa`.
-/

import Course.CourseLib

structure Dfa
  (α : Type) [Fintype α] [Nonempty α]
where
  σ : Type
  σ_deq_fin : DecidableEq σ × Fintype σ
  δ : σ → α → σ
  start : σ
  accepting : σ → Bool

variable {α : Type} [Fintype α] [Nonempty α]

namespace Dfa

def empty (M : Dfa α) : Bool :=
  !(reaches_accepting M {M.start})
where
  reaches_accepting (M : Dfa
  α) (states : Finset M.σ) : Bool :=
    if states.fold Bool.or false (M.accepting ·) then true
    else
      have ⟨_, _⟩ := M.σ_deq_fin
      let next := states.sup (fun s => Finset.univ.image (M.δ s ·))
      let acc := next ∪ states
      if acc.card ≤ states.card then false else reaches_accepting M acc
  termination_by
    have := M.σ_deq_fin.2
    (Fintype.card M.σ) - states.card
  decreasing_by
    /-
      We modify the termination proof to use `grind` instead of doing it
      manually. `grind` is aware of `Finset.card_le_univ`, but if we apply it
      (as `grind` would) letting it infer its implicit arguments then it infers
      a new instance of `Finset M.σ` other than the one in `M.σ_deq_fin.2`. As
      we discussed in `L18_ProofAdvice`, different instances can behave
      differently and so Lean cannot assume the result of the new `Finset.card`
      relates to the `Finset.card` in the code from the function body, which
      uses the instance of `Finset M.σ` stored in `M.σ_deq_fin.2`. Therefore we
      have to instantiate `Finset.card_le_univ` ourselves with explicit
      arguments to make sure it uses the right instance. Figuring this all out
      was made more difficult by the fact that the Lean pretty-printer made both
      versions of `Fintype.card M.σ` look exactly the same, without showing that
      they were using different instances. I figured it out (1) because the
      `grind` failure message included an "issues" segment that mentioned being
      unable to reconcile different instances; and (2) by using `generalize` to
      rewrite expressions as variables, which exposed the fact that I could
      rewrite one `Finset.card` expression but not the other. -/
    have := @Finset.card_le_univ M.σ M.σ_deq_fin.2 acc
    grind

#check Finset.card_le_univ
