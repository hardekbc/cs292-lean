/-
  # Revisiting DFA

  We re-implement `Dfa` using dependent types and see what that changes
-/

import Course.CourseLib

/-
  -----------------------------------------------------------
  IMPLEMENTATION
  -----------------------------------------------------------
-/

/-
  Instead of `ℕ` we allow states to be any finite type with decidable equality.
  Note that since `σ` is a field, we have to make the type class instances
  fields as well. `Dfa` is a dependent type because the type of the fields
  depends on the argument given for `σ` when making the `Dfa`. We require
  decidable equality on states because we'll be using `Finset` to hold sets of
  states, which requires decidable equality. Note that this definition means
  that the type `σ` has exactly as many elements as there are states, and so we
  cannot make the kinds of errors that we could with the previous version. -/
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

/-
  `runsto` becomes a dependent function -/
def runsto (M : Dfa α) (σ : M.σ) (w : List α) : M.σ :=
  w.foldl M.δ σ

/- Same as `L09_DFA` -/
def accepts (M : Dfa α) (w : List α) : Bool :=
  M.accepting (M.runsto M.start w)

/- Same as `L09_DFA` -/
def compl (M : Dfa α) : Dfa α :=
  { M with accepting := fun s => !(M.accepting s) }

/-
  Here we see a benefit of our new `Dfa` definition. The state type for the
  union of `M1` and `M2` is the type of pairs of states from `M1` and `M2`,
  directly following the standard definition of DFA union. -/
def union (M1 M2 : Dfa α) : Dfa α :=
  /-
    We need to bring these facts into the local context so that Lean can infer
    them where they are needed, specifically `inferInstance` which will try to
    infer instances of `DecidableEq` and `Fintype` for `M1.σ × M2.σ` based on
    the instances given in `M1.σ_deq_fin` and `M2.σ_deq_fin` -/
  have (_, _) := M1.σ_deq_fin
  have (_, _) := M2.σ_deq_fin
  { σ := M1.σ × M2.σ
    σ_deq_fin := ⟨inferInstance, inferInstance⟩
    δ := fun (σ₁, σ₂) a => (M1.δ σ₁ a, M2.δ σ₂ a)
    start := (M1.start, M2.start)
    accepting := fun (σ₁, σ₂) => M1.accepting σ₁ || M2.accepting σ₂ }

/- Same as `L09_DFA` -/
def intersect (M1 M2 : Dfa α) : Dfa α :=
  Dfa.compl (Dfa.union (Dfa.compl M1) (Dfa.compl M2))

/-
  Now that we are guaranteed finite states we can prove termination instead of
  using clocked recursion -/
def empty (M : Dfa α) : Bool :=
  !(reaches_accepting {M.start})
where
  /-
    Now that we aren't using clocked recursion we need to slightly change the
    way that the function works: instead of just passing on the _next_ set of
    states, we want to pass on the _union_ of the current and next sets of
    states, and have the recursion end if the union is the same as the current
    set of states. We use the set cardinality to check the ending condition to
    make the  termination proof a little easier. This change means that the
    `states` argument is monotonically increasing in terms of its size, and
    since there are only a finite number of possible elements it can only
    increase a finite number of times before the function must termination. -/
  reaches_accepting (states : Finset M.σ) : Bool :=
    if states.fold Bool.or false (M.accepting ·) then true
    else
      /-
        We need to make the type class instances available in this scope so the
        various operations can infer them appropriately; that's what the `have`
        below is for -/
      have ⟨_, _⟩ := M.σ_deq_fin
      let next := states.sup (fun s => Finset.univ.image (M.δ s ·))
      let acc := next ∪ states
      if acc.card ≤ states.card then false else reaches_accepting acc
  termination_by
    /-
      Our termination proof is based on set cardinality (`card`). `Fintype.card`
      is the cardinality of the finite set, i.e., the largest a set of that type
      can possibly get. As long as `states.card` is increasing, the expression
      `(Fintype.card M.σ) - states.card` is decreasing towards 0. -/
    have := M.σ_deq_fin.2
    (Fintype.card M.σ) - states.card
  decreasing_by
    /-
      `Finset.card_le_univ` provides an important fact about finite sets that we
      need for our proof. However, we need to bring `M`s type class instances
      into the local scope so that it can infer them correctly. -/
    have ⟨_, _⟩ := M.σ_deq_fin
    have := Finset.card_le_univ acc
    lia

/- Same as `L09_DFA` -/
def equals (M1 M2 : Dfa α) : Bool :=
  (M1.intersect M2.compl).empty &&
  (M2.intersect M1.compl).empty

end Dfa

/-
  -----------------------------------------------------------
  FORMALIZATION (same as `L09_DFA`)
  -----------------------------------------------------------
-/

abbrev Language (α : Type) [Fintype α] [Nonempty α] :=
  Set (List α)

instance : Mul (Language α) := ⟨Set.image2 (· ++ ·)⟩

def kleene_star (L : Language α) : Language α :=
  { w : List α | ∃ ℓ : List (List α), w = ℓ.flatten ∧ ∀ w' ∈ ℓ, w' ≠ [] ∧ w' ∈ L }

namespace Dfa

inductive RunsTo (M : Dfa α) : M.σ → List α → M.σ → Prop where
  | empty σ : RunsTo M σ [] σ
  | step {σ₁ σ₂ σ₃ w a} : RunsTo M σ₁ w σ₂ → M.δ σ₂ a = σ₃ → RunsTo M σ₁ (w ++ [a]) σ₃

def accepts_prop (M : Dfa α) (w : List α) : Prop :=
  ∃ σ, M.RunsTo M.start w σ ∧ M.accepting σ

def L (M : Dfa α) : Language α :=
  { w : List α | M.accepts_prop w }

/-
  -----------------------------------------------------------
  PROOFS
  -----------------------------------------------------------
-/

/-
  The following are all the same as `L09_DFA` up until we get to the proof of
  `union` -/

attribute [simp] compl
attribute [simp] union
attribute [simp] intersect
attribute [simp] empty
attribute [simp] empty.reaches_accepting
attribute [simp] equals
attribute [simp] kleene_star
attribute [simp] RunsTo.empty
attribute [simp] RunsTo.step
attribute [simp] accepts_prop
attribute [simp] L
attribute [simp] runsto
attribute [simp] accepts

namespace RunsTo

/- Same as `L09_DFA` -/
lemma runsto_equiv₁
  {M : Dfa α} {σ₁ σ₂ : M.σ} {w : List α}
  : M.RunsTo σ₁ w σ₂ → M.runsto σ₁ w = σ₂
:= by
  intro h
  induction h with simp_all

/- Same as `L09_DFA` -/
lemma runsto_equiv₂
  {M : Dfa α} {σ₁ σ₂ : M.σ} {w : List α}
  : M.runsto σ₁ w = σ₂ → M.RunsTo σ₁ w σ₂
:= by
  induction w using List.reverseRecOn generalizing σ₂ with
  | nil => simp_all
  | append_singleton as a ih =>
    intro h
    simp_all
    exact RunsTo.step ih h

/- Same as `L09_DFA` -/
lemma runsto_equiv
  {M : Dfa α} {σ₁ σ₂ : M.σ} {w : List α}
  : M.RunsTo σ₁ w σ₂ ↔ M.runsto σ₁ w = σ₂
:= ⟨runsto_equiv₁, runsto_equiv₂⟩

end RunsTo

/- Same as `L09_DFA` -/
lemma accepts_of_accepts_prop
  {M : Dfa α} {w : List α}
  : M.accepts_prop w → M.accepts w
:= by simp_all [RunsTo.runsto_equiv]

/- Same as `L09_DFA` -/
lemma accepts_prop_of_accepts
  {M : Dfa α} {w : List α}
  : M.accepts w → M.accepts_prop w
:= by
  intro h
  let σ := M.runsto M.start w
  exists σ
  have : M.RunsTo M.start w σ := RunsTo.runsto_equiv.2 (by simp [σ])
  simp_all [σ]

/- Same as `L09_DFA` -/
theorem accepts_is_correct
  {M : Dfa α} {w : List α}
  : M.accepts_prop w ↔ M.accepts w
:= ⟨accepts_of_accepts_prop, accepts_prop_of_accepts⟩

/- Same as `L09_DFA` -/
theorem compl_is_correct {M : Dfa α} : M.compl.L = M.Lᶜ := by
  ext
  simp [RunsTo.runsto_equiv]

/-
  **NEW PROOF FOR UNION**
  Structured similarly to the one from `L09_DFA` but does not require any axioms
  and the cases of the induction can be solved entirely by `simp_all`. Note that
  we are using the `List.reverseRecOn` induction principle again.
-/
lemma fold_pairing
  {M1 M2 : Dfa α} {w : List α}
  : let paired := w.foldl
      (fun σ a => (M1.δ σ.1 a, M2.δ σ.2 a))
      (M1.start, M2.start)
    paired.1 = w.foldl M1.δ M1.start ∧ paired.2 = w.foldl M2.δ M2.start
:= by induction w using List.reverseRecOn with simp_all

theorem union_is_correct
  {M1 M2 : Dfa α}
  : (M1.union M2).L = M1.L ∪ M2.L
:= by
  ext
  simp [RunsTo.runsto_equiv]
  rw [fold_pairing.1, fold_pairing.2]

/-
  Same as `L09_DFA` -/
theorem intersect_is_correct
  {M1 M2 : Dfa α}
  : (M1.intersect M2).L = M1.L ∩ M2.L
:= by
  unfold intersect
  rw [compl_is_correct, union_is_correct, compl_is_correct, compl_is_correct]
  simp_all

/-
  **NEW PROOF FOR EMPTY**
  Now that we have guaranteed finite types we can actually prove that `empty`
  is correct.

  Before we do, let's consider what we need to show in order to prove that
  `empty` is correct. The idea of `empty` is to compute all states reachable
  from the starting state and see if any of them are accepting states; if not
  then the language of the DFA is empty. Conversely, if the language is empty
  then there will be no reachable accepting states.

  How do we show that these two things imply each other? The language being
  empty means, according to our definitions above, that there is no word `w` and
  state `σ` s.t. `M.RunsTo M.start w σ ∧ M.accepting σ`. So we need to make a
  connection between `RunsTo` and `empty`, or more precisely, between `RunsTo`
  and `empty.reaches_accepting`. There are various ways we could do this, but I
  will take advantage of the opportunity to introduce a new concept: _subtypes_.
  We will use subtypes to create a new version of `empty` that is more amenable
  to the proofs we need to do.
-/

/-
  Here is an example of a subtype. A subtype is a dependent pair of some value
  `x` and a proposition on that value `P x`. It is implemented as a structure
  with two fields: `val` and `property`. The `Reached` subtype is the type of
  finite sets of states s.t. for each state in the set, there is some word `w`
  that proves `M` runs to that state beginning from the start state. Notice that
  since we've defined `Reached` in the `Dfa` namespace we can use dot notation,
  i.e., `M.Reached`. -/
abbrev Reached (M : Dfa α) :=
  { S : Finset M.σ // ∀ σ ∈ S, ∃ w, M.RunsTo M.start w σ }

/-
  This lemma will be useful for reasons that will become apparent in a bit -/
lemma start_is_reached
  {M : Dfa α}
  : ∀ σ ∈ ({M.start} : Finset M.σ), ∃ w, M.RunsTo M.start w σ
:= by simp; exists []; simp

/-
  Here's what we'll do. Instead of `reaches_accepting` that returns a `Bool`
  indicating whether an accepting state is reachable, we'll have `reaches` that
  returns the set of reachable states. Not just that, we'll use subtypes to have
  `reaches` return a _proof_ that for every state it returns, there is some word
  `w` that proves `M` runs to that state beginning from the start state (i.e.,
  the property of the `Reached` subtype). We'll annotate `empty_v2` for `simp`,
  but will _not_ annotate `reaches` for `simp`: remember that `simp` can go into
  an infinite loop when unfolding recursive functions. -/
@[simp]
def empty_v2 (M : Dfa α) : Bool :=
  /-
    Our initial value is an element of the subtype; we need to prove that
    `{M.start}` satisfies the property. This is why we need the
    `start_is_reached` lemma (I'll explain why it's a separate lemma and not
    inlined here shortly). -/
  let init := ⟨{M.start}, start_is_reached⟩
  /-
    We then compute the reachable states using `reaches` -/
  let reached := reaches M init
  /-
    Then we filter the reachable states to keep only those that are accepting
    states. Notice that we use `reached.val` to project out the value part of
    the subtype pair. -/
  let accepting := reached.val.filter (M.accepting ·)
  /-
    Finally, the language is empty if `accepting` is not non-empty (this is a
    bit convoluted, but the easiest way that I could find to do it because we
    need to return a `Bool` not a `Prop`) -/
  !accepting.Nonempty
where
  /-
    Notice the new signature: `reaches` takes a `Reached` subtype and returns a
    `Reached` subtype. Also, instead of stopping as soon as we reach an
    accepting state we'll keep going so we get all reachable states (it's less
    efficient, but easier for our proofs). -/
  reaches (M : Dfa α) (S : M.Reached) : M.Reached :=
      have ⟨_, _⟩ := M.σ_deq_fin
      /-
        The next set of states is computed the same way as before, but now we
        also prove that the resulting states have the desired property. Notice
        that we project out the `property` field of the subtype to help. -/
      let next : M.Reached :=
        ⟨S.val.sup (fun s => Finset.univ.image (M.δ s ·)), by
          intro σ hσ
          simp_all
          obtain ⟨σ₁, hσ₁, a, ha⟩ := hσ
          obtain ⟨w, hw⟩ := S.property σ₁ hσ₁
          exists (w ++ [a])
          exact RunsTo.step hw ha⟩
      /-
        The accumulated set of states is also computed the same as before, but
        we also need to prove the desired property -/
      let acc := ⟨next.val ∪ S.val, by
          simp
          intro σ hσ
          cases hσ with
          | inl h => exact next.property σ h
          | inr h => exact S.property σ h⟩
      /-
        These two following `let` are necessary to prevent a typeclass inference
        error in the `if` guard. Specifically, they make the intended types
        clear instead of asking Lean to infer them: try removing the type
        ascription `: Fintype M.σ` from the line below to see the error. -/
      let acc_set : Finset M.σ := acc.val
      let S_set : Finset M.σ := S.val
      /-
        The `if-else` is the same except we return the set of reached states
        instead of a `Bool` for the true branch -/
      if acc_set.card ≤ S_set.card then acc else reaches M acc
  termination_by
    have := M.σ_deq_fin.2
    (Fintype.card M.σ) - S.val.card
  decreasing_by
    have ⟨_, _⟩ := M.σ_deq_fin
    have := Finset.card_le_univ acc.val
    lia

/-
  Make `empty_v2.reaches` available as just `reaches`, for convenience -/
open empty_v2

/-
  We will need a couple of lemmas about `reaches` that will help us show that
  its result contains all reachable states. This first one says that if a state
  `σ₁` is in the result of `reaches` and there is another state `σ₂` reachable
  from `σ₁`, then `σ₂` is also in `reaches`. -/
lemma reaches_complete
  {M : Dfa α} {σ₁ σ₂ : M.σ} {S : M.Reached} {a : α}
  : σ₁ ∈ (reaches M S).val → M.δ σ₁ a = σ₂ → σ₂ ∈ (reaches M S).val
:= by
  fun_induction reaches M S with
  | case1 S _ _ _ next acc _ _ h1 =>
    intro h2 h3
    simp [acc, next]
    left
    have : S.val = acc.val := by
      simp only [acc]
      exact Finset.eq_of_subset_of_card_le (by simp) h1
    exists σ₁
    constructor
    · simp_all
    · exists a
  | case2 => simp_all

/-
  This second one says that if a state `σ` is in the initial set given to
  `reaches`, then `σ` is contained in the result of `reaches` -/
lemma reaches_monotone
  {M : Dfa α} {σ : M.σ} {S : M.Reached}
  : σ ∈ S.val → σ ∈ (reaches M S).val
:= by
  intro h2
  fun_induction reaches M S with
  | case1 S _ _ _ next acc acc_set S_set h1 =>
    have : S.val = acc.val := by
      simp only [acc]
      exact Finset.eq_of_subset_of_card_le (by simp) h1
    simp_all
  | case2 S _ _ _ next acc acc_set S_set h1 ih =>
    simp_all only [acc]
    exact ih (by simp_all)

/-
  And now we can prove that if `RunsTo` says that a state is reachable then
  `reaches` agrees -/
lemma reaches_if_runsto
  {M : Dfa α} {σ₁ σ₂ : M.σ} {w : List α} {S : M.Reached}
  : M.RunsTo σ₁ w σ₂ → σ₁ ∈ S.val → σ₂ ∈ (reaches M S).val
:= by
  intro h1 h2
  induction h1 with
  | empty => exact reaches_monotone h2
  | step h3 h4 ih => exact reaches_complete ih h4

/-
  And finally the theorem we've been working up to -/
theorem empty_is_correct {M : Dfa α} : M.empty_v2 ↔ M.L = {} := by
  constructor
  case mp =>
    simp_all
    intro h1
    by_contra h2
    push Not at h2
    obtain ⟨w, σ, hσ1, hσ2⟩ := h2
    let init : M.Reached := ⟨{M.start}, start_is_reached⟩
    have h2 : M.start ∈ init.val := Finset.mem_singleton.2 (by simp)
    have h3 := h1 (reaches_if_runsto hσ1 h2)
    rw [hσ2] at h3
    contradiction
  case mpr =>
    intro h1
    by_contra h2
    simp_all
    obtain ⟨σ, hσ1, hσ2⟩ := h2
    /-
      We need a name for this expression, and use `let` to make one. This `let`
      is why I pulled out `start_is_reached` as a separate lemma, so I could
      refer to it here. -/
    let S := (reaches M ⟨{M.start}, start_is_reached⟩)
    obtain ⟨w, hw⟩ := S.property σ hσ1
    rw [Set.eq_empty_iff_forall_notMem] at h1
    replace h1 := h1 w
    simp at h1
    replace h1 := h1 σ hw
    rw [hσ2] at h1
    contradiction

/-
  **NEW PROOF FOR EQUALS**
  We can also now prove that `equals` is correct
-/

/-
  Because we made a new version of `empty` we also need to make a new version of
  `equals`; the only change is that we call `empty_v2` instead of `empty` -/
def equals_v2 (M1 M2 : Dfa α) : Bool :=
  (M1.intersect M2.compl).empty_v2 &&
  (M2.intersect M1.compl).empty_v2

/-
  Note that I use `unfold` instead of `simp`, because `simp` would simplify the
  terms _too_ much; `unfold` lets me then apply a bunch of relevant theorems.
  Remember that for `rw` the order of the theorems is important; each theorem
  rewrites the result of the rewrite before it. -/
theorem equals_is_correct
  {M1 M2 : Dfa α}
  : M1.equals_v2 M2 ↔ M1.L = M2.L
:= by
  unfold equals_v2
  rw [Bool.and_eq_true,
    empty_is_correct, intersect_is_correct, compl_is_correct,
    empty_is_correct, intersect_is_correct, compl_is_correct,
    ← Set.sdiff_eq, ← Set.sdiff_eq, Set.sdiff_eq_empty, Set.sdiff_eq_empty]
  constructor
  case mp =>
    intro h
    exact Set.eq_of_subset_of_subset h.1 h.2
  case mpr =>
    intro h
    rw [h]
    simp

end Dfa
