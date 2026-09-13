/-
  # Example for `L14`: Revisiting DFA with `grind`
-/

import Course.CourseLib

@[grind cases]
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

@[grind, simp]
def runsto (M : Dfa α) (σ : M.σ) (w : List α) : M.σ :=
  w.foldl M.δ σ

@[grind, simp]
def accepts (M : Dfa α) (w : List α) : Bool :=
  M.accepting (M.runsto M.start w)

@[grind, simp]
def compl (M : Dfa α) : Dfa α :=
  { M with accepting := fun s => !(M.accepting s) }

@[grind, simp]
def union (M1 M2 : Dfa α) : Dfa α :=
  have (_, _) := M1.σ_deq_fin
  have (_, _) := M2.σ_deq_fin
  { σ := M1.σ × M2.σ
    σ_deq_fin := ⟨inferInstance, inferInstance⟩
    δ := fun (σ₁, σ₂) a => (M1.δ σ₁ a, M2.δ σ₂ a)
    start := (M1.start, M2.start)
    accepting := fun (σ₁, σ₂) => M1.accepting σ₁ || M2.accepting σ₂ }

@[grind, simp]
def intersect (M1 M2 : Dfa α) : Dfa α :=
  Dfa.compl (Dfa.union (Dfa.compl M1) (Dfa.compl M2))

@[grind, simp]
def empty (M : Dfa α) : Bool :=
  !(reaches_accepting M {M.start})
where
  @[grind] -- _not_ `simp` because recursive
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
    have ⟨_, _⟩ := M.σ_deq_fin
    have := Finset.card_le_univ acc
    lia

@[grind, simp]
def equals (M1 M2 : Dfa α) : Bool :=
  (M1.intersect M2.compl).empty &&
  (M2.intersect M1.compl).empty

end Dfa

abbrev Language (α : Type) [Fintype α] [Nonempty α] :=
  Set (List α)

instance : Mul (Language α) := ⟨Set.image2 (· ++ ·)⟩

@[grind, simp]
def kleene_star (L : Language α) : Language α :=
  { w : List α | ∃ ℓ : List (List α), w = ℓ.flatten ∧ ∀ w' ∈ ℓ, w' ∈ L }

namespace Dfa

@[grind cases, grind intro]
inductive RunsTo (M : Dfa α) : M.σ → List α → M.σ → Prop where
  | empty σ : RunsTo M σ [] σ
  | step {σ₁ σ₂ σ₃ w a} : RunsTo M σ₁ w σ₂ → M.δ σ₂ a = σ₃ → RunsTo M σ₁ (w ++ [a]) σ₃

@[grind, simp]
def accepts_prop (M : Dfa α) (w : List α) : Prop :=
  ∃ σ, M.RunsTo M.start w σ ∧ M.accepting σ

@[grind, simp]
def L (M : Dfa α) : Language α :=
  { w : List α | M.accepts_prop w }

/-
  -----------------------------------------------------------
  PROOFS
  -----------------------------------------------------------
-/

attribute [simp] RunsTo.empty
attribute [simp] RunsTo.step
attribute [simp] accepts_prop

namespace RunsTo

@[grind →]
lemma runsto_equiv₁
  {M : Dfa α} {σ₁ σ₂ : M.σ} {w : List α}
  : M.RunsTo σ₁ w σ₂ → M.runsto σ₁ w = σ₂
:= by
  intro h
  induction h with simp_all

@[grind .]
lemma runsto_equiv₂
  {M : Dfa α} {σ₁ σ₂ : M.σ} {w : List α}
  : M.runsto σ₁ w = σ₂ → M.RunsTo σ₁ w σ₂
:= by induction w using List.reverseRecOn generalizing σ₂ with grind

lemma runsto_equiv
  {M : Dfa α} {σ₁ σ₂ : M.σ} {w : List α}
  : M.RunsTo σ₁ w σ₂ ↔ M.runsto σ₁ w = σ₂
:= ⟨runsto_equiv₁, runsto_equiv₂⟩

end RunsTo

@[grind →]
lemma accepts_of_accepts_prop
  {M : Dfa α} {w : List α}
  : M.accepts_prop w → M.accepts w
:= by simp_all [RunsTo.runsto_equiv]

@[grind →]
lemma accepts_prop_of_accepts
  {M : Dfa α} {w : List α}
  : M.accepts w → M.accepts_prop w
:= by grind

@[grind =, simp]
theorem accepts_is_correct
  {M : Dfa α} {w : List α}
  : M.accepts_prop w ↔ M.accepts w
:= ⟨accepts_of_accepts_prop, accepts_prop_of_accepts⟩

@[grind =, simp]
theorem compl_is_correct {M : Dfa α} : M.compl.L = M.Lᶜ := by
  ext; simp [RunsTo.runsto_equiv]

@[grind .]
lemma fold_pairing
  {M1 M2 : Dfa α} {w : List α}
  : let paired := w.foldl
      (fun σ a => (M1.δ σ.1 a, M2.δ σ.2 a))
      (M1.start, M2.start)
    paired.1 = w.foldl M1.δ M1.start ∧ paired.2 = w.foldl M2.δ M2.start
:= by induction w using List.reverseRecOn with simp_all

@[grind =, simp]
theorem union_is_correct
  {M1 M2 : Dfa α}
  : (M1.union M2).L = M1.L ∪ M2.L
:= by ext; simp [RunsTo.runsto_equiv]; grind

@[grind =, simp]
theorem intersect_is_correct
  {M1 M2 : Dfa α}
  : (M1.intersect M2).L = M1.L ∩ M2.L
:= by
  unfold intersect
  grind

abbrev Reached (M : Dfa α) :=
  { S : Finset M.σ // ∀ σ ∈ S, ∃ w, M.RunsTo M.start w σ }

@[grind .]
lemma start_is_reached
  {M : Dfa α}
  : ∀ σ ∈ ({M.start} : Finset M.σ), ∃ w, M.RunsTo M.start w σ
:= by simp [RunsTo.runsto_equiv]; exists []

@[grind, simp]
def empty_v2 (M : Dfa α) : Bool :=
  let init := ⟨{M.start}, start_is_reached⟩
  let reached := reaches init
  let accepting := reached.val.filter (M.accepting ·)
  !accepting.Nonempty
where
  @[grind]
  reaches (S : M.Reached) : M.Reached :=
      have ⟨_, _⟩ := M.σ_deq_fin
      let next : M.Reached :=
        ⟨S.val.sup (fun s => Finset.univ.image (M.δ s ·)), by
          intro σ hσ
          simp_all
          obtain ⟨σ₁, hσ₁, a, ha⟩ := hσ
          obtain ⟨w, hw⟩ := S.property σ₁ hσ₁
          exists (w ++ [a])
          grind⟩
      let acc := ⟨next.val ∪ S.val, by grind⟩
      let acc_set : Finset M.σ := acc.val
      let S_set : Finset M.σ := S.val
      if acc_set.card ≤ S_set.card then acc else reaches acc
  termination_by
    have := M.σ_deq_fin.2
    (Fintype.card M.σ) - S.val.card
  decreasing_by
    have ⟨_, _⟩ := M.σ_deq_fin
    have := Finset.card_le_univ acc.val
    lia

open empty_v2

lemma reaches_complete
  {M : Dfa α} {σ₁ σ₂ : M.σ} {S : M.Reached} {a : α}
  : σ₁ ∈ (reaches M S).val → M.δ σ₁ a = σ₂ → σ₂ ∈ (reaches M S).val
:= by
  fun_induction reaches M S with
  | case1 S _ _ _ next acc _ _ h1 =>
    intro h2 h3
    have : S.val = acc.val := by
      simp only [acc]
      exact Finset.eq_of_subset_of_card_le (by simp) h1
    simp [acc, next]
    grind
  | case2 => simp_all

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
  | case2 S _ _ _ next acc acc_set S_set h1 ih => grind

@[grind →]
lemma reaches_if_runsto
  {M : Dfa α} {σ₁ σ₂ : M.σ} {w : List α} {S : M.Reached}
  : M.RunsTo σ₁ w σ₂ → σ₁ ∈ S.val → σ₂ ∈ (reaches M S).val
:= by
  intro h1 h2
  induction h1 with
  | empty => exact reaches_monotone h2
  | step h3 h4 ih => exact reaches_complete ih h4

/-
  `grind` isn't very good at picking out specific objects to use for existential
  witnesses or to instantiate a universally quantified given. It can do it
  sometimes by brute force, but sometimes, as in the example below, we need to
  help it. -/
theorem empty_is_correct {M : Dfa α} : M.empty_v2 ↔ M.L = {} := by
  constructor
  case mp =>
    intro h1
    by_contra h2
    simp_all
    push Not at h2
    obtain ⟨w, σ, hσ1, hσ2⟩ := h2
    have := h1 (reaches_if_runsto hσ1 (by grind))
    grind
  case mpr =>
    intro h1
    by_contra h2
    simp_all
    obtain ⟨σ, hσ1, hσ2⟩ := h2
    let S := (reaches M ⟨{M.start}, start_is_reached⟩)
    obtain ⟨w, hw⟩ := S.property σ hσ1
    rw [Set.eq_empty_iff_forall_notMem] at h1
    replace h1 := h1 w
    grind

def equals_v2 (M1 M2 : Dfa α) : Bool :=
  (M1.intersect M2.compl).empty_v2 &&
  (M2.intersect M1.compl).empty_v2

theorem equals_is_correct
  {M1 M2 : Dfa α}
  : M1.equals_v2 M2 ↔ M1.L = M2.L
:= by
  unfold equals_v2
  rw [Bool.and_eq_true,
    empty_is_correct, intersect_is_correct, compl_is_correct,
    empty_is_correct, intersect_is_correct, compl_is_correct,
    ← Set.sdiff_eq, ← Set.sdiff_eq, Set.sdiff_eq_empty, Set.sdiff_eq_empty]
  grind

end Dfa
