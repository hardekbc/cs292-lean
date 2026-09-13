/-
  # Intro to Theorem-Proving in Lean

  - We will begin with proving theorems at the level of an introduction to discrete math course, e.g., propositional and predicate logic and properties of natural numbers, sets, relations, and functions

    + I assume you are all familiar with the material, the main point is to show how to state and prove these theorems _in Lean_

    + Later we'll start defining and proving properties about more Computer Science related topics, like algorithms and data structures, computability theory, programming language implementations, etc

  - For now Lean will just be "magic"; later on in the course you will gain an understanding of exactly how it all works

    + We will focus on _tactic-based_ proofs, where we can think of a _tactic_ as a command to manipulate the proof state in a certain way (this will make more sense when we see the examples below). We'll get into what tactics really are and how they work later in the course, as well as term-based proofs as an alternative to tactics.

    + There are in general many ways to write the same proof; I am giving you an opinionated guide here that shows only a few ways to avoid overwhelming you with options

  - To see how to type the various Unicode symbols below, hover over them in VS Code
-/

import Course.CourseLib

topic::PROPOSITIONAL_LOGIC
/-
  - For propositional logic we first need propositional variables, i.e., variables that stand for some arbitrary logical proposition

  - We say `(A : Prop)` to declare that `A` is some (unspecified) proposition, like `2 + 2 = 4`; we can declare multiple such variables at once using, e.g., `(A B C : Prop)`
-/
variable (A B C : Prop)

/-
  We then need the various logical connectives; we will focus on conjunction,
  disjunction, implication, and negation -/
#check A ∧ B
#check A ∨ B
#check A → B
#check ¬A

/-
  - We will demonstrate Lean with a series of examples, using the `example` keyword. The format is: `example <givens> : <goal> := by <proof>`

    + A given will look like `(<name> : <proposition>)`
    + A goal will just be a proposition
    + A proof will be a series of tactics deriving the goal from the givens
-/

/-
  Here is an example of an `example` proof. It has no givens, just a goal, which
  is about negation. To Lean a negation `¬A` is actually shorthand for an
  implication `A → False`; you can check the logical equivalence of the two
  statements yourself using a truth table. We prove it in Lean in the example
  below. Note how the _infoview_ panel in VS Code allows you to step through the
  proof and see the proof state before and after each step (if you don't have
  the panel open then open it by pressing `Ctrl + Shift + Enter` or clicking on
  the `∀` symbol at the top right and selecting `Toggle Infoview`). Also note
  that if we make a mistake in the proof then Lean will give an error message
  (try swapping `h1` and `h2` in the last line `exact h1 h2` to see the error
  message). You will understand what this proof is saying after we cover the
  topics below. -/
example : (¬A) ↔ (A → False) := by
  constructor
  · intro h1 h2
    contradiction
  · intro h1 h2
    exact h1 h2

/-
  Lean has powerful proof automation facilities, which we will cover later in
  the course. For now, we will only use them in select circumstances so that you
  have the opportunity to learn how to prove things yourself. -/
example : (¬A) ↔ (A → False) := by grind

/-
  For all of the examples below, step through the proofs using the infoview to
  see how the various tactics affect the proof state -/

subtopic::CONJUNCTION
/-
  A proof of a conjunction is a pair consisting of proofs of the left and right
  sides. We can extract proofs of the left and right sides from a proof of a
  conjunction using `obtain` as shown below. We are given a proof of `A ∧ B`
  named `h` and are asked to prove `A`. The `exact` tactic says that we are
  about to exactly prove the goal, and its argument is the proof of the goal. -/
example (h : A ∧ B) : A := by
  obtain ⟨hA, hB⟩ := h
  exact hA

/-
  If we have two proofs we can combine them into a pair to prove a conjunction
  goal, as shown below. We are given a proof of `A` and proof of `B` and are
  asked to prove `A ∧ B`. -/
example (hA : A) (hB : B) : A ∧ B := by
  exact ⟨hA, hB⟩

/-
  In this example we combine the two examples above -/
example (h : A ∧ B) : B ∧ A := by
  obtain ⟨hA, hB⟩ := h
  exact ⟨hB, hA⟩

/-
  Sometimes we have a conjunction as goal and don't yet have proofs of the two
  conjuncts; when this happens we can decompose the conjunction goal into two
  separate goals using `constructor` as shown below. Notice using the infoview
  that immediately after we use `constructor` we have removed the `B ∧ A` goal
  and replaced it with a `B` goal and a separate `A` goal. The `·` tells Lean to
  focus in on the next goal, allowing us to structure the proof and make it more
  readable. -/
example (h : A ∧ B) : B ∧ A := by
  obtain ⟨hA, hB⟩ := h
  constructor
  · exact hB
  · exact hA

/-
  When there are multiple goals we might want to name each goal explicitly
  instead of using `·`; we can do so using the `case` tactic. `case` takes the
  name of the goal being proved (as shown in the infoview). -/
example (h : A ∧ B) : B ∧ A := by
  obtain ⟨hA, hB⟩ := h
  constructor
  case left => exact hB
  case right => exact hA

end_subtopic CONJUNCTION


subtopic::IMPLICATION
/-
  A proof of an implication `A → B` means that given a proof of `A`, we can get
  a proof of `B`. We can therefore treat an implication like a function, where
  the antecedent is the argument and the consequent is the result. Note that we
  use the common functional language syntax for function calls where applying
  function `f` to arguments `a` and `b` is written `f a b`, _not_ `f(a, b)`. -/
example (h1 : A → B) (h2 : A) : B := by
  exact h1 h2

/-
  To prove an implication `A → B` we assume that we have a proof of `A` and show
  that we can derive a proof of `B`. We use the `intro` tactic to assume the
  antecedent and give that assumption a name. -/
example : A → A := by
  intro h
  exact h

/-
  We can use `intro` to assume multiple antecedents at once, and we can compose
  multiple function calls at once -/
example : (A → B) → (B → C) → (A → C) := by
  intro hAB hBC hA
  exact hBC (hAB hA)

/-
  The `contrapose` tactic will transform an implication goal into its
  contrapositive -/
example (h : A → B) : ¬B → ¬A := by
  contrapose
  exact h

/-
  A biimplication `A ↔ B` is essentially the conjunction `A → B ∧ B → A` (though
  Lean treats them slightly differently so we can't use conjunction and
  biimplication completely interchangeably). If we have a biimplication as a
  given then we can use `obtain` to get its constituent implications. -/
example (h : A ↔ B) (hA : A) : B := by
  obtain ⟨hAB, hBA⟩ := h
  exact hAB hA

/-
  And a biimplication as a goal can be proven using `⟨...⟩` -/
example (hAB : A → B) (hBA : B → A) : A ↔ B := by
  exact ⟨hAB, hBA⟩

/-
  Or by using `constructor` to break it into two separate goals. Note our use of
  `_`, which essentially means "don't care": we don't give an explicit name for
  these assumptions because we already have them as givens. -/
example (hA : A) (hB : B) : A ↔ B := by
  constructor
  · intro _
    exact hB
  · intro _
    exact hA

end_subtopic IMPLICATION


subtopic::DISJUNCTION
/-
  A proof of a disjunction `A ∨ B` is either a proof of `A` _or_ a proof of `B`,
  but we don't know which one. Given a disjunction we can prove a goal by cases:
  we assume the left side and prove the goal, and then we assume the right side
  and prove the same goal. The `cases` tactic takes a disjunction as its
  argument and transforms the current goal into two separate goals, one assuming
  the left side and one assuming the right side. In VS Code if you put the
  cursor immediately at the end of the `with`, a lightbulb will appear on the
  left; clicking it will show available code actions, including an auto-complete
  for generating the two cases. -/
example (h : A ∨ B) (hAC: A → C) (hBC : B → C) : C := by
  cases h with
  | inl hA => exact hAC hA
  | inr hB => exact hBC hB

/-
  To prove a disjunction `A ∨ B` we must prove either `A` or `B`. We can use the
  tactics `left` or `right` to indicate which one we will do. Tactics can be
  separated by `;`, which is the same as putting them on separate lines. -/
example (h : A ∨ B) : B ∨ A := by
  cases h with
  | inl hA => right; exact hA
  | inr hB => left; exact hB

/-
  Sometimes we want to do a proof by cases on `A ∨ ¬A` for some proposition `A`,
  but this disjunction is not in the list of givens. We can use `by_cases h : A`
  to do so, which will copy the current goal into two goals: one in the context
  where `h : A` and one in the context where `h : ¬A`. -/
example : A ∨ ¬A
:= by
  by_cases h : A
  case pos => left; exact h
  case neg => right; exact h

end_subtopic DISJUNCTION


subtopic::INTERLUDE_HAVE
/-
  So far we have only been able to create new givens using the `intro` tactic,
  but it can be convenient to prove intermediate results along the way to
  proving the final goal. The `have` tactic allows us to create new givens by
  proving them from the current givens. The form is:

  `have <name> : <proposition> := <proof>` _or_
  `have <name> : <proposition> := by <proof>`

  The first version is if the proof does not use tactics (so far that means
  proving a conjunction or biimplication with `⟨...⟩` or using an implication
  like a function call); the second is if it does use tactics (everything else
  we've covered).
-/

/-
  Here is an example where the `have` proof does not use tactics -/
example : (A → B) → (B → C) → (A → C) := by
  intro hAB hBC hA
  have hB : B := hAB hA
  exact hBC hB

/-
  Here is an example where it does use tactics -/
example (hA : A) (hB : B) : (A ∧ B) ∨ False := by
  have hAB : A ∧ B := by
    constructor
    · exact hA
    · exact hB
  left
  exact hAB

/-
  If the proposition being proved is obvious from the proof itself we can omit
  it, as in the example below. Note that the `have` does not explicitly say that
  `hB` is a proof of `B` but Lean infers it anyway, as can be seen in the
  infoview. -/
example : (A → B) → (B → C) → (A → C) := by
  intro hAB hBC hA
  have hB := hAB hA
  exact hBC hB

end_subtopic INTERLUDE_HAVE


subtopic::NEGATION
/-
  If we have a negation as a given or goal then often, if possible, we would
  like to rewrite it to remove the negation. We can use the `push Not` tactic
  for this purpose, on the goal or a specified given. -/

example (h : A ∧ B) : ¬(¬A ∨ ¬B) := by
  push Not
  exact h

example (hn : ¬(¬A ∨ ¬B)) : A ∧ B := by
  push Not at hn
  exact hn

/-
  Otherwise suppose we have a negation as a goal and we can't remove the
  negation. Then we can try proof by contradiction: assume the opposite and
  attempt to derive a contradiction. Recall that `¬A` is really `A → False`, so
  to assume the opposite in this case we can use `intro` just like we did for
  `→`. The `contradiction` tactic checks whether there are two givens that
  contradict each other, e.g., one is the negation of the other. -/
example (h : A → ¬B) (hA : A) : ¬B := by
  intro hB
  have hnB := h hA
  contradiction

/-
  If the negation is a given then you can still try proof by contradiction by
  trying to prove the opposite -/
example (hnA : ¬A) : A → B := by
  intro hA
  contradiction

/-
  Sometimes we wish to do a proof by contradiction but the goal isn't negated
  and there is no useful negation in the givens. If the current goal is `P`, we
  can use `by_contra h` to introduce the given `h : ¬P` and change the current
  goal to `False` (i.e., prove a contradiction). -/
example (h : ¬B → ¬A) (hA : A) : B := by
  by_contra h1
  have h2 := h h1
  contradiction

end_subtopic NEGATION


subtopic::USEFUL_THEOREMS
/-
  Here are some useful tactics and theorems we can use to manipulate the
  propositional connectives -/

 /-
   For theorems that use `↔` we can use the `rw` tactic (standing for "rewrite")
   to rewrite either a given or a goal that matches one side of the `↔` into the
   other side -/
#check @imp_iff_or
#check @imp_iff_not_or
#check @Classical.not_imp
#check @not_imp_not

/- Rewrite the goal -/
example (h : ¬A ∨ B) : A → B := by
  rw [imp_iff_not_or]
  exact h

/- Rewrite a given -/
example (h : A → B) : ¬A ∨ B := by
  rw [imp_iff_not_or] at h
  exact h

/- Rewrite in the other direction -/
example (h : A → B) : ¬A ∨ B := by
  rw [← imp_iff_not_or]
  exact h

/-
  For example, if we have a goal `A ∨ B` sometimes it's helpful to assume the
  negation of one disjunct and then prove the other; we can use `rw` with
  `imp_iff_or` to rewrite the disjunction into an implication `¬A → B` and then
  use `intro` to assume `¬A` while we prove `B` -/

/-
  `rw` also works for equalities, e.g., if there is a given `h : x = y` then we
  can use `rw` to rewrite an `x` into a `y` using `rw [h]`, or a `y` into an `x`
  using `rw [← h]`. However, `rw` is very sensitive to syntax: the thing being
  rewritten has to match one side of the `↔` or `=` _exactly_. -/

/-
  These theorems can be useful if we want to derive an implication from a
  given disjunction -/
#check @Or.resolve_left
#check @Or.resolve_right
#check @Or.neg_resolve_left
#check @Or.neg_resolve_right

/-
  - There are _many_ theorems in the Mathlib library, and they can be hard to find

  - One method is to use `exact?` or `apply?` (i.e., adding a question mark), which will cause Lean to search for a theorem that could solve the current goal

    + Note that it must completely solve the current goal or Lean won't find it, and that even if Lean finds something, it isn't guaranteed to be the simplest possible version

  - Another method is to use `Loogle!` (https://loogle.lean-lang.org/), a web search engine specifically for searching Mathlib

    + There is a Mathlib command for searching Loogle from within a Lean file: `#loogle`. It takes the same search input as described on the Loogle webpage (but truncates the results instead of returning all of them)

  - Another method is to use `LeanSearch` (https://leansearch.net/), a web search engine for Mathlib using natural language queries

    + There is a Mathlib command for using LeanSearch from within a Lean file: `#leansearch` (but it also truncates the results)

  - Finally, you could just guess the theorem name and see if it exists. This strategy isn't as silly as it sounds because Mathlib has very strict rules about how theorems are named that make the names fairly easy to guess (once you've internalized the rules): https://leanprover-community.github.io/contribute/naming.html.
-/

/-
  Look for theorems that involve both a disjunction and a negation of the left
  disjunct -/
#loogle ?a ∨ ?b, ¬?a

/-
  Look for theorems whose names contain the strings "Or" and "resolve" -/
#loogle "Or", "resolve"

/-
  A natural language search-/
#leansearch "a or b is the same as not a implies b."

end_subtopic USEFUL_THEOREMS
end_topic PROPOSITIONAL_LOGIC


topic::SETS
/-
  - Sets in Lean are always over some type: if `U` is a type (e.g., `ℕ`, `String`, etc) then a value of type `Set U` is a (possibly infinite) set whose elements are from `U`

    + I'll emphasize that `Set` in Lean includes _infinite_ sets, e.g., we can define the set of all prime numbers as:

      `def primes : Set ℕ := { p : ℕ | p > 1 ∧ ∀ n < p, Nat.gcd n p = 1 }`

    + In most languages the `Set` data structure is for finite sets; if we want something similar in Lean we would use, e.g., `Finset`, `HashSet`, or `TreeSet`

  - We say `(U : Type)` to mean that `U` is some type, `(S T : Set U)` to mean that `S` and `T` are sets whose elements are from `U`, and `(x : U)` to mean that `x` is of type `U`
-/
variable (U : Type) (S T : Set U) (x : U)

/- Set membership is a proposition -/
#check x ∈ S
#check x ∉ S

/- So is the subset relation -/
#check S ⊆ T
#check ¬(S ⊆ T)

/-
  We can use set operators such as `∪`, `∩`, and `\` (note that the last one is
  typed with a double backslash or `\setminus`, not a single backslash) -/
#check S ∪ T
#check S ∩ T
#check S \ T

/-
  - Membership propositions on set operations can be seen as propositions that use logical connectives:

    + `x ∈ S ∪ T` ≡ `x ∈ S ∨ x ∈ T`
    + `x ∈ S ∩ T` ≡ `x ∈ S ∧ x ∈ T`
    + `x ∈ S \ T` ≡ `x ∈ S ∧ ¬(x ∈ T)`

  - Also the subset relation:

    + `S ⊆ T` ≡ `x ∈ S → x ∈ T`

  - We can use the `whnf` ("weak head normal form") tactic to rewrite such propositions into their logical connective form

    + `whnf` by itself will rewrite the goal; `whnf at <name>` will rewrite the named given; `whnf at *` will rewrite everywhere

    + `whnf` only works if the target is directly a subset relation or a membership proposition on set operations (i.e., it doesn't do anything if the proposition is underneath a connective like `→` or `∧`)

    + `whnf` also works on other things besides set propositions to unfold their definitions, as we'll see later

  - Rewriting using `whnf` usually isn't necessary...you can continue the proof _as if_ the proposition is in its logical connective form even if it isn't, `whnf` just makes it more clear. There are some cases where it _is_ necessary, e.g., the `rw` tactic which requires that things syntactically match, where using `whnf` or not can be the difference between working or not working.
-/

/-
  Using `whnf` to rewrite a proposition in goal and given. Note that if we use
  `whnf` before the `intro` then nothing happens, because the main goal
  proposition is an implication and the relevant propositions are beneath it. -/
example : x ∈ S ∪ T → x ∈ T ∪ S
:= by
  whnf -- nothing happens
  intro h1
  whnf at *
  cases h1 with
  | inl h => right; exact h
  | inr h => left; exact h

/-
  Here is the same proof except we didn't bother rewriting the propositions.
  Even though `h1` is a proposition about `∪` we can still use the `cases`
  tactic as if it were a disjunction. -/
example : x ∈ S ∪ T → x ∈ T ∪ S
:= by
  intro h1
  cases h1 with
  | inl h => right; exact h
  | inr h => left; exact h

/-
  - Two sets `S` and `T` are equal iff `S ⊆ T ∧ T ⊆ S`. The _set extensionality_ principle encodes this definition: it says that `S = T` is the same as `x ∈ S ↔ x ∈ T` (for arbitrary object `x`).

    + The `ext` tactic applies the set extensionality principle (among other extensionality principles, e.g., function extentionality)
-/

/-
  Using set extensionality to prove two sets are equal. Note that we treat the
  set intersection as a conjunction without bothering to rewrite it. Also note
  that the two sub-proofs are identical---in a prose proof we would handwave the
  second sub-proof and say something like "similar to the first"; in Lean we
  can't do that, we have to give both proofs. This is annoying in the sense that
  we have to repeat ourselves, but it is useful in the sense that sometimes a
  "similar" proof doesn't turn out to be that similar in reality (and can even
  be unprovable). Proof automation can also help. -/
example : S ∩ T = T ∩ S
:= by
  ext a -- `a` is the name we give to the arbitrary object
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h
    exact ⟨h2, h1⟩
  · intro h
    obtain ⟨h1, h2⟩ := h
    exact ⟨h2, h1⟩

end_topic SETS


topic::PREDICATE_LOGIC
/-
  For predicate logic we add predicates and quantifers. A _predicate_ is a
  function from objects in some _universe of discourse_ to a proposition. In
  Lean, every predicate must make its universe of discourse explicit using
  types. In the example below, `is_42` is a predicate over natural numbers. -/
def is_42 (n : ℕ) := n = 42
#check (is_42)

/-
  We can quantify over predicates to get propositions via the universal and
  existential quantifiers -/
#check ∀ (n : ℕ), is_42 n
#check ∃ (n : ℕ), is_42 n

/-
  If the universe of discourse is obvious from the predicate we're quantifying
  over then we don't need to state it explicitly -/
#check ∀ n, is_42 n
#check ∃ n, is_42 n

/-
  We can create predicates that themselves use quantifiers -/

def even (n : ℤ) := ∃ (k : ℤ), 2*k = n
#check (even)

def prime (n : ℕ) := n > 1 ∧ ∀ k < n, Nat.gcd n k = 1
#check (prime)

/-
  A proof of a universally quantified predicate means we can get a proof for any
  object in the domain of discourse. To do so we treat it like function call
  (just like an implication, except that the argument is an object in the domain
  of discourse, not a proposition). Note in particular the use of the `lia`
  tactic, which stands for "linear integer arithmetic": it can solve a goal that
  is solely about, as the name implies, linear integer arithmetic. Also note
  that `∀ n ≤ 100, P n` is short for `∀ n, n ≤ 100 → P n`. -/
example (P : ℕ → Prop) (h : ∀ n ≤ 100, P n) : P 42 := by
  have h2 : 42 ≤ 100 := by lia
  exact h 42 h2

/-
  Proving a universally quantified predicate is also similar to proving an
  implication: we assume there is an arbitrary object from the domain of
  discourse using `intro` and prove the predicate is true about that object. -/
example : ∀ (n : ℕ), n ≤ 0 → n = 0 := by
  intro a ha -- we can use any name for the object, not just `n`
  lia

/-
  A proof of an existentially quantified predicate means that there is some
  (unknown) witness, i.e., an object in the domain of discourse for which the
  predicate is true. We can think of the proof as a pair of (witness, proof the
  predicate is true for the witness), and retrieve these pieces using `obtain`
  just like we did for conjunctions. -/
example
  (A : Prop) (P : ℕ → Prop)
  (h1 : ∃ x, P x) (h2 : ∀ x, P x → A) : A
:= by
  obtain ⟨a, ha⟩ := h1
  exact h2 a ha

/-
  To prove an existentially quantified predicate as a goal we need to provide a
  witness and then prove that the predicate holds for that witness. We use
  `exists` to supply the witness. `exists` will try to close the goal (i.e.,
  prove the witness is correct) automatically if it's easy to do so, otherwise
  we need to supply the proof manually. In this example the first `exists`
  cannot prove the goal automatically but the second one can. -/
example (P : ℕ → Prop) (h : P 42) : ∃ n, P n ∧ even n := by
  exists 42
  constructor
  · exact h
  · exists 21

end_topic PREDICATE_LOGIC


topic::EXAMPLES_SETS_AND_LOGIC
/-
  Proof examples about sets and logic -/

example
  (P Q R : Prop)
  (h : P → (Q → R))
  : ¬R → (P → ¬Q)
:= by
  intro h1 h2 h3
  have h4 := h h2 h3
  contradiction

example
  (U : Type) (A B C : Set U) (a : U)
  (h1 : a ∈ A)
  (h2 : a ∉ A \ B)
  (h3 : a ∈ B → a ∈ C)
  : a ∈ C
:= by
  have h4 : a ∈ B := by
    by_contra h4
    have h5 : a ∈ A \ B := ⟨h1, h4⟩
    contradiction
  exact h3 h4

example
  (U : Type) (A B C : Set U)
  (h1 : A ⊆ B ∪ C)
  (h2 : ∀ (x : U), x ∈ A → x ∉ B)
  : A ⊆ C
:= by
  whnf
  intro a hA
  have h3 := h1 hA
  whnf at h1 h3
  cases h3 with
  | inl h =>
    have h4 := h2 a hA
    contradiction
  | inr h => exact h

example
  (U : Type) (P Q : U → Prop)
  (h1 : ∀ (x : U), ∃ (y : U), P x → ¬ Q y)
  (h2 : ∃ (x : U), ∀ (y : U), P x → Q y)
  : ∃ (x : U), ¬P x
:= by
  obtain ⟨x, hx⟩ := h2
  obtain ⟨y, hy⟩ := h1 x
  have h2 := hx y
  exists x
  intro h3
  have h4 := hy h3
  have h5 := h2 h3
  contradiction

/-
  When we apply `whnf` to `h1` we see `∀ ⦃a : U⦄, a ∈ A → a ∈ B`: the `⦃...⦄`
  means that the argument will be automatically inferred by Lean, all we need to
  supply is a proof of `a ∈ A`. -/
example
  (U : Type) (A B C D : Set U)
  (h1 : A ⊆ B)
  (h2 : ¬∃ (c : U), c ∈ C ∩ D)
  : A ∩ C ⊆ B \ D
:= by
  push Not at h2
  whnf
  intro a hA
  whnf
  whnf at h1 hA
  constructor
  · exact h1 hA.left
  · intro h3
    have h4 := h2 a
    have h5 : a ∈ C ∩ D := ⟨hA.right, h3⟩
    contradiction

example
  (U : Type) (A B C : Set U)
  : A \ (B \ C) ⊆ (A \ B) ∪ C
:= by
  intro a hA
  whnf
  whnf at hA
  obtain ⟨h1, h2⟩ := hA
  by_cases h3 : a ∈ C
  · right
    exact h3
  · left
    whnf
    have h4 : a ∉ B := by
      intro h4
      have h5 : a ∈ B \ C := ⟨h4, h3⟩
      contradiction
    exact ⟨h1, h4⟩

example
  (U : Type) (A B C : Set U)
  (h1 : A ⊆ B ∪ C)
  (h2 : ¬∃ (x : U), x ∈ A ∩ B)
  : A ⊆ C
:= by
  push Not at h2
  whnf
  whnf at h1
  intro a hA
  have h3 := h1 hA
  have h4 := h2 a
  cases h3 with
  | inl h =>
    have h5 : a ∈ A ∩ B := ⟨hA, h⟩
    contradiction
  | inr h => exact h

/-
  Recall that `rw` works with both `↔` and `=`; here we use it with `=`. The
  `nlinarith` tactic works on (some) non-linear arithmetic expressions. -/
example : ∀ (a b c : ℤ), a ∣ b → b ∣ c → a ∣ c
:= by
  intro a b c h1 h2
  whnf
  whnf at h1 h2
  obtain ⟨k1, h3⟩ := h1
  obtain ⟨k2, h4⟩ := h2
  exists (k1 * k2)
  rw [h3] at h4
  nlinarith

example : ∀ (n : ℤ), 6 ∣ n ↔ 2 ∣ n ∧ 3 ∣ n
:= by
  intro n
  constructor
  · intro h1
    obtain ⟨k, h2⟩ := h1
    constructor
    · exists (3 * k)
      lia
    · exists (2 * k)
      lia
  · intro ⟨h1, h2⟩ -- `intro` can pattern-match like `obtain`
    obtain ⟨k1, h3⟩ := h1
    obtain ⟨k2, h4⟩ := h2
    exists (k1 / 3)
    lia

end_topic EXAMPLES_SETS_AND_LOGIC


topic::THEOREMS
open PREDICATE_LOGIC (is_42) -- makes `is_42` available from previous topic

/-
  - All of the examples we've given so far have used `example`, which allows us to prove things without giving a name for the proof under the assumption that we will never need to refer to that proof later

  - We can provide a name using `theorem`, which looks just like `example` except that we give a name to the proof we're creating
-/

/-
  Note a couple of new things in this example: we can decompose a proof into
  more than two pieces using `obtain`, and we can use tactics inside a `⟨...⟩`
  as long as we use `by` before them. Try removing the `, h2` from the `obtain`
  to see what that does to `h1` (besides giving an error because `h2` isn't
  defined anymore on the next line) -/
theorem example_thm (P : ℕ → Prop) (h : ∃n ≤ 50, P n) : ∃n ≤ 100, P n := by
  obtain ⟨a, h1, h2⟩ := h
  have h3 : a ≤ 100 ∧ P a := ⟨by lia, h2⟩
  exists a

/-
  - The benefit of giving a name is that we can use the theorem in other proofs. The following proof is silly, but demonstrates the concept: given a predicate `is_42` and a proof that `∃n ≤ 50, is_42 n`, we can supply them as arguments to the theorem `example_thm` and it returns a proof that `∃n ≤ 100, is_42 n`.

  - The `unfold` tactic replaces the name of a definition with its content. Unlike `whnf` it takes the name of the definition to be unfolded, and it works even if the name is underneath some other construct.

  - The `rfl` tactic ("reflexivity") proves that something equals itself. It is a more powerful tactic than it appears at first glance and we'll talk more about what equality means exactly later in the course.

  - Note that `example_thm` is expecting its second argument to be an existential proof, so we can use the `⟨...⟩` shorthand and Lean understands what we mean. Lean is also flexible enough to allow us to provide the conjunction proof `42 ≤ 50 ∧ is_42 42` separately as `h1` and `h2` instead of making us explicitly combine them into a conjunction first.
-/
example : ∃n ≤ 100, is_42 n := by
  have h1 : 42 ≤ 50 := by lia
  have h2 : is_42 42 := by
    unfold is_42
    rfl
  exact example_thm is_42 ⟨42, h1, h2⟩

/-
  We can also apply a theorem using `apply` if its conclusion matches the goal;
  `apply` will create new goals based on the premises of the theorem being
  applied. -/
example : ∃n ≤ 100, is_42 n := by
  apply example_thm
  exists 42

/-
  `apply` also has an `apply?` variant (like `exact?`) that will attempt to
  search for a theorem whose conclusion matches the current goal; this is
  another good way to discover relevant theorems. The result is not necessarily
  the _best_ answer (as seen below), but it can be useful -/

example : ∃n ≤ 100, is_42 n := by
  apply?

end_topic THEOREMS


topic::RELATIONS
/-
  - Binary relations are often described as a subset of the cartesian product of two sets, e.g., `R ⊆ S × T`. In Lean they can be represented in two ways:

    + With `SetRel α β`, where `α` and `β` are types. This definition uses a set of pairs as in the standard definition, i.e., `R : SetRel α β` means `R ⊆ Set (α × β)`

    + With `Rel α β`, where `α` and `β` are types. Under the hood `Rel α β` is defined as a binary predicate `α → β → Prop`.

  - We will use the standard definition, though the `Rel` definition can be convenient in certain cases and which one to use depends on context
-/

/- The type of a relation between natural numbers and integers -/
#check SetRel ℕ ℤ

/-
  A relation `SetRel α α` may be reflexive, symmetric, and/or transitive; we can
  describe these ideas using predicates -/

variable {α : Type}

/- Reflexivity -/
def is_refl (R : SetRel α α) :=
  ∀ (a : α), (a, a) ∈ R

/- Symmetry -/
def is_symm (R : SetRel α α) :=
  ∀ (a b : α), (a, b) ∈ R ↔ (b, a) ∈ R

/- Transitivity -/
def is_trans (R : SetRel α α) :=
  ∀ (a b c : α), (a, b) ∈ R → (b, c) ∈ R → (a, c) ∈ R

/-
  A relation that is all three is an equivalence relation -/
def eqrel (R : SetRel α α) :=
  is_refl R ∧ is_symm R ∧ is_trans R

/-
  Here is an example of proving that a relation is an equivalence relation -/

/-
  Relation: `n` and `m` are both even or both odd. We extract the first element
  of a pair using `.1` and the second using `.2`. We use _set comprehension_
  notation to define the set of pairs: `{ <var> : <type> | <proposition> }`. -/
def parity_matches : SetRel ℕ ℕ :=
  { pair : ℕ × ℕ | pair.1 % 2 = pair.2 % 2 }

/-
  Note that the `whnf` in the proofs below are unnecessary, I've put them in
  just to make the proof state more clear -/

/- `parity_matches` is reflexive -/
theorem pm_is_refl : is_refl parity_matches := by
  unfold is_refl parity_matches
  intro a
  whnf
  rfl

/- `parity_matches` is symmetric -/
theorem pm_is_symm : is_symm parity_matches := by
  unfold is_symm parity_matches
  intro a b
  constructor
  · intro h
    whnf at *
    lia
  · intro h
    whnf at *
    lia

/- `parity_matches` is transitive -/
theorem pm_is_trans : is_trans parity_matches := by
  unfold is_trans parity_matches
  intro a b c h1 h2
  whnf at *
  lia

/- `parity_matches` is an equivalence relation -/
theorem pm_is_eqrel : eqrel parity_matches := by
  exact ⟨pm_is_refl, pm_is_symm, pm_is_trans⟩

end_topic RELATIONS


topic::EXAMPLES_RELATIONS

variable {α β : Type}

/-
  `comp` is relational composition: `R.comp S` means `R ∘ S`, i.e., { (a,c) | ∃
  b, (a,b) ∈ R ∧ (b, c) ∈ S } -/

example
  (α β γ δ : Type)
  (R : SetRel α β) (S : SetRel β γ) (T : SetRel γ δ)
  : R.comp (S.comp T) = (R.comp S).comp T
:= by
  ext x
  constructor
  case mp =>
    intro h1
    whnf
    obtain ⟨b, h1, h2⟩ := h1
    obtain ⟨c, h2, h3⟩ := h2
    have h4 : (x.1, c) ∈ R.comp S := by exists b
    exists c
  case mpr =>
    intro h1
    obtain ⟨b, h1, h2⟩ := h1
    obtain ⟨c, h1, h3⟩ := h1
    whnf
    have h4 : (c, x.2) ∈ S.comp T := by exists b
    exists c

/-
  `inv` is relational inverse: `R.inv` mean { (b,a) | (a,b) ∈ R } -/

example
  (α β γ : Type)
  (R : SetRel α β) (S : SetRel β γ)
  : (R.comp S).inv = S.inv.comp R.inv
:= by
  ext x
  constructor
  case mp =>
    intro h1
    whnf at h1
    obtain ⟨b, h1, h2⟩ := h1
    whnf
    exists b
  case mpr =>
    intro h1
    obtain ⟨b, h1, h2⟩ := h1
    exists b

open RELATIONS (is_refl is_symm is_trans eqrel)

/-
  We can construct `ℤ` from `ℕ` by using pairs of natural numbers `(a, b)` to
  represent the integer `a - b`. However, then there are an infinite number of
  representations for every integer. We can show that all of these
  representations are equivalent to each other under the `SameInt` equivalence
  relation, allowing us to define the integers as the quotient of `SameInt`.
  Here we will prove that `SameInt` is an equivalence relation. Note that Lean
  set comprehensions require that the left side of the `|` be a single variable,
  so `x : (ℕ × ℕ) × (ℕ × ℕ)`; we'll cover `let` later but basically it just
  breaks the pair of pairs into individual elements. -/
abbrev SameInt : SetRel (ℕ × ℕ) (ℕ × ℕ) :=
  { x | let ((a, b), (c, d)) := x; a + d = b + c}

theorem sameint_refl : is_refl SameInt := by
  intro (a, b)
  whnf
  lia

theorem sameint_symm : is_symm SameInt := by
  intro (a, b) (c, d)
  constructor
  case mp =>
    intro h
    whnf at *
    lia
  case mpr =>
    intro h
    whnf at *
    lia

theorem sameint_trans : is_trans SameInt := by
  intro (a, b) (c, d) (e, f) h1 h2
  whnf at *
  lia

theorem sameint_eqrel : eqrel SameInt := by
  exact ⟨sameint_refl, sameint_symm, sameint_trans⟩

end_topic EXAMPLES_RELATIONS


topic::FUNCTIONS
/-
  Lean is a functional language, so functions (in the mathematical sense) are
  built into Lean already -/

/- A function that doubles its argument -/
def double (n : ℕ) := 2 * n

#check (double)

/-
  We can prove that functions are equal using the _function extensionality_
  principle: functions `f` and `g` are equal iff (1) they have the same domains
  and codomains; and (2) ∀ `x` in the domain, `f(x) = g(x)` -/

/-
  A function that is semantically the same as `double` -/
def double' (n : ℕ) := n + n

/-
  The `ext` tactic invokes the function extensionality principle (as well as the
  set extensionality principle, shown earlier) -/
example : double = double' := by
  unfold double double'
  ext x
  lia

/-
  A function may be injective and/or surjective; again we define these ideas
  using predicates -/

variable {α β : Type}

/- Injection (one-to-one) -/
def inj (f : α → β) :=
  ∀ (x y : α), f x = f y → x = y

/- Surjection (onto) -/
def surj (f : α → β) :=
  ∀ (y : β), ∃ (x : α), f x = y

/-
  A function that is both is a bijection -/
def bijection (f : α → β) :=
  inj f ∧ surj f

/-
  Here is an example proving that a function is a bijection -/

/- Doubling for real numbers -/
def double_real (a : ℝ) := 2 * a

#check (double_real)

/-
  Note in the proofs below that we use `linarith`, a tactic for linear
  arithmetic, instead of `lia`, the tactic for linear _integer_ arithmetic
  (since we're computing over the reals instead of integers) -/

/- `double_real` is injective -/
theorem dr_is_inj : inj double_real
:= by
  unfold inj double_real
  intro x y h
  linarith

/- `double_real` is surjective -/
theorem dr_is_surj : surj double_real
:= by
  unfold surj double_real
  intro y
  exists (y / 2)
  linarith

/- `double_real` is bijective -/
theorem dr_is_bij : bijection double_real := by
  exact ⟨dr_is_inj, dr_is_surj⟩

end_topic FUNCTIONS


topic::EXAMPLES_FUNCTIONS
open FUNCTIONS (inj surj bijection)

variable {α β : Type}

example
  {A B C : Type}
  (f : A → B) (g : B → C)
  : inj f → inj g → inj (g ∘ f)
:= by
  intro h1 h2 x y h3
  have h4 := h1 x y
  have h5 := h2 (f x) (f y)
  rw [Function.comp, Function.comp] at h3 -- this is unnecessary
  have h6 := h5 h3
  exact h4 h6

example
  {A B : Type}
  (f : A → B) (g : B → A)
  (h : f ∘ g = id)
  : surj f
:= by
  intro y
  exists (g y)
  have h1 : (f ∘ g) y = y := by rw [h]; rfl
  rw [Function.comp] at h1 -- this is unnecessary
  exact h1

end_topic EXAMPLES_FUNCTIONS


topic::INDUCTION
/-
  - Induction is an important proof principle, and Lean fully supports it (in fact, in many different ways)

  - We will focus here on induction over natural numbers. The tactic to use is `induction`, which takes a variable as argument and creates goals for the base case and the inductive case.

    + The `induction` tactic is very general and has many options on how to use it, we're just looking at the simplest version for now

  - When we used `induction n`, Lean decomposed `n` into the base case `zero` (n = 0) and the inductive case `succ m` (n = m + 1), where the inductive case automatically receives `ih`, the inductive hypothesis

  - This example proves that 2 evenly divides into `n^2 + n` for any `n`

    + `∣` stands for "divides"; note that the symbol is different from `|` although it can be difficult to tell

    + In the last step of the inductive case we use the `nlinarith` tactic which handles a subset of non-linear arithmetic (which is undecidable in general); if `nlinarith` didn't work we would have to prove the goal manually
-/
example : ∀ (n : ℕ), 2 ∣ (n^2 + n)
:= by
  intro n
  induction n with
  | zero => lia   -- base case
  | succ m ih =>  -- inductive case (with inductive hypothesis)
    whnf at ih
    have ⟨k, hk⟩ := ih
    exists (k + m + 1)
    nlinarith

end_topic INDUCTION


topic::EXAMPLES_INDUCTION

example : ∀ n, 3 ∣ n ^ 3 + 2 * n := by
  intro n
  induction n with
  | zero => lia
  | succ m ih =>
    obtain ⟨k, h⟩ := ih
    exists (m^2 + m + 1 + k)
    lia

/- Even naturals -/
abbrev even (n : ℕ) :=
  ∃ (k : ℕ), n = 2 * k

/- Odd naturals -/
abbrev odd (n : ℕ) :=
  ∃ (k : ℕ), n = 2 * k + 1

example : ∀ n, ¬(even n ∧ odd n) := by
  intro n
  -- we need to pass an additional flag to `push` or it does too much
  -- (try it without the `(distrib := true)` to see what it does)
  push (distrib := true) Not
  induction n with
  | zero =>
    right
    intro k
    lia
  | succ m ih =>
    cases ih with
    | inl h =>
      right
      intro k
      have h1 := h k
      lia
    | inr h =>
      left
      intro k
      have h1 := h (k - 1)
      lia

end_topic EXAMPLES_INDUCTION


topic::TACTICS_REFERENCE
/-
  - `apply`, `exact`: apply a theorem to solve the current goal; using `exact` signals that this is the end of the current proof, using `apply` may add new goals for the premises of the theorem being applied

  - `by_cases`: given a predicate `P` split the current goal into two separate goals, one where `P` and one where `¬P`

  - `by_contra`: if the goal is `P`, introduce the given `¬P` and change the goal to `False`

  - `case`: if there are multiple available goals, focus on a single one by name (the name given to it in the infoview). If there are any unnamed givens in the focused-on goal then optionally give them names.

  - `cases`: if there is a given `∨`, break the current goal into two copies one for each side of the `∨`

  - `constructor`: break a `∧` or `↔` goal into two separate goals, one for each side

  - `contradiction`: prove the current goal by detecting two contradictory givens

  - `contrapose`: rewrite the current `→` goal into its contrapositive

  - `exists`: supply a witness object to prove the current `∃` goal

  - `ext`: apply the extensionality principle to prove the current `=` goal (for sets or functions)

  - `have`: create a new given

  - `induction`: do a proof by induction on the given name

  - `intro`: for a `→` goal make the antecedent a given and update the goal to the consequent; for a `∀` goal add an arbitrary object as a given and update the goal to a predicate on that object

  - `left`, `right`: update the current `∨` goal to either the left or right side of the `∨`

  - `lia`, `linarith`, `nlinarith`: solve linear and (some) nonlinear propositions over integers and reals

  - `obtain`: pattern match to decompose a `∧` or `∃` given into its constituent subcomponents

  - `push Not`: push a negation through a proposition

  - `rfl`: prove equality via reflexivity

  - `rw`: rewrite a given or goal using an equality or `↔`

  - `unfold`: unfold a definition name into its content

  - `whnf`: normalize some notation into a simpler form
-/
end_topic TACTICS_REFERENCE
