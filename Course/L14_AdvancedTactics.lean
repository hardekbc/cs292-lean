/-
  # Advanced Tactics

  We'll cover some advanced uses of tactics, including more tactics for proof
  automation -/

import Course.CourseLib

topic::TACTIC_COMBINATORS
/-
  - There is a mid-ground between using only the tactics given to us and writing our own tactics: _tactic combinators_, i.e., tactics that combine other tactics

  - Some terminology: a tactic either _succeeds_ or it _fails_; each tactic decides the criteria for success vs failure

    + Some tactics only succeed if they complete the current goal, others succeed if they make any progress towards the goal even if they do not complete it; "success" is defined by the person creating the tactic

  - Here are some tactic combinators that may come in handy
-/

inductive Even : ℕ → Prop
  | zero : Even 0
  | add2 {n} : Even n → Even (n+2)

/-
  The `<;>` ("and then") combinator applies its left-hand side and then applies
  its right-hand side to any subgoals created by the left-hand side (but not any
  other goals) -/

example : (Even 0 ∧ Even 0) ∧ (Even 0 ∧ Even 0) := by
  constructor -- creates two goals `left` and `right`
  constructor <;> exact Even.zero -- closes `left`
  constructor <;> exact Even.zero -- closes `right`

/-
  The `repeat' <tactic>` combinator repeats its argument recursively on all
  goals, then all subgoals created from those goals, etc until it fails on all
  goals. It always returns success. -/

example : (Even 2 ∧ Even 4) ∧ (Even 6 ∧ Even 8) := by
  repeat' apply And.intro -- creates 4 goals `{left, right}.{left, right}`
  repeat' apply Even.add2 -- reduces all 4 goals to `Even 0`
  repeat' apply Even.zero -- closes all goals

/-
  The `all_goals <tactic>` combinator applies its argument once to all current
  goals, succeeding only if its argument succeeds on all goals -/

example : Even 2 ∧ Even 2 := by
  constructor
  all_goals apply Even.add2
  all_goals apply Even.zero

/-
  The `any_goals <tactic>` combinator applies its argument to all current goals,
  succeeding if its argument succeeds on any goal -/

example : Even 0 ∧ Even 2 := by
  constructor
  any_goals apply Even.add2
  all_goals apply Even.zero

/-
  The `try <tactic>` combinator applies its argument and always succeeds,
  regardless of whether its argument succeeds -/

example : Even 0 ∧ Even 2 := by
  constructor
  all_goals try apply Even.add2
  all_goals apply Even.zero

/-
  The `first <tactic> | ... | <tactic>` combinator tries each tactic given as an
  argument in turn until one succeeds. It fails if none of the tactics succeed.
-/

example : Even 2 := by
  first | trivial | apply Even.zero | apply Even.add2
  apply Even.zero

/-
  The `solve <tactic> | ... | <tactic>` combinator tries each tactic given as an
  argument in turn until one closes the current goal. It fails if none of the
  tactics close the current goal. -/

example : Even 2 := by
  solve | trivial | apply Even.zero | (apply Even.add2; apply Even.zero)

/-
  The combinators can all be combined into complex expressions -/

example : (Even 3 ∨ Even 4) ∧ (Even 6 ∨ Even 7) := by
  constructor <;> all_goals (first
    | left; (repeat' apply Even.add2); apply Even.zero
    | right; (repeat' apply Even.add2); apply Even.zero)

end_topic TACTIC_COMBINATORS


topic::GRIND
/-
  - The `grind` tactic is relatively new to Lean, but is rapidly becoming one of the most-used tactics available. It is based on the algorithms behind SMT solvers and can be extremely effective given proper setup.

    + Unlike `simp` and `aesop` (discussed below), the `grind` tactic is intended to be a "finisher" tactic: it either succeeds in proving the goal or fails and nothing is changed. Success is all or nothing, there is no partial result.

    + There is an interactive mode, but it requires some expertise to use

  - The core of `grind` is based on repeatedly deriving new facts from the set of currently-known facts based on congruence closure, constraint propagation, case analysis, and "e-matching", a form of pattern-matching. It also employs a host of other solvers as helpers, giving them access to the current set of facts and letting them derive new facts.

    + We'll discuss the specifics in a bit more detail below

  - Many of the Lean core library and Mathlib theorems are annotated with `grind`, so if you are using those definitions `grind` can be very powerful right out of the box. If you are using your own definitions then you need to do some work to give `grind` enough information to be effective.

    + When `grind` fails it prints the complete set of information about what it was able to derive, so it is possible to examine the data and determine what facts it was missing (and then try to add theorems/annotations to allow it to derive those facts). However, interpreting the data can be complicated and requires a lot of patience and knowledge about how `grind` works.

  - Note that `grind` has a hard time with existential goals and coming up with case splits for things that aren't in the givens, and will not automatically apply induction. If your proof requires these things then you may have to manually create the proof up to where you've specified the appropriate induction/witness/by_cases and then use `grind` from there.

  - The examples given here are adapted from the Lean Language Reference. There are many more details about `grind` which can be found there.
-/

variable {α : Type}

/-
  _Congruence closure_ is about taking advantage of the properties of equality,
  namely (1) that equality is reflexive, symmetric, and transitive; and (2) that
  applying a function to equal things results in equal things. `grind` uses
  these properties to derive new equalities from existing equalities by taking
  the closure of these properties over the current set of facts. -/
example
  (f g : α → α) (a b c : α)
  (h₁ : a = b) (h₂ : b = c) (h₃ : f a = g b)
  : f c = g a
:= by grind

/-
  Inductive type constructors are just functions, so congruence closure works on
  them the same way (recall that `::` is notation for applying the `List.cons`
  constructor) -/
example
  (x y : α) (xs ys : List α)
  (h₁ : x = y) (h₂ : xs = ys)
  : x :: xs = y :: ys
:= by grind

/-
  Pretty much anything that creates an object is a constructor call once the
  various levels are stripped away, e.g., pairs `(a, b)` are really a call to
  the structure constructor `Pair.mk` which is really a constructor of an
  inductive type -/
example
  (a b c : α)
  (h : a = b)
  : (a, c) = (b, c)
:= by grind

/-
  - _Constraint propagation_ uses a small set of rules to derive facts from the logical consequences of existing facts, such as:

    + Logical connectives: `A True` → `A ∨ B True`; `A ∧ B True` → `A True` and `B True`; etc

    + Inductive types: if two terms created by _different_ constructors of the same inductive type are made equivalent then this counts as a contradiction (e.g., `.none = .some 42` for the type `Option ℕ`). If two terms created by the _same_ constructor of the same inductive type are made equivalent then their arguments are made equivalent (e.g., if `.some a = .some b` then `a = b`); this is justified by the fact that constructors are guaranteed to be injective.

    + Reduction: definitional equalities are propagated, e.g., `(a, b).1 = a`, and if `a = b` then `(if a = b then c else d) = c`
-/

/- Logical connectives -/
example
  (a b c : Bool)
  : (a || b || c) || (!a && !b && !c)
:= by grind

/- Inductive types -/
example
  (a b : α) (xs : List α)
  (h : a :: xs = b :: xs)
  : a = b
:= by grind

/- Reduction -/
example
  (c : Bool) (t e : Nat)
  (h : c = true)
  : (if c then t else e) = t
:= by grind

/-
  _Case analysis_ works like the `cases` and `split` tactics: `grind` will
  consider each possible way that a term could have been built and work on each
  case separately. This case splitting is _not_ exhaustive (that would be far
  too expensive), and its behavior can be configured by a number of options.
-/

/- Here `grind` considers all possible values of `c` -/
example
  (c : Bool) (x y : ℕ)
  (h : (if c then x else y) = 0)
  : x = 0 ∨ y = 0
:= by grind

/- Here `grind` splits the `match` cases -/
example {x y}
  (h : y = match x with | 0 => 1 | _ => 2)
  : y > 0
:= by grind

/-
  - When defining an inductive type (or structure) it can be annotated with `@[grind cases]`, in which case `grind` will always consider it as a candidate for case splitting regardless of the `grind` configuration options.

    + The annotation is _scoped_, which means that it only has effect inside the namespace it is declared in _or_ when that namespace has been opened

  - Comment out the `@[grind cases]` annotation on `Even` to see what happens to the example proofs.
-/
namespace EvenExample1

@[grind cases]
inductive Even : ℕ → Prop
  | zero : Even 0
  | add2 {n} : Even n → Even (n + 2)

example (h : Even 5) : False := by grind
example {n} (h : Even (n + 2)) : Even n := by grind

end EvenExample1

/-
  - _E-matching_ uses pattern-matching on facts to instantiate and apply theorems in its rule-set. Theorems are added to the rule-set by annotating them with `@[grind]`. The exact form of the annotation controls what kind of pattern `grind` uses in order to find matches for that theorem (using `@[grind]` by itself will cause Lean to suggest some possible forms to use). Here are the forms we will cover below:

    + `@[grind .]`
    + `@[grind =]`, `@[grind =_]`, `@[grind _=_]`
    + `@[grind →]`, `@[grind ←]`

  - There are more annotation forms available than we will cover here, and we can also use `grind_pattern` to manually specify a particular pattern-matching scheme rather than relying on any of the annotation forms (see the Lean Language Reference for more details)

  - Appropriately annotating theorems is important for getting the maximum benefit from `grind`. Given an annotation `@[grind <modifier>]`, you can change it to `@[grind? <modifier>]` to see the exact pattern that `grind` generated. If the pattern isn't quite right we can remove the annotation and use `grind_pattern` to specify exactly what it should be.

    + The `grind` patterns use de Bruijn indices for its arguments, so some interpretation is required. You will see expressions like `#1`, `#2`, etc; these refer to the theorem's parameters, numbered right to left starting from 0 (so `#0` is the parameter immediately before the conclusion, `#1` is the parameter immediately before that, etc).

    + We can also use `grind? +suggestions` to have `grind` suggest useful theorems to use that aren't currently annotated for `grind`. This is the "quick start" method: don't annotate anything, then if the same theorem keeps showing up for `grind +suggestions` go ahead and annotate it. Note that `grind +suggestions` is using a lot of heuristics, so this isn't a "definitely always works" solution, just a way to get started without being overwhelmed by having to figure out a bunch of annotations---`grind` will definitely work better (i.e., succeed more) with hand-crafted annotations as long as they are done well.

    + The `try?` tactic mentioned at the beginning will attempt `grind +suggestions` as part of its search

  - The key thing to remember about annotations is that they are telling `grind` when the annotated theorem should be considered relevant. All of the annotation options are just different specifications of what things need to be in the current proof state for `grind` to think that the annotated theorem should be tried.
-/

/-
  - `@[grind .]` (or `@[grind ·]`) is called the "default" pattern: it tells `grind` to create a pattern from all of the theorem premises _and_ the conclusion. Comment out the `grind` annotations in the example theorems below to see the effect on the third example theorem.
-/

def even (n : ℕ) := ∃ k, 2*k = n
def odd (n : ℕ) := ∃ k, 2*k + 1 = n

@[grind .]
theorem even_not_odd {x : ℕ} : even x → ¬ odd x := by
  grind [even, odd]

/-
  Notice here that we have an existential goal that `grind` has trouble with, so
  we had to provide the witness ourselves -/
@[grind .]
theorem even_add2 {x : ℕ} : even x → even (x+2) := by
  intro h
  obtain ⟨k, hk⟩ := h
  exists (k+1)
  lia

example {x : ℕ} : even x → ¬ odd (x + 2) := by
  grind

/-
  - `@[grind =]` tells `grind` to check that the conclusion of the theorem is an equality and use the left-hand side of the equality as a pattern. On a match it will add the right-hand side. This behavior is similar to `simp` (except there is no rewriting involved), and many theorems annotated with `@[simp]` should also be annoted with `@[grind =]`.

    + This annotation _may_ fail if the left-hand side does not contain all of the arguments to the theorem

  - `@[grind =_]` is like `@[grind =]` except it uses the right-hand side of the equality as a pattern and, on a match, adds the left-hand side

    + This annotation _may_ fail if the right-hand side does not contain all of the arguments to the theorem

  - `@[grind _=_]` is like adding two rules: one using `@[grind =]` and one using `@[grind =_]`
-/

def f (a : Nat) : Nat := a + 1
def g (a : Nat) : Nat := a - 1

@[grind =]
theorem gf (x : Nat) : g (f x) = x := by
  simp [f, g]

/-
  We know that `f b = a`, and since equality is symmetric then `a = f b`, so
  then `g a = g (f b)`, so one way to view the goal is `g (f b) = b`; the term
  `g (f b)` triggers the `gf` theorem, so `g (f b) = b` becomes `b = b`, which
  is `True` and closes the goal -/
example {a b} (h : f b = a) : g a = b := by
  grind

/-
  - `@[grind →]` does forwards reasoning: it tells `grind` to to take _all_ the premises of the theorem as a pattern (i.e,. there must be a match for each premise), and on a match add the conclusion of the theorem

  - In the example below we define a relation `le` and a theorem `le_trans` that establishes that `le` is transitive. We annotate the theorem with `@[grind ·]` so that the two premises `le x y` and `le y z` must match, and if they do then `grind` can add the fact `le x z`.

  - We then make use of the annotated theorem in the example proof (comment out the grind annotation on `le_trans` to see the effect on the example proof)
-/

def le : ℤ → ℤ → Prop :=
  fun x y => x ≤ y

@[grind →]
theorem le_trans
  {x y z}
  : le x y → le y z → le x z
:= by grind [le]

example
  {a b c d}
  : le a b → le b c → le c d → le a d
:= by grind

/-
  - `@[grind ←]` does backwards reasoning: it tells grind to create a pattern from the conclusion, so that when a goal matches the pattern it will try to prove the premises

    + This annotation _may_ fail if the conclusion does not contain all of the arguments to the theorem

  - Notice that this is the same theorem that previously we annotated with `@[grind .]`. Remember that the annotation just specifies under what conditions to use the theorem, not what the theorem actually does when it is used. If the patterns overlap (i.e., either pattern would be triggered by the proof state) then the results in terms of what `grind` does will be the same.
-/

@[grind ←]
theorem even_plus2 {n} : even n → even (n + 2) := by
  simp [even]
  intro x h
  exists (x + 1)
  grind

/-
  Notice that I have explicitly removed `even_add2` from the `grind` rule set so
  that it can only rely on `even_plus2` -/
example {n} : even n → even (n + 6) := by grind [-even_add2]

/-
  - We can apply the `@[grind intro]` annotation to inductive predicates to instruct `grind` to add the constructors as e-matching theorems

    + The documentation doesn't say what pattern this generates, but using `grind? intro` shows that in the examples below the pattern is based on the "conclusion", i.e., the result type of the constructor
-/

namespace EvenExample2

/-
  This is the same `Even` predicate used in a previous example, but in addition
  to the `grind cases` annotation (instructing `grind` to break `Even` objects
  into separate cases by constructor) we have added `grind intro` instructing
  `grind` to add each constructor as a theorem to match on -/
@[grind cases, grind intro]
inductive Even : ℕ → Prop
  | zero : Even 0
  | add2 {n} : Even n → Even (n + 2)

/-
  These are the same proofs as before, relying only on `grind cases` -/
example (h : Even 5) : False := by grind
example {n} (h : Even (n + 2)) : Even n := by grind

/-
  These are new, and rely on the `grind intro` annotation (comment out that
  annotation to see the error). Note that `grind cases` doesn't help in the
  first example because the only fact we have is `Even x`, and breaking it down
  into cases just tells us that either `x = 0` or `∃n, Even(n) ∧ n + 2 = x`,
  neither of which is helpful for proving that `Even (x+6)`. `grind cases`
  doesn't help in the second example because there is no fact to do a case
  analysis on. -/
example {x} (h : Even x) : Even (x + 6) := by grind
example : Even 0 := by grind

end EvenExample2

/-
  Here is another example, proving that the inductive predicate `Decreasing` and
  the function `decreasing` agree with each other. Both the `cases` and `intro`
  annotations on `Decreasing` are necessary for `grind` to completely prove the
  goals after using `fun_induction`. -/

@[grind cases, grind intro]
inductive Decreasing : List ℤ → Prop
  | nil : Decreasing []
  | singleton x : Decreasing [x]
  | cons {x y xs} : Decreasing (x :: xs) → y > x → Decreasing (y :: x :: xs)

def decreasing : List Int → Bool
  | [] | [_] => true
  | y :: x :: xs => y > x && decreasing (x :: xs)

theorem decreasingCorrect {xs}
  : decreasing xs = Decreasing xs
:= by fun_induction decreasing with grind

/-
  Besides `@[grind <modifier>]` we can also use `@[grind! <modifier>]`, which
  changes the heuristic Lean uses to construct the pattern. I find that the best
  way to choose how to annotate a theorem with `grind` is to try different
  versions and see what patterns they produce, then pick the one that makes the
  most sense. -/

/-
  - _Auxiliary solvers_: Beyond congruence closure, constraint propogation, case analysis, and e-matching, `grind` uses a set of auxiliary solvers that can derive new facts for certain kinds of objects

  - By default these solvers include linear integer arithmetic, linear arithmetic, and algebraic solvers. The solvers rely on type classes (such as `IntModule`, `IsPartialOrder`, `Semiring`, `Ring`, `Field`, `Commutative`, etc), so if we are defining objects s.t. we can create instances for some of these type classes then `grind` will automatically apply the relevant solvers to them. See the Lean Language Reference for more details.

  - We can also write our own solvers and add them to `grind` so that it will apply them during its search
-/

/- Linear integer arithmetic -/
example {x y : ℤ} : 2 * x + 4 * y ≠ 5 := by grind

/- Linear arithmetic -/
example {a b : ℝ} (h : a ≤ b) : 3 • a + b ≤ 4 • b := by grind

/- Algebra -/
example (x : ℤ) : (x + 1) * (x - 1) = x ^ 2 - 1 := by grind

end_topic GRIND


topic::AESOP
/-
  - The `aesop` tactic performs a Prolog-like backtracking proof search. It is more powerful than (but also more expensive than) `simp`, and takes all `simp` annotated theorems into account automatically.

  - Rather than just rewriting equalities, `aesop` will introduce new givens, split cases, and apply lemmas, building a search tree until it find a proof or times out. Because of this fact we have to distinguish between "safe" and "unsafe" rules for `aesop`:

    + A "safe" rule guarantees that if the original state has a proof, then the new state after applying the rule has a proof (`simp` is always safe, unlike `aesop`). Safe rules are eagerly applied and never backtrack---the more safe rules, the better the performance.

    + An "unsafe" rule does not provide that guarantee, which means that if `aesop` determines that the current state does not allow a proof it must backtrack to a prior proof state to try something else rather than saying that the goal is unprovable. Unsafe rules require the previous proof state to be remembered to allow potential backtracking---the more unsafe rules, the worse the performance.

  - Rules for `aesop` are provided via the annotation `@[aesop]`. Again, the core library and Mathlib have many already-annotated definitions and theorems.

    + Note that `aesop` isn't that useful for arithmetic or algebraic manipulations; those usually require other tactics such as `lia` or `ring`

    + We can also add our own annotations for things that we define, expanding `aesop`s utility

  - The examples below are adapted from the `aesop` Github repo. There are many more examples there that illustrate how to use it.
-/

variable {α : Type}

/-
  Notice in the example below that `aesop` won't try to use induction (doing so
  automatically is too expensive and fragile), we have to do it ourselves and
  then we can have `aesop` handle each case. The `with aesop` part means to use
  the `aesop` tactic on all goals created by the `induction` tactic. -/
theorem append_nil {xs : List α} : xs ++ [] = xs:= by
  induction xs with aesop

/-
  If we want to know what proof `aesop` found we can ask (and optionally replace
  the tactic with the discovered proof directly) -/
theorem append_assoc {xs ys zs : List α}
  : (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
:= by induction xs with aesop?

/-
  The above examples work because there are a bunch of `List` theorems and
  definitions annotated for `aesop`. How to we do annotations for our own
  definitions and theorems? -/

/-
  We'll define our own list data structure, separate from Lean's `List` -/
inductive MyList (α : Type)
  | nil
  | cons : α → MyList α → MyList α

namespace MyList

variable {x : α} {xs ys : MyList α}

/- Append two lists together -/
def append : MyList α → MyList α → MyList α
  | .nil, ys => ys
  | .cons x xs, ys => cons x (xs.append ys)

/- Provide append notation `++` -/
instance : Append (MyList α) := ⟨MyList.append⟩

/- `simp` annotations are automatically used by `aesop` -/

@[simp]
theorem nil_append : .nil ++ xs = xs := rfl

@[simp]
theorem cons_append : .cons x xs ++ ys = .cons x (xs ++ ys) := rfl

/-
  Now we will define the "nonempty" predicate on `MyList` and annotate it for
  `aesop`. The annotation tells `aesop` to create two kinds of rules for its
  search: the `constructors` part tells it to try the `Nonempty` constructors
  whenever there is a goal `Nonempty _`; and the `cases` part tells it to look
  for givens of the form `Nonempty _` and perform a case analysis on them like
  the `cases` tactic does. The annotation also specifies that these are both
  safe rules. The `constructors` and `cases` rules are useful for annotating
  inductive types (predicates or otherwise). -/
@[aesop safe [constructors, cases]]
inductive Nonempty : MyList α → Prop
  | cons x xs : Nonempty (.cons x xs)

/-
  Now we can use `aesop` to prove a theorem about `Nonempty`. At the same time,
  we annotate this new theorem for `aesop`, marking it as an unsafe rule along
  with a percentage likelihood that the theorem will be helpful (which `aesop`
  uses to guide its search). The `apply` part tells it to apply this theorem
  whenever the target is of the form `Nonempty (_ ++ _)`, i.e., it acts like the
  `apply` tactic. It makes sense for this rule to be marked unsafe because there
  are multiple ways to possibly prove a goal such as `Nonempty (xs ++ ys)`: we
  could attempt to prove `Nonempty xs` (as per this theorem), _or_ we could try
  to prove `Nonempty ys` via some other method. If this rule was marked as safe
  then `aesop` would only consider the first possibility and never the second.
-/
@[aesop unsafe 50% apply]
theorem nonempty_append (ys : MyList α)
  : Nonempty xs → Nonempty (xs ++ ys)
:= by aesop

/-
  Using the above theorem we can now prove another theorem using `aesop` -/
example (ys zs : MyList α)
  : Nonempty xs → Nonempty (xs ++ ys ++ zs)
:= by aesop

/-
  Finally, we can also add "temporary" rules to `aesop` that are only active for
  that one invocation. The `(add...)` argument means `aesop` will act as if the
  `MyList` inductive type had been annotated with `@[aesop unsafe 10% cases]`,
  but only for that one invocation of `aesop`. We give a low likelihood of
  helpfulness because doing a case analysis on `xs : MyList α` would give us
  both `x : α` and `ys : MyList α` (i.e., we would get _another_ `MyList`),
  which means `aesop` could go into a cycle of doing case analysis on `MyList`;
  the low percentage means that `aesop` will prioritize other rules when
  possible. -/
example (xs : MyList α)
  : xs = .nil → ¬ Nonempty xs
:= by aesop (add unsafe 10% cases MyList)

end MyList

/-
  - Another type of `aesop` rule is `tactic`, which instructs `aesop` to use the given tactic during its search for a proof. We can use this kind of rule to combine `aesop` with other tactics such as `grind`, e.g., `aesop (add safe (by grind))`.

  - We have seen the annotation rules `constructors`, `cases`, `apply`, and `tactic`; other types of rules are `forward`, `destruct`, and more (see the Github repo for more information).
-/

end_topic AESOP


topic::PROOF_AUTOMATION_TIPS
/-
  - `simp`, `aesop`, and `grind` are the major proof automation techniques for general proofs (i.e., not specialized to a specific domain like `lia` is specialized to linear integer arithmetic). They can be extremely useful in allowing us to "hand-wave" uninteresting parts of a proof while still formally verifying that they are correct.

  - However, there is a cost: proof automation is compute-intensive. Depending on how powerful your machine is you may be affected by this fact more or less, but if there is a lot of proof automation happening you'll probably feel it.

    + Whenever we change something in a file, Lean is forced to check that everything below that point is still verified. If there are many uses of proof automation then Lean has to rerun them all, which can make edits very expensive in some cases.

  - If Lean is getting bogged down by proof automation, here are a few tips to help the situation beyond "get a more powerful machine"

    + One simple thing to do if you are working on part of a file that has a lot of proof automation below it is to comment out all of the file below the point you're working on so that Lean doesn't have to re-verify it with every edit. Recall that Lean comments can be nested so it's as easy as wrapping `/- ... -/` around things, even if they already include comments.

    + Another thing you can do is separate your proofs into different files, using `import` to organize things. Lean only has to verify proofs in the current file, so the fewer the proofs in the file the faster it is.

    + Finally, you can use `only` to restrict the size of the rule database that `simp` and `grind` use, which can significantly speed them up in aggregate. The easiest way to do this is to use `simp` or `grind` as normal, then once the proof is finished replace them with `simp?` and `grind?`, which will offer a suggestion about the `only` version you can use instead (in VS Code there is an `apply` button in the infoview that you can use to do the replacement automatically).
-/
end_topic PROOF_AUTOMATION_TIPS
