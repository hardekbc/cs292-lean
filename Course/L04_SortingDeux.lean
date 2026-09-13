/-
  # Verified Sorting Part Deux

  We'll do one more sorting algorithm, _mergesort_. We won't dwell as much on it
  (and will leave most of the proofs as exercises), but it will allow us to
  introduce an important part of Lean, plus some more new concepts. Recall that
  mergesort splits its input into two sublists, recursively sorts them, and then
  merges the two sorted lists into a single sorted list. -/

import Course.CourseLib

/-
  Split a list into two lists. We saw the product type `α × β` before when we
  talked about `SetRel`; hover over the `×` below to get a reminder. Hover over
  `take` and `drop` to see what they do. -/
def split (ℓ : List ℕ) : (List ℕ) × (List ℕ) :=
  let half := ℓ.length / 2
  (ℓ.take half, ℓ.drop half)

/-
  Merge two sorted lists into one sorted list. We see two new concepts here:
  syntactic sugar for functions that immediately use pattern-matching on their
  inputs, and the fact that we can pattern-match on multiple things at once. -/
def merge : List ℕ → List ℕ → List ℕ
  | [], ℓ₂ => ℓ₂
  | ℓ₁, [] => ℓ₁
  | x :: ℓ₁, y :: ℓ₂ =>
    if x ≤ y then x :: merge ℓ₁ (y :: ℓ₂)
    else y :: merge (x :: ℓ₁) ℓ₂

/-
  _Syntactic sugar for pattern-matching on parameters_

  A common coding pattern is to take an inductive type (like `List`) as a
  function parameter and immediately pattern-match on it. Lean gives us some
  syntactic sugar for this coding pattern as shown in `merge`. Note that the
  inductive type(s) being matched on come immediately _after_ the `:` in the
  function signature and there is no `:=` or `match <exp> with`.
-/

/-
  _Pattern-matching on multiple expressions simultaneously_

  We can match on multiple inductive types at once, simultaneously. `merge` is
  matching on its first _and_ second arguments, both of which are lists. The
  `merge` example merges (pun intended) the simultaneous matching and syntactic
  sugar for pattern-matching on parameters, but we can use them separately.
  Below is an example where we use `match` for simultaneous pattern-matching.
  Note again that `_` basically means "don't care".
-/
example (ℓ₁ ℓ₂ : List ℕ) : ℕ :=
  match ℓ₁, ℓ₂ with
  | [], [] => 0
  | [], _ :: ys => ys.length
  | _ :: xs, [] => xs.length
  | _ :: xs, _ :: ys => xs.length + ys.length

/-
  And here's the big new concept: Lean's termination requirement and the
  difference between structural and well-founded recursion. We try to define
  `merge_sort'` as a recursive program and Lean gives an error message about
  termination.

  We will use the `#guard_error` command to show errors: it checks the output of
  the next command or definition and verifies that it matches the docstring
  immediately above it. If you see `#guard_error` in these lecture notes it is
  always because the next thing is causing an error, and the docstring above the
  `#guard_error` says what the error is (you can comment out the `#guard_error`
  line to see the actual Lean error). Note that `#guard_error` is a macro
  defined in `CourseLib.lean`, not a standard Lean command. -/
/--
  error: fail to show termination for merge_sort' -/
#guard_error
def merge_sort' : List ℕ → List ℕ
  | [] => []
  | [n] => [n]
  | x :: y :: ℓ =>
    let (ℓ₁, ℓ₂) := split (x :: y :: ℓ)
    merge (merge_sort' ℓ₁) (merge_sort' ℓ₂)

/-
  - We've discussed the fact that Lean requires termination to ensure a consistent logic. We also know that recursion can cause infinite loops...so how does Lean reconcile those two facts? We must _prove_ that a recursive function terminates before that function's definition can be accepted.

  - In `L03_Sorting` we defined `insertion_sort` and `insert`, both of which are recursive functions, but we didn't need to prove anything about them. That's because there is a particular kind of recursion called _structural recursion_ that Lean automatically recognizes as terminating.

    + Structural recursion means that we have an inductive type as a function parameter, and any recursive call must be made on a sub-component of the inductive type value that was passed in as an argument. In `insertion_sort` we had a parameter named `ℓ : List ℕ`, which is an inductive type, and in the recursive call we passed the tail of `ℓ` as the argument, which is a sub-component of `ℓ`.

    + Because all inductive type values must have at least one base case used in their construction, if we always recursively call the function with a sub-component we must necessarily at some point reach a base case, and thus terminate. Lean knows this is true, and so we don't need to prove anything explicitly. For `List` the base case is `nil`, i.e., the empty list---we cannot construct a list without ending in `nil`, so recursively decomposing a list will always end in `nil`.

    + As a sidenote: `ℕ` is also an inductive type (try `#print Nat`, where `Nat` is the actual name of the natural number type; `ℕ` is an alias). It has two constructors, `zero` (the base case) and `succ` (which takes a `ℕ` as argument and constructs a new `ℕ` that is one greater than its argument). This means that recursing on smaller numbers counts as structural recursion.
s
  - However, `merge_sort'` is _not_ structurally recursive: the recursive calls pass `ℓ₁` and `ℓ₂` as arguments, which are returned by a call to `split`. Of course, _we_ know that `split` is returning sub-components of `x :: y :: ℓ`, but Lean doesn't.

  - There are three ways we could address this issue, which we'll cover here in the context of `merge_sort`
-/

/-
  _Partial functions_

  The first method is to tell Lean that we don't care about termination, via the
  `partial` keyword that identifies the following definition as a partial
  function (i.e., a function that is not defined for every argument in its
  domain). The drawback of this option is that, because nontermination implies
  inconsistent logic, Lean will not allow any reasoning about partial functions.
  So this option is mainly useful when you do not care about proving anything
  related to the function you are defining. -/

/-
  This is exactly the same as `merge_sort'` except that we added the `partial`
  keyword in front of the `def` -/
partial def merge_sort_partial : List ℕ → List ℕ
  | [] => []
  | [n] => [n]
  | x :: y :: ℓ =>
    let (ℓ₁, ℓ₂) := split (x :: y :: ℓ)
    merge (merge_sort_partial ℓ₁) (merge_sort_partial ℓ₂)

#eval merge_sort_partial [3, 2, 1]
#eval merge_sort_partial [3, 2, 1, 1, 2, 3]

/-
  We cannot reason about `merge_sort_partial`, even for terminating arguments -/
/--
  error: Tactic `unfold` failed to unfold `merge_sort_partial` -/
#guard_error
example : merge_sort_partial [] = [] := by
  unfold merge_sort_partial

/-
  _Clocked recursion_

  - Clocked recursion adds an additional `ℕ` parameter to a recursive function, commonly called _fuel_ (yes, we're mixing metaphors). The value of this parameter decreases with every recursive call, thus guaranteeing termination in a structural way that Lean can recognize. That is, clocked recursion forces the function to use structural recursion and Lean can take it from there.

  - We need to consider what happens if we provide insufficient fuel...what should the function return?

    + The default answer is to modify the return value to an `Option` type. The type `Option ℕ`, for example, can have the value `none` or `some n` for some `n : ℕ`. `Option` is a way to say that there may not be a real answer at all. If the function runs out of fuel it returns `none`, otherwise if it computes a final answer `a` it returns `some a`.

    + In some cases, such as `merge_sort`, there is already a suitable answer we can give without changing the return type, as we will see below

  - The drawback of this approach is twofold:

    + When executing the function we need to be sure to provide sufficient fuel, and therefore we have to figure out how much fuel is "sufficient". If we change its return type to `Option` we also have to modify all calls to the function to determine whether the result was `none` or `some a` and figure out what to do if it's `none`.

    + When reasoning about the function we need to modify all the theorems to say something like "if we provide an amount of fuel s.t. that the result is `some a`, ...". This can make the statements womewhat awkward, and we have to be careful that the specification is saying what we really want (especially since the specification is only talking about _terminating_ executions of the function in question).

  - If the function we're defining actually _does_ have nonterminating inputs then clocked recursion is basically the only method we can use if we actually want an executable function that we can reason about (there is an alternative if we only want to _reason_ about the function but don't care about _executing_ the function, which we'll discuss later).
-/

/-
  Here is the clocked version of `merge_sort`. We use a nested auxiliary
  function to do the actual recursion, thereby hiding the fact that we're using
  fuel from the user of the function. If we reason about the mergesort algorithm
  it is clear that there can be no more than `ℓ.length` recursive calls along
  any path, therefore we are guaranteed that providing `ℓ.length` as fuel is
  always sufficient. Therefore we can just return `[]` for running out of fuel
  because that will never happen. -/
def merge_sort_clocked (ℓ : List ℕ) : List ℕ :=
  merge_sort_aux ℓ.length ℓ
where
  merge_sort_aux : ℕ → List ℕ → List ℕ
  /-
    Simultaneous pattern-matching. The first element is the amount of fuel, the
    second is the list we're sorting. Lean matches in the order the patterns are
    given, so in all the cases after `0, _` we're guaranteed that the fuel is
    non-zero. In the last case the fuel was `n+1`, so `n` is one less. -/
  | 0, _ | _, [] => [] -- ran out of fuel or terminates normally
  | _, [n] => [n]      -- terminates normally
  | n + 1, ℓ =>        -- recursive call with one less fuel
    let (ℓ₁, ℓ₂) := split ℓ
    merge (merge_sort_aux n ℓ₁) (merge_sort_aux n ℓ₂)

/-
  _Well-founded recursion_

  - The ideal way to handle the issue, assuming that the recursive function really is guaranteed to terminate, is to _prove_ that it terminates

  - A termination proof works as follows:

    + We must define some well-founded measure. A "measure" means some way to calculate the "size" of an input to the function. "Well-founded" means that we compare values of the measure using a well-founded order relation, i.e., for that order there is always a "least" value in any set of values. `ℕ` with `≤` is well-founded, because in any set of `ℕ` there is always a least value. `ℤ` with `≤` is _not_ well-founded because, e.g., the set of all `ℤ` does not have a least value.

    + We must then prove that, according to our well-founded measure, the size of a parameter (or some combination of parameters) is always decreasing with each recursive call

    + The facts that the measure is well-founded _and_ always decreasing mean that it must reach a least value at some point and cannot decrease further, therefore it must terminate. If this sounds like the termination argument for structural recursion that's not an accident: structural recursion _is_ a type of well-founded recursion that's easy for Lean to recognize without any help from the programmer.

  - We use `termination_by` to define our termination measure; for `merge_sort` we'll use the size of the input list

  - We use `decreasing_by` to prove that the measure decreases; for `merge_sort` our argument will be that the size of the input list is always decreasing. In order to prove that we'll need to prove a helper lemma about `split`.

    + We'll introduce a very helpful tactic called `simp` (and its variant `simp_all`) during these proofs. We'll describe what they do after we complete all the proofs.
-/

/-
  If the argument to `split` is not empty or a singleton list, then the two
  output lists are strictly smaller than the input list -/
lemma split_len
  {ℓ : List ℕ} (hs₁ : ℓ ≠ []) (hs₂ : ∀ x, ℓ ≠ [x])
  : let ℓs := split ℓ
    ℓs.1.length < ℓ.length ∧ ℓs.2.length < ℓ.length
:= by
  unfold split
  simp_all [← List.length_pos_iff_ne_nil]
  have h1 : 2 ≤ ℓ.length := by
    by_contra h1
    have h2 : ℓ.length = 0 ∨ ℓ.length = 1 := by lia
    cases h2 with
    | inl h => lia
    | inr h => simp_all [List.length_eq_one_iff]
  exact ⟨by lia, h1⟩

def merge_sort : List ℕ → List ℕ
  | [] => []
  | [n] => [n]
  | x :: y :: ℓ =>
    /-
      Notice that I've modified the `let` from the original version; I'll
      explain why inside the termination proof -/
    let ℓs := split (x :: y :: ℓ)
    merge (merge_sort ℓs.1) (merge_sort ℓs.2)
termination_by ℓ => ℓ.length
decreasing_by
  /-
    There are two recursive calls in `merge_sort`, so `decreasing_by` has two
    separate goals, one per call. Notice that `decreasing_by` has brought some
    knowledge from the body of `merge_sort`, namely that `ℓs` is just a name for
    `split (x :: y :: ℓ)`. If we used pattern-matching in the `let`, such as
    `let (ℓ₁, ℓ₂) = split...`, then we lose that connection between `ℓ₁` and
    `ℓ₂` and `split`, which makes the proof impossible. Try changing the `let`
    back to the original version to see what it does to the proof state here. -/
  · exact (split_len (by simp) (by simp)).1
  · exact (split_len (by simp) (by simp)).2

#eval merge_sort [3, 2, 1]
#eval merge_sort [3, 2, 1, 1, 2, 3]

/-
  _The simp tactic_

  - Now we have a straightfoward implementation of `merge_sort` that we can reason about, but we made liberal use of the `simp` and `simp_all` tactics in our proofs. What are they doing? The `simp` tactic ("simplifier") is a rewrite engine that attempts to transform its target proposition using a database of rules. It is one of the most commonly-used tactics and has a number of variations.

  - The rules used by `simp` are equality or biimplication theorems: `simp` will attempt to match its target to the left side of an equality or biimplication and, if successful, transform it into the right side. It repeats applying rules from the database until none of them are applicable (or it times out).

    + To be available for `simp` to use, a theorem must be _annotated_ using `@[simp]` _or_ provided directly as an argument to the `simp` tactic (multiple theorems can be given as arguments at the same time). There are many already-annotated theorems in core Lean plus even more in Mathlib.

  - If the `simp` target is the current goal and it reduces the goal to `True` then `simp` will automatically close the goal. Otherwise it creates a new proof state where its target has been replaced by its reduced form.

    + If we want to know what theorems `simp` used we can ask by changing the `simp` into `simp?`, which will give a message listing the theorems. There is no guarantee that the list it returns gives the _minimal_ set of needed theorems, this is just the set that it happened to use that allowed it to make progress.

    + Using `simp [<comma-separated names>]` tells `simp` to add the named theorems or givens as rewrite rules to its database (only for that invocation of `simp`)

    + Using `simp [← <name>]` tells `simp` to treat the equality or bi-implication in the opposite direction, i.e., matching the right-hand side and rewriting it into the left-hand side instead of vice-versa

    + Using `simp only [...]` tells `simp` to only try the listed theorems for rewrites, instead of every theorem in its rule database.

    + Using `simp` by itself targets the current goal, using `simp at <name>` targets the named given, using `simp at *` targets all givens

    + Using `simp_all` targets all givens _and_ the current goal, and adds all equality and biimplication givens in the current proof state to its rewrite rules. `simp_all` has all the same options as `simp`.

  - Looking at `split_len`, the first use of `simp_all` adds the theorem `List.length_pos_iff_ne_nil` to its rule database but in the opposite direction from usual. `simp_all` is not able to close the goal, but it does drastically simplify it using the existing annotated theorems in Mathlib + the extra theorem. The second use of `simp_all` adds the `List.length_eq_one_iff` theorem and it is sufficient to close the current goal. In the `decreasing_by` for `merge_sort` we use `simp` to prove the required arguments for `split_len` and it is able to close the goals without any help.

  - We'll talk about `simp` again later in more detail and with more examples, including how and when to add our own theorems to its database; for now just consider it as a possibly-useful tactic that can often simplify things that are related to the Mathlib library. Feel free to use it, but be aware that it's possible to simplify things _too far_, making the proof more difficult instead of less.
-/

/-
  Since we can reason about `merge_sort` now that we've proven termination, we
  can verify that it is correct in a similar way as we did `insertion_sort`.
  However, we will leave these proofs as exercises rather than doing them here.
-/
