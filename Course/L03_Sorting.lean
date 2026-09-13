/-
  # Verified Sorting

  We will start diving deeper into Lean by defining and proving properties about
  a simple sorting algorithm: _insertion sort_. There are a large number of Lean
  concepts being exercised by this example; we'll go through them all and
  explain them. -/

import Course.CourseLib

topic::INSERTION_SORT_P1
/-
  Here is an implementation of insertion sort. It takes a list and returns a
  version of the list sorted in ascending order. -/
def insertion_sort (ℓ : List ℕ) : List ℕ :=
  match ℓ with -- A list is either empty or has a front element
  | [] => []   -- `ℓ = []`, i.e., it is empty (and so already sorted)
  | x :: xs => -- `ℓ = x :: xs`; `x` is the head of `ℓ` and `xs` is the tail
    /-
      Recursively sort the tail of the list (i.e., `xs`) and then insert `x`
      into the proper spot -/
    insert x (insertion_sort xs)
where
  /-
    Insert `n` into list `ℓ` in correct ascending order (assumes that `ℓ` is
    already sorted) -/
  insert (n : ℕ) (ℓ : List ℕ) : List ℕ :=
    match ℓ with -- Again a list is empty or has a front element
    | [] => [n]  -- If empty, return the singleton list containing `n`
    | x :: xs => -- Otherwise `ℓ = x :: xs`
      /-
        If `n ≤ x` then `n` should be at the front of the list, otherwise we
        keep `x` as the head and recursively insert `n` into the tail of the
        list, i.e., `xs` -/
      if n ≤ x then n :: x :: xs
      else x :: insert n xs

/-
  One concept we've been seeing since the beginning: _comments_. This current
  comment is a block comment that can span multiple lines. /- Unlike in many
  languages, block comments can be nested -/-/

-- And this is a single-line comment

/-
  `def` is used to create a top-level definition. That definition can be of any
  type, but has special syntax if we're defining a function (as we are above).
  Syntax for top-level function definitions:

  `def` <name> `(`<prm> `:` <type>`)` `:` <return type> `:=` <expression>

  So the example above is defining a function named `insertion_sort` that has
  one parameter, a `List ℕ` named `ℓ`, and that returns a `List ℕ`.

  A function can also contain _nested_ functions, which are _not_ top-level
  definitions, using a `where` clause. The format is the same except using
  `where` immediately after the main function and not using `def`. So the
  example above is also defining a nested function `insert` that has two
  parameters, a natural number `n` and a list `ℓ`, and returns a list. Nested
  functions are convenient if we don't want to pollute the top-level namespace,
  e.g., if we're never going to use the nested function outside of the main
  function.
-/

/-
  If we use `#check` on a function it shows us the type using special syntax; if
  we put `()` around the name it shows us the type without special syntax. -/
#check insertion_sort
#check (insertion_sort)

/-
  `insert` is nested inside `insertion_sort` -/
#check insertion_sort.insert
#check (insertion_sort.insert)

/-
  Lists are a fundamental data structure in functional programming with lots of
  syntactic support. Established terminology is that the first element of the
  list is called the _head_ and the rest of the list is called the _tail_. The
  Lean `#eval` command interactively evaluates an expression and shows the
  result. -/

/-
  Create a list of natural numbers (type inferred from context) -/
#eval [1, 2, 3]

/-
  Concatenate an element to the head of a list -/
#eval 1 :: [2, 3]

/-
  Concatenate a series of elements starting from the empty list -/
#eval 1 :: 2 :: 3 :: []

/-
  The body of `insertion_sort` is using _pattern-matching_ (via `match`) on the
  list parameter `ℓ` to decompose it into two cases: either the list is empty
  (the `[]` case) or it has a head element `x` concatenated to the tail `xs`
  (the `x :: xs` case). Think of `match` as a more versatile `if`.

  Another thing to note is that all functional programs are _expressions_, there
  are no _statements_. That is, everything returns a value. A function's body is
  an expression that evaluates to a result, and that is the return value of the
  function; there is no `return` statement. Functions in a functional language
  are very much modeled on mathematical functions.

  `insert` is also using pattern-matching on its list parameter, and in the
  second match case it is also using `if-else`. In functional programming
  `if-else` is _not_ a statement, it is an expression---that is, it returns a
  value. Because of that fact, an `if` must always have an `else` branch.
-/

/-
  Here is the sorting algorithm in action -/
#eval insertion_sort [3, 2, 1]
#eval insertion_sort [3, 2, 1, 1, 2, 3]

/-
  We have defined a sorting algorithm, but does it actually do what we want? To
  verify it we need to state and prove various properties -/

/-
  First we define a predicate (a function from object to `Prop`) saying that a
  given list is sorted in ascending order. We take advantage of a built-in
  function on lists called `Pairwise` that applies a binary predicate to each
  successive pair of elements and succeeds only if all calls succeed. We see
  three new Lean concepts in play, which we will explain below. -/
def sorted (ℓ : List ℕ) : Prop :=
  ℓ.Pairwise (· ≤ ·)

/-
  First, the _dot notation_ `ℓ.Pairwise`. `ℓ` is of type `List ℕ`, and the
  `Pairwise` function is actually defined as `List.Pairwise` in the Lean
  library. These two facts allow us to use `ℓ.Pairwise` as syntactic sugar to
  mean `List.Pairwise ℓ`, i.e., calling `Pairwise` with argument `ℓ`. Note that
  dot notation is completely unrelated to objects, classes, and other OOP
  concepts. If a function is defined as `<type>.<name>` and an expression `e`
  has type `<type>`, then `e.<name>` means `<type>.<name> e`. -/

/-
  Second and third, the _anonymous function_ `(· ≤ ·)`, which in addition is
  using syntactic sugar (Lean tries to be very ergonomic with its syntax and has
  lots of syntactic sugar, as we'll be seeing---it's very convenient when you're
  used to it, but can make learning Lean sometimes frustrating because it
  obscures the underlying reality).

  An anonymous function is simply a function without any name; it is also
  sometimes called a "lambda" or "closure". Syntax for anonymous functions:

  `fun` `(`<prm> `:` <type>`)` `=>` <expression>
-/

/-
  Here is an anonymous function with two parameters. Note that if the parameters
  have the same type we don't need to use separate `(_ : ℕ)` for each one, they
  can share. Also note that we call an anonymous function just like a regular
  function except that we use the function itself instead of the function name
  (since it doesn't have one). -/
#eval (fun (a b : ℕ) => a * b) 2 3

/-
  If the types of the parameters are obvious to Lean from context then they can
  be omitted -/
#eval (fun a b => a * b) 2 3

/-
  If a parameter is used exactly once in the body of the anonymous function then
  we can remove it from the parameter list and use `·` in the body instead -/
#eval (fun b => · * b) 2 3

/-
  We can do it for more than one parameter (the first `·` means the first
  parameter, the second `·` means the second, etc), and if there are no
  parameters left then we don't even need the `fun` part -/
#eval (· * ·) 2 3

/-
  So our `sorted` predicate without any of the syntactic sugar would look like
  the following. In other words, if we apply the binary predicate `≤` to each
  pair of consecutive elements in the list and it always returns true, then the
  list is sorted. -/
example (ℓ : List ℕ) : Prop :=
  List.Pairwise (fun a b => a ≤ b) ℓ

end_topic INSERTION_SORT_P1


topic::INSERTION_SORT_P2
/-
  Let's recap. Here is the insertion sort algorithm and sorted predicate without
  the commentary. -/

def insertion_sort (ℓ : List ℕ) : List ℕ :=
  match ℓ with
  | [] => []
  | x :: xs => insert x (insertion_sort xs)
where
  insert (n : ℕ) (ℓ : List ℕ) : List ℕ :=
    match ℓ with
    | [] => [n]
    | x :: xs =>
      if n ≤ x then n :: x :: xs
      else x :: insert n xs

def sorted (ℓ : List ℕ) : Prop :=
  ℓ.Pairwise (· ≤ ·)

/-
  It will turn out to be useful to define several lemmas about how `sorted`
  behaves. `lemma` is a keyword defined in Mathlib (not core Lean) and is just a
  synonym for `theorem`. Which one to use is a subjective choice. Note that
  defining a theorem or lemma uses exactly the same syntax as defining a
  function, except using `theorem` or `lemma` instead of `def`. We use `:= by`
  to say that the proof will be using tactics.

  We see several new Lean concepts in these lemmas, which we'll explain after we
  prove them all. Also, how did I know about the various theorems used in the
  proofs? I used Loogle. The `#loogle` command gave some help but truncated the
  results and so I needed to go to the Loogle website to see all of them.

  Remember to use the infoview to see the proof states, and hover over the
  theorem names to see their definitions. The proof stategies should be apparent
  if you do those things.
-/

/-
  The empty list is sorted -/
lemma empty_sorted : sorted [] := by
  unfold sorted
  exact List.Pairwise.nil

/-
  A singleton list is sorted -/
lemma singleton_sorted {n : ℕ} : sorted [n] := by
  unfold sorted
  exact List.pairwise_singleton (· ≤ ·) n

/-
  If the list `n :: ℓ` is sorted then `n` is ≤ all other elements in the list -/
lemma head_sorted
  {n : ℕ} {ℓ : List ℕ}
  : sorted (n :: ℓ) → ∀ m ∈ ℓ, n ≤ m
:= by
  unfold sorted
  intro h1
  obtain ⟨h2, _⟩ := List.pairwise_cons.1 h1
  exact h2

/-
  If the list `n :: ℓ` is sorted then `ℓ` is sorted -/
lemma tail_sorted
  {n : ℕ} {ℓ : List ℕ}
  : sorted (n :: ℓ) → sorted ℓ
:= by
  unfold sorted
  intro h1
  exact List.Pairwise.tail h1

/-
  If `ℓ` is sorted and `n` is ≤ all elements of `ℓ`, then `n :: ℓ` is sorted -/
lemma cons_sorted
  {n : ℕ} {ℓ : List ℕ}
  : sorted ℓ → (∀ m ∈ ℓ, n ≤ m) → sorted (n :: ℓ)
:= by
  unfold sorted
  intro h1 h2
  exact List.Pairwise.cons h2 h1

/-
  If `m :: ℓ` is sorted and `n ≤ m` then `n :: m :: ℓ` is sorted -/
lemma cons_sorted'
  {n m : ℕ} {ℓ : List ℕ}
  : sorted (m :: ℓ) → n ≤ m → sorted (n :: m :: ℓ)
:= by
  unfold sorted
  intro h1 h2
  have h3 := (List.pairwise_cons.1 h1).1
  have h4 : ∀ k ∈ m :: ℓ, n ≤ k := by
    intro k hk
    /-
      `h3` is only about members of `ℓ` but `k` is a member of `m :: ℓ`, so we
      need to split that fact into `k = m ∨ k ∈ ℓ` and case on it. -/
    cases List.mem_cons.1 hk with
    | inl h => lia
    | inr h =>
      have h4 := h3 k h
      lia
  exact List.pairwise_cons.2 ⟨h4, h1⟩

/-
  Notice that inside the lemmas we needed to unfold the definition of `sorted`
  to prove them. One advantage of having these lemmas is that we can now prove
  propositions that use `sorted` without needing to worry about how `sorted` is
  defined exactly: the lemmas hide the implementation details. In fact, we could
  change the definition of `sorted` (as long as the lemmas are still true)
  without affecting any later proofs. We would just need to reprove the lemmas
  themselves. This observation is very similar to the "encapsulation" principle
  of software engineering, and you should think about "proof engineering" in the
  same way. -/

/-
  We see two new Lean concepts in the lemmas above. The minor one is in
  `head_sorted` and `cons_sorted'` where we see things like
  `List.pairwise_cons.1`. `List.pairwise_cons` is a `↔`, which previously we
  deconstructed using `obtain`. However, a `↔` is really just a pair, and like
  any pair we can access its elements using `.1` (the forward implication) and
  `.2` (the backward implication). This is also true for `∧`, where `.1` is the
  left conjunct and `.2` is the right conjunct.

  The more major new concept is _implicit parameters_, which we see in all the
  lemmas. These are the parameters surrounded by `{}` instead of `()`. Given a
  call to the function (recall that `theorem` is a function definition whose
  body is a proof) Lean will try to automatically infer the arguments to be
  passed for those parameters, based on the values passed to other parameters,
  rather than having them be explicitly passed by the caller. If we look at
  `head_sorted`, for example, we see that `n` and `ℓ` are implicit; if we call
  `head_sorted` and pass in a proof of `sorted (n :: ℓ)`, that gives Lean enough
  information to figure out what `n` and `ℓ` are supposed to be.
-/

/-
  Notice that we call `head_sorted` only with `h` and Lean automatically infers
  that the implicit parameter `n` should be `k` and `ℓ` should be `xs`. -/
example (k : ℕ) (xs : List ℕ) (h : sorted (k :: xs)) :=
  head_sorted h

/-
  Implicit parameters can be used for any function definition, not just
  theorems. We should generally only make a parameter implicit if the remaining
  parameters give enough information for Lean to figure them out, but there are
  sometimes reasons to do otherwise. -/

end_topic INSERTION_SORT_P2


topic::INSERTION_SORT_P3
open INSERTION_SORT_P2 -- make the definitions in `P2` available here

/-
  We would like to verify `insertion_sort`, but to do so we'll also need to
  verify `insert`. What does it mean for `insert` to be correct? Of course we
  would like its output to be sorted, but that isn't sufficient; we would also
  like it to have actually added `n` to the output. But that also isn't
  sufficient or our implementation could just always return `[n]`, which is a
  sorted list that contains `n`. We also need to require that the output list
  contains all the elements of the input list (including any duplicate
  elements). Finally, `insert` only works if its input list is also sorted.
  Correctly specifying the verification condition is a critical part of
  verification: if we have the specification wrong then everything that follows
  is wasted. -/

/-
  Here is the verification condition for `insert`. We use the already-existing
  `List.Perm` to state that two lists are permutations of each other. The `let`
  allows us to give a name to some expression so that we don't need to keep
  writing the expression multiple times. -/
def insert_correct_prop (n : ℕ) (ℓ : List ℕ) : Prop :=
  let ℓ' := insertion_sort.insert n ℓ
  (sorted ℓ → sorted ℓ') ∧ ℓ'.Perm (n :: ℓ)

/-
  We could prove the entire proposition at once, but I like to break them down
  into simpler lemmas and then recombine them into a final proof. Whether you
  think this is worthwhile is a personal style decision (in this case we
  actually need to use `insert_perm` in the proof of `insert_sorted`, so it's a
  good idea). I'll break each conjunct into a separate lemma, and then prove the
  actual theorem we want by combining those proofs. We will see some more new
  Lean concepts, which we will explain further after the proofs. -/

lemma insert_perm
  {n : ℕ} {ℓ : List ℕ}
  : (insertion_sort.insert n ℓ).Perm (n :: ℓ)
:= by
  /- Structural induction on list `ℓ` -/
  induction ℓ with
  | nil => exact List.Perm.refl [n]
  | cons x xs ih =>
    /-
      `insertion_sort.insert` does different things depending on whether `n ≤ x`
      or not, so we need to case on that -/
    by_cases h : n ≤ x
    case pos =>
      unfold insertion_sort.insert
      rw [if_pos h] -- reduce the `if` in the goal
    case neg =>
      unfold insertion_sort.insert
      rw [if_neg h] -- reduce the `if` in the goal
      have h1 : (x :: insertion_sort.insert n xs).Perm (x :: n :: xs) :=
        List.Perm.cons x ih
      have h2 : (x :: n :: xs).Perm (n :: x :: xs) :=
        List.Perm.swap n x xs
      exact List.Perm.trans h1 h2

lemma insert_sorted
  {n : ℕ} {ℓ : List ℕ}
  : sorted ℓ → sorted (insertion_sort.insert n ℓ)
:= by
  intro h1
  /-
    Functional induction on the definition of `insertion_sort.insert`, with one
    case per control-flow path through the function -/
  fun_induction insertion_sort.insert with
  | case1 => exact singleton_sorted
  | case2 x xs h2 => exact cons_sorted' h1 h2
  | case3 m xs h ih =>
    /-
      The only non-trivial case. We need to apply a number of lemmas and
      theorems to reach the desired goal. -/
    have h2 := tail_sorted h1
    have h3 := ih h2
    have h4 := head_sorted h1
    have h5 := @insert_perm n xs
    have h6 : ∀ k ∈ (insertion_sort.insert n xs), m ≤ k := by
      intro k hk
      have h6 := (List.Perm.mem_iff h5).1 hk
      cases List.mem_cons.1 h6 with
      | inl h7 => lia
      | inr h7 =>
        have h8 := h4 k h7
        lia
    unfold sorted
    unfold sorted at h3
    exact List.pairwise_cons.2 ⟨h6, h3⟩

theorem insert_correct {n : ℕ} {ℓ : List ℕ} :
    let ℓ' := insertion_sort.insert n ℓ
    (sorted ℓ → sorted ℓ') ∧ ℓ'.Perm (n :: ℓ)
:= ⟨insert_sorted, insert_perm⟩

/-
  Let's talk about the new concepts encountered in these proofs. The minor thing
  is the `@` in `insert_sorted` in `case3`: `@insert_perm n xs`. Recall that
  `insert_perm` has two implicit arguments `n` and `ℓ` that we would like Lean
  to automatically infer. However, in this case Lean does not have sufficient
  information to infer them and so we need to provide them explicitly. Using `@`
  tells Lean to treat implicit parameters as if they were explicit parameters.

  The major new concepts are _structural induction_ and _functional induction_.
  You may or may not have heard of structural induction; some lower-level
  courses cover it and some don't. We'll cover it here to be thorough, and then
  contrast it with functional induction.
-/

subtopic::STRUCTURAL_INDUCTION
/-
  The lemma `insert_perm` uses structural induction on lists, so let's see how
  it works. We have used lists, but we haven't looked at how they are defined.
  Here is a custom definition of lists that closely mimics the actual
  definition. -/

/-
  This is an _inductive type_. A `MyList` can be made using one of two
  _constructors_: the `nil` constructor takes no arguments and creates an empty
  `MyList`, and the `cons` constructor takes a value of the correct type and
  another `MyList` to create a new `MyList`. -/
inductive MyList (α : Type) where
  | nil : MyList α
  | cons (x : α) (xs : MyList α) : MyList α

/-
  An inductive type is similar to what functional programmers call "algebraic
  datatypes". The constructors are really just functions whose return type is
  the inductive type being defined (hence the name "constructor"), however they
  are functions without any bodies. Instead, they save their arguments to be
  retrieved later using pattern-matching. -/

#check MyList.nil
#check MyList.cons

/-
  Here is the list [1, 2] -/
def list := MyList.cons 1 (MyList.cons 2 MyList.nil)

/-
  Here is a function that uses pattern-matching to sum the elements of a list of
  numbers. Note that the `cons` case gives us access to the value and list that
  were used as arguments to the `cons` constructor. -/
def sum_list (ℓ : MyList ℕ) : ℕ :=
  match ℓ with
  | .nil => 0
  | .cons x xs => x + sum_list xs

#eval sum_list list

/-
  The standard `List` data structure is almost exactly like the `MyList`
  definition, but Lean has special syntax to make it easier to use -/

/-
  These are all the same -/
#eval [1, 2]
#eval 1 :: 2 :: []
#eval List.cons 1 (List.cons 2 List.nil)

/-
  What does all this have to do with induction? We can do an inductive proof on
  terms of any inductive type; this is called _structural induction_. The base
  cases and inductive cases depend on the constructors: each constructor that
  does not have a recursive mention of the type being defined is a base case,
  each other constructor is an inductive case. -/

/-
  We have one base case `nil` and one inductive case `cons`, where the inductive
  case has an inductive hypothesis `ih` -/
example {α : Type} (ℓ : List α) : ℓ.tail.length ≤ ℓ.length := by
  induction ℓ with
  | nil =>
    unfold List.tail List.length
    rfl
  | cons x xs ih =>
    rw [List.tail_cons, List.length_cons]
    lia

end_subtopic STRUCTURAL_INDUCTION


subtopic::FUNCTIONAL_INDUCTION
/-
  When trying to prove something about a recursive function, induction is the
  natural approach. However, it is usually best for the inductive proof to
  follow the structure of the recursive function or things can get messy. In the
  lemma `insert_perm`, in the inductive case, we had to use `by_cases` to cover
  two different paths in the `insertion_sort.insert` function: one where `n ≤ x`
  and one where `¬n ≤ x`. This is a very mild case showing where the structural
  induction cases and the function definition don't quite line up; there are
  much nastier examples.

  Lean provides a method to tailor induction to the specific recursive function
  we're proving something about; this is called _functional induction_. In other
  words, functional induction follows the recursive structure of the function
  definition, not the structure of an object given as argument to the function.
  There is a case per control-flow path through the function; the case is a base
  case if there is no recursive call on that path, otherwise it is an inductive
  case (with an inductive hypothesis). The lemma `insert_sorted` uses functional
  induction instead of structural induction. Notice that we don't need to
  manually mimic the branches of the code inside the function, `fun_induction`
  did it for us.

  Whether structural or functional induction is the right strategy depends on
  the specific circumstances, there is no one right answer. Sometimes you can
  prove the goal either way (but one may be messier than the other) and
  sometimes you _have_ to use one or the other or the goal is unprovable. The
  key thing to consider is what the inductive hypotheses will be and whether you
  need to reason about the different code paths in a function; these are usually
  the deciding factors.
-/
end_subtopic FUNCTIONAL_INDUCTION
end_topic INSERTION_SORT_P3


topic::INSERTION_SORT_P4
open INSERTION_SORT_P2 INSERTION_SORT_P3

/-
  So far we have defined `insertion_sort` (with nested function `insert`),
  defined a `sorted` predicate on lists of numbers, and proven that
  `insertion_sort.insert` behaves correctly. We can now prove the main theorem,
  that `insertion_sort` behaves correctly. I will again break the main theorem
  into two sub-lemmas and then combine them to prove the main theorem. Notice
  that the control-flow of `insertion_sort` exactly mimics the structure of `ℓ`,
  so structural and functional induction will both do the same thing. However,
  functional induction will automatically unfold the function for us, so it's a
  little (very little) bit more convenient. -/

lemma insertion_sort_sorted {ℓ : List ℕ} : sorted (insertion_sort ℓ) := by
  fun_induction insertion_sort with
  | case1 => exact empty_sorted
  | case2 x xs ih => exact insert_sorted ih

lemma insertion_sort_perm {ℓ : List ℕ} : (insertion_sort ℓ).Perm ℓ := by
  fun_induction insertion_sort with
  | case1 => exact List.Perm.nil
  | case2 x xs ih =>
    have h1 := @insert_perm x (insertion_sort xs)
    have h2 := (List.perm_cons x).2 ih
    exact List.Perm.trans h1 h2

theorem insertion_sort_correct
  (ℓ : List ℕ)
  : let ℓ' := insertion_sort ℓ
    sorted ℓ' ∧ List.Perm ℓ' ℓ
:= ⟨insertion_sort_sorted, insertion_sort_perm⟩

/-
  No surprises and no new concepts; with the lemmas we proved ahead of time the
  proofs are very straightforward -/

end_topic INSERTION_SORT_P4
