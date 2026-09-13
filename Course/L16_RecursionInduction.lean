/-
  # Recursion and Induction

  We go more in-depth into recursion and induction, including mutual
  recursion, recursors, and custom induction principles -/

import Course.CourseLib

topic::MUTUAL_RECURSION
/-
  We can define mutually recursive functions using the `mutual` keyword (which
  starts a block that must be ended with `end`). Everything defined inside the
  mutual block is available in the bodies of all other definitions in the same
  block (but not their signatures). -/

/- A mutually-recursive way to compute the Fibonacci numbers -/
mutual
def A (i : ℕ) :=
  if i = 0 then 1
  else A (i-1) + B (i - 1)
def B (i : ℕ) :=
  if i = 0 then 1
  else A (i - 1)
end

def T (i : ℕ) :=
  A i + B i

#eval T 0
#eval T 1
#eval T 2
#eval T 3

/-
  Note that the following does not work because the definitions are _not_
  available in other definition's signatures, only their bodies. If we remove
  the mutual block but leave the `abbrev` and `def` then it works fine. -/
/--
  error: Unknown identifier `MyNat` -/
#guard_error
mutual
abbrev MyNat := ℕ
def n : MyNat := 42
end

/-
  - We didn't call it out at the time, but the `where` block for defining nested functions also allows for mutual recursion

  - Defining mutually-recursive functions puts more restrictions on what Lean can automatically recognize as structural recursion; for details see the Lean Language Reference
-/

/-
  `fun_induction` unfortunately does not work on mutually-recursive functions -/

mutual
def even : ℕ → Bool
  | 0 => true
  | n + 1 => odd n
def odd : ℕ → Bool
  | 0 => false
  | n + 1 => even n
end

/--
  error: No functional induction theorem for `even`, or function is mutually
  recursive -/
#guard_error
example (n : ℕ) : even (2 * n) := by
  fun_induction even

/-
  If we try to do regular induction on `n` then we get into a nested series of
  `unfold` followed by `split`, over and over again -/
example (n : ℕ) : even (2 * n) := by
  induction n with
  | zero => simp [even]
  | succ n ih =>
    unfold even at ih
    split at ih
    case h_1 heq =>
      have h1 : 2*(n + 1) = 2*n + 2 := by lia
      rw [h1, heq]
      decide
    case h_2 m heq =>
      have h1 : 2*(n + 1) = 2*n + 2 := by lia
      rw [h1, heq]
      unfold odd at ih
      split at ih
      case h_1 => contradiction
      case h_2 m => sorry -- keeps going...

/-
  So we do want to use functional induction, but we can't use our normal
  methods. One way to proceed is to use mutually-recursive theorems. -/

mutual
theorem even_double (n : ℕ) : even (2 * n) :=
  match n with
  | 0 => by simp [even]
  | m + 1 => by
    have h : 2 * (m + 1) = (2 * m + 1) + 1 := by rfl
    rw [h]
    simp [even]
    exact odd_double m

theorem odd_double (n : ℕ) : odd (2 * n + 1) :=
  match n with
  | 0 => by simp [even, odd]
  | m + 1 => by
    simp [odd]
    exact even_double (m + 1)
end

/-
  We've discussed before that Lean generates _recursors_ for inductive types,
  and that we can specify different induction principles when doing induction.
  Lean _also_ generates recursors for recursive functions, usually named
  `<function name>.induct`. The `fun_induction` tactic is just shorthand for
  using the corresponding function's recursor as an alternate induction
  principle. -/

/-
  A recursive function that we previously used `fun_induction` on -/
def alternate {α : Type} : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => x :: alternate ys xs
termination_by xs ys => xs.length + ys.length

/-
  It's recursor, which is what `fun_induction` was actually using -/
#check @alternate.induct

/-
  Now consider the mutually-recursive functions `even` and `odd` defined above
  (which `fun_induction` doesn't work on). We see that `even`s recursor has
  _two_ motives, one for each mutually-recursive function, and _four_ cases, one
  for each control-path through each mutually-recursive function -/
#check @even.induct

/-
  We can use `even.induct` directly as an alternate induction principle.
  `induction` will implicitly figure out `motive_1` from the goal, but we need
  to explicitly specify `motive_2`. -/
example (n : ℕ) : even (2 * n) := by
  induction n using even.induct (motive_2 := fun n => odd (2 * n + 1)) with
  | case1       => simp_all [even]
  | case2 m ih1 => simp_all [even, odd, Nat.mul_add]
  | case3       => simp_all [even, odd]
  | case4 m ih1 => simp_all [even, odd, Nat.mul_add]

/-
  `odd` also has a recursor -/
#check odd.induct

/-
  And we can prove a similar theorem in a similar way (though now we need to
  explicitly specify `motive_1` instead of `motive_2`). In fact, notice that
  we're redoing a lot of the work that we did in the previous example. -/
example (n : ℕ) : odd (2 * n + 1) := by
  induction n using odd.induct (motive_1 := fun n => even (2 * n)) with
  | case1       => simp_all [even]
  | case2 m ih1 => simp_all [even, odd, Nat.mul_add]
  | case3       => simp_all [even, odd]
  | case4 m ih1 => simp_all [even, odd, Nat.mul_add]

/-
  Lean will also generate a recursor that allows us to prove both motives as
  once, called `<function name>.mutual_induct`. Notice that it is almost the
  same as the previous recursors, except the conclusion is a conjunction of the
  two conclusions from the previous recursors. -/
#check even.mutual_induct

/-
  However, `induction` can't handle this recursor because it isn't in the form
  that it expects, and so if we want to use it then we need to apply it manually
  instead of using the `induction` tactic -/
example : ((n : ℕ) → even (2 * n)) ∧ ((n : ℕ) → odd (2 * n + 1)) := by
  apply even.mutual_induct
  · simp_all [even]
  · simp_all [even, odd, Nat.mul_add]
  · simp_all [even, odd]
  · simp_all [even, odd, Nat.mul_add]

end_topic MUTUAL_RECURSION


topic::RECURSORS
/-
  Every inductive type has a set of _constructors_ that give a way to create a
  value of that type. However, to actually use a value of that type we also need
  an _eliminator_, i.e., something that can take such a value and do something
  with it. In Lean, that eliminator is called a _recursor_ and one is
  automatically created for every inductive type. All recursion and induction
  (and degenerate forms of recursion and induction, such as pattern-matching and
  proof by cases) is implemented in terms of recursors. -/

/-
  We previously looked at the recursor for `ℕ` -/
#check Nat.recOn

/-
  Here is the recursor for `List` -/
#check List.recOn

/-
  - Here it is in a more readable format:

    List.recOn.{u_1, u}
      {α : Type u}
      {motive : List α → Sort u_1}
      (t : List α)
      (nil : motive [])
      (cons : (head : α) →
                (tail : List α) →
                  motive tail →
                    motive (head :: tail))
      : motive t

  - For an inductive type `T`, the recursor's type has the following parameters. When Lean elaborates an instance of recursion or induction, it is turned into a call to a recursor with the appropriate arguments for these parameters.

    1. `T`s parameters. Because the parameters of an inductive type are consistent across all constructors, we can abstract them out of the individual constructors. `List` has the parameter `α : Type u`, and thus so does its recursor.

    2. The _motive_, i.e., the type of an application of the recursor. The parameter of the motive is an element of `T` and the result type is `Sort u`, which basically means either `Prop` or `Type u` for some number `u`.

      + Think of the motive as stating "when we call the recursor on a value of type `T`, this is the type that we'll get back"

      + If we're using the recursor for recursion then we'll get back a value of some type. For example if we're recursing through a list to compute its length then the motive will have signature `motive : List α → ℕ`.

      + If we're using the recursor for induction then we'll get back a proof of some proposition, i.e., the motive is a _predicate_. For example if we're doing induction on a list to prove that the length of the tail of a list is no greater than the length of the list then the motive will have a signature like `motive : (ℓ : List α) → ℓ.tail.length ≤ ℓ.length`, which can also be written as `motive : ∀ (ℓ : List α), ℓ.tail.length ≤ ℓ.length`.

    3. A _minor premise_ for each constructor, establishing the motive for each possible case. The `List` recursor has a minor premise for `nil` establishing `motive []` and another for `cons` establishing that, given `head : α`, `tail : List α`, and `motive tail` (i.e., the result of calling the recursor on `tail`) establishes `motive head :: tail`.

      + If we're doing induction then the minor premises for cases without recursive mentions of `T` are the base cases and the minor premises for cases with recursive mentions of `T` are the inductive cases (where the extra `motive` arguments, e.g., `motive tail` in the `cons` minor premise for the `List` example, are the inductive hypotheses)

    4. A _major premise_, aka "target", i.e., the value of type `T` we're calling the recursor on. For the `List` recursor this is `t : List α`. The major premise will also include any indices if `T` has them.

      + If we're doing induction then the major premise is the object of type `T` that we're doing induction on

  - Pattern-matching and proof by cases are implemented by `T.casesOn`, which in turn is implemented using `T.recOn`
-/

#check Nat.casesOn

#check List.casesOn

/-
  - There can be multiple recursors for the same inductive type. For example, for `List` we have (at least): `List.recOn`, `List.rec`, `List.brecOn`, `List.recOnNeNil`, and `List.reverseRecOn`.

    + `List.rec` is the same as `List.recOn` except it orders the parameters differently

    + `List.brecOn` is the `List` version of strong induction, i.e., it has one minor case with an argument that establishes the motive for all elements of the list "below" (that is, _before_) the current one (`brecOn` stands for "below" `recOn`)

    + `List.recOnNeNil` is a recursor specifically for non-empty lists

    + `List.reverseRecOn` we've seen before, it recursively traverses the list from front to back instead of back to front

  - Some recursors are automatically generated for each inductive type (I believe just `rec` and `recOn`), the others have to be created manually
-/

#check List.rec

#check List.brecOn

#check List.recOnNeNil

#check List.reverseRecOn

/-
  _All_ inductive types get recursors, even ones that don't recursively mention
  themselves. For these types the recursor is essentially just a "by cases". -/

inductive T
  | one : ℕ → T
  | two : Bool → T

#check T.recOn

/-
  Recursive functions also get recursors (but not non-recursive functions). The
  recursor is called `induct` instead of `recOn` and its signature is determined
  by the set of control-flow paths through the function. This recursor is the
  induction principle being applied when we use the `fun_induction` tactic. -/

def sum : ℕ → ℕ
  | 0 => 0
  | n + 1 => 1 + sum n

/-
  Notice that when the function is defined in a way that mirrors the definition
  of the inductive type given as argument (i.e., the body of the function is a
  pattern-match on the inductive type) then the function's recursor is the same
  as the inductive type's recursor, as in this example. For functions like this
  doing `fun_induction` is the same as doing `induction` on the argument. -/
#check sum.induct

/-
  Here is the `merge` function from our merge-sort example -/
def merge : List ℕ → List ℕ → List ℕ
  | [], ℓ₂ => ℓ₂
  | ℓ₁, [] => ℓ₁
  | x :: ℓ₁, y :: ℓ₂ =>
    if x ≤ y then x :: merge ℓ₁ (y :: ℓ₂)
    else y :: merge (x :: ℓ₁) ℓ₂

/-
  Notice that there are four minor premises, one for each possible control-flow
  path through the function -/
#check merge.induct

/-
  In this example we directly use the `List` recursor to define a function that
  computes the sum of the elements of the list. We use named argument passing to
  make the example more clear. -/
def list_sum (ℓ : List ℕ) : ℕ :=
  @List.recOn
    (α := ℕ)
    (motive := fun _ => ℕ)
    (t := ℓ)
    (nil := 0)
    (cons := fun hd _tail acc => hd + acc)

/-
  And here we use the same recursor to prove a theorem that the length of the
  tail of a list is no greater than the length of the list itself -/
theorem list_len
  {α : Type} (ℓ : List α)
  : ℓ.tail.length ≤ ℓ.length
:=
  @List.recOn
    (α := α)
    (motive := fun ℓ => ℓ.tail.length ≤ ℓ.length)
    (t := ℓ)
    (nil := by grind)
    (cons := fun hd tail ih => by grind)

/-
  Surface-level Lean is complicated (though the kernel is very simple, and
  that's the part that's verified), and dependent type-checking is not
  decidable, so sometimes we might try recursion or induction (via tactics or
  otherwise) and it gives an error or doesn't work the way we think it should.
  One thing we can do in that situation is try to directly use the recursor,
  by-passing all the complicated elaboration that Lean usually has to do. -/

end_topic RECURSORS


topic::CUSTOM_INDUCTION_PRINCIPLES
/-
  Now that we understand recursors, we can talk about how to create our own
  induction principles. The concept is simple: we write our own recursor. When
  we apply the tactic `induction <whatever> using <principle>`, the
  `<principle>` we specify is just the recursor that we want Lean to use. -/

variable {α : Type}

/-
  -----------------------------------------------------------
  INTEGER INDUCTION EXAMPLE (adapted from Mathlib)
  -----------------------------------------------------------
-/

/-
  Integers are defined on top of natural numbers, with two cases each taking a
  natural number `n`: (1) `n` is an integer, covering all non-negative integers;
  (2) `-(n+1)` is an integer, covering all negative integers -/
#print Int

/-
  - There is a principle of induction defined for `ℤ` in Mathlib, but we will reimplement here. Note that it is specialized to `Prop`, so it can only be used for induction not recursion.

  - Our induction principle has three cases, one base case and two inductive cases:

    + P 0
    + ∀ (n : ℕ), P n → P (n+1)
    + ∀ (n : ℕ), P (-n) → P (-n-1)

  - The proof is required to show that these cases are sufficient to cover all integers. Note the `↑` in the proof state, which we have not encountered before: this marker represents a type coercion, in this case from `ℕ` to `ℤ`.
-/
theorem int_ind
  {motive : ℤ → Prop}
  (t : ℤ)
  (zero : motive 0)
  (succ : ∀ (n : ℕ), motive n → motive (n + 1))
  (pred : ∀ (n : ℕ), motive (-n) → motive (-n - 1))
  : motive t
:= by
  cases t with
  | ofNat n => (induction n with grind)
  | negSucc n =>
    /-
      Because of the "negative successor" way of defining negative integers,
      doing induction on `n` won't help here (try it and you'll see that the
      inductive hypothesis won't allow us to use `pred` the way we need to).
      Instead we'll prove something stronger, and then leverage that to use
      `pred` to get our final result. -/
    have h : ∀ n : ℕ, motive (-n) := by
      intro n
      induction n with first | assumption | grind
    exact h (n + 1)

example : ∀ (z : ℤ), Even z ∨ Odd z := by
  intro z
  /-
    We can do the whole proof with `grind` but I want to show the structure of
    the inductive principle we defined -/
  induction z using int_ind with
  | zero => grind
  | succ n ih => grind
  | pred n ih => grind

/-
  -----------------------------------------------------------
  PALINDROME EXAMPLE (adapted from lean-lang.org)
  -----------------------------------------------------------
-/

/-
  An type describing palindromes: strings s.t. each half mirrors the other. We
  will be more general than just strings and use lists of arbitrary elements. -/
@[grind cases, grind intro]
inductive Palindrome : List α → Prop where
  | nil         : Palindrome []
  | single a    : Palindrome [a]
  | mirror a as : Palindrome as → Palindrome ([a] ++ as ++ [a])

/-
  Here is the default recursor. The names have been cleaned up a little in the
  signature to make it easier to read.

  Palindrome.recOn
    {α : Type}
    {motive : ∀ (ℓ : List α), Palindrome ℓ → Prop}
    {ℓ : List α}
    (t : Palindrome ℓ)
    (nil : motive [] Palindrome.nil)
    (single : ∀ (a : α), motive [a] (Palindrome.single a))
    (mirror : ∀ (a : α) (as : List α) (ih : Palindrome as),
        motive as ih → motive ([a] ++ as ++ [a]) (Palindrome.mirror a as ih))
    : motive ℓ t
-/
set_option pp.proofs true in
#check Palindrome.recOn

/-
  Dropping the last element in a list and appending that same element back again
  yields the original list (if the list was not empty) -/
@[simp, grind =]
lemma dropLast_append_getLast
  {as : List α} (h : as ≠ [])
  : as.dropLast ++ [as.getLast h] = as
:= by induction as using List.reverseRecOn with grind

/-
  The default recursor is fine for reasoning about `Palindrome`, but we also
  want to be able to reason about _lists_ (e.g., to prove that they are
  palindromes) and `List` does not have an appropriate induction principle. So
  we create a custom induction principle for lists that we want to reason about
  in terms of palindromes. -/
theorem palindrome_ind
    (motive : List α → Prop)
    (nil_case : motive [])
    (single_case : (a : α) → motive [a])
    (mirror_case : (a b : α) → (as : List α) → motive as → motive ([a] ++ as ++ [b]))
    (t : List α)
    : motive t
:=
  /-
    Standard `List` induction on `t` is a terrible way to prove this, which is
    why we're creating this induction principle in the first place. Instead
    we'll do a term proof with explicit recursion. -/
  match t with
  | [] => nil_case
  | [a] => single_case a
  | a :: b :: tail =>
    let (eq := heq) tail' := (b :: tail).dropLast
    have ih := palindrome_ind motive nil_case single_case mirror_case tail'
    have h : [a] ++ tail' ++ [(b :: tail).getLast (by simp)] = a :: b :: tail := by grind
    h ▸ mirror_case _ _ _ ih
termination_by t.length

/-
  If a string reads the same forwards as backwards, it is a palindrome -/
theorem palindrome_of_eq_reverse
  {as : List α} (h : as.reverse = as)
  : Palindrome as
:= by
  /-
    We can do the whole proof using `grind`, but I want to show the structure of
    the new inductive principle -/
  induction as using palindrome_ind with
  | nil_case => grind
  | single_case a => grind
  | mirror_case a b as ih => grind

/-
  -----------------------------------------------------------
  REFLEXIVE TRANSITIVE CLOSURE EXAMPLE (adapted from LoVe)
  -----------------------------------------------------------
-/

/-
  The reflexive, transitive closure of a relation. Notice that we have defined
  it in terms of adding the transitive closure on the "tail", i.e., the proof is
  `a R⋆ b → b R c → a R⋆ c` -/
@[grind cases, grind intro]
inductive Rtc (R : α → α → Prop) : α → α → Prop
  | refl (a : α) : Rtc R a a
  | tail {a b c : α} : Rtc R a b → R b c → Rtc R a c

/-
  Here is the default recursor. Notice that Lean promoted the first index to a
  parameter; it does that whenever it can, i.e., it observes that every
  recursive call uses the same argument in that position (as happens in `Rtc`
  for the first index). The names have been cleaned up a little in the signature
  to make it easier to read.

  Rtc.recOn
    {α : Type}
    {R : α → α → Prop} <<--- parameter
    {a : α}            <<--- erstwhile first index, now a parameter
    {motive : ∀ (b : α), Rtc R a b → Prop}
    {y : α}            <<--- second (now only) index
    (t : Rtc R a y)
    (refl : motive a (Rtc.refl a))
    (tail : ∀ {b c : α} (h₁ : Rtc R a b) (h₂ : R b c),
        motive b h₁ → motive c (Rtc.tail h₁ h₂))
    : motive y t
-/
set_option pp.proofs true in -- tells Lean to print proofs instead of ⋯
#check Rtc.recOn

/-
  We can also prove a transitive relation via `x R y → y R⋆ z → x R⋆ z -/
lemma Rtc.head
  {α : Type} {R : α → α → Prop} {x y z : α} (hab : R x y) (hbc : Rtc R y z)
  : Rtc R x z
:= by
  /-
    We could do the whole proof with `grind`, but I want to make the default
    induction principle clear -/
  induction hbc with
  | refl => exact tail (refl x) hab
  | tail hab' hbc' ih => grind

/-
  If we use the standard induction principle it assumes we're trying to add a
  new relation onto the "tail" of the existing transitive closure---but
  sometimes we want to reason the other way around, i.e., by taking an existing
  transitive closure and add a new relation to the "head". We will create a new
  induction principle that allows us to reason this way. -/
theorem Rtc.from_head_ind
  {α : Type}
  {R : α → α → Prop} -- <<--- parameter
  {x : α}            -- <<--- erstwhile first index, now parameter
  {motive : (a : α) → Rtc R a x → Prop}
  {y : α}            -- <<--- second (now only) index
  (t : Rtc R y x)
  (refl_case : motive x (Rtc.refl x))
  (head_case : ∀ {a b : α} (h₁ : R a b) (h₂ : Rtc R b x),
        motive b h₂ → motive a (head h₁ h₂))
  : motive y t
:= by induction t with aesop

/-
  We define a relation between lists stating that the first list is equal to the
  second minus its last element -/
def missing_last (xs ys : List α) := ∃ a, xs ++ [a] = ys

/-
  The reflexive, transitive closure of this relation is the prefix relation -/
def prefix_of := @Rtc (List α) missing_last

/-
  We try to prove, using the standard induction principle for `Rtc`, that if
  `xs` is a prefix of `ys` then there is some element `a` s.t. `xs ++ [a]` is
  still a prefix of `ys`, assuming that `xs ≠ ys`. -/
example
  {xs ys : List α}
  : xs ≠ ys → prefix_of xs ys → ∃ a, prefix_of (xs ++ [a]) ys
:= by
  intro h₁ h₂
  induction h₂ with
  | refl => sorry
  | tail h₃ h₄ ih =>
    rename_i as bs
    /- Inductive hypothesis isn't much help -/
    sorry

/-
  Here is the same theorem, proved using our new induction principle -/
example
  {xs ys : List α}
  : xs ≠ ys → prefix_of xs ys → ∃ a, prefix_of (xs ++ [a]) ys
:= by
  intro h₁ h₂
  induction h₂ using Rtc.from_head_ind with
  | refl_case => contradiction
  | head_case h₁ h₂ ih =>
    rename_i as bs h₃
    obtain ⟨a, ha⟩ := h₃
    exists a
    by_cases h₄ : bs = ys
    case pos =>
      rw [← h₄, ha]
      exact Rtc.refl bs
    case neg =>
      obtain ⟨b, hb⟩ := ih h₄
      rw [← ha] at hb
      have h₅ : missing_last (as ++ [a]) (as ++ [a] ++ [b]) := by exists b
      exact Rtc.head h₅ hb

end_topic CUSTOM_INDUCTION_PRINCIPLES
