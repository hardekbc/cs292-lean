/-
  # Primer on Functional Programming

  - For anyone who is not experienced with functional programming in general, we give a really quick tutorial to introduce the topic. This tutorial is sufficient to at least understand what we're doing in the rest of the course, but to truly understand functional programming you have to _practice_.

  - I recommend the online book "Functional Programming in Lean" (link given in `L01_Intro`) as a good resource; it was written for people who do not already know functional programming and, as the name implies, is specific to Lean. There are also many functional programming tutorials available on the web for other functional languages whose ideas carry over into Lean.
-/

import Course.CourseLib

topic::OVERVIEW
/-
  - Functional programming is strongly inspired by mathematical functions: given some input, that input is plugged into an expression and evaluated to get the output. There are no statements, only expressions. There are no mutations or assignments: within a given scope, a variable or expression _always_ has the same value wherever it is used. There is no iteration via loops, only recursion (note that all loops can be expressed as recursion, and vice-versa).

  - This is an entirely new perspective on programming than imperative programming, and if you aren't used to it then it can take some time to wrap your head around. People coming to functional programming from imperative programming often approach decomposing problems and writing functions in the same way they would have in an imperative language and it becomes extremely painful. This is because functional programming requires a different way of _thinking_ about decomposing problems and writing functions; if you try to approach it like imperative programming things won't go well.

  - Higher-order functions play a key role. These used to be solely a functional language concept, but more recently even mainstream imperative languages have borrowed this idea. However, in functional programming they are ubiquitious.

  - If you are only familiar with imperative programming, it is valuable to learn functional programming just to learn this new perspective and way of thinking about problems.
-/
end_topic OVERVIEW


topic::HIGHER_ORDER_FUNCTIONS
/-
  Higher-order functions take other functions as arguments and/or return other
  functions as their result. First-order functions abstract _data_, higher-order
  functions abstract _computation_. -/

/-
  This first-order function always does the same computation (adding two
  numbers), but abstracts _which_ two numbers as parameters -/
def first_order (n m : ℕ) := n + m

#eval first_order 40 2

/-
  This higher-order function additionally abstracts _what_ computation to
  perform on the two numbers as another parameter -/
def higher_order (n m : ℕ) (f : ℕ → ℕ → ℕ) := f n m

#eval higher_order 40 2 (· + ·)
#eval higher_order 40 2 (· * ·)

end_topic HIGHER_ORDER_FUNCTIONS


topic::ITERATION
/-
  - There are some standard higher-order functions that use this concept to implement the recursion necessary for iterating through a list, but abstract out the computation to perform while doing that iteration

  - Many things that would require loops in an imperative language can be handled by these functions, so that the recursion is hidden away

  - We will define some of these functions ourselves here for pedagogical purposes, but they are all already defined in the Lean standard library
-/

/- `map` transforms each element of a list using a given function -/
#check List.map

/-
  `α` : the type of elements in the given list
  `β` : the type of elements in the resulting list
  `f` : the function to transform each element in the list
-/
def map {α β : Type} (f : α → β) : List α → List β
  | [] => []
  | hd :: tl => f hd :: map f tl

#eval map (· * 2) [1, 2, 3]
#eval map (·.length) ["a", "ab", "abc"]

/-
  `foldl` ("fold left") traverses a list and accumulates an aggregate value from
  all of the list elements -/
#check List.foldl

/-
  `α` : the type of the result
  `β` : the type of elements in the given list
  `f` : takes the current accumulated value and the current element and
        returns the new accumulated value
  `init` : the initial value, also the result if the list is empty
-/
def fold {α β : Type} (f : α → β → α) (init : α) : List β → α
  | [] => init
  | hd :: tl => fold f (f init hd) tl

#eval fold (· + ·) 0 [1, 2, 3]
#eval fold (fun acc el => -el :: acc) [] [1, 2, 3]

/- `filter` removes elements that don't satisfy a given predicate -/
#check List.filter

/-
  `α` : the type of elements in the given list
  `f` : a boolean predicate on type `α`
-/
def filter {α : Type} (f : α → Bool) : List α → List α
  | [] => []
  | hd :: tl =>
    if f hd then hd :: filter f tl
    else filter f tl

#eval filter (· % 2 = 0) [1, 2, 3, 4]

/-
  If we want to iterate over multiple lists, pairing up corresponding elements,
  then we use _zip_. This function takes two lists and turns them into a single
  list of pairs. -/
#eval [1, 2, 3].zip [4, 5, 6]

/-
  Takes two lists and returns a single list whose elements are the product of
  the corresponding elements of the input lists -/
def mul_lists (ℓ₁ ℓ₂ : List ℕ) : List ℕ :=
  (ℓ₁.zip ℓ₂).map (fun (a, b) => a * b)

#eval mul_lists [1, 2, 3] [4, 5, 6]

/-
  The dual is _unzip_, which takes a list of pairs and returns a pair of two
  lists. -/
#eval [(1, 4), (2, 5), (3, 6)].unzip

end_topic ITERATION


topic::COMPOSITION
/-
  In imperative programming we often build up to a final result by computing a
  bunch of intermediate results, one per statement. In functional programming we
  instead use _function composition_ to feed intermediate results directly to
  the next computation without even naming them. This mirrors the way that
  mathematical functions work: to build complex functions we compose simpler
  functions together. This general principle of programming is called
  _point-free_ programming (where breaking each intermediate result into its own
  isolated computation and naming the result is called _pointful_). -/

/-
  Here are two function (trivial functions since it's just an example, but they
  could be arbitrarily complex) -/
def double (a : ℕ) := 2 * a
def add2 (a : ℕ) := a + 2

/-
  One way to combine them is pointfully, as in imperative programming -/
example (a : ℕ) :=
  let x := double a
  add2 x

/-
  Here we instead combine them using function composition. This is identical to
  the mathematical notion of function composition, and also has the same
  requirements (the codomain of the right-side function has to match the domain
  of the left-side function). -/
def double_then_add := add2 ∘ double
def add_then_double := double ∘ add2

#check double_then_add
#check add_then_double

#eval double_then_add 2
#eval add_then_double 2

/-
  Suppose we want to take a list of numbers, filter them to only those that are
  ≤ 10, double the elements of the resulting list, then sum them all to get a
  final result. Here is a pointful way to do that. -/
example (ℓ : List ℕ) :=
  let x := ℓ.filter (· ≤ 10)
  let y := x.map (· * 2)
  y.foldl (· + ·) 0

/-
  Here is the point-free way to do it -/
example (ℓ : List ℕ) :=
  ((ℓ.filter (· ≤ 10)).map (· * 2)).foldl (· + ·) 0

/-
  Having to use all the parentheses can be annoying, so Lean provides the _pipe_
  operator `|>` (and its dual `<|`). `|>` evaluates its left side and then feeds
  it as input to its right side. Here is the same function using pipes. Lean is
  able to infer that `filter` and `map` are on `List` so we don't have to say it
  explicitly, but it can't for `foldl` (presumably because of various type
  coercions). -/
example (ℓ : List ℕ) :=
  ℓ |> .filter (· ≤ 10)
    |> .map (· * 2)
    |> List.foldl (· + ·) 0

end_topic COMPOSITION


topic::TAIL_RECURSION
/-
  - Typically every recursive call pushes a new stack frame onto the function stack, which can be bad for deeply-recursive executions

  - A common optimization in functional languages is to recognize _tail-recursive functions_ and optimize them to avoid using the function stack

    + A function is tail-recursive if, for all execution paths in the function that contain a recursive call, that call is the last thing to be executed along that execution path

    + This fact means that once that recursive call returns, there is nothing left to do in the caller and it will immediately return itself without further computation...and so there is no point in pushing a new stack frame for the recursive call, we can just re-use the existing stack frame, since it won't be used after the call anyway

    + This optimization is called _tail-call optimization_, and it ensures that recursive calls that "act like loops" are as efficient as loops

  - If we look at `map`, `fold`, and `filter` above:

    + `map` is _not_ tail-recursive, because after the recursive call to `map` it still needs to preprend `f hd` to the return value of the recursive call

    + `fold` _is_ tail-recursive, because along the execution path that leads to the recursive call to `fold`, that call is that last thing to do

    + `filter` is _not_ tail-recursive, because while there is one execution path that has a recursive call in tail-recursive position, there is another path with a recursive call that is not in tail-recursive position

  - There is a common idiom called _accumulators_ that can be used to turn some non-tail-recursive functions into tail-recursive functions

    + The idea is to add an extra parameter to the function that "accumulates" the final result, rather than waiting to compute the result as the recursion returns
-/

/- This factorial implementation is not tail-recursive -/
def factor₁ (n : ℕ) :=
  if n = 0 then 1
  else n * factor₁ (n-1)

#eval factor₁ 7

/- But this one _is_, where `acc` is the accumulator -/
def factor₂ (n : ℕ) (acc : ℕ := 1) :=
  if n = 0 then acc
  else factor₂ (n-1) (n*acc)

#eval factor₂ 7

/-
  The interface to the function changed; we fixed the issue by using a default
  value for `acc`, but we can also fix it using `let rec` or a `where` clause -/

def factor₃ (n : ℕ) :=
  let rec fact (n acc : ℕ) :=
    if n = 0 then acc
    else fact (n-1) (n*acc)
  fact n 1

def factor₄ (n : ℕ) :=
  fact n 1
where fact (n acc : ℕ) :=
  if n = 0 then acc
  else fact (n-1) (n*acc)

#eval factor₃ 7
#eval factor₄ 7

end_topic TAIL_RECURSION


topic::CURRYING
/-
  We have seen that functions can have multiple parameters, but in reality this
  is an illusion: all functions have exactly one parameter. However, we can act
  as if a function has multiple parameters using _currying_. The idea is to nest
  one function definition immediately inside of another, as in the example
  below. -/
def curried_add : ℕ → ℕ → ℕ := fun n₁ => fun n₂ => n₁ + n₂

/-
  If we call `curried_add` with one argument, e.g., `2`, we get back a new
  function that also takes one argument. That function has had the first
  parameter, i.e., `n₁`, replaced with the provided argument `2`. Calling a
  function with only some of its arguments is called _partial application_. -/
def partially_applied_add := curried_add 2

#check partially_applied_add

/-
  When we call the partially-applied function result with an argument we get the
  final result, which is the value provided for `n₁` (i.e., `2`) plus the value
  provided for `n₂`. -/
#eval partially_applied_add 5
#eval partially_applied_add 40

/-
  Lean's syntactic sugar allows us to define functions _as if_ they have
  multiple parameters, and to call them with multiple arguments, but under the
  hood it is using currying and we can always partially apply a function if we
  want -/
def add₁ (n₁ : ℕ) (n₂ : ℕ) := n₁ + n₂
def add2₁ := add₁ 2

#eval add₁ 2 5
#eval add2₁ 5

def add₂ : ℕ → ℕ → ℕ := fun n₁ n₂ => n₁ + n₂
def add2₂ : ℕ → ℕ := add₂ 2

#eval add₂ 2 5
#eval add2₂ 5

end_topic CURRYING
