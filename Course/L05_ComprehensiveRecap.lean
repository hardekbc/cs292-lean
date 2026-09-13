/-
  # Comprehensive Recap

  - We have learned a lot of Lean by example up to this point, which is good from one perspective but bad from another: all the material is scattered around and introduced piece-meal, and we have only seen the specific variations of concepts used in the examples

  - Here we review all of the things we have learned, organized and all in one place; we also take the opportunity to fill in some missing pieces and go more into detail on how things work and their different variations

    + This recap expands on material covered in L03--L04

  - I will not be covering most of this material in lecture; I expect you to read it on your own and be responsible for knowing it. However, I will pick out some particularly important highlights to discuss.
-/

import Course.CourseLib

topic::INTERACTION
/-
  The Lean IDE allows you to interact with it directly in the editor via
  _commands_, which often (but not always) start with `#`. There are a number of
  commands, but we will highlight `#check`, `#eval`, and `#print`. -/

/-
  Outputs the type of an expression -/
#check 2 + 40

/-
  `#check` will use special syntax for showing the type of a top-level function
  unless we put its name in `()` -/
def f (n : ℕ) : ℕ := n + 1

#check f
#check (f)

/-
  Evaluates an expression -/
#eval 2 + 40

/-
  We can create any top-level definition using `def`, not just functions -/
def sum := 2 + 40

/-
  Prints the definition of the given name (does _not_ evaluate it) -/
#print sum

/-
  VS Code reminder: if you see a keyword, function name, or other definition
  that you don't recognize, hover over it and a tooltip will pop up with an
  explanation. Similarly, if you see a symbol that you don't know how to type,
  hover over it and a tooltip will explain how to type it. But where do those
  tooltips from from? -/

/--
  A _docstring_ looks just like a block comment except that it starts with two
  hyphens instead of one. If you hover over the `x` in the `example` below you
  will see this text in the tooltip. -/
def x := 42
example : ℕ := x

/-
  - Lean also allows us to import other files into the current file, making its definitions available (and those of any files that _that_ file imports). However, definitions declared as `private` will not be made available. A definition can be made private by using `private def <name> := ...`.

  - There is no demo given here for the import command because all imports _must_ happen at the top of the file, that is, as the very first non-comment code in the file

  - The syntax is: `import <path>.<to>.<file>`, where the path starts from the project root, directory slashes are replaced by `.`, and the file is specified by name without the `.lean` extension. There is an example `import` statement at the top of this file, importing the course library `CourseLib.lean`.

  - Definitions from imported files can clash with definitions in the current file; Lean has a standard solution to this problem called _namespaces_. We will discuss those further later.
-/
end_topic INTERACTION


topic::TYPES
/-
  Lean has the concept of _type universes_. We will discuss these in much more
  detail later, but for now we highlight two common universes: `Type` and
  `Prop`. We will wave our hands a bit when explaining them here, and clarify
  things when we dig deeper into the concept later. -/

/-
  `Type` is the universe of computable things. The types you are used to from
  other languages all live in `Type`, such as integers, booleans, lists, trees,
  etc...all the things that you might write functions to manipulate. -/
#check ℤ
#check Bool
#check List ℕ

/-
  `Prop` is the universe of logical propositions. Propositions are types, but
  they are types that Lean interprets specifically as things we want to prove,
  not things we want to compute. -/
#check 2 + 2 = 4
#check ∀ x, Even x → Even (x + 2)

/-
  Here are some types in Lean that you are probably familiar with from other
  languages. They all live in `Type`. -/
#check 42
#check -42
#check true
#check "a string"
#check ['l', 'i', 's', 't']
#check #["i'm", "an", "array"]

/-
  Note that `ℕ` is notation for the type `Nat` (natural numbers) and `ℤ` is
  notation for the type `Int` (integers). Integers and natural numbers (aka
  unsigned integers) can be arbitrarily large; they are not confined to a
  particular bit-width -/
#check (42 : Nat)
#check (42 : Int)

/-
  Here are some Lean types that you may be familiar with if you have done any
  functional programming. Again, they all live in `Type`. -/

/-
  `Unit` is the type that has exactly one possible value, written `()`. Every
  expression in a functional programming language must have a value; `Unit` is
  what we use to say that an expression's value doesn't really matter. -/
#check ()

/-
  `Prod` is the type of pairs, and has special notation -/
#check (1, 2)
#check (-2, "A")

/-
  `Sum` is the type of disjoint unions, and also has special notation. A sum
  type `α ⊕ β` (where `α` and `β` are types) means that a value can be either
  from `α` or from `β`. Moreover, given a value of a sum type we can ask _which_
  side it came from, that is, is the value an `α` or a `β`. We'll talk a bit
  more about how to use sum types in the next topic. -/
#check (Sum.inl 42 : ℕ ⊕ String)
#check (Sum.inr "A" : ℕ ⊕ String)

/-
  `Option` is the type of things that may not have a value. A value of type
  `Option α` (where `α` is a type) can be either `some v` where `v : α`, or it
  can be `none` meaning "no value". -/
#check Option.some 42
#check (Option.none : Option String)

/-
  Here are some types peculiar to Lean -/

/-
  `Fin n` is the type of natural numbers ≤ `n`. For example `x : Fin 2` means
  that `x` must be 0 or 1. -/
#check (42 : Fin 64)

/-
  Sets in Lean can be _infinite_ sets, e.g., the set of all even natural
  numbers. This is distinct from most languages where sets must be finite. -/
#check { n : ℕ | Even n }

/-
  Under the hood, `Set` is really a predicate `α → Prop`, i.e., it is the
  characteristic function of a set -/
#print Set

/-
  If we want specifically _finite_ sets we can use `Finset` (among other
  options) -/
#check ({1, 2, 3} : Finset ℕ)

/-
  - Here is a list of other data structures that are in core Lean or in the Mathlib library:

    + Associative list
    + Binary heap
    + Binomial heap
    + Bitvector
    + Floating-point
    + HashMap
    + HashSet
    + Int{8, 16, 32, 64}
    + Range
    + TreeMap
    + TreeSet
    + UInt{8, 16, 32, 64}
    + Union-find

  - There may be other data structures available in the _Reservoir_ at https://reservoir.lean-lang.org/, a public registry for third-party Lean libraries and binaries
-/

/-
  Notice in the examples above that Lean will infer types automatically whenever
  it can. Where we are supposed to use `: <type>`, if Lean can infer the
  information automatically then we don't need to have those. This includes when
  defining function parameters and return types. -/

/-
  In some of the examples above I _did_ have to specify types, using the syntax
  `( <exp> : <type> )`. If Lean can't figure out the type of an expression by
  itself, or gives it a different type than you want, you can tell it explicitly
  what type to use with _type ascription_. `(<exp> : <type>)` means to ascribe
  the type `<type>` to the expression `<exp>` -/
#check 42
#check (42 : ℤ)

/-
  We can use type ascription around any expression at any point. The type being
  ascribed must be compatible or you'll get an error -/
#check_failure (42 : String)

end_topic TYPES


topic::EXPRESSIONS
/-
  Like all functional languages Lean is "expression-oriented". There is no
  "statement" vs "expression", _everything_ is an expression. Sometimes things
  may look like statements, but they are just syntactic sugar for expressions
  (we'll see examples later). -/

/-
  Arithmetic expressions. Note that subtraction on natural numbers saturates at
  0 and that any number divided by 0 equals 0. These definitions are consistent
  with the fact that subtracting a larger natural number from a smaller one and
  dividing by zero are both mathematically undefined, and they are necessary
  because Lean functions must be total. For `Fin n` arithmetic wraps around. -/
#eval 40 + 2
#eval 2 - 40
#eval 42 % 5
#eval 42 / 0
#eval (2 - 40 : ℤ)
#eval (4 : Fin 6) + 3
#eval (4 : Fin 6) - 5

/- List expressions with concatenation and appending -/
#eval 1 :: [2, 3] ++ [4, 5]

/-
  We can get the head element of a list using `.head`, but doing so requires a
  proof that the list is not empty. Using `.head?` does not require a proof, but
  returns an `Option` type instead that is `none` if the list is empty. We can
  get the tail elements of a list using `.tail`; it returns `[]` if the list is
  empty. We can also index into a list as if it were an array; we need a proof
  that the index is within bounds but Lean will infer it automatically if
  possible. -/
#eval [1, 2, 3].head (by simp)
#eval [1, 2, 3].head?
#eval ([] : List ℕ).head?
#eval [1, 2, 3].tail
#eval ([] : List ℕ).tail
#eval [1, 2, 3][1]

/- String expressions, including string interpolation -/
#eval "hello " ++ "world"
#eval s!"40 + 2 = {40 + 2}"

/-
  Array expressions with indexing, appending, and subarrays. We need a proof
  that the index is within bounds, but Lean infers it automatically when
  possible. -/
#eval #[1, 2, 3][1]
#eval #[1, 2] ++ #[3]
#eval #[1, 2, 3, 4][1:3]
#eval #[1, 2, 3][1 + 1]

/- Set operations on finite sets -/
#eval ({1, 2, 3} ∪ {3, 4, 5} : Finset ℕ)
#eval ({1, 2, 3} ∩ {3, 4, 5} : Finset ℕ)

/-
  `if-else` expressions (we _always_ need the else branch) -/
#eval if 1 < 3 then "true" else "false"

/-
  If we need an expression or proof but don't have anything to use, we can
  always use `sorry` which is an expression that Lean infers to have whatever
  type is necessary to make the overall expression type-check correctly. Think
  of `sorry` as a temporary placeholder. We can use it in computable expressions
  or in proofs (it counts as a tactic). -/
#check 2 + sorry
#check "hello" ++ sorry
#check [1, 2, 3].head sorry
example : 2 + 2 = 4 := by sorry

/-
  However, an expression with `sorry` in it cannot be evaluated -/
/--
  error: Aborting evaluation since the expression depends on the 'sorry' axiom,
  which can lead to runtime instability and crashes. -/
#guard_error
#eval 2 + sorry

/-
  If the expression does not have a textual representation it will also cause an
  error. In this example the value of the expression is a closure, which does
  not have a textual representation. -/
/--
  error: Could not synthesize a `ToExpr`, `Repr`, or `ToString` instance for
  type ℕ → ℕ -/
#guard_error
#eval fun (x : ℕ) => x

end_topic EXPRESSIONS


topic::FUNCTIONS
/-
  - Functions can be defined at the top-level using `def` with syntax:
    `def` <name> `(`<prm> `:` <type>`)` `:` <return type> `:=` <expression>

  - They can also be defined as "anonymous" functions (aka lambda expressions, aka closures) anywhere an expression is legal:
    `fun` `(`<prm> `:` <type>`)` `=>` <expression>
-/

/-
  Defining `foo` as a top-level function; it has a `ℕ` as a parameter and
  returns the negation of its argument as an `ℤ` -/
def foo₁ (n : ℕ) : ℤ := -n
#check foo₁
#check (foo₁)

/-
  Here is the same function defined as an anonymous function in four different
  ways. Notice that there is no way to specify the return type for anonymous
  functions except by giving an explicit type for the entire `def`. Again, we
  can omit the parameter type if Lean can infer one (which it definitely can if
  we give the `def` an explicit type). If we don't give the `def` an explicit
  type then Lean can still infer one, but it may not be the one we intended
  unless we use a type ascription. -/
def foo₂ : ℕ → ℤ := fun (n : ℕ) => -n
def foo₃ : ℕ → ℤ := fun n => -n
def foo₄ := fun n => -n
def foo₅ := (fun n => -n : ℕ → ℤ)

#check (foo₂)
#check (foo₃)
#check (foo₄)
#check (foo₅)

/-
  We left out one variation above: what if we give the parameter type without
  giving the return type? Then for this example Lean gives us an error because
  we can't take the negative of a natural number and Lean does not generally do
  implicit type conversions. -/
/--
  error: failed to synthesize instance of type class Neg ℕ -/
#guard_error
def foo₆ := fun (n : ℕ) => -n

/-
  To fix the error, besides specifying the type of `foo₆` or giving the entire
  function a type ascription, we could also just give `n` a type ascription in
  the body. -/
def foo₆ := fun (n : ℕ) => -(n : ℤ)

/-
  The general rule is that as long as we give Lean enough information to infer a
  valid type for every expression, it doesn't really matter how or where we give
  it the necessary information. Also, all of the `fooₙ`s are essentially the
  same thing, there is no difference between a top-level function definition and
  an anonymous function definition -/

/-
  As syntactic sugar we can also replace `fun` with `λ` and/or `=>` with `↦`.
  Note that the commonly accepted standard is to use `fun` and `=>`. -/
def foo₇ := λn ↦ -n
def foo₈ := λ(n : ℕ) ↦ -(n : ℤ)

#check (foo₇)
#check (foo₈)

/-
  We call a function as follows: <function name> <argument>. It doesn't matter
  whether the function is top-level or anonymous. -/
#eval foo₁ 42
#eval foo₂ 42

/-
  We can also call an anonymous function directly, without using `def` to give
  it a name first -/
#eval (fun n => -n) 42

/-
  As syntactic sugar, if an expression `e` has some type `<type>` and a function
  is defined as `<type>.<name>`, then we can call the function as `e.<name>` and
  it will act as if we had said `<type>.<name> e`, i.e., as if we had called the
  function using normal function call syntax. This feature is related to
  namespaces and we will discuss it more when we cover that topic. -/
#check List.length
#eval [1, 2, 3].length

/-
  All of the function examples so far have had a single parameter, but there can
  be an arbitrary number of parameters -/
def bar₁ (n₁ : ℕ) (n₂ : ℕ) : ℕ := n₁ + n₂
#eval bar₁ 2 40

/-
  Parameters that have the same type can be grouped together -/
def bar₂ (n₁ n₂ : ℕ) : ℕ := n₁ + n₂
#eval bar₂ 2 40

/-
  As syntactic sugar, if we are defining an anonymous function where each
  parameter is used exactly once then we can define it as a parenthesized
  expression using `·` to stand for each parameter in turn -/

/- This is the same as `(fun x => x + 1) 2` -/
#eval (· + 1) 2

/- This is the same as `(fun x y => x + y) 1 2` -/
#eval (· + ·) 1 2

/-
  Nested functions can be defined in a subordinate `where` clause to a parent
  function. This is easiest to explain by example, as below. -/
def outer_fun (n : ℕ) :=
  double n + triple n
where
  double (n : ℕ) := 2 * n
  triple (n : ℕ) := 3 * n

#check (outer_fun)
#check_failure double
#check_failure triple
#check (outer_fun.double)
#check (outer_fun.triple)

#eval outer_fun 2
#eval outer_fun.double 2
#eval outer_fun.triple 2

/-
  We can give function parameters _default values_, i.e., the parameter will
  take that value unless the caller gives it a different one -/
def add_default_5 (n₁ : ℕ) (n₂ : ℕ := 5) := n₁ + n₂

#eval add_default_5 2
#eval add_default_5 2 40

/-
  But default parameters should go last in the parameter list or they can cause
  problems. In the following example the first parameter has a default value but
  the second one does not. -/
def add_default_3 (n₁ : ℕ := 3) (n₂ : ℕ) := n₁ + n₂

/-
  When we call the function with one value it is used to replaced the default
  value of the first parameter, not as the value of the second parameter. -/
#check add_default_3 2

/--
  error: Could not synthesize a `ToExpr`, `Repr`, or `ToString` instance for
  type ℕ → ℕ -/
#guard_error
#eval add_default_3 2

/-
  We can also call functions with _named arguments_ instead of using the default
  _positional arguments_, i.e., we can specify each parameter's value by name
  instead of giving them in the order of the parameter list (and so we can give
  the arguments in any order) -/
#eval add_default_3 (n₂ := 2)
#eval add_default_3 (n₂ := 2) (n₁ := 40)

/-
  - We can specify some function parameters to be _implicit_, i.e., given a call Lean will infer the value for the parameter automatically rather than having it be explicitly specified by the call.

  - In the example below, the first function parameter is a type and the second is a list of that type. The first parameter is made implicit by using `{}` instead of `()`.
-/
def list_len {α : Type} (ℓ : List α) := ℓ.length

#check list_len

/-
  For the calls in the following two lines Lean is able to infer the value of
  parameter `α` (i.e., `ℕ` and `String`) because for parameter `ℓ` we are
  passing in a `List ℕ` and a `List String`. In general parameters should only
  be made implicit if their value is obvious based on the remaining parameters.
-/
#eval list_len [1, 2, 3]
#eval list_len ["a", "b", "c"]

/-
  Sometimes Lean is not able to infer the correct value for an implicit
  parameter; fortunately there is a way to tell Lean to ignore "implicitness"
  and treat every parameter as explicit: simply prepend `@` to the name of the
  function. -/
#check (@list_len)
#check (@list_len String)
#eval @list_len ℤ [1, 2, 3]

/- Or alternatively, we can use named arguments to override "implicitness" -/
#eval list_len (α := ℤ) [1, 2, 3]

/-
  - As a convenience, by default Lean will also automatically insert any undefined variables used in a function's signature as implicit parameters. This is mainly useful for theorems (which we will discuss later), but works for functions as well.

  - I have turned off this feature for the code in this repo, but in the following example I have turned it back on just for the definition of `list_len₂`. Notice that the parameter uses `α` which is not defined anywhere, but Lean still accepts the definition because it has inserted `{α : Type}` as an implicit parameter.
-/
set_option autoImplicit true in
def list_len₂ (ℓ : List α) := ℓ.length

/-
  Notice in `list_len₂`s type that Lean has inserted `α` as an implicit
  parameter, and recursively also inserted a universe variable. We'll talk more
  about universes later, so ignore the `u_1` parts for now. -/
#check list_len₂

/-
  Not everyone thinks this behavior is a good idea, e.g., a typo could cause an
  implicit parameter to be inserted instead of being flagged as an error. You
  can turn this behavior off locally inside a particular file by using the
  command `set_option autoImplicit false` (I have turned this option off by
  default for the entire repo using `lakefile.toml`). The following definition
  shows the error you get instead of the default auto-implicit behavior. -/
/--
  error: Unknown identifier `α` -/
#guard_error
def list_len₃ (ℓ : List α) := ℓ.length

end_topic FUNCTIONS


topic::EXPRESSIONS_PART2
/-
  A quick trip back to expressions. Sometimes inside a function we may want to
  use the same expression in multiple places. Rather than repeating ourselves,
  we can use `let` to give the expression a name and just use that name multiple
  times. -/

/- Without `let` -/
def some_fun₁ (n : ℕ) :=
  2 * (n + 1) + 3 * (n + 1)

/- With `let` -/
def some_fun₂ (n : ℕ) :=
  let plus_one := n + 1
  2 * plus_one + 3 * plus_one

#eval some_fun₁ 1
#eval some_fun₂ 1

/-
  `let` may look like a statement, but it's really an expression. We can think
  of it as short-hand for a function call. Here is the same function with `let`
  rewritten in terms of a function call. -/
def some_fun₃ (n : ℕ) :=
  (fun plus_one => 2 * plus_one + 3 * plus_one) (n + 1)

/-
  `let` can also use pattern-matching to destruct certain types into their
  constituent elements, such as pairs. In the following example the function is
  given a pair and we use `let` to extract the elements of the pair. -/
example (pair : ℕ × ℕ) : ℕ :=
  let (a, b) := pair
  a * b

/-
  We can combine `let` pattern-matching with an `if-else`. If the `let`
  pattern-match works we execute the true branch, otherwise the false branch. -/
example (maybe_val? : Option ℕ) : ℕ :=
  if let some n := maybe_val? then n + 2 else 0

/-
  Use `let rec` to refer to a recursive expression (subject to the same
  constraints that we discuss in the `RECURSION` topic below). Remove the `rec`
  part to see the error. -/
example (n : ℕ) : ℕ :=
  let rec fact (n : ℕ) :=
    if n = 0 then 1 else n * fact (n-1)
  fact n

end_topic EXPRESSIONS_PART2


topic::INDUCTIVE_TYPES
/-
  Inductive types are user-defined data structures. They are Lean's version of
  what standard functional languages call "algebraic datatypes". Because of
  Lean's nature, they are in many ways more general than algebraic datatypes but
  in a few ways are more restricted (due to the requirement for totality). -/

/-
  Here is a simple inductive type that is similar to an enum from C++ (except
  that it doesn't map entries to integers). The name of the type is `Enum` and
  there are three _constructors_, i.e., three different ways that a value of
  type `Enum` can be created: `first`, `second`, and `third`. -/
inductive Enum : Type where
  | first  : Enum
  | second : Enum
  | third  : Enum

#check (Enum.first)
#check (Enum.second)
#check (Enum.third)

/-
  The `: Type`, `where`, and `: Enum` are all optional. If there is no `: Type`
  (which specifies that the inductive type being defined lives in the universe
  `Type`) then it is just assumed. -/
inductive Enum'
  | first
  | second
  | third

/-
  The constructors can have (multiple) parameters; in fact, they're really just
  functions whose final codomain is the type being defined, and they can be used
  anywhere a function is expected. The constructor functions don't have
  explicit bodies; the arguments to the constructor are preserved and can be
  retrieved using pattern-matching. -/
inductive WithConsParams
  | first (n : ℕ)
  | second (s : String)

#check (WithConsParams.first)
#check (WithConsParams.second)

#check WithConsParams.first 42
#check WithConsParams.second "hello"

/-
  We can give the constructor types directly, similar to the type of an
  anonymous function. If we do so then we _must_ specify the final codomain as
  the inductive type being defined (as shown below). The definition below is the
  same as the definition above except that the constructor parameters don't have
  names. -/
inductive WithConsParams'
  | first  : ℕ → WithConsParams'
  | second : String → WithConsParams'

/-
  These types are called _inductive_ because we can use them to inductively
  define a type with infinite possible values. We do this by giving constructors
  parameters that are the type being defined. Note that we always need at least
  one base case (i.e., a constructor that doesn't take the type being defined)
  or there won't be any way to actually create such a type. -/

/-
  A list of natural numbers -/
inductive ℕList
  | nil -- empty list
  | cons (head : ℕ) (tail : ℕList) -- prepend ℕ to existing list

#eval ℕList.cons 1 (ℕList.cons 2 ℕList.nil)

/-
  A binary tree whose leaves hold natural numbers -/
inductive ℕBinTree
  | leaf : ℕ → ℕBinTree
  | node (left : ℕBinTree) (right : ℕBinTree)

#eval ℕBinTree.node
  (ℕBinTree.leaf 1)
  (ℕBinTree.node (ℕBinTree.leaf 2) (ℕBinTree.leaf 3))

/-
  We can also give inductive types themselves parameters (as opposed to their
  constructors); the requirement is that they are used in a consistent way
  across all constructors for that type (explained in more detail below). In the
  example below the parameter is of type `Type`, but it can be of any type in
  general. I added the `where` even though it is optional just to show where the
  parameter is placed. -/
inductive MyList (α : Type) where
  | nil
  | cons : α → MyList α → MyList α

#check (MyList)
#check @MyList ℕ

/-
  Note that any inductive type parameters become implicit parameters of the
  constructors, even if they are _explicit_ parameters of the inductive type -/

#check MyList.nil
#check @MyList.nil ℕ

#check MyList.cons
#check @MyList.cons ℕ
#check MyList.cons 42 MyList.nil

/-
  By "consistent" we mean that all occurrences of the type being defined must
  have exactly the same argument in all of the constructors that recursively
  mention the type being defined. See the errors below for examples of
  inconsistent usage. -/

/-
  Here the type of argument `e` is `ExampleIT₁ x` but should be `ExampleIT₁ n`
  to be consistent with the type parameter -/
/--
  error: (kernel) invalid occurrence of datatype 'INDUCTIVE_TYPES.ExampleIT₁'
  being declared -/
#guard_error
inductive ExampleIT₁ (n : ℕ)
| one (x : ℕ) (e : ExampleIT₁ x) : ExampleIT₁ n

/-
  Here the result type for constructor `two` is `ExampleIT₂ x`, but should be
  `ExampleIT₂ n` to be consistent with the type parameter -/
/--
  error: Mismatched inductive type parameter in ExampleIT₂ x The provided
  argument x is not definitionally equal to the expected parameter n -/
#guard_error
inductive ExampleIT₂ (n : ℕ)
  | one (x : ℕ) : ExampleIT₂ n
  | two (x : ℕ) : ExampleIT₂ x

/-
  - So far inductive types mirror algebraic datatypes pretty closely; later we'll see how they can be even more expressive when we make use of dependent typing. However, here we will see how they are more restricted than algebraic datatypes, due to their requirement for _strict positivity_.

  - A position is _strictly positive_ if:

    1. It is not in a function's argument type (even if the function is nested inside another function's type); and

    2. It is not an argument of any expression other than constructors of inductive types.

  - Lean requires that all occurrences of the type being defined must only appear in a strictly positive position. This requirement allows Lean to rule out problematic cases that would admit nontermination and unsoundness, at the cost of also ruling out some non-problematic cases as well.

  - The two example inductive types below both fail the strictly positive check, the first because `FailsSP₁` appears in the argument type of a function and the second because `FailsSP₂` appears as the argument to a non-constructor.
-/

/--
  error: (kernel) arg #1 of 'INDUCTIVE_TYPES.FailsSP₁.bad' has a non positive
  occurrence of the datatypes being declared -/
#guard_error
inductive FailsSP₁
  | bad : (FailsSP₁ → ℕ) → FailsSP₁

/--
  error: (kernel) arg #2 of 'INDUCTIVE_TYPES.FailsSP₂.bad' contains a non valid
  occurrence of the datatypes being declared -/
#guard_error
inductive FailsSP₂ (f : Type → Type)
  | bad : f (FailsSP₂ f) → FailsSP₂ f

/-
  The following example is fine and passes the strictly positive check; the
  requirement that `IsSP` cannot occur in any function's argument type doesn't
  apply to `IsSP`s constructors, just any parameters of those constructors -/
inductive IsSP
  | good : IsSP → IsSP → IsSP

/-
  There is one situation where we can technically violate strict positivity:
  nested inductive types. A nested inductive type is where the type being
  defined occurs as the argument to another inductive type. Lean is able to
  guarantee soundness if certain conditions are met (see the Lean Language
  Reference for details). -/

/-
  A tree whose nodes can have an arbitrary number of children. Since `RoseTree`
  is passed as an argument to `List`, this is a nested inductive type. -/
inductive RoseTree (α : Type)
  | leaf : α → RoseTree α
  | node : List (RoseTree α) → RoseTree α

end_topic INDUCTIVE_TYPES


topic::INDUCTIVE_PREDICATES
/-
  _Inductive predicates_ are a useful way to define predicates that recursively
  mention themselves. In reality they are just inductive types that live in
  `Prop` instead of in `Type`, and are defined in exactly the same way except
  that we need to specify that the type being defined lives in `Prop`. -/

/-
  - A predicate on lists defining whether they are palindromes (adapted from `lean-lang.org`):

    + An empty list is a palindrome (case `empty`)
    + A single-element list is a palindrome (case `singleton`)
    + If `as` is a palindrome, then for any element `a`, `[a] ++ as ++ [a]` is a palindrome (case `mirror`)

  - To be useful an inductive predicate will usually be _indexed_, i.e., instead of `: Prop` we use `: <type> → Prop` (for unary predicates; we would use `: <type₁> → <type₂> → Prop` for binary predicates, etc). The index indicates the object that the predicate is about. In this example we specify `List α → Prop`, meaning that this is a unary predicate about objects of type `List α`. We will talk more in-depth about indices later.

    + Note in the example below that we give different arguments for the index each time we refer to `Palindrome` in the constructors. This is one important difference between indices and parameters: parameters must be consistent, indices do not.

    + To reiterate: it's an inductive type _parameter_ if it comes _before_ the `:`, it's an inductive type _index_ if it comes _after_ the `:`
-/
inductive Palindrome {α : Type} : List α → Prop
  | empty : Palindrome []
  | singleton (a : α) : Palindrome [a]
  | mirror (a : α) {as : List α} : Palindrome as → Palindrome ([a] ++ as ++ [a])

/-
  A proof that the empty list of natural numbers is a palindrome (we need to use
  `@` because the empty list doesn't give enough information for Lean to tell
  that it's a list of `ℕ` specifically). The proof is simply a construction of
  `Palindrome []` using the `Palindrome.empty` constructor. -/
example : @Palindrome ℕ [] :=
  Palindrome.empty

/-
  A proof that `[3]` is a palindrome, using the `Palindrome.singleton`
  constructor -/
example : Palindrome [3] :=
  Palindrome.singleton 3

/-
  A proof that `[1, 3, 1]` is a palindrome, using the `Palindrome.mirror`
  constructor. Note that we need to use the `Palindrome.singleton` constructor
  to create a proof that `[3]` is a palindrome in order to pass it to the
  `Palindrome.mirror` constructor. -/
example : Palindrome [1, 3, 1] :=
  Palindrome.mirror 1 (Palindrome.singleton 3)

/-
  - We could actually write a function that determines whether a list is a palindrome, with signature `List α → Bool`, so the above example doesn't strongly motivate inductive predicates. Consider a more useful example: the reflexive transitive closure of a relation. Recall that `Rel α α` is a binary relation on type `α` that is implemented as a function `α → α → Prop`.

    + We'll use the infix notation `a R b` for `R a b` and `a R* b` for `RTC R a b`
    + `base` case: if `a R b` then `a R* b`
    + `refl` case: `a R* a`
    + `trans` case: if `a R* b` and `b R* c` then `a R* c`
-/
inductive Rtc {α : Type} (R : Rel α α) : Rel α α
  | base (a b : α) : R a b → Rtc R a b
  | refl (a : α) : Rtc R a a
  | trans (a b c : α) : Rtc R a b → Rtc R b c → Rtc R a c

/-
  - Consider how we might write a function that computes the reflexive transitive closure relation for an arbitrary input relation, as shown in `Rtc_fun` below.

    + The first problem is the error: Lean needs to know how to compute on the relationship and its elements. This problem is fixable (we'll cover the necessary topics later).

    + The second problem becomes apparent when we try to handle the transitivity case: we would somehow need to find some element `x` s.t. `a R x` and `x R b`, but we don't really have any way to do that
-/
/--
  error: failed to synthesize instance of type class Decidable -/
#guard_error
def Rtc_fun {α : Type} (R : Rel α α) : Rel α α :=
  fun (a b : α) =>
    if a = b then True
    else if R a b then True
    else
      -- need to determine if there is some `x` s.t. `a R* x` and `x R* b`
      sorry

/-
  - The advantage of the inductive predicate is that it allows us to state what is necessary for a predicate to be true without having to describe how to figure those things out for ourselves

    + We can use the inductive predicate to constructively prove a specific instance of the predicate is true without committing to the idea that the predicate is actually decidable for all possible instances

    + The downside of an inductive predicate is exactly that it is _not_ computable: it doesn't give us a procedure for determining whether it is true, it only describes the necessary criteria

  - Let's look at another example, the _Collatz Conjecture_. Consider the sequence that starts with `0 1` and then the `n`th number of the sequence is either: (1) if `n` is even then `n/2`; else (2) if `n` is odd then `3n + 1`. Does the sequence always converge to 1?

    + Nobody knows...it converges for all inputs we've checked (which is a lot), but so far no one has been able to prove that it _always_ converges

    + That means that we can't write a function for it that we can prove to Lean must terminate.
-/
/--
  error: fail to show termination for INDUCTIVE_PREDICATES.collatz -/
#guard_error
def collatz : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n =>
    if n % 2 = 0 then collatz (n / 2)
    else collatz (3*n + 1)

/-
  However, we _can_ write an inductive predicate about it. The inductive
  predicate `Collatz n r` means that for input `n` the result is `r`. -/
inductive Collatz : ℕ → ℕ → Prop where
  | base0 : Collatz 0 0
  | base1 : Collatz 1 1
  | even (n r : ℕ) : n ≠ 0 → n % 2 = 0 → Collatz (n / 2) r → Collatz n r
  | odd (n r : ℕ) : n ≠ 1 → n % 2 ≠ 0 → Collatz (3*n + 1) r → Collatz n r

/-
  - We cannot use `Collatz` to compute the answer, but we _can_ use it to prove things _about_ the Collatz sequence

  - As another approach we could use the "clocked recursion" strategy to force the `collatz` function to terminate, and then quantify over the fuel used
-/
def collatz' : ℕ → ℕ → Option ℕ
  | 0, _ => .none
  | f+1, n => match n with
    | 0 => .some 0
    | 1 => .some 1
    | n =>
      if n % 2 = 0 then collatz' f (n / 2)
      else collatz' f (3*n + 1)

/-
  The proposition that the Collatz sequence always converges, stated in two
  different ways -/
def collatz_converges₁ := ∀ n, Collatz n 1
def collatz_converges₂ := ∀ n, ∃ fuel, collatz' fuel n = .some 1

/-
  - Which approach is best depends on what you're trying to do, exactly; there is no "one best way" to specify things

  - We can even get the best of both worlds by proving that `Collatz` and `collatz'` agree with each other, so that we can use either one interchangeably depending on which one suits the moment
-/
end_topic INDUCTIVE_PREDICATES


topic::PATTERN_MATCHING
open INDUCTIVE_TYPES

/-
  If we have a value of some inductive type, we need to be able to determine
  which constructor was used to create it and what arguments (if any) were given
  to that constructor. We do this using _pattern matching_. -/

/-
  The `match` expression in the function below has one case per constructor.
  Note that Lean checks to be sure the pattern match cases are exhaustive (try
  commenting out one of the cases below to see the error). -/
def enum_tostring (e : Enum) : String :=
  match e with
  | Enum.first => "first"
  | Enum.second => "second"
  | Enum.third => "third"

#eval enum_tostring Enum.first
#eval enum_tostring Enum.second
#eval enum_tostring Enum.third

/-
  If Lean knows the type being pattern matched against, we don't need to give
  the entire type name in each case and instead just use `.<constructor>`. If a
  constructor has parameters then we can add variable names for each parameter;
  these names are scoped to only that specific case. -/
def consprms (w : WithConsParams) : String :=
  match w with
  | .first n => s!"n = {n}"
  | .second s => s!"s = {s}"

#eval consprms (WithConsParams.first 42)
#eval consprms (WithConsParams.second "hello")

/-
  Sometimes we want to pattern-match on components of an inductive type, but
  still have a name for the entire value. We can use `@` as shown below; `ℓ` is
  the name of the entire `.leaf n` value, while we still have access to the name
  `n` for the number inside the leaf. -/
example (t : ℕBinTree) : ℕBinTree :=
  match t with
  | ℓ@(.leaf n) => if n % 2 = 0 then ℓ else .leaf 0
  | .node left _ => left

/-
  We can match on multiple inductive types at once, simultaneously. Note that
  `_` in a pattern stands for "don't care", i.e., it will match anything -/
def simul_match (e : Enum) (w : WithConsParams) : String :=
  match e, w with
  | .first, .first n => s!"first/first, n = {n}"
  | .second, .second s => s!"second/second, s = {s}"
  | _, _ => ""

#eval simul_match Enum.first (WithConsParams.first 42)
#eval simul_match Enum.second (WithConsParams.second "hello")
#eval simul_match Enum.first (WithConsParams.second "hello")

/-
  A common coding pattern is to take an inductive type as a function parameter
  and immediately pattern match on it (as in the examples above). Lean gives us
  some syntactic sugar for this coding pattern as shown in the example below. -/

/-
  Note that the inductive type(s) being matched on come immediately after the `:` and there is no `:=` or `match <exp> with` -/
def enum_tostring' : Enum → String
  | Enum.first => "first"
  | Enum.second => "second"
  | Enum.third => "third"

def consprms' : WithConsParams → String
  | .first n => s!"n = {n}"
  | .second s => s!"s = {s}"

def simul_match' : Enum → WithConsParams → String
  | .first, .first n => s!"first/first, n = {n}"
  | .second, .second s => s!"second/second, s = {s}"
  | _, _ => ""

/-
  We can also use pattern matching in `let` expressions and function parameters
  if there is only one possible applicable constructor; we saw this before with
  `let` and pairs -/

def let_pattern (pair : ℕ × String) : String :=
  let (num, str) := pair
  s!"num = {num}, str = {str}"

#eval let_pattern (42, "hello")

def fun_pattern : ℕ × ℕ → ℕ :=
  fun (x, y) => x + y

#eval fun_pattern (40, 2)

/-
  We can use `if-let` for pattern matching when there is more than one possible
  applicable constructor, but we only care about one possibility. Note that we
  use `_tail` with an underscore to indicate that we intentionally don't use
  that variable, otherwise Lean would give a warning (remove the `_` in `_tail`
  below to see the warning). -/
def if_let_pattern (ℓ : List ℕ) : ℕ :=
  if let .cons head _tail := ℓ then head + 1
  else 0

end_topic PATTERN_MATCHING


topic::RECURSION
/-
  - We have stated before that nontermination leads to an inconsistent logic, which is why Lean insists that all functions (that it is allowed to reason about logically) must terminate. Why is this the case?

  - Consider the following function and theorem. If Lean did not prevent nontermination then `bad` would be a legitimate function, and we could use it as in the theorem `wrong` to prove anything we want.
-/

/--
  error: fail to show termination for RECURSION.bad -/
#guard_error
def bad {α} (_u : Unit) : α := bad ()

theorem wrong : 0 = 1 := bad ()

/-
  Strict positivity is enforced because we can use it to construct
  nonterminating functions that can be used to prove `False`, which by the
  principle of explosion allows us to again prove anything. Consider the example
  below, which causes an error. -/
/--
  error: (kernel) arg #1 of 'RECURSION.Bad.abs' has a non positive occurrence of
  the datatypes being declared -/
#guard_error
inductive Bad where
  | app : Bad → Bad → Bad
  | abs : (Bad → Bad) → Bad

/-
  Then we can define the following function of type `Bad → Bad` -/
def problem (b : Bad) : Bad :=
  match b with
  | .app => b
  | .abs f => f b

/-
  And then the following term is nonterminating (commented out to prevent Lean
  from actually trying to evaluate it). We won't show it here, but we can use a
  diagonalization-like construction to turn the nonterminating term into a proof
  of `False`. -/
-- #eval problem (.abs problem)

/-
  There are three possible approaches to recursive functions in Lean; they are:
  _partial functions_, _structural recursion_, and _well-founded recursion_. We
  can turn a partial function into structural recursion using the design pattern
  called _clocked recursion_. -/

/-
  _Partial functions_

  The `partial` keyword tells Lean that a function is not defined for every
  possible input, i.e., it may not terminate. The drawback of this option is
  that, because nontermination implies inconsistent logic, Lean will not allow
  any reasoning about partial functions (including about functions that call
  partial functions). This option is mainly useful when you do not care about
  proving anything related to the function you are defining. -/

/-
  Note that this function does not terminate if `n` is less than 0. Comment out
  the `partial` keyword to see the resulting error message. -/
partial def inf_loop (n : ℤ) : ℤ :=
  if n = 0 then n
  else if n > 0 then inf_loop (n - 1)
  else inf_loop n

#eval inf_loop 12

/-
  _Structural recursion_

  - If we use structural recursion then Lean can automatically determine that the recursion must terminate and will allow it without problem. Structural recursion means that we have an inductive type as a function parameter, and any recursive call must be made on a sub-piece of the inductive type value that was passed in as an argument.

    + Because all inductive types must have at least one base case, if we always recursively call the function with a sub-piece we must necessarily at some point reach a base case, and thus terminate
-/

/-
  Recall that `List` is an inductive type, with `nil` as a base case. Note that
  the recursive call is on `tl`, which is a sub-piece of the argument, i.e., a
  smaller list. -/
def list_sum : List ℤ → ℤ
  | .nil => 0
  | .cons n tl => n + list_sum tl

#eval list_sum [-5, 1, 6]

/-
  Recall that `ℕ` is also an inductive type, with `zero` as a base case, so we
  can use structural recursion on natural numbers. In this example Lean is able
  to figure out that in the false branch `n` cannot be 0, so then it must be
  `.succ n₁` for some `n₁`, and that `n-1` is the same thing as `n₁`, thus
  fulfilling the requirement for structural recursion. -/
def fact (n : ℕ) : ℕ :=
  if n = 0 then 1 else n * fact (n-1)

#eval fact 5

/-
  We could also make it more explicit by treating `ℕ` as an inductive type
  directly. -/
def fact₂ : ℕ → ℕ
  | .zero => 1
  | n@(.succ n₁) => n * fact₂ n₁

#eval fact₂ 5

/-
  The parameter being used for structural recursion doesn't have to be the first
  parameter, and any other parameter can increase instead of decrease so long as
  at least one parameter fits the structural recursion requirement -/
def fact₃ (cnt : ℤ) (n : ℕ) : ℤ × ℕ :=
  if n = 0 then (cnt, 1)
  else
    let (cnt', n') := fact₃ (cnt+1) (n-1)
    (cnt', n * n')

#eval fact₃ 0 5

/-
  _Clocked recursion_

  - Not all recursion can be expressed via structural recursion even if it is guaranteed to terminate. We can force functions to be structurally recursive by adding an additional inductive type parameter, usually of type `ℕ`, that always decreases with every recursive call. This extra parameter is often called _fuel_, because the size of the initial argument determines how many recursive calls can be made.

  - We need to consider what happens if we provide insufficient fuel...what should the function return? The default answer is to modify the return value to an `Option` type. If the function runs out of fuel it returns `none`, otherwise if it computes a final answer `a` it returns `some a`. There may be other answers.

  - The drawback of this approach is twofold:

    + When executing the function we need to be sure to provide sufficient fuel, and therefore we have to figure out how much fuel is "sufficient". If we change its return type to `Option` we also have to modify all calls to the function to determine whether the result was `none` or `some a` and figure out what to do if it's `none`.

    + When reasoning about the function we need to modify all the theorems to say something like "if we provide an amount of fuel s.t. that the result is `some a`, ...". This can make the statements womewhat awkward, and we have to be careful that the specification is saying what we really want.
-/

/-
   The following function computes the greatest common divisor of two natural
   numbers using the Euclidean algorithm. It is guaranteed to terminate but it
   does _not_ use structural recursion, and so Lean will not accept it. -/
/--
  error: fail to show termination for RECURSION.gcd -/
#guard_error
def gcd (m n : ℕ) : ℕ :=
  if m = 0 then n
  else gcd (n % m) m

/-
  Here is the version using clocked recursion -/
def clocked_gcd (fuel m n : ℕ) : Option ℕ :=
  if fuel = 0 then .none
  else if m = 0 then .some n
  else clocked_gcd (fuel-1) (n % m) m

#eval clocked_gcd 3 15 35
#eval clocked_gcd 2 15 35

/-
  _Well-founded recursion_

  - The final way to handle recursion is to prove to Lean that the recursion terminates using our own proof. A termination proof works as follows:

    + We must define some well-founded measure. A "measure" means some way to calculate the "size" of an input to the function. "Well-founded" means that we compare values of the measure using a well-founded order relation, i.e., for that order there is always a "least" value in any set of values. `ℕ` with `≤` is well-founded, because in any set of `ℕ` there is always a least value. `ℤ` with `≤` is _not_ well-founded because, e.g., the set of all `ℤ` does not have a least value.

    + We must then prove that, according to our well-founded measure, the size of a parameter (or some combination of parameters) is always decreasing with each recursive call. Thus, since the order is well-founded, it must eventually reach a least value where it cannot decrease further and hence the function terminates.

  - We use `termination_by` to define our measure. The measure should be some function of the arguments and must come from a well-founded set (e.g., the natural numbers). By default Lean uses a measure called `sizeOf` that is automatically implemented for every inductive type.

  - We use `decreasing_by` to prove that the measure decreases. By default Lean uses `decreasing_tactic` for the proof, which is specialized for creating such proofs. We can call `decreasing_tactic` manually if we need to explicitly provide some extra information for `decreasing_by` but then want to automate the rest.

  - We don't always need to provide both, sometimes Lean can infer one or the other
-/

/-
  Here we prove that `gcd'` terminates. Our measure is the value of the first
  parameter, and we prove that it always decreases for every recursive call. -/
def gcd' (m n : ℕ) : ℕ :=
  if m = 0 then n
  else gcd' (n % m) m
termination_by m -- select what measure is decreasing
decreasing_by    -- prove that (n % m) < m
  apply Nat.mod_lt _ (Nat.zero_lt_of_ne_zero _)
  assumption     -- m ≠ 0 because we're in the `else` branch

/-
  Here is another example that splices two lists together, alternating entries.
  This function is not structurally recursive, but it is well-founded. The
  measure is the sum of the lengths of the two argument lists---even though a
  particular argument's length is not always decreasing, the sum of the lengths
  is. We provide this information to Lean via `termination_by`, and it is able
  to automatically prove that the measure is decreasing. -/
def alternate {α : Type} : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => x :: alternate ys xs
termination_by xs ys => xs.length + ys.length

#eval alternate ["1", "2", "3"] ["a", "b", "c"]

/-
  Whether we need to provide arguments to `termination_by` (e.g., the `xs ys =>`
  in the example above) depends on whether there are parameters to the right of
  the `:` in the function signature. For example, here is the same function
  except that we have moved the arguments to the left of the `:`; notice that
  `termination_by` now has access to those arguments automatically. -/
def alternate' {α : Type} (xs ys : List α) : List α :=
  match xs, ys with
  | [], ys => ys
  | x :: xs, ys => x :: alternate' ys xs
termination_by xs.length + ys.length

/-
  Here is a function that is well-founded, but not obviously so. Lean infers the
  correct measure `n` but we need to prove to Lean that it decreases via
  `decreasing_by`. Note that the proof has `n ≠ 0` as a given because we're in
  the false branch of the conditional when we make the recursive call. -/
def foo₁ (n : ℕ) : ℕ :=
  if n = 0 then 1
  else foo₁ (((n * n) / n) - 1)
decreasing_by simp_all; lia

/-
  The default `decreasing_tactic` uses the `assumption` tactic, which checks
  whether any of the current givens close the goal. We can take advantage of
  this behavior to provide the necessary information inside the function itself
  if we want. However, in the following example the proof doesn't go through
  because we don't have the fact that `n ≠ 0` in the current context. Look at
  the proof state where the `sorry` is: the goal is not true for `n = 0`. -/
def foo₂ (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    have : ((n * n) / n) - 1 < n := sorry
    foo₂ (((n * n) / n) - 1)

/-
  We can fix that problem by adding `h :` to the `if` guard, which propagates
  the givens `h : n = 0` into the true branch and `h : n ≠ 0` into the false
  branch. Now we don't need a `decreasing_by` clause, because the default tactic
  picks up on the `have`. Besides `if` we can do the same trick with `match` to
  propagate guard conditions. -/
def foo₃ (n : ℕ) : ℕ :=
  if h : n = 0 then 1
  else
    have : ((n * n) / n) - 1 < n := by simp_all; lia
    foo₃ (((n * n) / n) - 1)

/-
  Here is an example where we need to provide both clauses. The function
  determines the minimum and maximum of the arguments, then makes a recursive
  call passing the minimum as first argument and the maximum - 1 as the second
  argument. The function is too complex for Lean to infer what to do. We tell
  Lean in the `termination_by` clause that our measure is on pairs of natural
  numbers, using the standard ordering on `Product` which is a lexicographic
  order (i.e., `(a, b) < (c, d)` if `a < c` or `a = c ∧ b < d`). We then have to
  prove that the arguments decrease according to this order. -/
set_option pp.proofs true in
def foo₄ (a b : ℕ) : ℕ :=
  if a = 0 then 1
  else
    let x := [a, b].min (by grind)
    let y := ([a, b].erase x).min (by grind)
    foo₄ x (y-1)
termination_by (a, b)
decreasing_by
  simp_all
  rw [Prod.lex_def, imp_iff_or]
  simp_all
  lia

/-
  Consider the following `Tree` type, where every internal node has three
  children: left, center, and right. -/
inductive Tree
  | leaf
  | node : Tree → Tree → Tree → Tree

/-
  Lean automatically generates a `sizeOf` implementation for `Tree`; it
  recursively counts the number of subexpressions -/
#print Tree._sizeOf_1

/-
  We would like to normalize a tree so that every left-most child is a leaf, by
  taking any left-most child that is a node and replacing it with its own
  left-most child, moving the other children into both the center and right-most
  children of the node's parent, and then recursively normalizing the result.
  Lean can't prove that the function terminates because, according to the
  default `sizeOf` implementation for `Tree`, the size of the tree is _not_
  decreasing at all (since the center and right-most nodes are both actually
  getting "bigger", more than the left-most tree is getting "smaller"). -/
def norm₁ : Tree → Tree
  | .leaf => .leaf
  | .node (.node il ic ir) c r =>
    norm₁ (.node il (.node il c r) (.node ir c r))
  | .node l c r => .node (norm₁ l) (norm₁ c) (norm₁ r)
decreasing_by
  · /-
      `sizeOf` is not actually decreasing; the culprit is the middle case above
      that makes the center and right nodes larger -/
    sorry
  · simp_all; lia
  · simp_all; lia
  · simp_all

/-
  Our solution is to define our own notion of tree size, where we weight the
  size of the left-most child sufficiently that the fact that its size goes
  _down_ makes up for the fact that the sizes of the other children go _up_. -/
def Tree.treeSize : Tree → ℕ
  | .leaf => 0
  | .node l c r => 2 * treeSize l + max (treeSize c) (treeSize r) + 1

/-
  Now we can prove that the function terminates, by specifying that the measure
  to use is our definition of tree size rather than the default `sizeOf`. -/
def norm₂ : Tree → Tree
  | .leaf => .leaf
  | .node (.node il ic ir) c r =>
    norm₂ (.node il (.node ic c r) (.node ir c r))
  | .node l c r => .node (norm₂ l) (norm₂ c) (norm₂ r)
termination_by t => t.treeSize
decreasing_by
  · simp_all [Tree.treeSize]; lia
  · simp_all [Tree.treeSize]; lia
  · simp_all [Tree.treeSize]; lia
  · simp_all [Tree.treeSize]; lia

/-
  Sometimes Lean can infer both the measure and the decreasing proof
  automatically even for non-structurally recursive functions. For example, here
  is Ackermann's function, which is well-founded but not structurally recursive.
  Notice that Lean infers both the `termination_by` and `decreasing_by` clauses
  without us having to specify them manually. -/
def ack : Nat → Nat → Nat
  | 0,   y   => y + 1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x + 1) y)

/-
  There is one other kind of clause that we can use besides `termination_by` and
  `decreasing_by`: it is `partial_fixpoint`, which marks a function as
  potentially non-terminating but in a way that we can still safely reason
  about. The requirements for using `partial_fixpoint` are somewhat complex, and
  only apply in certain cases; see the Lean Reference Manual for details. -/

/-
  Example adapted from the Lean Reference Manual. Given a predicate on natural
  numbers, it tries increasingly larger numbers until it finds one that makes
  the predicate true (or never terminates if there is no such number). -/
def find (P : ℕ → Bool) (n : ℕ := 0) : Option ℕ :=
  if P n then n else find P (n + 1)
partial_fixpoint

#check find.fixpoint_induct
#check find.partial_correctness

/-
  We can't use the `induction` tactic with these partial fixpoint theorems so we
  have to apply them manually -/
example
  (P : ℕ → Bool) (n : ℕ)
  : find P 0 = n → P n
:= by
  apply find.partial_correctness P (fun _ n => P n)
  intro find h1 n₂ r h2
  by_cases h3 : P n₂ = true
  case pos => simp_all
  case neg =>
    simp_all
    exact h1 (n₂ + 1) r h2

end_topic RECURSION


topic::TACTICS
/-
  We have seen `cases` when doing a proof by cases on a disjunction. `∨` is
  defined as an inductive predicate---what `cases` is doing is a proof by cases
  on the constructors of the given inductive type. So we can use `cases` for
  that purpose on _any_ inductive type. Think of `cases` as the "proof" version
  of `match`. -/

inductive Ranged (n : ℕ)
  | r10_20 (hn : 10 ≤ n ∧ n ≤ 20) : Ranged n
  | r50_60 (hn : 50 ≤ n ∧ n ≤ 60) : Ranged n
  | r1000_1100 (hn : 1000 ≤ n ∧ n ≤ 1100) : Ranged n

example (n : ℕ) (r : Ranged n) : n < 100 ∨ n ≥ 1000 := by
  cases r with
  | r10_20 hn => left; lia
  | r50_60 hn => left; lia
  | r1000_1100 hn => right; lia

/-
  Here are a couple of convenience tactics that I will use in future examples:
  `rename_i` and `replace` -/

/-
  `rename_i` will rename inaccessible givens (the ones with their names greyed
  out) so that they are accessible. Tactics can sometimes create new givens and
  by default their names are inaccessible: Lean won't allow you to use them;
  `rename_i` is one way to make them accessible so they can be used. Using
  `rename_i x₁ ... xₙ` renames the last `n` inaccessible names to the given
  names. -/
example : ∀ a b c d : ℕ, a = b → a = d → a = c → c = b := by
  intros
  rename_i h1 _ h2
  simp_all

/-
  `replace` acts exactly like `have` except that you use the name of an existing
  given and that given is replaced -/
example {A B C : Prop} (h₁ : A → B) (h₂ : B → C) (h₃ : A) : C := by
  replace h₁ := h₁ h₃
  exact h₂ h₁

/-
  _Structural induction_

  We can use the `induction` tactic to do an inductive proof on terms of any
  inductive type; this is called _structural induction_. The base cases and
  inductive cases depend on the constructors: each constructor that does not
  have a recursive mention of the type being defined is a base case, each other
  constructor is an inductive case. We demonstrate by doing induction over a
  tree data structure that has two different kinds of leaves and whose nodes
  have either two or three children. -/
inductive Tree
  | leafA -- base case
  | leafB -- base case
  | binode  (val : ℕ) (left right : Tree) : Tree        -- inductive case
  | trinode (val : ℕ) (left center right : Tree) : Tree -- inductive case

/- Number of leaves in a `Tree` -/
def Tree.num_leaves : Tree → ℕ
  | .leafA | .leafB => 1
  | .binode _ left right =>
    left.num_leaves + right.num_leaves
  | .trinode _ left center right =>
    left.num_leaves + center.num_leaves + right.num_leaves

/- Number of nodes in a `Tree` -/
def Tree.num_nodes : Tree → ℕ
  | .leafA | .leafB => 0
  | .binode _ left right =>
    left.num_nodes + right.num_nodes + 1
  | .trinode _ left center right =>
    left.num_nodes + center.num_nodes + right.num_nodes + 1

/-
  We prove by structural induction that the number of leaves is at least the
  number of nodes + 1 and at most twice the number of nodes + 1. Notice that
  `induction` gives us two base cases (`leafA` and `leafB`) and two inductive
  cases (`binode` and `trinode`), where each inductive case has an inductive
  hypothesis for each recursive reference to `Tree`. -/
example {t : Tree}
  : t.num_nodes + 1 ≤ t.num_leaves ∧ t.num_leaves ≤ 2 * t.num_nodes + 1
:= by
  induction t with
  | leafA =>
    unfold Tree.num_nodes Tree.num_leaves
    exact ⟨by lia, by lia⟩
  | leafB =>
    unfold Tree.num_nodes Tree.num_leaves
    exact ⟨by lia, by lia⟩
  | binode _ left right left_ih right_ih =>
    unfold Tree.num_nodes Tree.num_leaves
    exact ⟨by lia, by lia⟩
  | trinode _ left center right left_ih center_ih right_ih =>
    unfold Tree.num_nodes Tree.num_leaves
    exact ⟨by lia, by lia⟩

/-
  _Functional induction_

  When trying to prove something about a recursive function, induction is the
  natural approach. However, it is usually best for the inductive proof to
  follow the structure of the recursive function or things can get messy. Lean
  provides a method to tailor induction to the specific recursive function we're
  proving something about; this is called _functional induction_. The examples
  here are adapted from a post on lean-lang.org/blog/. -/

/-
  `alternate` is a recursion function that takes two lists and outputs a list
  whose elements alternate between the two input lists. It is not structurally
  recursive, and so we need to supply a termination argument. -/
def alternate {α : Type} : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => x :: alternate ys xs
termination_by xs ys => xs.length + ys.length

#eval alternate ["a", "b"] ["1", "2"]

/-
  We want to prove that the length of the output list is the sum of the lengths
  of the input lists. `alternate` itself is structured as a pattern match on
  both inputs, with the inputs switching between the two parameters with each
  call. We can't express that with the standard `induction` tactic, so we try
  only doing induction on `xs`...but fail. -/
theorem length_alternate1
  {α : Type} (xs ys : List α)
  : (alternate xs ys).length = xs.length + ys.length
:= by
  induction xs with
  | nil => simp_all [alternate]
  | cons x xs ih =>
    simp_all [alternate]
    /-
      `ih` is in terms of `alternate xs ys`, but the goal is in terms of
      `alternate ys xs` which is not the same list; we're stuck
    -/
    sorry

/-
  This is where the `fun_induction` tactic comes in. It takes the name of the
  recursive function as an argument and creates base and inductive cases that
  mirror the function's recursive structure: there is one case per control-flow
  path through the function. The case is a base case of there is no recursive
  call in the path, otherwise it is an inductive case with an inductive
  hypothesis. -/
theorem length_alternate3
  {α : Type} (xs ys : List α)
  : (alternate xs ys).length = xs.length + ys.length
:= by
  fun_induction alternate with
  | case1 ys => simp
  | case2 x xs ys ih =>
    simp_all
    lia

/-
  `fun_induction <name>` will look for a call to `<name>` in the goal that has
  all of its arguments (i.e., isn't being partially applied) and those arguments
  are variables. -/

/-
  Here is another example where `fun_induction` is helpful. `cut_n` will take a
  list and cut it up into a list of sublists, where each sublist is no more than
  `n` elements long. -/
def cut_n {α : Type} (n : ℕ) : List α → List (List α)
  | [] => []
  | x :: xs => (x :: xs.take (n-1)) :: cut_n n (xs.drop (n-1))
termination_by xs => xs.length

#eval cut_n 3 [1, 2, 3, 4, 5, 6, 7, 8]

/-
  We want to prove that flattening all the sublists together will give us back
  the original list. If we try `induction xs` we run into trouble. -/
theorem cut_flatten₁
  {α : Type} (n : ℕ) (xs : List α)
  : List.flatten (cut_n n xs) = xs
:= by
  induction xs with
  | nil => simp [cut_n]
  | cons x xs ih =>
    /-
      If we start unfolding `cut_n` and simplifying we don't get anywhere
      useful; the induction hypothesis isn't what we need -/
    sorry

/-
  Here is the proof using `fun_induction`. Notice the difference from the
  `cut_flatten₁` inductive hypothesis. -/
theorem cut_flatten₂
  {α : Type} (n : Nat) (xs : List α)
  : List.flatten (cut_n n xs) = xs
:= by
  fun_induction cut_n with
  | case1 => simp
  | case2 x xs ih => simp_all

end_topic TACTICS


topic::SIMP
/-
  - We pull out `simp` as a separate topic from the rest of the tactics because it is our first example of _proof automation_

  - The `simp` tactic ("simplifier") is a rewrite engine that attempts to transform its target proposition using a database of rules. It is one of the most commonly-used tactics and has a number of variations.

  - The rules used by `simp` are equality or bi-implication theorems: `simp` will attempt to match its target to the left side of the equality or bi-implication and, if successful, transform it into the right side

    + To be available for `simp` to use, a theorem must be _annotated_ using `@[simp]` _or_ provided directly as an argument to the `simp` tactic (multiple theorems can be given as arguments at the same time)

    + There are already-annotated theorems in core Lean plus many more in Mathlib, and we can annotate our own theorems as well to add them to the database

    + We can annotate non-equalities (e.g., `A ∧ B`) and `simp` will interpret that as meaning an equality with `True` (e.g., `A ∧ B = True`). Note that annotating a theorem `A → B` _will not_ rewrite an `A` into a `B`, it will only do that for `A ↔ B` or `A = B`.

  - `simp` also uses built-in reduction rules whose use can be controlled by setting the configuration parameter (see the Lean Language Reference for details). These rules are used by default even if there are no applicable annotated theorems.

  - If the `simp` target is the current goal and it reduces the goal to `True` then `simp` will automatically close the goal. Otherwise it creates a new proof state where its target has been replaced by its reduced form.
-/

/-
  These theorems have been annotated for `simp` (which we can see by looking
  them up in the Mathlib API) -/
#check Nat.zero_add
#check Nat.add_zero

/-
  Using `simp` to take advantage of the theorems. In this example `simp` can
  reduce the left-hand side to `n`, leaving `n = n`, which is `True`, and so
  `simp` closed the goal and the proof is complete. -/
example (n : ℕ) : 0 + 0 + 0 + n = n := by
  simp

/-
  If we want to know what theorems `simp` used we can ask. In this example
  `simp` used `add_zero` to repeatedly reduce `... + 0` to `...`, finally ending
  with `0 + n`, which it used `zero_add` to reduce to `n` (and then `True`). -/
example (n : ℕ) : 0 + 0 + 0 + n = n := by
  simp?

/-
  `simp only [...]` tells `simp` to only try the listed theorems for rewrites,
  instead of every theorem in its rule database. Note that `simp?` doesn't
  guarantee the minimal list of necessary theorems, just the ones it happened to
  use in a particular order that let it make progress---here we see that we only
  really needed `zero_add`. -/
example (n : ℕ) : 0 + 0 + 0 + n = n := by
  simp only [zero_add]

/-
  If `simp` cannot complete the goal then it will leave us in the simplified
  proof state. Here we see that `add_zero` is _not_ sufficient on its own. -/
example (n : ℕ) : 0 + 0 + 0 + n = n := by
  simp only [add_zero]
  exact Nat.zero_add n

/-
  There are many annotated theorems in Lean already, for numbers, lists, and
  many other things. The Mathlib API can tell you which theorems are already
  annotated for `simp`. Note that you may have to import specific files to get
  access to the theorems contained in those file. -/
example (a b c d : ℕ): [a, b] ++ [] ++ [c, d] = [a, b, c, d] := by
  simp

/-
  We can add our own theorems by either annotating them with `@[simp]` or by
  passing them to `simp` directly. The latter is especially useful when we want
  `simp` to use a local given as a rule. Here we pass the given `h` as a rule
  for `simp`, letting it complete the goal (try removing the `[h]` to see what
  happens). -/
example (n : ℕ) (h : n = 40) : n + 2 = 42 := by
  simp [h]

/-
  We can add all givens as rules using `[*]` -/
example (n₁ n₂ : ℕ) (h₁ : n₁ = 40) (h₂ : n₂ = 42) : n₁ + 2 = n₂ := by
  simp [*]

/-
  We can add any theorem, not just local givens. `Nat.mul_add` is about
  distribution of multiplication over addition and has _not_ been annotated for
  `simp` (try removing `[mul_add]` to see what happens). -/
example (a b c : ℕ) : a * (b + c) = a * b + a * c := by
  simp [mul_add]

/-
  We can target givens, not just the current goal -/
example (x a b c : ℕ) (h : x = a * (b + c)) : x = a * b + a * c := by
  simp [mul_add] at h
  exact h

/-
  We can target _all_ givens using `*` -/
example (x a b c : ℕ) (h : x = a * (b + c)) : x = a * b + a * c := by
  simp [mul_add] at *
  exact h

/-
  And we can target all givens _and_ the current goal (adding all current  givens
  to the set of rules) using `simp_all`. Note that `simp_all` has the same
  interface as `simp`, including `?`, `only`, `[...]`, and more. -/
example
  (x y a b c : ℕ)
  (h₁ : x = a * (b + c)) (h₂ : y = x)
  : y = a * c + a * b
:= by simp_all only [mul_add, add_comm]

/-
  `simp` always rewrites from left to right by default, but sometimes the
  theorem gives the equality in the opposite direction from what you need. You
  can tell `simp` to apply the rewrite in the other direction using `←`. -/
example (a b : ℕ) (h₁ : b = a) (h₂ : a = 42) : b = 42 := by
  simp [← h₁] at h₂
  exact h₂

/-
  `simp` can also unfold definitions, but it will only unfold reducible ones by
  default (we will talk more about what this means later). To unfold a
  semi-reducible definition (e.g., one defined using `def`) you can give the
  name to `simp` as an argument. -/

def fact (n : ℕ) :=
  if n = 0 then 1 else n * fact (n - 1)

/- Try removing the `[fact]` to see what happens -/
example : fact 3 = 6 := by
  simp [fact]

/-
  However, using simp to unfold a recursive definition can be dangerous because
  `simp` will repeatedly apply the unfolding, resulting in a timeout. It is
  better to use `unfold` for recursive definitions, which will only unfold once.
-/
/--
  error: Tactic `simp` failed with a nested error: maximum recursion depth has
  been reached -/
#guard_error
example (n : ℕ) : fact n = n * fact (n-1) := by
  simp [fact]

/-
  - One consequence of the many existing Lean core library and Mathlib theorems and annotations is that you get many benefits of `simp` "for free", whereas if you are using your own data structures and definitions then you need to write all the `simp` theorems yourself

    + This implies that it's almost always easier for proving things if you rely on the existing definitions and data structures rather than writing your own, unless you want to put in the work of adding all the extra annotated theorems

  - One might ask why we don't annotate _every_ theorem for `simp`, so that we don't need to explicitly tell it about theorems. The issue with unfolding recursive definitions hints at the answer: `simp` does not necessarily terminate if it enters an infinite cycle of rewriting.

    + Consider if we have theorem `P₁ : A ↔ B` and `P₂ : B ↔ A`, both of which are annotated for `simp`. Then `simp` will continually rewrite `A` to `B` to `A` to `B` to....

    + In reality these cycles may happen across multiple widely-separated theorems that don't appear at first to be related, making it difficult to detect such cycles. The general advice is to be careful which theorems you annotate, and to write the theorems so that the "simpler" or "more normal" form is always on the left

  - Another issue is that `simp` can _over-simplify_, to the point where things become less convenient instead of more convenient

  - Another issue is _where_ `simp` is used in a proof. We won't worry about this aspect for this class, while we're still learning Lean, but in the long term we should care about "proof maintenance".

    + Theorems can be added and theorem annotations can change as libraries (e.g., Mathlib) get updated, and these changes can affect the results of `simp` in existing proofs

    + The strong advice is that, unless it is closing the entire goal, you should always use `simp only` instead of `simp` by itself. This helps keep the behavior of `simp` stable across changes, because it doesn't rely on annotations.

  - There are many more variations of `simp` that can be useful in different circumstances; see the Lean Language Reference for more details.
-/
end_topic SIMP


topic::FINDING_THEOREMS
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

end_topic FINDING_THEOREMS


topic::TACTICS_REFERENCE
/-
  - `assumption`: look for a given that exactly matches the goal

  - `decreasing_tactic`: the default tactic that Lean uses to close a `decreasing_by` proof. Usually called implicitly by Lean, but can be called manually.

  - `fun_induction`: perform induction on a recursive function's definition

  - `rename_i`: given `n` arguments, renames the last `n` inaccessible (i.e., greyed out) names in the proof state with the given arguments

  - `replace`: acts like `have` except it takes an existing name as argument and replaces it with the new proof

  - `simp`, `simp_all`: simplifies the target by treating `=` and `↔` proofs as left-to-write rewrite rules and iterative applying them to the target.
-/
end_topic TACTICS_REFERENCE
