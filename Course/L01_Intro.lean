/-
  CS 292C: Intro to the Lean Interactive Theorem Prover

  Prof. Ben Hardekopf
  UCSB Computer Science Dept
  Fall 2026
-/

import Course.CourseLib

topic::COURSE_INTRO
/-
  # COURSE GOALS

  - Provide an introduction to modeling and proving properties of formalized systems using Lean

  - Be suitable as a foundation for students who wish to apply Lean to their own work

  # COURSE PREREQUISITES

  - *Programming experience*
    + Not necessarily _functional_ programming, though

  - *Logic and proof experience*
    + E.g., an intro to discrete math course

  - *Enjoy formalization and proof!*

  # COURSE ASSESSMENT

  - *Assignments in Lean*
    + Do most of the assignments most of the time
    + Do all of the assignments by end of quarter

  - *Final project*
    + Choose from a list, or suggest your own
    + Mid-project report and final report

  - 100% assignments + good-faith effort on project = Good grade

  # PLEASE ASK QUESTIONS!

  - Your willingness to ask questions is vital. I don't know what you already know and what you don't, so I have to guess. If I guess wrong, it's your responsibility to let me know so that I can explain things in more detail.
-/
end_topic COURSE_INTRO


topic::COURSE_PLAN
/-
  # Topics

  - Lean as a language: functions, inductive types, structures, type classes, basics of functional programming, dependently-typed programming, and related language concepts

  - Lean as a proof assistant: necessary basics of dependent type-theory, term-mode and tactic-mode proofs, advanced tactics, proof advice and troubleshooting tips

  - The various Lean concepts will mainly be introduced via examples relevant to Computer Science (verified sorting algorithms, verified interpreter/type-checker, computability theory with DFA, etc)

  - _Not covered_ due to lack of time: functional programming abstractions such as monads and functors; metaprogramming, macros, and extensible syntax

  - This course is oriented more towards Computer Scientists interested in applying Lean to their research than many Lean courses that are available (though they are still excellent courses, covering mathematics and/or underlying Lean theory more than this course does)

  # Reference Material

  - The Lean Zulip at https://leanprover.zulipchat.com/
    + Where all the experts hang out

  - From https://lean-lang.org/learn:
    + Functional Programming in Lean
    + Theorem Proving in Lean
    + Hitchhiker's Guide to Logical Verification
    + Lean Language Reference
    + Mathlib API Reference

  - The Lean Game Server at https://adam.math.hhu.de/

  # Logistics

  - There is a course Slack workspace where all course-related communication will happen (announcements, assignments, etc)

    + Please also use the Slack to ask questions and help other students; ask questions publically if it makes sense so that other students can benefit from the answer, otherwise you can DM me directly

    + See the course Canvas page for a link to the Slack invite

  - The course has a repo containing all of the lecture notes, examples, and assignments

    + Everything you see in lecture (including these notes themselves) is contained in the repo

    + See the course Slack for instructions on how to get the repo and set it up, including installing Lean

  - The installation instructions require VS Code, a freely available IDE that is the officially-supported IDE for Lean and the one that I will be using in class

    + There is unofficial support for other IDEs, including Emacs, but I strongly suggest using VS Code (at least while you're learning). You can use other IDEs if you really want, but I won't be able to help you with them and it's likely that they won't have all the capabilities that VS Code has.

  - One unhelpful aspect of VS Code (and many other IDEs) is that they will practically force the use of AI "assistance". I strongly discourage using AI while learning, it defeats the whole purpose. Please turn off all AI assistance in VS Code for this course (do a web search for "vscode turn off ai assistance").
-/
end_topic COURSE_PLAN


topic::LOGIC_AND_COMPUTATION
/-
  # Relation Between Formal Logic and Computation

  - Formal logic relies on syntactic rules and precise meanings

    + Statements formalized in, e.g., predicate logic

    + Given some initial propositions as premises, there are a fixed set of rules that can be used to derive some set of new propositions

    + A valid argument must connect the initial premises to the conclusion using a series of correctly-applied rules

  - Creating a proof often requires creativity, but checking whether a proof is correct is entirely mechanical. This fact opens the door for using computation for checking proofs (and in some cases, for automatically creating those proofs that _don't_ require creativity).

    + Automatic theorem provers: SAT solvers, SMT solvers, ...
    + Interactive theorem provers: Lean, Rocq, Agda, Isabelle/HOL, ...
    + They aren't mutually exclusive, e.g., Lean can call into 3rd-party SAT or SMT solvers

  - Contrast with the typical proofs in math, that are non-formal, i.e., not written in formal logic (but are still fairly rigorous). There are lots of skipped steps and hand-waving where the author assumes the logic is "obvious".

  # Pros and Cons

  - Informal proof pros and cons

    + Informal proofs can be much easier to write and to understand, because they abstract out unnecessary detail

    + But informal proofs can also be wrong in subtle and hard-to-see ways, and are difficult to check

  - Formal proof pros and cons

    + Formal proofs require exacting detail, even for the "uninteresting" parts (though proof automation can help)

    + The sheer amount of detail can obscure the central point (though abstraction and modularization can help)

    + But formal proofs can be mechanically verified to be correct

    + And being formal also opens the door to computer-generated proofs
-/
end_topic LOGIC_AND_COMPUTATION


topic::LEAN_BACKGROUND
/-
  # Lean Interactive Theorem Prover

  - Lean is a dependently-typed, pure functional programming language designed as a proof assistant

  - We won't go deeply into the type-theoretic details of how Lean works (that's another course), but it's useful to have a basic understanding of what's going on

  # Curry-Howard Correspondence

  - The Curry-Howard Correspondence makes an observation about the relation between formal logic and functional programming:

    + Types are propositions
    + Programs are proofs

  - That is, a type encodes a propositional statement, and a program with that type encodes a proof of that proposition. When Lean verifies that a proof of a proposition is correct, what it's really doing is type-checking a program. When Lean uses proof automation to create a proof, what it's really doing is synthesizing a program.
-/

subtopic::CH_EXAMPLE

-- P and Q are arbitrary propositions
variable (P Q : Prop)

/-
  We can read `P ∧ (P → Q) → Q` as a proposition about conjunction and
  implication, or as a type describing a function that takes a pair as its
  argument (containing something of type `P` and some function from `P` to `Q`)
  that returns something of type `Q`. The following example is _both_ a function
  that applies the second element of its argument to the first element of its
  argument and returns the result _and_ a proof of the logical proposition. -/
example : P ∧ (P → Q) → Q :=
  fun hPandPQ =>
    have hP := hPandPQ.left
    have hPimpliesQ := hPandPQ.right
    hPimpliesQ hP

end_subtopic CH_EXAMPLE

/-
  # Some Caveats

  - Not just any type system will do:

    + Nontermination ⇒ inconsistent logic (we'll dive into this more later)
    + The expressiveness of the type system determines the expressiveness of the logic

  - It is important to remember that to guarantee logical consistency, the type system _must_ guarantee termination of any well-typed program. That is, functions must be _total_, i.e., true mathematical functions, not partial functions that can be undefined for some inputs.

  # Dimensions of Type Expressiveness

  - Term → Term (normal functions)
  - Type → Term (parametric polymorphism)
  - Type → Type (type constructors, aka generics)
  - Term → Type (dependent types)

  (A `Term` just means a syntactic expression in the language, e.g., `x + 2`.)
-/

subtopic::NORMAL_FUN_EXAMPLE
/-
  # Term → Term
  - A normal function takes a term as an argument and returns a new term
-/

/- `add2` takes something of type `ℤ` and returns something of type `ℤ` -/
def add2 : ℤ → ℤ :=
  fun n => n + 2

/-
  `#check` shows the type of an expression -/
#check add2
#check add2 3

/-
  Remember that functions are also terms: `do_twice` takes an argument of type
  `ℤ → ℤ` (a function from `ℤ` to `ℤ`) and returns something of type `ℤ → ℤ`,
  specifically, a new function that applies its argument function twice. -/
def do_twice : (ℤ → ℤ) → ℤ → ℤ :=
  fun f n => f (f n)

#check (do_twice)
#check do_twice add2

end_subtopic NORMAL_FUN_EXAMPLE


subtopic::POLYMORPHISM_EXAMPLE
/-
  # Type → Term
  - A polymorphic function takes a type as an argument and returns a new term
-/

/-
  `length` takes a type `α` and returns a function from a list of elements of
  type `α` to the length of the list -/
def length : (α : Type) → List α → ℕ :=
  fun _α ℓ => ℓ.length

/-
  We can see that `length` takes a _type_ as an argument (e.g., `String`) and
  returns a _term_ as its result (the function taking a list of strings and
  returning its length) -/
#check (length)
#check length String

end_subtopic POLYMORPHISM_EXAMPLE


subtopic::TYPE_CONSTRUCTOR_EXAMPLE
/-
  # Type → Type
  - A type constructor takes a type as an argument and returns a new type
-/

/-
  `MyList` defines a list data structure: a list is either empty (the `nil`
  case) or some element concatenated with some other list (the `cons` case); it
  is parameterized by `α`, the type of the list elements -/
inductive MyList (α : Type)
  | nil : MyList α
  | cons (a : α) (ℓ : MyList α) : MyList α

/-
  Note here that `MyList` is _not_ a type, it is a function from `Type` to
  `Type`...but `MyList String` _is_ a type -/
#check (MyList)
#check MyList String

end_subtopic TYPE_CONSTRUCTOR_EXAMPLE


subtopic::DEPENDENT_EXAMPLE
/-
  # Term → Type
  - A dependent type takes a term as an argument and returns a new type
-/

/-
  `depFun` takes a boolean `b` and, depending on the value of `b`, returns
  either a list of natural numbers or a string -/
def depFun : (b : Bool) → if b then List ℕ else String :=
  fun b => match b with
    | true => [0, 42]
    | false => "b was not true"

/-
  Note that `#check` doesn't reduce its output, but if we manually reduce it
  than `depFun true` has type `List ℕ` while `depFun false` has type `String` -/
#check (depFun)
#check depFun true
#check depFun false

end_subtopic DEPENDENT_EXAMPLE

/-
  - Lean's Type System

    + Put all of them together: *Calculus of Constructions*

    + Add inductive definitions: *Calculus of Inductive Constructions*, the basis of Lean's type system

    + Guarantees termination, ∴ a consistent logic
      - Predicate logic, expressive enough to encode ZFC set theory
      - _Not_ Turing-complete (but Lean has an escape hatch if needed)

  - An important concept in Lean is _type universes_, which we'll cover in detail later in the course. However, it is useful for now to dip our toes into the topic and talk about two common universes: `Type` and `Prop`

    + `Type` contains the types that most people are familiar with: `Bool`, `String`, `ℤ` (the type of unbounded integers), `ℕ` (the type of unbounded natural numbers), `List α` (the type of lists whose elements are some type `α`), etc. Things whose types are in universe `Type` are intended for computation, as you might expect in a programming language.

    + `Prop` stands for _proposition_, specifically a logical proposition. Things whose types are in universe `Prop` are intended as logical statements that can (hopefully) be proven.

    + We emphasized before that "types are propositions and programs are proofs", which applies to any program and any type. For pragmatic reasons (which we'll go into in detail later) Lean distinguishes between: (1) types and programs intended for computation (things living in `Type`); and (2) types and programs that are intended to express and prove logical statements (things living in `Prop`).
-/

/-
  These types live in `Type` -/
#check Bool
#check ℕ
#check List String

/-
  Here are values of the various types -/
#check true
#check 42
#check ["a", "b", "c"]

/-
  These types live in `Prop`. Again, a type can be interpreted as a proposition
  and a type living in `Prop` is intended to be read as such. -/
#check 2 + 2 = 4
#check 2 + 2 = 10

/-
  Here is a proof of the first proposition (obviously the second cannot be
  proved). In the same way that `42 : ℕ` or `true : Bool`, here the expression
  `rfl` (standing for "reflexivity") has type `2 + 2 = 4` and should be
  interpreted as a proof of that statement. -/
#check (rfl : 2 + 2 = 4)

/-
  A _predicate_ is a function that returns `Prop`. For example, `is_even` is a
  predicate over natural numbers and `nonempty` is a predicate over lists of
  natural numbers. -/
def is_even (n : ℕ) := ∃ k, 2*k = n
def nonempty (ℓ : List ℕ) := ¬ℓ.isEmpty

#check (is_even)
#check (nonempty)

/-
  As seen from the type, if we apply the function to an argument then we get a
  (unproven) proposition -/
#check is_even 42
#check is_even 13
#check nonempty [1, 2, 3]
#check nonempty []

/-
  In summary: if we're writing code that is intended to compute something we use
  types that live in `Type`; if we're writing code that is expressing and
  proving logical statements we use types that live in `Prop`. We'll see a lot
  of examples soon so that you can see how it works. -/

end_topic LEAN_BACKGROUND
