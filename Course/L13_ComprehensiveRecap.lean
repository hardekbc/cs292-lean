/-
  # Comprehensive Recap

  - Once again we have introduced many Lean concepts via example and we will now take the opportunity to cover them in more detail and a more organized manner. This recap expands on material covered in L08--L09 and L11--L12.
-/

import Course.CourseLib

set_option linter.unusedTactic false

topic::STRUCTURE_TYPES
/-
  Structure types are another kind of user-defined data structures. They are
  basically "records" or "structs", i.e., they have multiple fields that can be
  accessed independently. -/

structure Struct where
  one : ℕ
  two : String

/-
  Lean must know the desired type in order to use the `{}` syntax to create a
  value of some structure type -/
def struct : Struct := { one := 42, two := "hello" }

#eval struct.one
#eval struct.two

/- Lean allows us to put the desired type inside the `{}` for convenience -/
#eval { one := 42, two := "hello" : Struct }

/-
  To update a structure's values we can use the `with` syntax. This does not
  modify the original value, it creates a new structure with the same values as
  the old except for any updated values. -/
#eval { struct with one := 6 }
#eval { struct with one := 6, two := "world"}

/-
  `Prod` is the Lean product type, i.e., pairs, implemented as a structure. It
  has special notation `×` recognized by Lean. -/
#print Prod

def prod (pr : ℕ × String) : String :=
  s!"{pr.fst} and {pr.snd}"

#eval prod (42, "hello")

/-
  Lean also recognizes `.1` and `.2` instead of `.fst` and `.snd` -/
def prod2 (pr : ℕ × String) : String :=
  s!"{pr.1} and {pr.2}"

#eval prod2 (42, "hello")


subtopic::INHERITANCE
/-
  Structures can _inherit_ from other structures. Note that this is not the same
  as subtyping: `Struct` and `MoreStruct` are different types, it's just that
  we've implicitly copied `Struct` fields as `MoreStruct` fields. -/
structure MoreStruct extends Struct where
  three : Bool

def struct₂ := { one := 42, two := "hello", three := true : MoreStruct }

#eval struct₂.one
#eval struct₂.two
#eval struct₂.three

/-
  We _can_ cast a `MoreStruct` into a `Struct`, but doing so creates a new value
  that has erased any additional fields from `MoreStruct`. Note that the
  `toStruct` function was created automatically when we used inheritance from
  `Struct` to define `MoreStruct`. -/
#eval struct₂.toStruct

end_subtopic INHERITANCE


subtopic::BEHIND_THE_SCENES
/-
  Behind the scenes, structures are really inductive types. Here is how `Struct`
  is actually implemented -/

inductive Structᵢ where
  | mk (one : ℕ) (two : String)

def Structᵢ.one : Structᵢ → ℕ
  | mk one _ => one

def Structᵢ.two : Structᵢ → String
  | mk _ two => two

/-
  We can see this with the original `Struct` itself as shown below -/
#eval Struct.mk 42 "hello"
#check (Struct.one)
#check (Struct.two)

end_subtopic BEHIND_THE_SCENES


subtopic::SYNTACTIC_SUGAR
/-
  As more syntactic sugar, if an inductive type has exactly one constructor
  (which would include all structures) and Lean knows the desired type, we can
  use `⟨...⟩` to specify the value. Note that `⟨` and `⟩` are different from `<`
  and `>`. This notation may seem familiar from our proofs of conjunctions and
  biimplications, which themselves are defined as structures. -/
def struct₃ : Struct := ⟨42, "hello"⟩

#eval struct₃.one
#eval struct₃.two

end_subtopic SYNTACTIC_SUGAR
end_topic STRUCTURE_TYPES


topic::SUBTYPES
/-
  - _Subtypes_ are a convenient feature that rely on dependent pairs and propositions: we can create a type that restricts another type via some proposition

    + Important note: _subtype_ doesn't really have anything to do with subtyping in programming languages (or at least only very loosely)

  - Note that the notation for subtypes is close to that of set comprehensions, but uses `//` instead of `|`

    + A value of type `Set` is a predicate
    + A value whose type is a subtype is a pair of a value and a proof
-/

/- The type of even natural numbers -/
def Evenℕ := { n : ℕ // Even n }

/- The type of negative integers -/
def Negℤ := { n : ℤ // n < 0 }

/-
  Under the hood, a Subtype is a structure whose first field is a value of the
  overall type being restricted and whose second field is a proof that the
  corresponding proposition is true -/
structure MySubtype {α : Type} (P : α → Prop) where
  val : α
  property : P val

/-
  We don't have to use the `{... // ...}` notation; the line below is the same
  as the `Evenℕ` example above except we call `Subtype` directly -/
def Evenℕ₂ := Subtype (fun (n : ℕ) => Even n)

/-
  To create a value whose type is a Subtype, we must supply the value _and_ a
  proof that the corresponding proposition is true (we use `grind` for
  convenience; we'll talk about `grind` in detail soon) -/
def an_even_num : Evenℕ :=
  ⟨42, by grind⟩

/-
  We can also call the `Subtype` constructor directly -/
def an_even_num' : Evenℕ :=
  Subtype.mk 42 (by grind)

/-
  It is important to remember when dealing with Subtypes that a value is a
  _pair_: the _actual_ value (`.val`) _and_ a proof that the value satisfies the
  proposition (`.property`). Lean has coercions defined that can implicitly map
  between a subtype and its value, but it's usually best to be explicit. -/

/-
  One way to use subtypes is to specify post-conditions for functions when
  following the "assume/guarantee" or "require/ensure" model -/
def foo (n : ℤ) (require : 0 ≤ n) : { n : ℤ // n ≤ 0 } :=
  ⟨-n, by lia⟩

#check foo 6 (by lia)
#eval foo 6 (by lia)
#eval (foo 6 (by lia)).val

end_topic SUBTYPES


topic::TYPE_CLASSES
/-
  - Type classes allow for a principled form of "ad-hoc polymorphism" that improves over strategies like function overloading. They appear in Haskell and Scala and are similar to traits in Rust.

    + Important note: "class" does _not_ mean an OOP class; these are completely different ideas, don't get them confused

  - The idea is to declare an abstract interface (as a set of functions) and allow users to declare that a particular type implements that interface. We can then define functions whose parameters are any type that implements the desired interface.
-/

/-
  Here we declare a type class called `Foo` that takes a type `α` as a
  parameter. `Foo`s interface has two functions, `bar` and `baz`. A type class
  is really just a structure, but one that Lean treats specially. -/
class Foo (α : Type) where
  bar : α → α → α
  baz : α → α


subtopic::INSTANCES
/-
  There is a database of types that implement various interfaces, and we can add
  entries to that database so that Lean knows about them. Importantly, we can
  register a type as implementing an interface even if we aren't the ones who
  created that type. -/

/- We declare that `ℕ` implements `Foo` -/
instance fooℕ : Foo ℕ where
  bar := fun x y => x * y
  baz := fun x => x + 2

/-
  We declare that `String` implements `Foo`. Note that we don't need to give an
  explicit name for the instance, Lean will create a default name for us (hover
  over the `instance` below in VS Code to see the generated name). -/
instance : Foo String where
  bar := fun x y => x ++ y ++ x
  baz := fun x => x ++ x

/-
  We define a function that takes anything implementing `Foo`. Note that `[...]`
  is another kind of implicit parameter, like `{...}` except for type classes.
  So this function takes a type `α` as an implicit parameter, but requires that
  the type must implement the `Foo` type class. -/
def adhoc_fun {α : Type} [Foo α] (x : α) :=
  Foo.bar x (Foo.baz x)

/- We can now call `adhoc_fun` with a ℕ argument -/
#eval adhoc_fun 42

/- And with a String argument -/
#eval adhoc_fun "hello"

/-
  If we declare multiple instances for the same type, then Lean will use the
  most recently-declared instance in the current scope -/
instance : Foo ℕ where
  bar := fun x y => x - y
  baz := fun x => x * x

#eval adhoc_fun 42

end_subtopic INSTANCES


subtopic::INSTANCE_SEARCH
open INSTANCES (adhoc_fun)

/-
  The thing that makes type classes so powerful and expressive is that instance
  declarations can themselves be parameterized by type classes, requiring
  multiple levels of type class inference (with possible backtracking). The
  search mechanism is analogous to Prolog. -/

/-
  We declare that the type of pairs of any two types that themselves implement
  `Foo` also implements `Foo`. -/
instance {α β : Type} [Foo α] [Foo β] : Foo (α × β) where
  bar := fun ⟨x1, y1⟩ ⟨x2, y2⟩ => (Foo.bar x1 x2, Foo.bar y1 y2)
  baz := fun ⟨x, y⟩ => (Foo.baz x, Foo.baz y)

#eval adhoc_fun (42, "hello")

end_subtopic INSTANCE_SEARCH


subtopic::NOTATION_VIA_TYPE_CLASSES
/-
  Lean uses type classes to map certain notation to certain operations -/

/- Here is a type describing positive natural numbers -/
inductive Pos where
  | one
  | succ : Pos → Pos

/- We can define a function to add two `Pos` -/
def addPos : Pos → Pos → Pos
  | .one, b => .succ b
  | .succ a, b => .succ (addPos a b)

def two : Pos := (.succ .one)
def three : Pos := .succ (.succ .one)

#eval addPos two three

/- We will declare an instance of the `Add` type class for `Pos` -/
instance : Add Pos where
  add := addPos

/- And now we can use `+` instead of `addPos` -/
#eval two
#eval three
#eval two + three

/-
  The output still isn't very readable. We now define a function to convert
  `Pos` to `ℕ` -/
def posToℕ : Pos → ℕ
  | .one => 1
  | .succ n => 1 + (posToℕ n)

/-
  And declare an instance of the `ToString` type class for `Pos`, which will
  piggyback on the existing `ToString` instance for `ℕ` -/
instance : ToString Pos where
  toString x := toString (posToℕ x)

/- Now we try the same `#eval` again -/
#eval two
#eval three
#eval two + three

/-
  - There are many symbols in Lean that one can coopt for their own types by declaring the appropriate instances; here are a few examples:

    + `Mul`, `Div`, `Sub` for `*`, `/`, `-`
    + `Empty` for `∅` and `{}`
    + `Membership`, `HasSubset` for `∈`, `⊆`
    + `Singleton`, `Insert` for `{...}`
    + `Union`, `Inter`, `SDiff` for `∪`, `∩`, `\`
-/

end_subtopic NOTATION_VIA_TYPE_CLASSES


subtopic::DERIVING_TYPE_CLASSES
/-
  It can be tedious to implement instances for a type when the implementation is
  "the obvious thing to do". Lean allows for _instance derivation_ to
  automatically define instances for some type classes where there is an
  "obvious" implementation. -/

inductive Pos'
  | one
  | succ : Pos' → Pos'
deriving BEq

def two' : Pos' := .succ .one
def three' : Pos' := .succ (.succ .one)

/-
  `BEq` stands for "boolean equality" and allows us to use the boolean equality
  and disequality symbols -/
#eval two' == three'
#eval two' != three'

end_subtopic DERIVING_TYPE_CLASSES
end_topic TYPE_CLASSES


topic::ORGANIZING_CODE
/-
  - Lean has several mechanisms for organizing code, particularly _namespaces_ and _sections_

    + There are also _modules_, a very new language feature that I haven't explored yet and that we won't go into for this class
-/

subtopic::NAMESPACES
/-
  - Namespaces are a common feature in modern languages; they serve to separate definitions into distinct spaces so that they do not clash

  - The `(sub)topic` delimiters that are used in all of these files are macros for `namespace` created in `CourseLib.lean` that allow VS Code to selectively provide color highlighting (if VS Code is set up to do that with the proper extension)
-/

namespace ThisIsANamespace
def name := 42
#check name
end ThisIsANamespace

/-
  We are now outside ThisIsANamespace and so cannot use `name` directly, but
  only by qualifying it with the namespace it belongs to -/
#check_failure name
#check ThisIsANamespace.name

/-
  The same namespace can be created multiple times, both within the same file
  and in multiple files, and their definitions are cumulative -/
namespace ThisIsANamespace
#check name
end ThisIsANamespace

/-
  We can also _open_ namespaces to directly access things defined in it. The
  namespace is opened until the end of the current namespace (or file) -/
open ThisIsANamespace
#check name

/- Here is another namespace -/
namespace AnotherNamespace
def an_name₁ := 42
def an_name₂ := 42
end AnotherNamespace

/-
  When we open a namespace, we can choose to _hide_ definitions inside of it in
  order to avoid name clashes -/
open AnotherNamespace hiding an_name₁
#check_failure an_name₁
#check an_name₂

/- Here is yet another namespace -/
namespace YetAnotherNamespace
def yan_name₁ := 42
def yan_name₂ := 42
end YetAnotherNamespace

/-
  When we open a namespace, we can also choose to _rename_ definitions inside of
  it in order to avoid name clashes -/
open YetAnotherNamespace renaming yan_name₁ → blah₁, yan_name₂ → blah₂
#check_failure yan_name₁
#check_failure yan_name₂
#check blah₁
#check blah₂

/- Recall that we defined the type `ℕ'` earlier -/
inductive ℕ' where
  | zero
  | succ : ℕ' → ℕ'

/-
  We can create a namespace with the same name and define a function in it as in
  the example below -/
namespace ℕ'
def add1 (n : ℕ') : ℕ' := .succ n
end ℕ'

/-
  We can do the same thing by defining `ℕ'.<name>`, which automatically open the
  `ℕ'` namespace and adds the definition `<name>` -/
def ℕ'.add2 (n : ℕ') : ℕ' := .succ (.succ n)

/-
  If we have something of type `ℕ'` then we can use dot notation to call a
  function defined in the namespace `ℕ'` (as long as that function takes a `ℕ'`
  as an argument) -/
def one : ℕ' := .succ .zero
#eval one.add1
#eval one.add2

/-
  This is the same thing as calling the function directly, it's just a syntactic
  convenience -/
#eval ℕ'.add1 one
#eval ℕ'.add2 one

/-
  - However, defining things this way _only_ works if the definition was originally created in the current namespace. This is because Lean uses the _type_ of the expression to resolve names, and the type is fully qualified by the namespace (hover over the `Enum` in the `open INDUCTIVE_TYPES (Enum)` line below and then hover over the `Enum.print` below that to see the difference).

  - Consider the data structure `Enum` defined in `INDUCTIVE_TYPES`. We can open `INDUCTIVE_TYPES` to make that definition available, but if we then define a function `Enum.print` Lean will define `print` in the `ORGANIZING_CODE.NAMESPACES.Enum` namespace, _not_ the `INDUCTIVE_TYPES.Enum` namespace, and so using the dot notation for calling a function won't work. -/
namespace INDUCTIVE_TYPES
inductive Enum
  | first
  | second
  | third
end INDUCTIVE_TYPES

open INDUCTIVE_TYPES (Enum)

def Enum.print : Enum → String
  | .first  => "1"
  | .second => "2"
  | .third  => "3"

def enum : Enum := .second

/--
  error: Invalid field `print`: The environment does not contain
  `ORGANIZING_CODE.NAMESPACES.INDUCTIVE_TYPES.Enum.print`, so it is not possible
  to project the field `print` from an expression enum of type `Enum` -/
#guard_error
#eval enum.print

#eval Enum.print enum

/-
  We can see that by default Lean will always extend the current namespace. It
  is possible to get around this issue by using the fully-qualified namespace
  starting from the root namespace. -/
def _root_.ORGANIZING_CODE.NAMESPACES.INDUCTIVE_TYPES.Enum.print : Enum → String
  | .first  => "1"
  | .second => "2"
  | .third  => "3"

/- And now the dot notation works -/
#eval enum.print

end_subtopic NAMESPACES


subtopic::VARIABLE
/-
  - As another convenience, Lean allows us to declare variables within a file or namespace. These are _not_ global variables as you may be used to from some other languages, instead Lean automatically turns these variables into parameters of any function that uses them in its signature or body.

    + The intent is to clean up a series of functions that all have the same parameters, so that they don't all have to repeat the same parameter declarations over and over again

  - The scope of the variable declarations is whatever scope (file or namespace) they are declared in
-/
namespace VariableDemo

/-
  Here we declare two variables; `α` will be made an implicit parameter and `n`
  will be made an explicit parameter -/
variable {α : Type} (n : ℕ)

/- Note that we do not have `α` as a parameter, but we use it anyway -/
def foo (ℓ : List α) := ℓ.length

/- When we check `foo`s type `α` is included as an implicit parameter -/
#check foo
#eval foo [1,2,3]

/- Note that we do not have `n` as a parameter, but we use it anyway -/
def bar := n

/- When we check `bar`s type `n` is included as an explicit parameter -/
#check bar
#eval bar 42

end VariableDemo

end_subtopic VARIABLE


subtopic::SECTIONS
/-
  Sometimes we may wish to limit the scope of an `open` or `variable`
  declaration but do not want to create a new namespace to do so. We can instead
  use `section`, which serves this purpose. A section is not a new namespace,
  but it does confine the scope of `open` and `variable` commands. -/
section SectionDemo

variable (α : Type)

def f1 (ℓ : List α) := ℓ.length

end SectionDemo

/- Note that `f1` is still in scope outside the section -/
#check f1

/-
  But the variable declaration for `α` is not -/
/--
  error: Unknown identifier `α` -/
#guard_error
def f2 (ℓ : List α) := ℓ.length

/- Sections (unlike namespaces) can be anonymous -/
section
-- This is a section
end

end_subtopic SECTIONS
end_topic ORGANIZING_CODE


topic::INDUCTION
subtopic::RULE_INDUCTION
/-
  We can do induction on proofs of inductive predicates just like we do
  structural induction on inductive types; this is called _rule induction_. This
  fact shouldn't be a surprise: an inductive predicate is just an inductive type
  in `Prop`, and a proof of an inductive predicate is just a term of that type,
  so rule induction is really structural induction in disguise. -/
inductive Even : ℕ → Prop
  | zero : Even 0
  | add2 (n : ℕ) : Even n → Even (n + 2)

/-
  We prove by rule induction that all `Even` numbers mod 2 equal 0. It is rule
  induction because we are doing induction on `h`, the proof that `Even n`,
  instead of on `n` itself. Try doing the proof using induction on `n` to see
  where it goes wrong. -/
example : ∀ (n : ℕ), Even n → n % 2 = 0 := by
  intro a h
  induction h with
  | zero => rfl
  | add2 k hk ih => lia

/-
  Here is a more complex use of rule induction, where we prove that an
  interpreter for arithmetic expressions is semantically correct. We first
  define a language of arithmetic expressions as an inductive type. -/
inductive AExp
  | num : ℤ → AExp
  | var : String → AExp
  | add : AExp → AExp → AExp
  | mul : AExp → AExp → AExp

/-
  An environment assigns values to variables -/
def Env := String → ℤ

/-
  Here is our interpreter for the `AExp` language -/
def evalAE (env : Env) : AExp → ℤ
  | .num i     => i
  | .var x     => env x
  | .add e₁ e₂ => evalAE env e₁ + evalAE env e₂
  | .mul e₁ e₂ => evalAE env e₁ * evalAE env e₂

/-
  Here is a bigstep semantics for `AExp`, formally describing what a correct
  answer should be (in the same style as the `Exp` bigstep semantics from
  `L08_ExpLang`) -/
inductive BigstepAE : AExp → Env → ℤ → Prop
  | num (i env) : BigstepAE (.num i) env i
  | var (x env) : BigstepAE (.var x) env (env x)
  | add (e1 e2 n1 n2 env) (h1 : BigstepAE e1 env n1) (h2 : BigstepAE e2 env n2) :
    BigstepAE (.add e1 e2) env (n1 + n2)
  | mul (e1 e2 n1 n2 env) (h1 : BigstepAE e1 env n1) (h2 : BigstepAE e2 env n2) :
    BigstepAE (.mul e1 e2) env (n1 * n2)

/-
  And now we use rule induction to prove that if the `BigstepAE` semantics says
  that an expression should reduce to a particular result, then `evalAE`
  produces that result. We're using more proof automation with `simp_all`,
  though not as much as we could so that you can see the structure of the
  inductive proof. It is instructive to try to do the proof using structural
  induction on `exp` to see where it goes wrong. -/
example (exp : AExp) (env : Env) (result : ℤ)
  : BigstepAE exp env result → evalAE env exp = result
:= by
  intro h
  induction h with
  | num i env => rfl
  | var x env' => simp [evalAE]
  | add e1 e2 n1 n2 env h1 h2 h1_ih h2_ih => simp_all [evalAE]
  | mul e1 e2 n1 n2 env h1 h2 h1_ih h2_ih => simp_all [evalAE]

/-
  Here is the same proof where we just use `simp_all` -/
example (exp : AExp) (env : Env) (result : ℤ)
  : BigstepAE exp env result → evalAE env exp = result
:= by
  intro h
  induction h with simp_all [evalAE]

/-
  It is important to understand that the way you approach a proof can strongly
  influence how long and complicated it is. Of course, some proofs are
  inherently long and complex...but sometimes it's a signal that there's a
  better way, especially if there's a lot of repetition. Consider another
  approach to the example proof above, with the difference that we unfold
  `evalAE` at the very beginning. We can see that it becomes much longer and
  more complicated, and also has a lot repetition. The `simp_all` proof
  automation has become less useful as well. This is because `evalAE` has
  vanished (due to the unfolding) and is no longer available to help `simp_all`
  figure out what's going on. -/
example (exp : AExp) (env : Env) (result : ℤ)
  : BigstepAE exp env result → evalAE env exp = result
:= by
  intro h
  unfold evalAE
  induction h with
  | num i env => rfl
  | var x env =>
    split
    · contradiction
    · simp_all
    · contradiction
    · contradiction
  | add e1 e2 n1 n2 env h1 h2 h1_ih h2_ih =>
    split
    · contradiction
    · contradiction
    · rename_i heq
      replace heq := heq.symm -- trick to help `simp_all`
      split at h1_ih
      · split at h2_ih
        . simp_all [evalAE]
        . simp_all [evalAE]
        . simp_all [evalAE]
        . simp_all [evalAE]
      · split at h2_ih
        . simp_all [evalAE]
        . simp_all [evalAE]
        . simp_all [evalAE]
        . simp_all [evalAE]
      · split at h2_ih
        . simp_all [evalAE]
        . simp_all [evalAE]
        . simp_all [evalAE]
        . simp_all [evalAE]
      · split at h2_ih
        . simp_all [evalAE]
        . simp_all [evalAE]
        . simp_all [evalAE]
        . simp_all [evalAE]
    · contradiction
  | mul e1 e2 n1 n2 env h1 h2 h1_ih h2_ih =>
    split
    · contradiction
    · contradiction
    · contradiction
    · rename_i heq
      replace heq := heq.symm -- trick to help `simp_all`
      split at h1_ih
      · split at h2_ih
        . simp_all [evalAE]
        . simp_all [evalAE]
        . simp_all [evalAE]
        . simp_all [evalAE]
      · split at h2_ih
        . simp_all [evalAE]
        . simp_all [evalAE]
        . simp_all [evalAE]
        . simp_all [evalAE]
      · split at h2_ih
        . simp_all [evalAE]
        . simp_all [evalAE]
        . simp_all [evalAE]
        . simp_all [evalAE]
      · split at h2_ih
        . simp_all [evalAE]
        . simp_all [evalAE]
        . simp_all [evalAE]
        . simp_all [evalAE]

/-
  There's a lot of repetition and we can actually shorten this proof
  dramatically using the tactic combinators that we will be discussing in `L14`.
  However, the two-line proof is still obviously better. -/
example (exp : AExp) (env : Env) (result : ℤ)
  : BigstepAE exp env result → evalAE env exp = result
:= by
  intro h
  unfold evalAE
  induction h with
  | num i env => rfl
  | var x env =>
    split
    any_goals contradiction
    simp_all
  | add e1 e2 n1 n2 env h1 h2 h1_ih h2_ih
  | mul e1 e2 n1 n2 env h1 h2 h1_ih h2_ih =>
    split
    any_goals contradiction
    rename_i heq
    replace heq := heq.symm -- trick to help `simp_all`
    split at h1_ih
    all_goals (split at h2_ih <;> simp_all [evalAE])

/-
  The only difference between the above proof and the two-line version is what
  order we unfolded the definition of `evalAE` in. Again, the lesson is that how
  you approach a proof can have a big impact. You generally won't be able to
  determine _what_ impact until you try it, so if your proof is long and has
  lots of repetition it might be worth exploring other approaches. -/

end_subtopic RULE_INDUCTION


subtopic::INDUCTION_PRINCIPLES
/-
  - The `induction` tactic will allow us to use different induction principles than the default one for whatever object we're doing induction on

    + You should be familiar with the fact that there are different possible induction principles for doing induction over the same kind of object; for example, regular induction on `n : ℕ` and strong induction on `n : ℕ` are different induction principles. By default using `induction n` will do regular induction.

  - Here we'll look at some of the induction principles made available by the Lean core library and Mathlib; later we'll go over how to create our own

    + There are many more than covered here; if you need an alternate induction principle for a standard type be sure to look for it using the Mathlib API before implementing it yourself
-/

/-
  Recall that Lean automatically creates a _recursor_ for any inductive type.
  Here is a reminder from `L06_TermProofs`. -/
#check Nat.recOn

/-
  - Here is a more readable version of the recursor's type:

  Nat.recOn.{u}
    {motive : ℕ → Sort u}
    (t : ℕ)
    (zero : motive Nat.zero)
    (succ : (n : ℕ) → motive n → motive n.succ) : motive t

  - The `motive` is the predicate we're trying to prove; `t` is the number we're doing induction on; `zero` is the base case; `succ` is the inductive case. In other words, this is the standard principle of induction for natural numbers: to prove that a predicate `P` is true for all natural numbers: (1) prove `P 0` and (2) prove that `∀ n, P n → P (n+1)`

  - The `induction` tactic is just applying that recursor, taking the motive from the current proof goal

    + Recursion is also implemented in terms of the recursor, so really recursion and induction are exactly the same thing, just with different types (`Prop` vs `Type`)

  - By defining different recursors, we can implement different induction principles. There are a number of alternate induction principles already defined in the Lean core library and Mathlib
 -/

/-
  The regular induction principle for `ℕ` always starts at 0, but of course it
  is allowed to start induction at any base number. The induction principle
  `Nat.le_induction` allows us to do so. `Nat.le_induction` is just a different
  recursor over the same object `Nat`. -/

#check Nat.le_induction

/-
  - Here is the more readable version. The implicit `m` parameter is the base we're starting at. Notice that `P` (what was called `motive` in `Nat.recOn`) takes two arguments: the variable `n` we're doing induction over, and a proof that `m ≤ n`. The `base` case is `P m` instead of `P 0`, and the inductive case `succ` is similar to the inductive case for `Nat.recOn` but only looks at `n ≥ m`.

  Nat.le_induction
    {m : ℕ}
    {P : (n : ℕ) → m ≤ n → Prop}
    (base : P m ⋯)
    (succ : ∀ (n : ℕ) (hmn : m ≤ n), P n hmn → P (n + 1) ⋯) (n : ℕ) (hmn : m ≤ n) : P n hmn
-/

/-
  Here it is in action. Note the `using` keyword for `induction`, which is how
  we tell it to use an alternate induction principle, and the fact that we give
  `induction` two arguments because `P` has two explicit parameters. -/
example : ∀ n ≥ 5, 2 ^ n > n ^ 2 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => lia
  | succ m hmn ih =>
    ring_nf
    nlinarith

/-
  We can also use strong induction -/
#check Nat.strong_induction_on

def f : ℕ → ℕ
  | 0 => 1
  | 1 => 3
  | n + 2 => 2 * f n + f (n + 1)

example (n : ℕ) : f n ≤ 3^n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    fun_cases f with
    | case1 | case2 => lia
    | case3 m =>
      have h1 := ih m
      have h2 := ih (m + 1)
      lia

/-
  There are also alternate induction principles for other types, such as `List`.
  The regular induction principle for `List` says that if `P []` (the base case)
  and `∀ x ℓ, P ℓ → P (x :: ℓ)` (the inductive case) then `P` holds for all
  lists. Here we demonstrate the induction principle `List.reverseRec`, which
  says that if `P []` (the base case) and `∀ x ℓ, P ℓ → P (ℓ ++ [x])` (the
  inductive case) then `P` holds for all lists. -/

#check List.reverseRec

variable {α : Type}

/-
  Here is a theorem that states dropping the last element in a list and
  appending that same element back again yields the original list (if the list
  was not empty) -/
example
  {ℓ : List α} (h : ℓ ≠ [])
  : ℓ.dropLast ++ [ℓ.getLast h] = ℓ
:= by
  induction ℓ with
  | nil => contradiction
  | cons x xs ih =>
    /-
      We're stumped here, because there's nothing that says `xs` can't be empty
    -/
    sorry

/-
  Here is the same theorem but proved using the reverse induction principle,
  which doesn't have the problem we encountered above since it's coming from the
  other direction -/
example
  {ℓ : List α} (h : ℓ ≠ [])
  : ℓ.dropLast ++ [ℓ.getLast h] = ℓ
:= by induction ℓ using List.reverseRecOn with grind

end_subtopic INDUCTION_PRINCIPLES


subtopic::INDUCTION_TIPS
/-
  Here are a few additional tips that can help avoid problems with applying the
  `induction` tactic -/

/-
  - First, sometimes the inductive hypothesis automatically generated by `induction` is too weak. Specifically, a particular variable is the same in the goal and the inductive hypothesis, but should actually be different.

    + Consider the following example, which takes the arithmetic expression semantics and interpreter from the previous section on rule induction and tries to prove that if the interpreter evaluates to a result, then the semantics agrees with that result

    + This is the dual theorem to what we proved previously, which was that if the semantics dictates a particular result then the interpreter gives that result
-/

open _root_.INDUCTION.RULE_INDUCTION

/-
  We proceed by functional induction on `evalAE`, but a problem arises when we
  get to the inductive cases -/
example
  (exp : AExp) (env : Env) (result : ℤ)
  : evalAE env exp = result → BigstepAE exp env result
:= by
  fun_induction evalAE with
  | case1 n => grind [BigstepAE]
  | case2 x => grind [BigstepAE]
  | case3 e1 e2 e1_ih e2_ih =>
    /-
      The goal says (with some summarization):
      `eval e1 + eval e2 = result → BigstepAE (e1.add e2) result`

      The inductive hypotheses are (again with summarization):
      `eval e1 = result → BigstepAE e1 result`
      `eval e2 = result → BigstepAE e2 result`

      The goal and both hypotheses are using the _same_ variable `result`, and
      so we are stuck because the goal does not follow from these givens
    -/
    sorry
  | case4 e1 e2 e1_ih e2_ih =>
    /- Same problem here -/
    sorry

/-
  We can fix this problem by using the `generalizing` option to `induction`.
  Using `induction blah generalizing x` means that variable `x` will be
  universally quantified in the inductive hypothesis, and hence we can
  specialize it to whatever value we need. -/
example
  (exp : AExp) (env : Env) (result : ℤ)
  : evalAE env exp = result → BigstepAE exp env result
:= by
  fun_induction evalAE generalizing result with
  | case1 n => grind [BigstepAE]
  | case2 x => grind [BigstepAE]
  | case3 e1 e2 e1_ih e2_ih =>
    /- Now the inductive hypotheses have universally quantified `result` -/
    intro h1
    replace e1_ih := e1_ih (evalAE env e1) rfl -- specialize to `evalAE env e1`
    replace e2_ih := e2_ih (evalAE env e2) rfl -- specialize to `evalAE env e2`
    have h2 : BigstepAE (e1.add e2) env (evalAE env e1 + evalAE env e2) :=
      BigstepAE.add e1 e2 (evalAE env e1) (evalAE env e2) env e1_ih e2_ih
    rw [h1] at h2
    exact h2
  | case4 e1 e2 e1_ih e2_ih =>
    /-
      Now that we've generalized `result`, the `grind` tactic can actually
      handle the proof automatically; we could have done this for `case3` as
      well but I wanted to show the structure of the proof -/
    grind [BigstepAE]

/-
  - Second, when doing rule induction the `induction` tactic requires that any indices of the inductive predicate we're doing induction on must be variables. However, sometimes we need to do rule induction when this is not true. The `generalize` tactic can help, by replacing an expression with a variable.

    + `generalize h : <expression> = <variable>` replaces all occurrences of `<expression>` in the goal with `<variable>` and adds a given `h : <expression> = <variable>`

    + We can also do `generalize h : <exp> = <var> at h₁ ... hₙ` to do the same thing in the specified givens; `generalize h : <exp> = <var> at *` will generalize everywhere

    + Note that this strategy applies to `cases` as well as `induction`

    + Also note that the `generalize` tactic and the `generalizing` option for `induction` are two different things and use the term "generalize" in two different ways
-/

/-
  Here is an inductive predicate with three indices (`ℕ`, `List ℕ`, and `ℕ`) -/
inductive Sequence (f : ℕ → ℕ → ℕ) : ℕ → List ℕ → ℕ → Prop
  | empty n₁ : Sequence f n₁ [] n₁
  | step {n₁ n₂ n₃ w} a : Sequence f n₁ w n₂ → f n₂ a = n₃ → Sequence f n₁ (w ++ [a]) n₃

/-
  Suppose we want to prove the following theorem. We need to use rule induction
  on the hypothesis `Sequence f n₁ (a :: w) n₂`, but the second index is not a
  variable. -/
/--
  error: Invalid target: Index in target's type is not a variable (consider
  using the `cases` tactic instead) a :: w -/
#guard_error
example
  {f n₁ n₂ w a}
  : Sequence f n₁ (a :: w) n₂ → Sequence f (f n₁ a) w n₂
:= by
  intro h1
  induction h1

/-
  We use `generalize` to replace the expression `a :: w` with the variable `ℓ`
  before we try to use rule induction, and it works now -/
example
  {f n₁ n₂ w a}
  : Sequence f n₁ (a :: w) n₂ → Sequence f (f n₁ a) w n₂
:= by
  intro h1
  generalize h : a :: w = ℓ at h1
  induction h1 with sorry -- rest of proof is irrelevant

/-
  Third, it's generally a bad idea to try to do a nested inner induction inside
  one of the cases of an outer induction; things get complicated and messy. If
  you find yourself needing to do that, put the inner induction into a separate
  lemma. -/

end_subtopic INDUCTION_TIPS
end_topic INDUCTION


topic::MISC
subtopic::SPLIT
/-
  When we unfold a function, sometimes we get a `if-else` or `match`. The
  `split` tactic will break down the different cases into multiple subgoals.
  Note that usually the subgoals will have unnamed givens; we can use `case` to
  focus on a particular subgoal and give them names.-/

def f (n : ℕ) := if n = 0 then 1 else 2

example (n : ℕ) : f n < 10 := by
  unfold f
  split
  case isTrue h => lia
  case isFalse h => lia

def g : ℕ → ℕ
  | 0 => 1
  | _m + 1 => 2

example (n : ℕ) : g n < 10 := by
  unfold g
  split
  case h_1 x => lia
  case h_2 x m => lia

/-
  We can use `split` on a given as well -/

example (n : ℕ) (h : f n = 1) : n = 0 := by
  unfold f at h
  split at h
  case isTrue h1 => assumption
  case isFalse h1 => contradiction

end_subtopic SPLIT


subtopic::SUBST
/-
  - The `▸` macro is term that acts a bit like the `rw` tactic, in that it rewrites one type to another equal type. The term `h ▸ P a` where `h : a = b` yields a term of type `P b` (or the reverse: `h ▸ P b` yields `P a`, i.e., `▸` will try both directions of the equality) .

    + Think of `▸` as a type-casting operator, where we have to supply a proof that the two types being cast between are equal

  - `▸` is related to the general notion of _equality_, which we have already talked about.
-/

/-
  Equality is a binary relation. We have already seen uses of `Eq.symm` in some
  earlier examples to flip an equality, e.g., to help `simp` rewrite things
  appropriatel. -/
#check @Eq
#check @Eq.refl
#check @Eq.symm
#check @Eq.trans

/-
  A defining characteristic of equality is the substitution principle: equal
  things can be substituted for each other in any context -/
#check @Eq.subst

/-
  The `▸` macro is built on top of `Eq.symm` and `Eq.subst` -/

end_subtopic SUBST


subtopic::AXIOM
/-
  - Lean replies on a small set of axioms that underly its logical framework. Some are there to facilitate compilation to efficient code and aren't really relevant to users. Three of them are the main axioms that Lean relies on for reasoning:

    + _Propositional extensionality_: `axiom propext {a b : Prop} : (a ↔ b) → a = b`. That is, if two propositions imply each other then they are equal.

    + _Quotienting_: The ability to quotient a set by an equivalence relation, specifically the fact that any two elements related by the equivalence relation become identified (i.e., considered the same thing) in the quotient:

      ```
      axiom Quot.sound : ∀ {α : Type u} {r : α → α → Prop} {a b : α},
        r a b → Quot.mk r a = Quot.mk r b
      ```

      - For example, integers and rationals are defined on top of natural numbers using quotienting; reals are also defined using quotienting but the construction is more complex.

    + _The Axiom of Choice_: A famous mathematical axiom, it has been proven that mathematics is consistent with the axiom of choice or alternatively with its negation. Lean assumes it as an axiom: `axiom choice {α : Sort u} : Nonempty α → α`. That is, given a nonempty set, we can choose some element from that set.

  - A couple of things that we might assume were axioms are actually theorems derived from the axioms above:

    + _Function extensionality_: two functions are equal if they give identical results for identical inputs

    + _Law of the Excluded Middle_: `A ∨ ¬A`

  - Lean allows us to add new axioms using the `axiom` command. It acts like `theorem` except there is no proof: Lean will just accept that its true. The `sorry` expression is actually an axiom in disguise: any time you use `sorry` to prove a theorem, the proof of that theorem is based on the `sorry` axiom.

    + There are obvious dangers around using `axiom`, and the generally accepted practice is to try to avoid using it as much as possible...and if it isn't possible, try to make the axiom as simple as possible to help avoid mistakes.
-/
end_subtopic AXIOM
end_topic MISC


topic::TACTICS_REFERENCE
/-
  - `decide`: if the goal is within a decidable theory, algorithmically determine whether the goal is true or false (see `L15::DECIDABLE` for more information)

  - `generalize`: replace an expression with a variable, optionally adding a given that equates the variable and expression

  - `split`: create separate goals for each branch of an `if` or `match` in the target
-/
end_topic TACTICS_REFERENCE
