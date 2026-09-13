/-
  # A Verified Expression Language

  We will define and verify a simple expression language with a type checker and
  interpreter. The language is defined as follows:

  τ ∈ Ty ::= int | bool

  x ∈ Variable
  e ∈ Exp ::= ℤ | Bool | x | e₁ bop e₂ | uop e

  bop ∈ BinaryOp ::= + | * | ≤ | ∧ | ∨
  uop ∈ UnaryOp ::= - | ¬
-/

import Course.CourseLib

/-
  -----------------------------------------------------------
  DATA STRUCTURES
  -----------------------------------------------------------
-/

/-
  Language types. Note the `deriving` at the end: we need to be able to compare
  types for equality, and thus we need to specify that equality between types is
  decidable via `DecidableEq`. This is our first taste of _type classes_, which
  we'll talk more about later. -/
inductive Ty
  | int
  | bool
deriving DecidableEq

/-
  Variables are strings. `abbrev` was mentioned in `L07_TermsAsProofs`, it is
  just like `def` except that Lean will always unfold the name into its
  definition (unlike `def`, which is only sometimes unfolded). Basically this
  means that Lean treats `Var` as just a type alias for `String`, they are
  indistinguishable. -/
abbrev Var := String

/- Binary operations -/
inductive BinOp
  | add
  | mul
  | le
  | and
  | or

/- Unary operations -/
inductive UnOp
  | neg
  | not

/-
  Expressions. `Exp` is basically an abstract syntax tree. -/
inductive Exp
  | int   : ℤ → Exp
  | bool  : Bool → Exp
  | var   : Var → Exp
  | binop : BinOp → Exp → Exp → Exp
  | unop  : UnOp → Exp → Exp

/-
  Namespaces are a common feature in modern languages, you've likely encountered
  them before (perhaps by some other name). We use them so that we don't need to
  worry about clashing definitions. Here we will create a namespace called
  `Examples` so that its definitions don't clash with anything defined outside
  that namespace. -/
namespace Examples

-- The expression `(-2 * x) + 1`
def e1 : Exp :=
  .binop
    .add
    (.int 1)
    (.binop
      .mul
      (.unop .neg (.int 2))
      (.var "x"))

-- The expression `¬true ∨ (-20 ≤ x ∧ x ≤ 100)`
def e2 : Exp :=
  .binop
    .or
    (.unop .not (.bool true))
    (.binop
      .and
      (.binop .le (.int (-20)) (.var "x"))
      (.binop .le (.var "x") (.int 100)))

end Examples

/-
  -----------------------------------------------------------
  TYPE CHECKER
  -----------------------------------------------------------
-/

/-
  Type environment, mapping variables to their types. We use an associative list
  (`AList`) to do the mapping. `AList` allows for dependent types, but we don't
  use that feature (hence the argument is a function that throws away its
  argument and always returns `Ty`). Think of `AList` as a list of pairs with
  operations that allow us to treat it as a map. -/
abbrev Env := AList (fun (_ : Var) => Ty)

/-
  Type checking for `Exp`. Returns the type of the expression if it has one,
  otherwise `none` if there is a type error. The environment `Γ` gives the type
  of each variable. Since we're defining the function as `Exp.check`, we can use
  dot notation for calling it on a `Exp`-type argument. -/
def Exp.check (Γ : Env) : Exp → Option Ty
  | .int _ => .some .int    -- integers are type `int`
  | .bool _ => .some .bool  -- booleans are type `bool`
  | .var x => Γ.lookup x    -- variables are whatever type `Γ` says
  | .binop op left right =>
    match op with
    | .add | .mul =>
      -- `e₁ +/* e₂` is type `int` if `e₁` and `e₂` are type `int`
      match left.check Γ, right.check Γ with
      | .some .int, .some .int => .some .int
      | _, _ => .none
    | .le =>
      -- `e₁ ≤ e₂` is type `bool` if `e₁` and `e₂` are type `int`
      match left.check Γ, right.check Γ with
      | .some .int, .some .int => .some .bool
      | _, _ => .none
    | .and | .or =>
      -- `e₁ ∧/∨ e₂` is type `bool` if `e₁` and `e₂` are type `bool`
      match left.check Γ, right.check Γ with
      | .some .bool, .some .bool => .some .bool
      | _, _ => .none
  | .unop op e =>
    match op with
    | .neg =>
      -- `-e` is type `int` if `e` is type `int`
      match e.check Γ with
      | .some .int => .some .int
      | _ => .none
    | .not =>
      -- `¬e` is type `bool` if `e` is type `bool`
      match e.check Γ with
      | .some .bool => .some .bool
      | _ => .none

/-
  We can create the same namespace multiple times and it acts as if they were
  all the same namespace. E.g., if we create the `Examples` namespace again then
  we have access to the expressions defined previously. -/
namespace Examples

/-
  If `x` is `Ty.int` then the expression typechecks and has type `Ty.int`,
  otherwise it does not typecheck. -/
#eval e1.check [⟨"x", .int⟩].toAList = some Ty.int
#eval e1.check [⟨"x", .bool⟩].toAList = none

/-
  If `x` is `Ty.int` then the expression typechecks and has type `Ty.bool`,
  otherwise it does not typecheck. -/
#eval e2.check [⟨"x", .int⟩].toAList = some Ty.bool
#eval e2.check [⟨"x", .bool⟩].toAList = none

end Examples

/-
  -----------------------------------------------------------
  INTERPRETER
  -----------------------------------------------------------
-/

/-
  Values and operations on values. A value is the result of interpreting an
  expression. We include an `error` case for operations on things of invalid
  types, e.g., `int + bool`. -/
inductive Value
  | int  : ℤ → Value
  | bool : Bool → Value
  | error

/-
  Defining something like `<type>.<name>` (e.g., `Exp.check` above) really means
  that we're defining `<name>` inside the `<type>` namespace. We can instead
  explicitly create the namespace and put the definitions directly inside, as
  shown below. -/
namespace Value

def add : Value → Value → Value
  | .int z₁, .int z₂ => .int (z₁ + z₂)
  | _, _ => .error

def mul : Value → Value → Value
  | .int z₁, .int z₂ => .int (z₁ * z₂)
  | _, _ => .error

def le : Value → Value → Value
  | .int z₁, .int z₂ => .bool (z₁ ≤ z₂)
  | _, _ => .error

def and : Value → Value → Value
  | .bool b₁, .bool b₂ => .bool (b₁ && b₂)
  | _, _ => .error

def or : Value → Value → Value
  | .bool b₁, .bool b₂ => .bool (b₁ || b₂)
  | _, _ => .error

def neg : Value → Value
  | .int z => .int (-z)
  | _ => .error

def not : Value → Value
  | .bool b => .bool ¬b
  | _ => .error

end Value

/-
  The actual name of the function is, e.g., `add`, but outside the namespace we
  have to qualify it as `Value.add`. Namespaces have many useful features, which
  we'll describe in more detail later. -/
#check_failure add
#check Value.add

/-
  A program evaluation state maps variables to their values. This is just like
  `Env` except we're mapping to `Value` instead of `Ty`. -/
abbrev State := AList (fun (_ : Var) => Value)

/- Interpreter for `Exp` -/
def Exp.eval (σ : State) : Exp → Value
  | .int z => .int z
  | .bool b => .bool b
  | .var x => match σ.lookup x with
    | .some v => v
    | .none => .error
  | .binop .add left right => (left.eval σ).add (right.eval σ)
  | .binop .mul left right => (left.eval σ).mul (right.eval σ)
  | .binop .le left right  => (left.eval σ).le  (right.eval σ)
  | .binop .and left right => (left.eval σ).and (right.eval σ)
  | .binop .or left right  => (left.eval σ).or  (right.eval σ)
  | .unop .neg e => (e.eval σ).neg
  | .unop .not e => (e.eval σ).not

namespace Examples

#eval e1.eval [⟨"x", .int 0⟩].toAList
#eval e1.eval [⟨"x", .int 4⟩].toAList
#eval e1.eval [⟨"x", .bool true⟩].toAList

#eval e2.eval [⟨"x", .int (-1)⟩].toAList
#eval e2.eval [⟨"x", .int (-50)⟩].toAList
#eval e2.eval [⟨"x", .int 200⟩].toAList
#eval e2.eval [⟨"x", .bool true⟩].toAList

end Examples

/-
  -----------------------------------------------------------
  TYPE CLASSES
  -----------------------------------------------------------
-/

/-
  - What if we want to change the way that `Value` is shown, e.g., we want to output `-7` instead of `Value.int (-7)` or `ERROR` instead of `Value.error`? Then we need to tell Lean that there is a way to convert a `Value` into a `String` and explain how to do it. The way we do so is with _type classes_.

  - Type classes allow for a principled form of "ad-hoc polymorphism" that improves over strategies like function overloading. They appear in Haskell and Scala and are similar to traits in Rust. Important note: "class" does _not_ mean an OOP class; these are completely different ideas, don't get them confused.

  - The idea is to declare an abstract interface (as a set of functions) and allow users to declare that a particular type implements that interface. We can then define functions whose parameters are any type that implements the desired interface.

  - To bring it back to `Value`: there is a type class called `ToString`; when Lean outputs a value of type `T` as text it looks to see if `T` implements the `ToString` type class. If so then it uses the function defined there to convert the `T` value to a string. So to be able to convert `Value` to `String` we just need to register an instance of `ToString` for `Value`.
-/

/-
  Here is the definition of `ToString`. We'll see how to define our own type
  classes later, for now we'll just see how to use existing ones. `ToString` has
  one field `toString` which is of type `α → String`. To declare that `Value`
  implements `ToString` we need to give it a function with that signature, and
  from then on `Value.toString` will map to whatever function we gave it. -/
#print ToString

/-
  There is a database of types that implement various type classes, and we can
  add entries to that database so that Lean knows about them. Importantly, we
  can register a type as implementing an interface even if we aren't the ones
  who created that type (as is the case with `ToString`). -/

/-
  Ability to output values as strings. We declare an `instance` with type
  `ToString Value` and give `toString` a definition that shows how to convert a
  `Value` to a `String`. Notice that `ℤ` and `Bool` already have instances for
  `ToString` that we can use here. -/
instance ValueToString : ToString Value where
  toString v := match v with
    | .int z => toString z
    | .bool b => toString b
    | .error => "ERROR"

/-
  And here we see the effect of registering our `ToString` instance -/
namespace Examples

#eval e1.eval [⟨"x", .int 0⟩].toAList
#eval e1.eval [⟨"x", .int 4⟩].toAList
#eval e1.eval [⟨"x", .bool true⟩].toAList

#eval e2.eval [⟨"x", .int (-1)⟩].toAList
#eval e2.eval [⟨"x", .int (-50)⟩].toAList
#eval e2.eval [⟨"x", .int 200⟩].toAList
#eval e2.eval [⟨"x", .bool true⟩].toAList

end Examples

/-
  There's a lot more that we can do with type classes. For example, the
  `deriving DecidableEq` clause we used when defining `Ty` implicitly registered
  a type class instance for `Ty` for the `DecidableEq` type class (the
  implementation was trivial enough that Lean was able to synthesize it itself;
  it can only do that for a few type classes). It is also an important mechanism
  Lean uses to define notation (e.g., `+`, `∈`, `⊆`, `++`, etc). We'll see more
  examples and also discuss type classes in more detail later. -/

/-
  -----------------------------------------------------------
  TYPE CHECKER CORRECT
  -----------------------------------------------------------
-/

/-
  We need to define the type system as an inductive predicate. This is our
  specification for what it means for our type checker to be correct. It is a
  trinary predicate between an `Env`, an `Exp`, and a `Ty`. `HasType Γ e τ`
  means that in type environment `Γ`, expression `e` has type `τ`. If an
  expression is not well-typed under some environment `Γ` then `HasType` would
  not be true. -/
inductive HasType (Γ : Env) : Exp → Ty → Prop
  -- an `int` constant has type `int`
  | int  : HasType Γ (.int _) .int
  -- a `bool` constant has type `bool`
  | bool : HasType Γ (.bool _) .bool
  -- a variable has whatever type is assigned by `Γ`
  | var {x τ} : Γ.lookup x = .some τ → HasType Γ (.var x) τ
  -- `e₁ +/* e₂` has type `int` if `e₁` and `e₂` have type `int`
  | add_mul {op left right} :
      (op = .add ∨ op = .mul) → HasType Γ left .int → HasType Γ right .int →
      HasType Γ (.binop op left right) .int
  -- `e₁ ≤ e₂` has type `bool` if `e₁` and `e₂` have type `int`
  | le {left right} :
      HasType Γ left .int → HasType Γ right .int →
      HasType Γ (.binop .le left right) .bool
  -- `e₁ ∧/∨ e₂` has type `bool` if `e₁` and `e₂` have type `bool`
  | and_or {op left right} :
      (op = .and ∨ op = .or) → HasType Γ left .bool → HasType Γ right .bool →
      HasType Γ (.binop op left right) .bool
  -- `-e` has type `int` if `e` has type `int`
  | neg {e} : HasType Γ e .int → HasType Γ (.unop .neg e) .int
  -- `¬e` has type `bool` if `e` has type `bool`
  | not {e} : HasType Γ e .bool → HasType Γ (.unop .not e) .bool

/-
  Now we can proceed to prove the main theorem, that `Exp.check` and `HasType`
  agree with each other. As is my usual wont I have split the `↔` into two
  sub-lemmas, one for each direction. -/

/-
  This proof has a couple of new things in it. A minor one is that we are
  merging several cases together because they all have the same proof. This is
  possible as long as any parameters we name (like `h1` in the `add_mul` and
  `and_or` cases) are named consistently so they refer to the same thing across
  all the merged cases.

  The major new thing is that we are doing induction on `h`, the proof of
  `HasType Γ e τ`, instead of on an object like `e`. This is allowed because,
  again, inductive predicates are really just inductive types and can be treated
  the same way. When we do induction on an inductive predicate it is called
  _rule induction_. We have a case for each constructor, and any constructor
  parameter that is `HasType` has created an inductive hypothesis.

  The actual proofs are trivial enough that `simp_all` can complete them on its
  own; it just needs access to `Exp.check` to see how it is defined. -/
lemma exp_check₁
  {Γ : Env} {e : Exp} {τ : Ty}
  : HasType Γ e τ → e.check Γ == .some τ
:= by
  intro h
  induction h with
  | int | bool | var | le | neg | not => simp_all [Exp.check]
  | add_mul h1 | and_or h1 =>
    cases h1 with
    | inl h => simp_all [Exp.check]
    | inr h => simp_all [Exp.check]

/-
  Remember that we can annotate functions so that `simp` can see their bodies.
  We can either annotate them when they are defined, or (as here) we can
  annotate them after the fact using the `attribute` command. Here we are
  annotating the various `HasType` constructors so that `simp` can see how they
  are defined, which will make the proof below a lot shorter. -/
attribute [simp] HasType.int
attribute [simp] HasType.bool
attribute [simp] HasType.var
attribute [simp] HasType.add_mul
attribute [simp] HasType.le
attribute [simp] HasType.and_or
attribute [simp] HasType.neg
attribute [simp] HasType.not

/-
  For this proof we are using functional induction on `Exp.check`. There are 17
  possible paths, but many of them contradict the antecedent that says that
  `e.check Γ = .some τ`, because they correspond to error paths where we return
  `.none`. These cases are all taken care of in the default case at the end.
  There remaining paths all have the same proof and can be merged. There are
  again a couple of new things in this proof (besides merging cases, which we
  did above). We'll explain them where they are relevant.-/
lemma exp_check₂
  {Γ : Env} {e : Exp} {τ : Ty}
  : e.check Γ == .some τ → HasType Γ e τ
:= by fun_induction Exp.check generalizing τ with
  | case1 | case2 | case3 | case4 | case6 | case10 | case12 | case14 | case16 =>
    simp
    intro h
    /-
      The `replace` below is because `h : Ty.int/bool = τ` (depending on the
      case), so when we use `simp_all` it will rewrite all `Ty.int/bool` into
      `τ`. This is a problem because the `HasType` constructors prove the
      expression has type `Ty.int/bool`, which are not _definitionally_ the same
      as `τ`, hence the proof fails. `h.symm` flips the equality (`symm` stands
      for "symmetry", i.e., `a = b ↔ b = a`); by replacing `h` with its flipped
      version `simp_all` will now rewrite all `τ` as `Ty.int/bool` instead,
      which is the right thing to do. -/
    replace h := h.symm
    /-
      `simp_all` can close all of the goals for these cases because it knows the
      definitions of the various constructors, since we annotated them. If it
      didn't then we would have to have a separate proof for each case that ends
      in explicitly applying the appropriate constructor. -/
    simp_all
  | case8 _ _ _ _ ih₁ ih₂ =>
    /-
      I kept this case separate from the above even though it could be merged,
      because this is the case that needs the `generalizing τ` clause in the
      `fun_induction` above (it works with `induction` as well). Notice that
      `ih₁` and `ih₂` are universally quantified over `τ`. That's good, because
      `h` says that `τ = .bool`, but we need `ih₁` and `ih₂` to say that `left`
      and `right` have type `.int`. That is, the types of `left` and `right` are
      _different_ than the type of the overall expression. If we remove the
      `generalizing τ` clause then `ih₁` and `ih₂` are _not_ universally
      quantified, they are using the same `τ` that `h` says is `.bool`...and so
      we cannot use `HasType.le` to prove the goal. So `generalizing` just means
      "universally quantify this variable in the inductive hypotheses". Try
      removing the `generalizing τ` clause and re-prove this case to see what
      happens. -/
    simp
    intro h
    replace h := h.symm
    simp_all
  | _ => -- all remaining cases
    intro h
    contradiction

/-
  Now we have verified that our type checker and type system agree -/
theorem exp_check_is_correct
  {Γ : Env} {e : Exp} {τ : Ty}
  : HasType Γ e τ ↔ e.check Γ == .some τ
:= ⟨exp_check₁, exp_check₂⟩

/-
  -----------------------------------------------------------
  TYPE SYSTEM SOUND
  -----------------------------------------------------------
-/

/-
  We have proven that the type checker agrees with the type system, however, we
  have _not_ proven that the type system itself is sound, i.e., that a
  well-typed program will not have execution errors (i.e., return a result of
  `.error`). To do that we first need to define the semantics of `Exp`
  evaluation. We will use a method for describing formal semantics called
  _bigstep operational semantics_. This method directly maps expressions to
  their intended values, rather like a recursive interpreter (this makes it a
  good match for `Exp.eval`, which _is_ a recursive interpreter). -/

/-
  An inductive predicate defining the semantics of evaluating expressions.
  `BigstepE σ e v` means that under state `σ`, evaluating `e` results in value
  `v`.  Importantly, note that type-incorrect expressions (e.g., `false + 42`)
  do not have any defined evaluation. -/
inductive BigstepE (σ : State) : Exp → Value → Prop
  -- an int constant evaluates to itself
  | int z : BigstepE σ (.int z) (.int z)
  -- a bool constant evaluates to itself
  | bool b : BigstepE σ (.bool b) (.bool b)
  -- a variable evaluates to whatever the state maps it to
  | var {x v} : σ.lookup x = .some v → BigstepE σ (.var x) v
  -- `.add e₁ e₂` evaluates to `z1 + z2` if `left` evaluates to int `z1`
  -- and `right` evaluates to int `z2`
  | add {z1 z2 left right} :
      BigstepE σ left (.int z1) → BigstepE σ right (.int z2) →
      BigstepE σ (.binop .add left right) (.int (z1 + z2))
  -- `.mul e₁ e₂` evaluates to `z1 * z2` if `left` evaluates to int `z1`
  -- and `right` evaluates to int `z2`
  | mul {z1 z2 left right} :
      BigstepE σ left (.int z1) → BigstepE σ right (.int z2) →
      BigstepE σ (.binop .mul left right) (.int (z1 * z2))
  -- `.le e₁ e₂` evaluates to `z1 ≤ z2` if `left` evaluates to int `z1`
  -- and `right` evaluates to int `z2`
  | le {z1 z2 left right} :
      BigstepE σ left (.int z1) → BigstepE σ right (.int z2) →
      BigstepE σ (.binop .le left right) (.bool (z1 ≤ z2))
  -- `.and e₁ e₂` evaluates to `b1 && b2` if `left` evaluates to bool `b1`
  -- and `right` evaluates to bool `b2`
  | and {b1 b2 left right} :
      BigstepE σ left (.bool b1) → BigstepE σ right (.bool b2) →
      BigstepE σ (.binop .and left right) (.bool (b1 && b2))
  -- `.or e₁ e₂` evaluates to `b1 || b2` if `left` evaluates to bool `b1`
  -- and `right` evaluates to bool `b2`
  | or {b1 b2 left right} :
      BigstepE σ left (.bool b1) → BigstepE σ right (.bool b2) →
      BigstepE σ (.binop .or left right) (.bool (b1 || b2))
  -- `.neg e` evaluates to `-z` if `e` evaluates to int `z`
  | neg {e z} : BigstepE σ e (.int z) → BigstepE σ (.unop .neg e) (.int (-z))
  -- `.not e` evaluates to `¬b` if `e` evaluates to bool `b`
  | not {e b} : BigstepE σ e (.bool b) → BigstepE σ (.unop .not e) (.bool !b)

/-
  A predicate saying the given value matches the given type -/
abbrev value_matches_type : Ty → Value → Prop
  | .bool, v => ∃ b, v = .bool b
  | .int, v => ∃ z, v = .int z

/-
  And now we can almost say what it means for the type system to be sound; the
  last piece is that we need to be able to say that a particular runtime state
  respects the type environment, i.e., it maps variables to values that are the
  right type according to the type environment -/
def compatible (Γ : Env) (σ : State) : Prop :=
  ∀ {x τ}, Γ.lookup x = some τ →
    ∃ v, σ.lookup x = .some v ∧ value_matches_type τ v

/-
  It will also be helpful to annotate the `BigstepE` constructors, though not as
  helpful as it was for `HasType` because the various proofs for the cases below
  are not identical -/
attribute [simp] BigstepE.int
attribute [simp] BigstepE.bool
attribute [simp] BigstepE.var
attribute [simp] BigstepE.add
attribute [simp] BigstepE.mul
attribute [simp] BigstepE.le
attribute [simp] BigstepE.and
attribute [simp] BigstepE.or
attribute [simp] BigstepE.neg
attribute [simp] BigstepE.not

/-
  Now we can say what it means to be sound: if `Γ` and `σ` are compatible and
  `e` has type `τ`, then there is some value `v` such that the semantics say
  that `e` evaluates to `v` _and_ that value has type `τ`. Remember that the
  semantics doesn't have any rules for erroneous expressions, they are literally
  undefined in the semantics. Therefore if the semantics says `e` evaluates to a
  value that means that there can't have been any errors. So effectively what
  we're saying is that well-typed programs cannot have errors.

  We don't actually care that the final value has the right type (in the sense
  that it isn't necessary to show that there are no errors), but it turns out
  that we need that extra information to strengthen the inductive hypothesis and
  make the proof possible. -/
theorem exp_is_sound
  {Γ : Env} {σ : State} {e : Exp} {τ : Ty}
  : compatible Γ σ → HasType Γ e τ →
      ∃ v, BigstepE σ e v ∧ value_matches_type τ v
:= by
  intro h1 h2
  induction h2 with -- rule induction again
  | int =>
    rename_i v
    exists (.int v)
    simp
  | bool =>
    rename_i v
    exists (.bool v)
    simp
  | var h =>
    obtain ⟨v, h2, h3⟩ := h1 h
    exists v
    simp_all
  | add_mul h2 _ _ ih₁ ih₂ =>
    obtain ⟨v₁, hl, hv₁⟩ := ih₁; obtain ⟨z₁, hz₁⟩ := hv₁
    obtain ⟨v₂, hr, hv₂⟩ := ih₂; obtain ⟨z₂, hz₂⟩ := hv₂
    cases h2 with
    | inl h =>
      exists (.int (z₁ + z₂))
      simp_all
    | inr h =>
      exists (.int (z₁ * z₂))
      simp_all
  | le _ _ ih₁ ih₂ =>
    obtain ⟨v₁, hl, hv₁⟩ := ih₁; obtain ⟨z₁, hz₁⟩ := hv₁
    obtain ⟨v₂, hr, hv₂⟩ := ih₂; obtain ⟨z₂, hz₂⟩ := hv₂
    exists (.bool (z₁ ≤ z₂))
    simp_all
  | and_or h2 _ _ ih₁ ih₂ =>
    obtain ⟨v₁, hl, hv₁⟩ := ih₁; obtain ⟨b₁, hb₁⟩ := hv₁
    obtain ⟨v₂, hr, hv₂⟩ := ih₂; obtain ⟨b₂, hb₂⟩ := hv₂
    cases h2 with
    | inl h =>
      exists (.bool (b₁ && b₂))
      simp_all
    | inr h =>
      exists (.bool (b₁ || b₂))
      simp_all
  | neg _ ih =>
    obtain ⟨v, he, hv⟩ := ih; obtain ⟨z, hz⟩ := hv
    exists (.int (-z))
    simp_all
  | not _ ih =>
    obtain ⟨v, he, hv⟩ := ih; obtain ⟨b, hb⟩ := hv
    exists (.bool !b)
    simp_all

/-
  -----------------------------------------------------------
  INTERPRETER CORRECT
  -----------------------------------------------------------
-/

/-
  Now we know that the type checker and type system agree and that the type
  system is sound wrt to the semantics; the final piece is to verify that the
  interpreter and the semantics agree -/

/-
  Annotating the `Value.*` functions will be helpful -/
attribute [simp] Value.add
attribute [simp] Value.mul
attribute [simp] Value.le
attribute [simp] Value.and
attribute [simp] Value.or
attribute [simp] Value.neg
attribute [simp] Value.not

/-
  If the semantics says that an expression should evaluate to a certain
  non-error value then the interpreter does so -/
lemma exp_eval_matches_semantics
  {σ : State} {e : Exp} {v : Value}
  : BigstepE σ e v → e.eval σ = v
:= by
  intro h
  induction h with simp_all [Exp.eval]

/-
  We also will need lemmas about `Value` for the next proof, mainly centered
  around what type a value must be based on the operation that produced it.
  There is again a lot of annoying repetition which proof automation will allow
  us to avoid once we learn it -/
namespace Value

/-
  Here is a new tactic: `split`. It splits an `if-else` or `match` into its
  component cases, producing a separate goal for each case. We can split the
  goal or a given, as shown here. -/
lemma add_not_error
  {v₁ v₂ v : Value}
  : v₁.add v₂ = v → v ≠ .error →
      ∃ z₁ z₂, v₁ = .int z₁ ∧ v₂ = .int z₂ ∧ v = .int (z₁ + z₂)
:= by
  intro h1 h2
  simp_all
  split at h1
  · simp_all
  · simp_all

lemma mul_not_error
  {v₁ v₂ v : Value}
  : v₁.mul v₂ = v → v ≠ .error →
      ∃ z₁ z₂, v₁ = .int z₁ ∧ v₂ = .int z₂ ∧ v = .int (z₁ * z₂)
:= by
  intro h1 h2
  simp_all
  split at h1
  · simp_all
  · simp_all

lemma le_not_error
  {v₁ v₂ v : Value}
  : v₁.le v₂ = v → v ≠ .error →
      ∃ z₁ z₂, v₁ = .int z₁ ∧ v₂ = .int z₂ ∧ v = .bool (z₁ ≤ z₂)
:= by
  intro h1 h2
  simp_all
  split at h1
  · simp_all
  · simp_all

lemma and_not_error
  {v₁ v₂ v : Value}
  : v₁.and v₂ = v → v ≠ .error →
      ∃ b₁ b₂, v₁ = .bool b₁ ∧ v₂ = .bool b₂ ∧ v = .bool (b₁ && b₂)
:= by
  intro h1 h2
  simp_all
  split at h1
  case h_1 b₁ b₂ =>
    by_cases hc₁ : b₁ = true
    case pos =>
      by_cases hc₂ : b₂ = true
      · simp_all
      · simp_all
    case neg =>
      by_cases hc₂ : b₂ = true
      · simp_all
      · simp_all
  case h_2 =>
    replace h1 := h1.symm
    contradiction

lemma or_not_error
  {v₁ v₂ v : Value}
  : v₁.or v₂ = v → v ≠ .error →
      ∃ b₁ b₂, v₁ = .bool b₁ ∧ v₂ = .bool b₂ ∧ v = .bool (b₁ || b₂)
:= by
  intro h1 h2
  simp_all
  split at h1
  case h_1 b₁ b₂ =>
    by_cases hc₁ : b₁ = true
    case pos =>
      by_cases hc₂ : b₂ = true
      · simp_all
      · simp_all
    case neg =>
      by_cases hc₂ : b₂ = true
      · simp_all
      · simp_all
  case h_2 =>
    replace h1 := h1.symm
    contradiction

lemma neg_not_error
  {v₁ v₂ : Value}
  : v₁.neg = v₂ → v₂ ≠ .error →
      ∃ z, v₁ = .int z ∧ v₂ = .int (-z)
:= by
  intro h1 h2
  simp_all
  split at h1
  · simp_all
  · simp_all

lemma not_not_error
  {v₁ v₂ : Value}
  : v₁.not = v₂ → v₂ ≠ .error →
      ∃ b, v₁ = .bool b ∧ v₂ = .bool !b
:= by
  intro h1 h2
  simp_all
  split at h1
  case h_1 b =>
    by_cases hc : b = true
    · simp_all
    · simp_all
  case h_2 =>
    replace h1 := h1.symm
    contradiction

end Value

/-
  If the interpreter evaluates an expression to a non-error value then the
  semantics agrees it is the correct value. Again we need `generalizing`, and
  the cases are slightly different so we can't merge them (there is proof
  automation that will drastically shorten the proof once we learn about it).
  One interesting aspect is the theorem statement itself, specifically the part
  that says `v = e.eval σ`. Originally I had it the other way around, but then
  `simp` required me to rewrite that equality in each case to flip it in order
  for `simp` to work; rather than having to do that in a bunch of cases I just
  flipped the order in the theorem statement. -/
lemma exp_semantics_matches_eval
  {σ : State} {e : Exp} {v : Value}
  : v = e.eval σ → v ≠ .error → BigstepE σ e v
:= by
  fun_induction Exp.eval generalizing v with
  | case1 | case2 | case3 | case4 => simp_all
  | case5 _ _ ih₁ ih₂ =>
    intro h1 h2
    /-
      Notice how I use `.symm` to re-orient an equality to match the expected
      order of a theorem's parameter -/
    obtain ⟨z₁, z₂, h3, h4, h5⟩ := Value.add_not_error h1.symm h2
    replace ih₁ := ih₁ h3.symm (by simp)
    replace ih₂ := ih₂ h4.symm (by simp)
    simp_all
  | case6 _ _ ih₁ ih₂ =>
    intro h1 h2
    obtain ⟨z₁, z₂, h3, h4, h5⟩ := Value.mul_not_error h1.symm h2
    replace ih₁ := ih₁ h3.symm (by simp)
    replace ih₂ := ih₂ h4.symm (by simp)
    simp_all
  | case7 _ _ ih₁ ih₂ =>
    intro h1 h2
    obtain ⟨z₁, z₂, h3, h4, h5⟩ := Value.le_not_error h1.symm h2
    replace ih₁ := ih₁ h3.symm (by simp)
    replace ih₂ := ih₂ h4.symm (by simp)
    simp_all
  | case8 _ _ ih₁ ih₂ =>
    intro h1 h2
    obtain ⟨z₁, z₂, h3, h4, h5⟩ := Value.and_not_error h1.symm h2
    replace ih₁ := ih₁ h3.symm (by simp)
    replace ih₂ := ih₂ h4.symm (by simp)
    simp_all
  | case9 _ _ ih₁ ih₂  =>
    intro h1 h2
    obtain ⟨z₁, z₂, h3, h4, h5⟩ := Value.or_not_error h1.symm h2
    replace ih₁ := ih₁ h3.symm (by simp)
    replace ih₂ := ih₂ h4.symm (by simp)
    simp_all
  | case10 _ ih =>
    intro h1 h2
    obtain ⟨z, h3, h4⟩ := Value.neg_not_error h1.symm h2
    replace ih := ih h3.symm
    simp_all
  | case11 _ ih =>
    intro h1 h2
    obtain ⟨z, h3, h4⟩ := Value.not_not_error h1.symm h2
    replace ih := ih h3.symm
    simp_all

theorem exp_eval_is_correct
  {σ : State} {e : Exp} {v : Value}
  : (BigstepE σ e v → e.eval σ = v) ∧
    (v = e.eval σ → v ≠ .error → BigstepE σ e v)
:= ⟨exp_eval_matches_semantics, exp_semantics_matches_eval⟩
