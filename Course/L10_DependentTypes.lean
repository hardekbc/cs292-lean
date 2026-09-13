/-
  # Dependent types

  - We've alluded to dependent types several times, and in the `Dfa` example we saw that not using dependent types caused several problems. We'll dive into the topic now, give a number of examples, and then re-visit some of our earlier examples to see how dependent types can help.

  - In the context of "regular" programming (as opposed to theorem proving), the usefulness of dependent types is that they allow us to express much stronger statically-checked constraints on progams

    + As a trivial example, suppose that we have an integer that _should_ be in the range `[-20..20]` except that it can't be `0`. In a language without dependent types we can only express that we have an integer `z : ℤ`; any further checks must be made dynamically. In a language with dependent types we can express a much more constrained type `{ z : ℤ // -20 ≤ z ∧ z ≤ 20 ∧ z ≠ 0 }`, and this constraint is checked by the type system.

    + As a recent example, dependent types would allow us to constrain `Dfa` to have a finite number of states

    + Languages like _Idris_ focus on this aspect of dependent types; they are specifically for this kind of programming, not for theorem proving. Just being dependently-typed doesn't make a language a proof assistant.

  - Lean can certainly be used in this way, but the main reason for dependent types in Lean is to be able to prove theorems. We'll also see how dependent types fit into that aspect.
-/

import Course.CourseLib

topic::DEPENDENT_PAIRS
/-
  - A _dependent pair_ is a pair of two values `⟨a, b⟩` s.t. the type of `b` depends on the value of `a`

    + `⟨a, b⟩ : (a : α) × (β a)` where `α : Type` and `β : α → Type`

  - Dependent pairs are also sometimes called "dependent sums", which (while there is an argument to be made why it is a correct name) I think is rather confusing...in this course we will always use the term _dependent pair_

  - They are also sometimes called _Sigma types_, explaining the common notation `Σ` for indicating a dependent pair
-/

/-
  Here is a function mapping a natural number `n` to the type `Bool` or `String`
  depending on whether `n` is even or odd -/
def parity (n : ℕ) : Type :=
  if n % 2 = 0 then Bool else String

/-
  `DpType₁` is a dependent pair type of a natural number `n` and a value of type
  either `Bool` or `String` depending on whether `n` is even or odd -/
def DpType₁ := (n : ℕ) × (parity n)

/-
  `DpType₂` is exactly the same as `DpType₁`, we're just using different
  notation that is in line with the usual dependent pair notation in the
  literature -/
def DpType₂ := Σ n : ℕ, parity n

/-
  Behind the scenes a dependent pair type is a structure type with two fields:
  the first component and the second component. We create a dependent pair
  _value_ by constructing an instance of that structure. -/
#check (Sigma.mk 42 true : DpType₁)
#check_failure (Sigma.mk 42 "hello" : DpType₁)

/- We can also use the `⟨...⟩` shorthand for creating structures -/
#check (⟨3, "hello"⟩ : DpType₁)

/-
  Here is another example of a dependent pair where the first element is some
  positive natural number and the second is a natural number guaranteed to be
  less than the first -/
def LtType := Σ n : ℕ, Fin n

#check (⟨42, 0⟩ : LtType)
#check_failure (⟨0, 42⟩ : LtType)

/-
  Here is another example of a dependent pair that is essentially the same as
  `Option α`, i.e., `b` selects between having some `α` value and not having an
  `α` value (using `Unit` because it trivially only has one possible value) -/
def OptType (α : Type) := Σ (b : Bool), if b then α else Unit

#check (⟨true, "hello"⟩ : OptType String)
#check (⟨false, ()⟩ : OptType String)

/-
  We showed before that the various logical connectives were actually Lean data
  structures, but left out `∃`. Here is the Lean definition: it is a dependent
  pair of a witness object and a proof that the witness has the desired
  property, living in `Prop`. -/
#print Exists

/-
  Here is an implementation of our own `∃` version. An important note is that
  while `∃` is a dependent pair, recall that Lean treats things in `Prop`
  differently than things not in `Prop`. In particular, we cannot extract data
  from something in type `Prop`, i.e., we cannot retrieve the actual witness
  from an `Exists` proof object, we only know that one must have existed when
  the proof object was created. We'll talk about why this restriction exists
  later on in the course. -/
inductive Exists' {α : Type} (P : α → Prop) : Prop
  | intro (witness : α) (h : P witness) : Exists' P

/- A tactic-based proof -/
theorem exist_prop (α : Type) (P : α → Prop) (h : ∃ x, P x) : ∃ x, P x := by
  obtain ⟨x, hx⟩ := h
  exists x

#print exist_prop

/- A term-based proof -/
theorem exist_prop₁ (α : Type) (P : α → Prop) (h : ∃ x, P x) : ∃ x, P x :=
  match h with
  | .intro w h => Exists.intro w h

end_topic DEPENDENT_PAIRS


topic::DEPENDENT_FUNCTIONS
/-
  - A _dependent function_ is a function for which the type of the codomain depends on the value of its argument

    + `dep_function : (a : α) → (β a)` where `α : Type` and `β : α → Type`

  - Note that a non-dependent function of type `A → B` can be seen as a dependent function of type `(a : A) → fun (x : A) => B`, i.e., where the codomain function `β` just ignores the value of the argument and always returns `B`

    + In core Lean all function types are dependent, it's just that some use the argument value to compute `β` and some ignore the argument and return a constant value for `β`

  - Dependent functions are also sometimes called "dependent products", which again (despite there being a reasonable argument why that name is correct) I think is confusing...in this course we will always use the term _dependent function_

  - They are also sometimes called _Pi types_, explaining the common notation `Π` for indicating a dependent function
-/

/-
  We saw an example of a dependent function in the Intro: `depFun` takes a
  boolean `b` and, depending on the value of `b`, returns either a list of
  natural numbers or a string -/
def depFun : (b : Bool) → if b then List ℕ else String :=
  fun b => match b with
    | true => [0, 42]
    | false => "b was not true"

#eval depFun true
#eval depFun false

/-
  We also have alternative notation for dependent functions using `∀`; the
  following definition is exactly the same as for `depFun` except using the `∀`
  notation for the function type -/
def depFun' : ∀ (b : Bool), if b then List ℕ else String :=
  fun b => match b with
    | true => [0, 42]
    | false => "b was not true"

#eval depFun' true
#eval depFun' false

/-
  The last remaining logical connectives that we didn't connect to a Lean term
  is `∀`; the special notation above gives a hint: a `∀` is just a dependent
  function -/

/- This is a tactic-based proof -/
theorem forall_prop : ∀ (x : ℕ), 0 ≤ x := by
  intro x
  exact Nat.zero_le x

#print forall_prop

/-
  This is a term-based proof. Note that `forall_prop` has a dependent function
  type, which could also be written `(x : ℕ) → 0 ≤ x`: the type `0 ≤ x : Prop`
  depends on the value of the parameter `x` -/
theorem forall_prop' : ∀ (x : ℕ), 0 ≤ x :=
  fun x => Nat.zero_le x

/-
  - To do a term-based proof of a `∀` we create a function whose parameter is the type of the set being quantified over and whose body is the type of the predicate inside the quantifier, specialized to the function argument(s)

  - To use a proof object whose type is `∀` we just apply it as a function to an argument whose type matches the function's domain
-/

end_topic DEPENDENT_FUNCTIONS


topic::MATRIX_EXAMPLE
/-
  - We'll go through an example where we implement matrices in a way that makes the number of rows and columns explicit in their type, allowing us to specify when various matrix operations are valid

  - Mathlib has a similar `Matrix` type that is implemented using functions instead of arrays. Functions aren't a very efficient implementation, but they are generally easier to implement and reason about and are also more general, e.g., allowing for infinite-size matrices.

    + This is a common tradeoff that Mathlib makes, since most people using Mathlib don't care about computation or efficiency

  - Note that all of the operations where we might have used for-loops and iteration in an imperative language, we have implemented here using `map`. A key part of wrapping one's head around functional programming is to realize that a great many "iteration-like" operations can be accomplished with various combinations of `map`, `fold`, `filter`, etc.
-/

/-
  To avoid name conflicts with the existing Mathlib `Matrix` we could change the
  name, but instead we'll put our definitions inside their own namespace -/
namespace Matrices

/-
  The type of a matrix of natural numbers with `row` rows and `col` colummns. We
  use `Vector` from the standard library; we can learn about the available
  `Vector` operations using the Mathlib API. A vector is an array with a
  specified length, e.g., `v : Vector α n` means `v` is an array of `α` of
  length `n`. -/
abbrev Matrix (row col : ℕ) :=
  Vector (Vector ℕ col) row

variable {row col : ℕ}

instance : ToString (Matrix row col) where
  /- We can learn about `String.intercalate` using the Mathlib API -/
  toString m := " | ".intercalate ((m.map (fun r =>
    " ".intercalate (r.map (fun c => s!"{c}")).toList))).toList

/-
  Add two matrices. They are required to have the same numbers of rows and
  columns and result in a matrix with the same numbers of rows and columns.
  Recall that `zip` was covered in `L06_FP_Primer`. -/
def Matrix.add (m1 m2 : Matrix row col) : Matrix row col :=
  (m1.zip m2).map (fun (r1, r2) =>
    (r1.zip r2).map (fun (i, j) => i + j))

/-
  Multiply a matrix by a scalar. However many rows and columns the input matrix
  has, so does the output matrix. -/
def Matrix.scalar_mul (n : ℕ) (m : Matrix row col) : Matrix row col :=
  m.map (·.map (· * n))

/-
  Transpose a matrix. If the input matrix has `r` rows and `c` columns then the
  output matrix has `c` rows and `r` columns. The notation `[<idx>]!` means that
  we don't need a proof that `<idx>` is within bounds, but Lean will panic if it
  isn't (however, because of our `Matrix` typing we're guaranteed that it _is_
  in-bounds). -/
def Matrix.transpose (m : Matrix row col) : Matrix col row :=
  (Vector.range col).map (fun c_idx =>
    m.map (·[c_idx]!))

/-
  Multiply two matrices. The left side is required to have the same number of
  columns as the right side has rows. The resulting matrix has the same number
  of rows as the left side and the same number of columns as the right side. -/
def Matrix.mul {same : ℕ} (m1 : Matrix row same) (m2 : Matrix same col) : Matrix row col :=
  m1.map (fun r1 =>
    m2.transpose.map (fun r2 =>
      ((r1.zip r2).map (fun (i, j) => i * j)).sum))


/- Some examples -/

def M1 : Matrix 2 3 := #[
  #[1, 2, 3].toVector,
  #[4, 5, 6].toVector
].toVector

def M2 : Matrix 3 4 := #[
  #[1, 2, 3, 4].toVector,
  #[5, 6, 7, 8].toVector,
  #[9, 10, 11, 12].toVector,
].toVector

#eval toString M1
#eval toString M2

#eval toString (M1.add M1)

#eval toString (M2.scalar_mul 3)

#eval toString M1.transpose
#eval toString M2.transpose

#eval toString (M1.mul M2)

end Matrices
end_topic MATRIX_EXAMPLE


topic::NETWORK_EXAMPLE
/-
  - Here is an example using dependent function types in a different way: modeling the POSIX socket API (or at least, a simple proof of concept, with a fair amount of hand-waving)

    + Adapted from https://ngrislain.github.io/blog/2026-3-25-zerocost-posix-compliance-encoding-the-socket-state-machine-in-lean-4s-type-system/)

  - The socket API is a state machine: the legitimate operations on a socket depend on what state the socket is currently in. We can model these requirements at the type level so that we cannot violate the protocol.
-/

/-
  -----------------------------------------------------------
  DEFINITIONS
  -----------------------------------------------------------
-/

/- The possible states of a socket -/
inductive SocketState where
  | fresh      -- socket() returned a fresh socket
  | bound      -- bind() succeeded
  | listening  -- listen() succeeded
  | connected  -- connect() or accept() produced this socket
  | closed     -- close() succeeded
deriving DecidableEq

/-
  Lean has a socket library so we could actually implement a real socket
  interface, but I'm keeping things simple -/
def SocketHandle := ℕ
def SocketAddr := ℕ

/-
  A socket has a raw socket handle and carries its current state in its type.
  Note that there are methods to control visibility that we haven't gone into,
  so we could protect `raw` from being directly modified. -/
structure Socket (state : SocketState) where
  raw : SocketHandle

/-
  The implementations of the following functions are mock-ups. Again, we could
  use the Lean socket library to implement a real interface. The key aspect I
  want to emphasize is that each function's parameter specifies what state a
  socket must be in to be valid, and their return types specify what state the
  socket transitions to. -/

/- Create a fresh socket handle -/
def socket : Socket .fresh :=
  ⟨(42 : ℕ)⟩

/- Bind a fresh socket to an address -/
def bind (s : Socket .fresh) (_addr : SocketAddr) : Socket .bound :=
  ⟨s.raw⟩

/- Listen to an address -/
def listen (s : Socket .bound) (_backlog : ℕ) : Socket .listening :=
  ⟨s.raw⟩

/- Accept a connection to an address -/
def accept (s : Socket .listening) : Socket .connected × SocketAddr :=
  (⟨s.raw⟩, (42 : ℕ))

/- Connect to an address -/
def connect (s : Socket .fresh) (_addr : SocketAddr) : Socket .connected :=
  ⟨s.raw⟩

/- Send to an address -/
def send (_s : Socket .connected) (_data : ByteArray) : ℕ :=
  42

/- Receive from an address -/
def recv (_s : Socket .connected) (_maxlen : ℕ) : ByteArray :=
  ByteArray.empty

/-
  Close a socket handle. We enforce that the socket cannot already be closed
  using a proof obligation, but the obligation is so simple (just compare the
  socket's state againt `.closed`) that we can discharge it with a default
  automatic proof using the `decide` tactic which does exactly that. -/
def close
  {σ : SocketState} (s : Socket σ) (_ : σ ≠ .closed := by decide)
  : Socket .closed
:= ⟨s.raw⟩

/-
  -----------------------------------------------------------
  EXAMPLES
  -----------------------------------------------------------
-/
namespace Examples

/--
  error: Application type mismatch: The argument s has type Socket
  SocketState.fresh but is expected to have type Socket SocketState.connected in
  the application send s -/
#guard_error
def invalid1 :=
  let s := socket
  send s "hello".toByteArray

/--
  error: Application type mismatch: The argument s has type Socket
  SocketState.bound but is expected to have type Socket SocketState.listening in
  the application accept s -/
#guard_error
def invalid2 :=
  let s := socket
  let s := bind s (42 : ℕ)
  accept s

/--
  error: Tactic `decide` proved that the proposition SocketState.closed ≠
  SocketState.closed is false -/
#guard_error
def invalid3 :=
  let s := socket
  let s := close s
  close s

def valid :=
  let s := socket
  let s := bind s (42 : ℕ)
  let s := listen s 128
  let (s2, addr) := accept s
  let _ := send s2 "hello".toByteArray
  let _ := close s2
  close s

/-
  Note that we still have to be careful to replace each socket with the result
  of the call that updates the socket state, otherwise we could use a stale
  socket variable to mess up the protocol. We could fix this by using the State
  monad, which emulates "updateable state" in a guaranteed consistent way. -/

end Examples
end_topic NETWORK_EXAMPLE


topic::DEPENDENT_INDUCTIVE_TYPES
/-
  A related notion to dependent fuction types is _inductive type familes_, where
  inductive types are _indexed_ by some other type. We mentioned this briefly
  for inductive predicates, but it applies to all inductive types. -/

/-
  Notice that this definition is defining a _family_ of `IndexedFamily` types,
  one for each possible natural number. The specific natural number is called
  the _index_, and `ℕ` is called the _index type_. -/
inductive IndexedFamily : ℕ → Type
  | cons₁ (a : ℕ) : IndexedFamily a
  | cons₂ (a : ℕ) : IndexedFamily (2*a)

namespace IndexedFamily
/-
  Different arguments to the constructor create different members of the family
  of types, i.e., the resulting type is _dependent_ on the argument -/
#check (cons₁ 0 : IndexedFamily 0)
#check (cons₁ 42 : IndexedFamily 42)

/-
  We can use different constructors to get the same type -/
#check (cons₁ 42 : IndexedFamily 42)
#check (cons₂ 21 : IndexedFamily 42)

end IndexedFamily

/- We can use any index type we want, and can index by multiple types -/
inductive IndexedFamily2 : Bool → String → Type
  | cons (b : Bool) (s : String) : IndexedFamily2 (¬b) (s ++ "!")

namespace IndexedFamily2
#check (cons true "hello" : IndexedFamily2 false "hello!")
end IndexedFamily2

/-
  A common example of dependent inductive types is a _vector_, defined as a list
  (or array) of a specific length; these are the same vectors that we saw in the
  `Matrix` example except we're defining them here as a list instead of an
  array. -/
inductive VectorT (α : Type) : ℕ → Type
  | nil : VectorT α 0
  | cons (a : α) {n : ℕ} (v : VectorT α n) : VectorT α (n + 1)

#check VectorT.nil
#check VectorT.cons "a" VectorT.nil

/-
  Keep in mind that for inductive types, parameters and indices are _different_
  and cannot be treated the same

  - For functions, using `def fn (n : ℕ) : ℕ := ...` and `def fn : ℕ → ℕ := ...` are exactly the same and can be used interchangeably

  - For inductive type definitions this is _not_ true: using `inductive T (n : ℕ)` (where the `ℕ` is a parameter) and `inductive T : ℕ → Type` (where the `ℕ` is an index type) are different

    + In particular, remember that parameters must be used consistently across all constructors of the inductive type, whereas indices can be different for different constructors
-/

end_topic DEPENDENT_INDUCTIVE_TYPES
