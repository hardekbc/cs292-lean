/-
  # Dependent Parsing Example

  We illustrate both universe polymorphism and `partial_fixpoint` using a
  dependently-typed parser generator for context-free languages. These
  algorithms were not written to be efficient (and they are not) but to clearly
  express the underlying theory. -/

import Course.CourseLib

universe u v

/- -----------------------------------------------------------
  LANGUAGE DESCRIPTION DATA STRUCTURE
  ----------------------------------------------------------- -/
namespace Lang

/-
  A symbol is an alphabet character (i.e. a terminal symbol in the grammar) or a
  variable (i.e., a nonterminal in the grammar) -/
inductive Symbol (α : Type u)
  | char : α → Symbol α
  | var  : String → Symbol α

/-
  A dependently-typed map from symbols to the types that should result from
  parsing each particular symbol; used to ensure type-correct parsing -/
def TypeMap (α : Type v) := Symbol α → Type u

/-
  μ-regular expressions (basically the same as context-free grammars),
  parameterized by a `TypeMap` and indexed by the type that will be returned by
  the parser. Notice that we must use universe polymorphism due to the Lean
  universe restrictions. -/
inductive μRe {α : Type u} (τ : TypeMap α) : Type v → Type (max u v+1)
  | zero β     : μRe τ β                           -- Empty language
  | one  {β}   : β → μRe τ β                       -- Empty string
  | a    a     : μRe τ (τ (Symbol.char a))         -- Character
  | var  x     : μRe τ (τ (Symbol.var x))          -- Variable
  | mul  {β γ} : μRe τ β → μRe τ γ → μRe τ (β × γ) -- Concatenation
  | add  {β}   : μRe τ β → μRe τ β → μRe τ β       -- Union
  | star {β}   : μRe τ β → μRe τ (List β)          -- Kleene star
  | opt  {β}   : μRe τ β → μRe τ (Option β)        -- Optional
  | map  {β γ} : (β → γ) → μRe τ β → μRe τ γ       -- Map result type

/-
  The type of the global environment (i.e., the set of grammar rules). Maps a
  variable to the `μRe` expression associated with that variable. -/
def Env {α} (τ : TypeMap α) :=
  AList (fun x => μRe τ (τ (Symbol.var x)))

/-
  Total lookup for the environment, using a default "empty language" value for
  missing elements -/
def Env.get {α τ} (env : Env τ) (x : String) :=
  (env.lookup x).getD (@μRe.zero α τ _)

/-
  An expression is well-formed wrt a given environment if all variables that it
  uses are contained in that environment -/
def WellFormedExp {α β} {τ : TypeMap α} (env : Env τ) : μRe τ β → Bool
  | .var x => (env.lookup x).isSome
  | .mul e₁ e₂ | .add e₁ e₂ => WellFormedExp env e₁ ∧ WellFormedExp env e₂
  | .star e | .opt e | .map _ e => WellFormedExp env e
  | _ => true

/-
  An environment is well-formed if all expressions that it contains are
  well-formed -/
def WellFormedEnv {α} {τ : TypeMap α} (env : Env τ) : Bool :=
  env.entries.all (fun ⟨_, e⟩ ↦ WellFormedExp env e)

/-
  A language specification is a global environment mapping symbols to
  expressions and a starting variable indicating the expression to begin with,
  along with a guarantee that everything is well-formed -/
structure LangSpec {α} (τ : TypeMap α) where
  env : Env τ
  start : String
  well_formed : WellFormedEnv env := by decide

end Lang

/- -----------------------------------------------------------
  EXAMPLE LANGUAGE: ARITHMETIC EXPRESSIONS
  ----------------------------------------------------------- -/
namespace ArithExp
open Lang

/-
  We'll use a very simple grammar for the example, with an abstract syntax tree
  as shown below:

  ae ∈ ArithExp ::= var
                  | ae + ae
                  | ae * ae

  The concrete grammar must be in LL(1) form as shown below, where `this` means
  a terminal symbol:

  E  ::= T E'
  E' ::= `+` T E' | ε
  T  ::= F T'
  T' ::= `*` F T' | ε
  F  ::= `(` E `)` | `id`
-/

/- Abstract syntax tree -/
inductive Ast
  | var  : String → Ast
  | add : Ast → Ast → Ast
  | mul : Ast → Ast → Ast
deriving DecidableEq, Repr

/- Terminal symbols -/
inductive Term
  | plus   -- +
  | times  -- *
  | openp  -- (
  | closep -- )
  | id     -- identifier
deriving DecidableEq, Repr

abbrev tmap : TypeMap Term
  | .char a => match a with
    /-
      Map a `Term` to the type of the resulting parsed value, using `Unit` for
      things that have no meaningful result -/
    | .id => String
    | _ => Unit
  | .var x => match x with
    /-
      Map a grammar rule name to the type of the resulting parsed value, using
      `Unit` for things that have no meaningful result -/
    | "E" | "T" | "F" => Ast
    | "E'" | "T'" => Option Ast
    | _ => Unit

/-
  The set of grammar rules. The grammar rules are tailored to produce a parser
  that will translate an arithmetic expression into an abstract syntax tree (we
  could also define rules that actually evaluate the arithmetic expression as it
  is being parsed, for example).

  We can make the rules be easier to read and write by using Lean's extensible
  syntax, which would allow us to write them in something much closer to the way
  we would write them on paper. I've left them in the more inelegant form for
  the purposes of this class. -/
def ae_env : Env tmap := [
  -- rule: E ::= T E'
  ⟨"E", .map -- T E'
    (fun (lhs, rhs?) => match rhs? with
      | .some rhs => .add lhs rhs
      | .none => lhs)
    (.mul (.var "T") (.var "E'"))⟩,

  -- rule: E' ::= + T E' | ε
  ⟨"E'", .add
    (.map -- + T E'
      (fun (_, lhs, rhs?) => match rhs? with
        | .some rhs => .some (.add lhs rhs)
        | .none => .some lhs)
      (.mul (.a .plus) (.mul (.var "T") (.var "E'"))))
    (.one -- ε
      .none)⟩,

  -- rule: T ::= F T'
  ⟨"T", .map -- F T'
    (fun (lhs, rhs?) => match rhs? with
      | .some rhs => .mul lhs rhs
      | .none => lhs)
    (.mul (.var "F") (.var "T'"))⟩,

  -- rule: T' ::= * F T' | ε
  ⟨"T'", .add
    (.map -- * F T'
      (fun (_, lhs, rhs?) => match rhs? with
        | .some rhs => .some (.mul lhs rhs)
        | .none => .some lhs)
      (.mul (.a .times) (.mul (.var "F") (.var "T'"))))
    (.one  -- ε
      .none)⟩,

  -- rule: F ::= ( E ) | id
  ⟨"F", .add
    (.map -- ( E )
      (fun (_, e, _) => e)
      (.mul (.a .openp) (.mul (.var "E") (.a .closep))))
    (.map -- id
      (fun x => .var x)
      (.a Term.id))⟩,
].toAList

/-
  The well-formedness requirement is automatically inferred -/
def ae_lang : LangSpec tmap where
  env := ae_env
  start := "E"

end ArithExp

/- -----------------------------------------------------------
  PARSER GENERATOR
  We are making a derivative-based parser generator for
  an LL(1) grammar
  ----------------------------------------------------------- -/
namespace Parser
open Lang

variable {α : Type u} {β : Type v} {τ : TypeMap α}
         [DecidableEq α]

/-
  A token is a terminal symbol paired with its semantic value -/
def Token (τ : TypeMap α) := Σ a : α, τ (Symbol.char a)

/- A sequence of tokens -/
abbrev Tokens (τ : TypeMap α) := List (Token τ)

/-
  We need to compute information about each grammar rule; that information is
  stored in this structure for parsing to access -/
structure RuleInfo (α : Type u) (τ : TypeMap α) where
  /- Is the rule nullable? If so, what value does it evaluate to? -/
  nullable : (x : String) → Option (τ (Symbol.var x))
  /- Is the rule productive? -/
  prod : String → Bool
  /- What is the FIRST set of the rule? -/
  first : String → Finset α

/-
  Computes whether an expression is nullable, and if so what value it has. A
  result of `.none` means it is _not_ nullable; `.some v` means that it _is_
  nullable and it evaluates to `v`. -/
def nullable
    {β : Type v}
    (rule_info : RuleInfo α τ)
    : @μRe α τ β → Option β
  | .zero _ | .a _ => .none
  | .one v => .some v
  | .var x =>  rule_info.nullable x
  | .mul e1 e2 =>
    /-
      This code and the code for `.add` can both be made a lot nicer if we use
      monads, but I've left it in the more inelegant form for the purposes of
      this class -/
    match nullable rule_info e1 with
    | .some v1 => match nullable rule_info e2 with
      | .some v2 => .some (v1, v2)
      | .none => .none
    | .none => .none
  | .add e1 e2 =>
    match nullable rule_info e1 with
    | .some v => .some v
    | .none => nullable rule_info e2
  | .star _ => some []
  | .opt _ => .some .none
  | .map f e => (nullable rule_info e).map f

/-
  Computes whether an expression is productive, i.e., can it generate any
  strings -/
def productive
    {β : Type v}
    (rule_info : RuleInfo α τ)
    : @μRe α τ β → Bool
  | .zero _ => false
  | .one _ | .a _ | .star _ | .opt _ => true
  | .var x => rule_info.prod x
  | .mul e1 e2 => productive rule_info e1 && productive rule_info e2
  | .add e1 e2 => productive rule_info e1 || productive rule_info e2
  | .map _ e => productive rule_info e

/-
  Computes the FIRST set of an expression -/
def first
    {β : Type v}
    (rule_info : RuleInfo α τ)
    : @μRe α τ β → Finset α
  | .zero _ | .one _ => ∅
  | .a c => {c}
  | .var x => rule_info.first x
  | .mul e1 e2 =>
    let left :=
      if productive rule_info e2
      then first rule_info e1 else ∅
    let right :=
      if (nullable rule_info e1).isSome
      then first rule_info e2 else ∅
    left ∪ right
  | .add e1 e2 => first rule_info e1 ∪ first rule_info e2
  | .star e | .opt e | .map _ e => first rule_info e

/-
  Computes the derivative of an expression wrt the given token. The function is
  guaranteed to terminate for an LL(1) grammar, but the proof requires a lot of
  setup and is left for future work (and `partial_fixpoint` doesn't apply). -/
partial def derives
    {β : Type v}
    (rule_info : RuleInfo α τ) (env : Env τ)
    : μRe τ β → Token τ → μRe τ β
  | .zero β, _ | .one _, _ => .zero β
  | .a c₁, ⟨c₂, v⟩ => if h : c₁ = c₂ then h ▸ .one v else .zero (τ (Symbol.char c₁))
  | .var x, tk => derives rule_info env (env.get x) tk
  | .mul e1 e2, tk@⟨c, _⟩ =>
    let e1_null := nullable rule_info e1
    if _ : e1_null.isSome && c ∈ first rule_info e2 then
      let v := e1_null.get (by grind)
      .mul (.one v) (derives rule_info env e2 tk)
    else .mul (derives rule_info env e1 tk) e2
  | .add e1 e2, tk@⟨c, _⟩ =>
    if c ∈ first rule_info e1 then derives rule_info env e1 tk
    else derives rule_info env e2 tk
  | .star e, tk@⟨c, _⟩ =>
    if c ∈ first rule_info e then .map
      (fun (v, vs) => v :: vs)
      (.mul (derives rule_info env e tk) (.star e))
    else .zero _
  | .opt e, tk@⟨c, _⟩ =>
    if c ∈ first rule_info e then .map
      (fun v => .some v)
      (derives rule_info env e tk)
    else .zero _
  | .map f e, tk => .map f (derives rule_info env e tk)

/-
  The parser. Also a generator, because if we partially apply it to a
  `RuleInfo`, `Env`, and `μRe` then we get a function `Tokens → Option β`, i.e.,
  a parser specialized to the given grammar. -/
def parse
    (rule_info : RuleInfo α τ) (env : Env τ) (e : μRe τ β)
    : Tokens τ → Option β
  | [] => nullable rule_info e
  | tk@⟨term, _⟩ :: tks =>
    if term ∈ first rule_info e then
      let new_e := derives rule_info env e tk
      parse rule_info env new_e tks
    else .none

end Parser

/- -----------------------------------------------------------
  PARSER ANALYSES
  Computing the elements of `RuleInfo` for a given grammar
  ----------------------------------------------------------- -/
namespace ParserAnalyses
open Lang
open Parser (RuleInfo nullable productive first)

variable {α : Type u} {β : Type v} {τ : TypeMap α}
         [DecidableEq α]

/-
  Note that all of the analyses are guaranteed to terminate, but the proofs are
  complex. Fortunately they all qualify for `partial_fixpoint` so we don't
  actually need to prove termination. -/

/-
  Fixpoint computation to determine the nullability of each expression in the
  environment.

  Doing this the "right" way would mean checking whether the analysis result
  changed after each iteration, which would require that applying `τ` results in
  a type `β` such that `DecidableEq β`. We could make that happen by changing
  the current `TypeMap` definition to instead be something like:

  `def TypeMap := (α : Type v) : Symbol α → Σ (β : Type u), DecidableEq β`

  But this is the only place that needs that capability and that change would
  mean changing everything else that uses `τ`, so I'm going to cheese it here by
  doing something that is sub-optimal but still guaranteed to be correct:
  compute the fixpoint until no new variable becomes `.some`, then run it
  `env.keys.length` more times to ensure we actually reach a fixpoint. -/
def null_analysis
  (env : Env τ)
  (curr_soln : RuleInfo α τ)
  : RuleInfo α τ
:=
  let (changed, soln) := env.keys.foldl f (false, curr_soln)
  if changed then null_analysis env soln else fin soln env.keys.length
partial_fixpoint
where
  f := fun (changed, soln) x =>
    let res := nullable soln (env.get x)
    let new_change := changed || (res.isSome && ¬(soln.nullable x).isSome)
    (
      new_change,
      {soln with nullable := fun y => if h : x = y then h ▸ res else soln.nullable y}
    )
  fin soln : ℕ → RuleInfo α τ
    | 0 => soln
    | n + 1 => fin (env.keys.foldl f (false, soln)).2 n

/-
  Fixpoint computation to determine the productivity of each expression in the
  environment. -/
def prod_analysis
  (env : Env τ)
  (curr_soln : RuleInfo α τ)
  : RuleInfo α τ
:=
  let (changed, soln) := env.keys.foldl f (false, curr_soln)
  if changed then prod_analysis env soln else soln
partial_fixpoint
where f := fun (changed, soln) x =>
  let res := productive soln (env.get x)
  if res = soln.prod x then (changed, soln)
  else (
    true,
    {soln with prod := fun y => if x = y then res else soln.prod y}
  )

/-
  Fixpoint computation to determine the FIRST set of each expression in the
  environment. -/
def first_analysis
  (env : Env τ)
  (curr_soln : RuleInfo α τ)
  : RuleInfo α τ
:=
  let (changed, soln) := env.keys.foldl f (false, curr_soln)
  if changed then first_analysis env soln else soln
partial_fixpoint
where f := fun (changed, soln) x =>
  let res := first soln (env.get x)
  if res = soln.first x then (changed, soln)
  else (
    true,
    {soln with first := fun y => if x = y then res else soln.first y}
  )

/-
  Given a `LangSpec`, create a `RuleInfo` containing the nullability,
  productivity, and FIRST set information for that language -/
def create_rule_info (lang : LangSpec τ) : RuleInfo α τ :=
  let init_null := fun _ => .none
  let init_prod := fun _ => false
  let init_first := fun _ => ∅
  let r1 := null_analysis lang.env
    {nullable := init_null, prod := init_prod, first := init_first}
  let r2 := prod_analysis lang.env r1
  first_analysis lang.env r2

end ParserAnalyses

/- -----------------------------------------------------------
  PARSING EXAMPLE
  ----------------------------------------------------------- -/
namespace Example
open Lang ArithExp
open Parser (Tokens parse)
open ParserAnalyses (create_rule_info)

variable {β : Type v}

/-
  Generate the ArithExp parser -/
def parser := parse
  (create_rule_info ae_lang)
  ae_lang.env
  (ae_lang.env.get ae_lang.start)

#check parser

/-
  I have a monadic tokenizer defined, but since we aren't covering monads I'll
  just create the token stream directly for this example. It corresponds to the
  following concrete syntax: `a + (b + c) * d`. -/
def tk_stream : Tokens tmap := [⟨.id, "a"⟩, ⟨.plus, ()⟩, ⟨.openp, ()⟩, ⟨.id, "b"⟩,
  ⟨.plus, ()⟩, ⟨.id, "c"⟩, ⟨.closep, ()⟩, ⟨.times, ()⟩, ⟨.id, "d"⟩]

#eval parser tk_stream

end Example

/-
  FINAL THOUGHTS

  This is an intrinsically-typed parser, so we know that we'll always get the
  type that we expect from parsing an expression, but it is not a _verified_
  parser. For that we need to prove that the parser is actually parsing
  correctly, which in turn requires verifying that all the different pieces used
  by the parser are working correctly (including adding a check that the grammar
  is LL(1), which currently we're taking on faith).
-/
