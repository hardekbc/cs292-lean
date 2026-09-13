/-
  # EXERCISES FOR `L03`

  Reasoning about lists and sorting.

  ## INSTRUCTIONS

  Replace the `sorry` in each theorem below with a proof of the given
  proposition.
-/

import Course.CourseLib
import AutograderLib

variable {α : Type}

/-
  -----------------------------------------------------------
  REASONING ABOUT LISTS
  -----------------------------------------------------------
-/

/-
  Append an element to the end of a list -/
def snoc : List α → α → List α
  | [], a => [a]
  | x :: xs, a => x :: snoc xs a

/-
  Sum a list of numbers -/
def sum : List ℕ → ℕ
  | [] => 0
  | x :: xs => x + sum xs

@[autogradedProof 1]
theorem ex3_1
  (ℓ : List ℕ) (n : ℕ)
  : sum (snoc ℓ n) = n + sum ℓ
:= by
  sorry

@[autogradedProof 1]
theorem ex3_2
  (ℓ₁ ℓ₂ : List ℕ)
  : sum (ℓ₁ ++ ℓ₂) = sum ℓ₁ + sum ℓ₂
:= by
  sorry

@[autogradedProof 1]
theorem ex3_3
  (ℓ : List ℕ)
  : sum ℓ.reverse = sum ℓ
:= by
  sorry

/-
  -----------------------------------------------------------
  BINARY SEARCH TREE MAP
  -----------------------------------------------------------
-/

/-
  A map implemented as a binary search tree. We require that the type of map
  keys `α` have a linear order. The intended invariant is that all keys
  _smaller_ than the current key are in the left subtree and all keys _greater_
  than the current key are in the right subtree. -/
inductive BstMap (α β : Type) [LinearOrder α] where
  | empty
  | node (left right : BstMap α β) (key : α) (val : β)

namespace BstMap

variable {α β : Type} [LinearOrder α]

/- Return whether the map contain a given key -/
def contains : BstMap α β → α → Bool
  | .empty, _ => false
  | .node left right k _, key =>
    if k == key then true
    else if key < k then left.contains key
    else right.contains key

/-
  Look up a key in the map and return its value, returning a default value if
  the key is not in the map. Note that we're pattern matching on three things
  simultaneously, i.e., all three parameters of the function. -/
def lookup : BstMap α β → α → β → β
  | .empty, _, default => default
  | .node left right k v, key, default =>
    if k == key then v
    else if key < k then left.lookup key default
    else right.lookup key default

/-
  Return a new map with the given key mapped to the given value -/
def insert : BstMap α β → α → β → BstMap α β
  | .empty, key, val => .node .empty .empty key val
  | .node left right k v, key, val =>
    if k = key then .node left right key val
    else if key < k then .node (left.insert key val) right k v
    else .node left (right.insert key val) k v

/-
  An empty map doesn't contain any key -/
@[autogradedProof 1]
theorem contains_empty
  (key₁: α)
  : contains (.empty (α := α) (β := β)) key₁ = false
:= by
  sorry

/-
  A map s.t. a key has been inserted contains that key -/
@[autogradedProof 1]
theorem contains_insert
  (bst : BstMap α β) (key₁ : α) (val : β)
  : contains (.insert bst key₁ val) key₁ = true
:= by
  sorry

/-
  If looking for a key, inserting a _different_ key doesn't affect the result -/
@[autogradedProof 1]
theorem contains_preserves
  (bst : BstMap α β) (key₁ key₂ : α) (val : β)
  : key₁ ≠ key₂ → contains (insert bst key₁ val) key₂ = contains bst key₂
:= by
  sorry

/-
  Looking up a value in an empty map returns the default value -/
@[autogradedProof 1]
theorem lookup_insert_empty
  (key₁ : α) (default : β)
  : lookup (.empty (α := α) (β := β)) key₁ default = default
:= by
  sorry

/-
  Looking up a value for a key that we've inserted returns the value that we
  inserted -/
@[autogradedProof 1]
theorem lookup_insert_same_key
  (bst : BstMap α β) (key₁ : α) (val default : β)
  : lookup (insert bst key₁ val) key₁ default = val
:= by
  sorry

/-
  The result of looking up a value for one key is not affected by inserting a
  value with a _different_ key -/
@[autogradedProof 1]
theorem lookup_insert_diff_key
  (bst : BstMap α β) (key₁ key₂ : α) (val default : β)
  : key₁ ≠ key₂ → lookup (insert bst key₁ val) key₂ default = lookup bst key₂ default
:= by
  sorry

end BstMap
