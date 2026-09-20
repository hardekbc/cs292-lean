/-
  # EXERCISES FOR `L03`

  Reasoning about lists and sorting.

  ## INSTRUCTIONS

  Replace the `sorry` in each theorem below with a proof of the given
  proposition.
-/

import Course.CourseLib

variable {α : Type}

/-
  -----------------------------------------------------------
  BINARY SEARCH TREE MAP
  -----------------------------------------------------------
-/

/-
  A map implemented as a binary search tree. We require that the type of map
  keys `α` have a linear order (i.e., every element is comparable to every other
  element). The intended invariant is that all keys _smaller_ than the current
  key are in the left subtree and all keys _greater_ than the current key are in
  the right subtree. -/
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
  Return a new map with the given key mapped to the given value -/
def insert : BstMap α β → α → β → BstMap α β
  | .empty, key, val => .node .empty .empty key val
  | .node left right k v, key, val =>
    if k = key then .node left right key val
    else if key < k then .node (left.insert key val) right k v
    else .node left (right.insert key val) k v

/-
  HINT: you may find the following theorems useful -/
#check BEq.refl
#check Bool.if_true_left
#check beq_iff_eq
#check if_pos
#check if_neg


/-
  An empty map doesn't contain any key -/
theorem contains_empty
  (key₁: α)
  : contains (.empty (α := α) (β := β)) key₁ = false
:= by
  sorry

/-
  A map s.t. a key has been inserted contains that key -/
theorem contains_insert
  (bst : BstMap α β) (key₁ : α) (val : β)
  : contains (.insert bst key₁ val) key₁ = true
:= by
  sorry

/-
  If looking for a key, inserting a _different_ key doesn't affect the result -/
theorem contains_preserves
  (bst : BstMap α β) (key₁ key₂ : α) (val : β)
  : key₁ ≠ key₂ → contains (insert bst key₁ val) key₂ = contains bst key₂
:= by
  sorry

end BstMap
