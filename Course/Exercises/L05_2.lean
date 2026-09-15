/-
  # EXERCISES FOR `L05`
-/

import Course.CourseLib
import AutograderLib

/-
  ## INSTRUCTIONS

  We revisit the tree-based map from the `L03_2` exercises to finish proving
  correctness. The theorems from `L03_2` establish that the `BstMap` functions
  are consistent with each other, but do not prove that insertion preserves the
  binary search tree property. Fill in the `sorry` in the theorems below to
  establish that fact.
-/

/- Same as before -/
inductive BstMap (α β : Type) [LinearOrder α] where
  | empty
  | node (left right : BstMap α β) (key : α) (val : β)

namespace BstMap

variable {α β : Type} [LinearOrder α]

/- Same as before -/
def insert : BstMap α β → α → β → BstMap α β
  | .empty, key, val => .node .empty .empty key val
  | .node left right k v, key, val =>
    if k = key then .node left right key val
    else if key < k then .node (left.insert key val) right k v
    else .node left (right.insert key val) k v

/-
  **NEW**
  We need a predicate to be able to say that some proposition holds for every
  node in a `BstMap` -/
def every_node_prop (P : α → β → Prop) : BstMap α β → Prop
  | .empty => True
  | .node left right k v =>
    P k v ∧
    every_node_prop P left ∧
    every_node_prop P right

/-
  **NEW**
  The BST invariant, i.e., for each node its key is less than than all keys in
  its left subtree and greater than than all keys in its right subtree -/
inductive BstInv : BstMap α β → Prop
  | empty_inv : BstInv .empty
  | node_inv left right k v :
      every_node_prop (fun kₗ _ => kₗ < k) left →
      every_node_prop (fun kᵣ _ => k < kᵣ) right →
      BstInv left → BstInv right → BstInv (.node left right k v)

/-
  **NEW**
  It will be helpful to prove that inserting a (key, value) pair into a `BstMap`
  preserves the properties of other (key, value) pairs -/
@[autogradedProof 1]
lemma insert_preserves_pred
  (bst : BstMap α β) (key : α) (val : β) (P : α → β → Prop)
  : every_node_prop P bst → P key val → every_node_prop P (bst.insert key val)
:= by
  sorry

/-
  **NEW**
  Here is the main theorem that says `insert` preserves the `BstInv` property -/
@[autogradedProof 1]
theorem insert_preserves_bstinv
  (bst : BstMap α β) (key : α) (val : β)
  : BstInv bst → BstInv (insert bst key val)
:= by
  sorry

end BstMap
