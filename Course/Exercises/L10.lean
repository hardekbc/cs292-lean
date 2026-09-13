/-
  # EXERCISES FOR `L10`

  The three topics below each implement vectors (lists of a given length) in a
  different way, all based on dependent types. Fill in the `sorry` for each
  definition in each topic. The `#guard_msgs` should all pass without errors.
-/

import Course.CourseLib

topic::V1

inductive Vec (α : Type) : ℕ → Type
  | nil : Vec α 0
  | cons {n} : α → Vec α n → Vec α (n+1)

namespace Vec

variable {α β : Type} {n m : ℕ}

def head (v : Vec α (n+1)) : α :=
  sorry

def tail (v : Vec α (n+1)) : Vec α n :=
  sorry

def get (v : Vec α n) (i : Fin n) : α :=
  sorry

def zip (v₁ : Vec α n) (v₂ : Vec β n) : Vec (α × β) n :=
  sorry

def append (v₁ : Vec α n) (v₂ : Vec α m) : Vec α (n+m) :=
  sorry

def replicate (v : Vec α n) (num : ℕ) : Vec α (n * num) :=
  sorry

def filter (v : Vec α n) (P : α → Bool) : Σ k, Vec α k :=
  sorry

def v₁ : Vec ℕ 3 := .cons 1 (.cons 2 (cons 3 .nil))
def v₂ : Vec ℕ 2 := .cons 4 (.cons 5 .nil)
def v₃ : Vec Bool 3 := .cons true (.cons false (cons true .nil))

/-- info: 3 -/
#guard_msgs in
#eval v₁.tail.tail.head

/-- info: 2 -/
#guard_msgs in
#eval v₁.get (1 : Fin 3)

/-- info: (1, true) -/
#guard_msgs in
#eval (v₁.zip v₃).head

/-- info: 4 -/
#guard_msgs in
#eval (v₁.append v₂).get (3 : Fin 5)

/-- info: 2 -/
#guard_msgs in
#eval (v₁.replicate 3).get (7 : Fin 9)

/-- info: 2 -/
#guard_msgs in
#eval (v₁.filter (· ≤ 2)).1

end Vec
end_topic V1


topic::V2

structure Vec (α : Type) (n : ℕ) where
  ℓ : List α
  len : ℓ.length = n

namespace Vec

variable {α β : Type} {n m : ℕ}

def head (v : Vec α (n+1)) : α :=
  sorry

def tail (v : Vec α (n+1)) : Vec α n :=
  sorry

def get (v : Vec α n) (i : Fin n) : α :=
  sorry

def zip (v₁ : Vec α n) (v₂ : Vec β n) : Vec (α × β) n :=
  sorry

def append (v₁ : Vec α n) (v₂ : Vec α m) : Vec α (n+m) :=
  sorry

def replicate (v : Vec α n) (num : ℕ) : Vec α (n * num) :=
  sorry

def filter (v : Vec α n) (P : α → Bool) : Σ k, Vec α k :=
  sorry

def v₁ : Vec ℕ 3 := Vec.mk [1, 2, 3] (by simp)
def v₂ : Vec ℕ 2 := Vec.mk [1, 2] (by simp)
def v₃ : Vec Bool 3 := Vec.mk [true, false, true] (by simp)

/-- info: 3 -/
#guard_msgs in
#eval v₁.tail.tail.head

/-- info: 2 -/
#guard_msgs in
#eval v₁.get (1 : Fin 3)

/-- info: (1, true) -/
#guard_msgs in
#eval (v₁.zip v₃).head

/-- info: 4 -/
#guard_msgs in
#eval (v₁.append v₂).get (3 : Fin 5)

/-- info: 2 -/
#guard_msgs in
#eval (v₁.replicate 3).get (7 : Fin 9)

/-- info: 2 -/
#guard_msgs in
#eval (v₁.filter (· ≤ 2)).1

end Vec
end_topic V2


topic::V3

def Vec (α : Type) (n : ℕ) := Fin n → α

namespace Vec

variable {α β : Type} {n m : ℕ}

def head (v : Vec α (n+1)) : α :=
  sorry

def tail (v : Vec α (n+1)) : Vec α n :=
  sorry

def get (v : Vec α n) (i : Fin n) : α :=
  sorry

def zip (v₁ : Vec α n) (v₂ : Vec β n) : Vec (α × β) n :=
  sorry

def append (v₁ : Vec α n) (v₂ : Vec α m) : Vec α (n+m) :=
  sorry

def replicate (v : Vec α n) (num : ℕ) : Vec α (n * num) :=
  sorry

def filter (v : Vec α n) (P : α → Bool) : Σ k, Vec α k :=
  sorry

def v₁ : Vec ℕ 3 := fun n =>
  if n = 0 then 1
  else if n = 1 then 2
  else 3

def v₂ : Vec ℕ 2 := fun n =>
  if n = 0 then 4
  else 5

def v₃ : Vec Bool 3 := fun n =>
  if n = 0 || n = 2 then true
  else false

/-- info: 3 -/
#guard_msgs in
#eval v₁.tail.tail.head

/-- info: 2 -/
#guard_msgs in
#eval v₁.get (1 : Fin 3)

/-- info: (1, true) -/
#guard_msgs in
#eval (v₁.zip v₃).head

/-- info: 4 -/
#guard_msgs in
#eval (v₁.append v₂).get (3 : Fin 5)

/-- info: 2 -/
#guard_msgs in
#eval (v₁.replicate 3).get (7 : Fin 9)

/-- info: 2 -/
#guard_msgs in
#eval (v₁.filter (· ≤ 2)).1

end Vec
end_topic V3
