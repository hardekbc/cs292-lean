import Course.Exercises.L10

namespace V1

def v₁ : Vec ℕ 3 := .cons 1 (.cons 2 (.cons 3 .nil))
def v₂ : Vec ℕ 2 := .cons 4 (.cons 5 .nil)
def v₃ : Vec Bool 3 := .cons true (.cons false (.cons true .nil))

/-- info: true -/
#guard_msgs in
#eval v₁.tail.tail.head == 3

/-- info: true -/
#guard_msgs in
#eval v₁.get (1 : Fin 3) == 2

/-- info: true -/
#guard_msgs in
#eval (v₁.zip v₃).head == (1, true)

/-- info: true -/
#guard_msgs in
#eval (v₁.append v₂).get (3 : Fin 5) == 4

/-- info: true -/
#guard_msgs in
#eval (Vec.replicate "a" 3).get (2 : Fin 3) == "a"

/-- info: true -/
#guard_msgs in
#eval (v₁.filter (· ≤ 2)).1 == 2

end V1

namespace V2

def v₁ : Vec ℕ 3 := Vec.mk [1, 2, 3] (by simp)
def v₂ : Vec ℕ 2 := Vec.mk [4, 5] (by simp)
def v₃ : Vec Bool 3 := Vec.mk [true, false, true] (by simp)

/-- info: true -/
#guard_msgs in
#eval v₁.tail.tail.head == 3

/-- info: true -/
#guard_msgs in
#eval v₁.get (1 : Fin 3) == 2

/-- info: true -/
#guard_msgs in
#eval (v₁.zip v₃).head == (1, true)

/-- info: true -/
#guard_msgs in
#eval (v₁.append v₂).get (3 : Fin 5) == 4

/-- info: true -/
#guard_msgs in
#eval (replicate "a" 3).get (2 : Fin 3) == "a"

/-- info: true -/
#guard_msgs in
#eval (v₁.filter (· ≤ 2)).1 == 2

end V2

namespace V3

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

/-- info: true -/
#guard_msgs in
#eval v₁.tail.tail.head == 3

/-- info: true -/
#guard_msgs in
#eval v₁.get (1 : Fin 3) == 2

/-- info: true -/
#guard_msgs in
#eval (v₁.zip v₃).head == (1, true)

/-- info: true -/
#guard_msgs in
#eval (v₁.append v₂).get (3 : Fin 5) == 4

/-- info: true -/
#guard_msgs in
#eval (Vec.replicate "a" 3).get (2 : Fin 3) == "a"

/-- info: true -/
#guard_msgs in
#eval (v₁.filter (· ≤ 2)).1 == 2

end V3
