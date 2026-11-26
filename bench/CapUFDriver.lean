import Cap.UFIntegrated

/-!
A compiled driver for the general sealed union-find path.

It executes two full-path finds through `Sealed` on the returned successor state,
and the same two calls with an unrelated second allocation, then checks the
resulting roots, parent arrays and unrelated bytes. Run with
`lake exe capuf`.
-/

open Cap

private def check {α : Type} [BEq α] [Repr α]
    (name : String) (actual expected : α) : IO Unit := do
  unless actual == expected do
    throw (IO.userError s!"{name}: expected {repr expected}, got {repr actual}")

def main : IO Unit := do
  let first : Option (Nat × Cap.Integrated.Sealed) :=
    Cap.UFIntegrated.ufFirst.toOption
  let second : Option (Nat × Cap.Integrated.Sealed) :=
    Cap.UFIntegrated.ufSecond.toOption
  let both : Option (Nat × Cap.Integrated.Sealed) :=
    Cap.UFIntegrated.ufSecondOther.toOption
  let some (r₁, s₁) := first
    | throw (IO.userError "first find refused")
  let some (r₂, s₂) := second
    | throw (IO.userError "second find refused")
  let some (r₂', s₂') := both
    | throw (IO.userError "two-allocation find refused")
  check "first root" (some (some r₁)) (some (some 0))
  check "second root" (some (some r₂)) (some (some 0))
  check "first parent" (some (s₁.snapshot ⟨0⟩)) (some (some [0, 0, 0, 0, 2]))
  check "second parent" (some (s₂.snapshot ⟨0⟩)) (some (some [0, 0, 0, 0, 0]))
  check "second root (two allocations)" (some (some r₂')) (some (some 0))
  check "second parent (two allocations)" (some (s₂'.snapshot ⟨0⟩))
    (some (some [0, 0, 0, 0, 0]))
  check "unrelated allocation" (some (s₂'.snapshot ⟨1⟩)) (some (some [5, 0, 0]))
  IO.println s!"capuf: roots {r₁},{r₂},{r₂'}; parents {s₂.snapshot ⟨0⟩}; unrelated {s₂'.snapshot ⟨1⟩}"
