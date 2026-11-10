def program (v0 : Array Nat) (v1 v2 v3 v4 : Nat) : Array Nat :=
  (let v0 := v0.set! v1 v2; (let v0 := v0.set! v3 v4; v0))

def main : IO Unit := do
  let a := #[0, 0, 0, 0]
  IO.println s!"{program a 1 7 3 9}"
