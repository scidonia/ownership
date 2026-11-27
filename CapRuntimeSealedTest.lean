import CapRuntime

open CapRuntime

def main : IO Unit := do
  let a ← SealedOwned.new 4
  let a1 ← SealedOwned.write a 0 7
  -- a is consumed; using it again must fail
  match (← (try some <$> SealedOwned.write a 1 8 catch _ => pure none)) with
  | none => pure ()
  | some _ => throw (IO.userError "consumed handle accepted")
  -- a copy of the live handle shares the flag
  let copy := a1
  let _ ← SealedOwned.write a1 1 9
  match (← (try some <$> SealedOwned.write copy 2 1 catch _ => pure none)) with
  | none => pure ()
  | some _ => throw (IO.userError "duplicated handle accepted")
  IO.println "SealedOwned: consumed and duplicated handles refused"
