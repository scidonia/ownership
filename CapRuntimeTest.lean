import CapRuntime

open CapRuntime

/-- A fresh four-byte allocation reads zero, a write is visible, and free retires
the handle. -/
def main : IO Unit := do
  let (s, h) := State.empty.alloc 4
  unless s.read? { h with offset := 0 } == some 0 do
    throw (IO.userError "fresh byte is not zero")
  let s ← match s.write? { h with offset := 1 } 7 with
    | .ok s => pure s
    | .error e => throw (IO.userError e)
  unless s.read? { h with offset := 1 } == some 7 do
    throw (IO.userError "write not visible")
  unless s.read? { h with offset := 0 } == some 0 do
    throw (IO.userError "write affected another byte")
  let s ← match s.free? h with
    | .ok s => pure s
    | .error e => throw (IO.userError e)
  match s.write? { h with offset := 0 } 1 with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "stale write accepted")
  IO.println "CapRuntime: byte read/write/free/stale-refusal OK"
