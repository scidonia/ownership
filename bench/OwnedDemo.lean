/-
A guarded interface that *acts* affine, without affine types.

`Owned` hides the array behind a private constructor, and carries a shared
monotone flag: using a handle marks it used, and produces a fresh handle with a
*fresh* unused flag. A copy of a handle shares the old flag, so the second use of
either copy fails at run time — the type never sees the duplication.

This is dynamic enforcement. Static enforcement is the checker/macro over a
surface or the compiled IR; the model-level statement of affinity is
`Ownership.Accounted` (two handles at one count-one cell are refuted).
-/
structure Owned (α : Type) where
  private mk ::
  val : α
  used : IO.Ref Bool

namespace Owned

/-- Acquire: a fresh, unused handle. -/
def new (a : α) : IO (Owned α) := do
  let r ← IO.mkRef false
  pure ⟨a, r⟩

/-- Consume a handle, failing if it was used before (which includes any copy). -/
def take (o : Owned α) : IO α := do
  if ← o.used.get then
    throw (IO.userError "owned handle used twice")
  o.used.set true
  pure o.val

/-- Write through a handle, returning a fresh unused handle for the result. -/
def write (o : Owned (Array Nat)) (i v : Nat) : IO (Owned (Array Nat)) := do
  let a ← take o
  let r ← IO.mkRef false
  pure ⟨a.set! i v, r⟩

end Owned

def main : IO Unit := do
  let a ← Owned.new (#[0, 0, 0] : Array Nat)
  let a1 ← Owned.write a 0 7
  -- a second use of the *consumed* handle
  try
    let _ ← Owned.write a 1 8
    IO.println "BUG: reused a consumed handle"
  catch e =>
    IO.println s!"consumed handle refused: {e}"
  -- a copy of the live handle, then two uses
  let a2 := a1
  let _ ← Owned.write a1 1 9
  try
    let _ ← Owned.write a2 2 1
    IO.println "BUG: duplicated a live handle"
  catch e =>
    IO.println s!"duplicate refused: {e}"

#eval main
