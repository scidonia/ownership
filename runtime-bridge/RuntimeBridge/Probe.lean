/-
Priority 1 reproducer: the context-sensitive in-place observation.

Two cases with the same input construction, update and observations:

* `separate-*`: the update runs in its own function (`separateCase`), the shape
  the `inplace` harness uses.
* `inline-*`: the same update is written out in `main`, in a larger `do` block.

Each is run at exact capacity (`slack = 0`) and with one spare slot (`slack =
1`). The observations are taken through `IO` before the write, and the original
array is not used after it, so the observation does not retain the alias it
measures. `sealed` repeats a write through `Structured.runFresh`.

Run a mode with and without `SCIDONIA_CHECK_INPLACE=1`; the check-enabled run
aborts at a write that would copy.
-/
import Scidonia.FracPerm
import Scidonia.FracPerm.StateVar.Layout5

open Scidonia.FracPerm
open Scidonia.FracPerm.StateVar

def exclusive {α : Type} (x : @& α) : Bool := unsafe isExclusiveUnsafe x
def address {α : Type} (x : @& α) : USize := unsafe ptrAddrUnsafe x
def addressIO {α : Type} (x : @& α) : IO USize := return address x

abbrev layout : Layout5.Layout := .arr (.struct (.leaf .uint) (.leaf .uint))
def p3 : Layout5.ObsPath layout := ⟨.index 3 (.left .here), .uint, rfl⟩

def freshStructs (n : Nat) (slack : Nat) : Array (UInt64 × UInt64) := Id.run do
  let mut a : Array (UInt64 × UInt64) := Array.mkEmpty (n + slack)
  for i in [0:n] do
    a := a.push ((i + 1).toUInt64, (i + 101).toUInt64)
  return a

/-- The update in its own function: the array is the function's input and is not
used after the call. -/
def separateCase (name : String) (slack : Nat) : IO Unit := do
  let a := freshStructs 8 slack
  let e := exclusive a
  let ab ← addressIO a
  let fb ← addressIO (a[3]!)
  let (b, ok) := Layout5.setLeaf p3 (77 : UInt64) a
  let aa ← addressIO b
  let fa ← addressIO (b[3]!)
  IO.println s!"{name}: exclusive_before={e} same_buffer={ab == aa} same_focused={fb == fa} ok={ok} value={b[3]!}"

/-- The sealed interface: the array is created inside `runFresh`; the client sees
only the program's results. -/
def freshStructsIO (n : Nat) (slack : Nat) : IO (Array (UInt64 × UInt64)) := do
  let mut a : Array (UInt64 × UInt64) := Array.mkEmpty (n + slack)
  for i in [0:n] do
    a := a.push ((i + 1).toUInt64, (i + 101).toUInt64)
  return a

/-- A parameterless case: the same pure construction, but closed. -/
def closedCase : IO Unit := do
  let a := freshStructs 8 0
  let e := exclusive a
  let ab ← addressIO a
  let fb ← addressIO (a[3]!)
  let (b, ok) := Layout5.setLeaf p3 (77 : UInt64) a
  let aa ← addressIO b
  let fa ← addressIO (b[3]!)
  IO.println s!"closed-case: exclusive_before={e} same_buffer={ab == aa} same_focused={fb == fa} ok={ok} value={b[3]!}"

def sealedCase : IO Unit := do
  let r ← Structured.runFresh { size := 8, fill := 1 } (do
    let w0 ← Structured.Program.set 0 17
    let w1 ← Structured.Program.set 1 23
    return (w0, w1))
  IO.println s!"sealed: writes={r}"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["separate-exact"] => separateCase "separate-exact" 0; return 0
  | ["separate-spare"] => separateCase "separate-spare" 1; return 0
  | ["closed-case"] => closedCase; return 0
  | ["inline-io"] =>
    let a ← freshStructsIO 8 0
    let e := exclusive a
    let ab ← addressIO a
    let fb ← addressIO (a[3]!)
    let (b, ok) := Layout5.setLeaf p3 (77 : UInt64) a
    let aa ← addressIO b
    let fa ← addressIO (b[3]!)
    IO.println s!"inline-io: exclusive_before={e} same_buffer={ab == aa} same_focused={fb == fa} ok={ok} value={b[3]!}"
    return 0
  | ["sealed"] => sealedCase; return 0
  | ["inline-exact"] =>
    let a := freshStructs 8 0
    let e := exclusive a
    let ab ← addressIO a
    let fb ← addressIO (a[3]!)
    let (b, ok) := Layout5.setLeaf p3 (77 : UInt64) a
    let aa ← addressIO b
    let fa ← addressIO (b[3]!)
    IO.println s!"inline-exact: exclusive_before={e} same_buffer={ab == aa} same_focused={fb == fa} ok={ok} value={b[3]!}"
    return 0
  | ["inline-spare"] =>
    let a := freshStructs 8 1
    let e := exclusive a
    let ab ← addressIO a
    let fb ← addressIO (a[3]!)
    let (b, ok) := Layout5.setLeaf p3 (77 : UInt64) a
    let aa ← addressIO b
    let fa ← addressIO (b[3]!)
    IO.println s!"inline-spare: exclusive_before={e} same_buffer={ab == aa} same_focused={fb == fa} ok={ok} value={b[3]!}"
    return 0
  | _ =>
    IO.eprintln "usage: probe separate-exact|separate-spare|inline-exact|inline-spare|sealed"
    return 2
