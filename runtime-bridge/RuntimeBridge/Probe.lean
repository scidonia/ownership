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

def mkAIO (n : Nat) : IO (Array Nat) := do
  let mut a : Array Nat := Array.mkEmpty n
  for i in [0:n] do a := a.push i
  return a

/-- Compare the model's predicted disposition with the runtime observation. -/
def diffCase (name : String) (predExcl predSame : Bool) (excl same : Bool) : IO Bool := do
  let ok := (excl == predExcl) && (same == predSame)
  IO.println s!"differential {name}: predicted exclusive={predExcl} same={predSame}; observed exclusive={excl} same={same}; agree={ok}"
  return ok

/-- The model's predicates on the runtime corpus: exclusive iff one reference and
non-persistent; the write mutates iff exclusive; a persistent or shared source
copies; dropping the extra reference restores in-place. -/
def differential : IO UInt32 := do
  let mut ok := true
  -- unique
  let a0 ← mkAIO 8
  let e0 := exclusive a0
  let ab0 ← addressIO a0
  let b0 := a0.set! 0 7
  let aa0 ← addressIO b0
  ok := (← diffCase "unique" true true e0 (ab0 == aa0)) && ok
  -- count two: a live alias
  let a1 ← mkAIO 8
  let kept1 := a1
  let e1 := exclusive a1
  let ab1 ← addressIO a1
  let b1 := a1.set! 0 7
  let aa1 ← addressIO b1
  ok := (← diffCase "alias2" false false e1 (ab1 == aa1)) && ok
  IO.println s!"differential alias2-kept: alias reads {kept1[0]!} (expected 0), write reads {b1[0]!} (expected 7)"
  -- count back to one: the alias is released before the write
  let a2 ← mkAIO 8
  let holder ← IO.mkRef (some a2)
  holder.set none
  let e2 := exclusive a2
  let ab2 ← addressIO a2
  let b2 := a2.set! 0 7
  let aa2 ← addressIO b2
  ok := (← diffCase "drop-to-one" true true e2 (ab2 == aa2)) && ok
  -- persistent literal
  let p := #[1, 2, 3]
  let ep := exclusive p
  let abp ← addressIO p
  let bp := p.set! 0 7
  let aap ← addressIO bp
  ok := (← diffCase "persistent" false false ep (abp == aap)) && ok
  -- a closure holding the array
  let c ← mkAIO 8
  let f := fun () => c.size
  let ch ← IO.mkRef (some f)
  let ec := exclusive c
  let abc ← addressIO c
  let bc := c.set! 0 7
  let aac ← addressIO bc
  let _ ← ch.get
  ok := (← diffCase "closure" false false ec (abc == aac)) && ok
  if ok then return 0 else return 1

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
  | ["differential"] => differential
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
