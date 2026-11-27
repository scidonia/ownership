import Cap.UFIntegrated
import Cap.UFCertified

/-!
Union-find performance probe, not a proof.

The same parent chain is created for three representations:

* `lean-array` — native Lean `Array Nat` find with full path compression;
* `uf-list`    — the functional `Cap.UF` model (`findRootF` + `compressAll`);
* `sealed`     — the byte-encoded `Cap.Sealed` machine, with each parent read
  through `chase?` and each compression write checked by `Sealed.write`.

Construction is outside each timed region. The sealed figure includes capability
checks and list-backed byte storage; it is not a native implementation claim.
The `n ≤ 256` bound is the machine's byte-per-parent limit.
-/

open Cap

namespace Cap.UFPerformance

abbrev N := 256

/-- Parent of `i` in the chain `i → i-1`, root at zero. -/
def parent (i : Nat) : Nat := if i = 0 then 0 else i - 1

def chainArr (n : Nat) : Array Nat :=
  (Array.range n).map parent

def chainList (n : Nat) : UF.Arr :=
  (List.range n).map parent

/-- Native Lean find and full path compression. -/
partial def nativeFind (p : Array Nat) (x : Nat) : Nat × Array Nat :=
  let px := p.getD x 0
  if px = x then (x, p)
  else
    let (r, p') := nativeFind p px
    (r, p'.set! x r)

/-- The functional UF model with the same full-path compression. -/
def listFind (p : UF.Arr) (x : Nat) : Nat × UF.Arr :=
  let fuel := p.length + 1
  let r := UF.findRootF p fuel x
  (r, UF.compressAll p r (Cap.rootPath p fuel x))

/-- Build the parent chain in the sealed byte machine. -/
def sealedChain (n : Nat) : Sealed :=
  Id.run do
    let mut s := Sealed.initial ⟨0⟩ n (n + 1) (Nat.succ_pos n) ⟨1⟩ ⟨2⟩
    for i in [0:n] do
      match s.write ⟨0⟩ ⟨1⟩ i (UInt8.ofNat (parent i)) with
      | .ok s' => s := s'
      | .error e => panic! s!"sealed setup refused at {i}: {e}"
    return s

/-- The byte parent array read back after compression, for checksums. -/
def sealedParent (s : Sealed) (x : Nat) : Option Nat :=
  (s.read? ⟨0⟩ x).map UInt8.toNat

/-- One native trial: build outside the timer, find inside. -/
def timeNative (n : Nat) : IO Nat := do
  let p := chainArr n
  let t0 ← IO.monoNanosNow
  let (r, p') := nativeFind p (n - 1)
  let t1 ← IO.monoNanosNow
  unless r = 0 && p'.getD (n - 1) 0 = 0 do
    throw (IO.userError s!"native wrong result at n={n}")
  return t1 - t0

/-- One functional-list trial. -/
def timeList (n : Nat) : IO Nat := do
  let p := chainList n
  let t0 ← IO.monoNanosNow
  let (r, p') := listFind p (n - 1)
  let t1 ← IO.monoNanosNow
  unless r = 0 && p'.getD (n - 1) 0 = 0 do
    throw (IO.userError s!"uf-list wrong result at n={n}")
  return t1 - t0

/-- One sealed trial: construction outside the timer. -/
def timeSealed (n : Nat) : IO Nat := do
  let s := sealedChain n
  let t0 ← IO.monoNanosNow
  let result := UFGeneric.sealedFind s ⟨0⟩ ⟨1⟩ (n + 1) (n - 1)
  let t1 ← IO.monoNanosNow
  match result with
  | .ok (r, s') =>
      unless r = 0 && sealedParent s' (n - 1) = some 0 do
        throw (IO.userError s!"sealed wrong result at n={n}")
      return t1 - t0
  | .error e => throw (IO.userError s!"sealed find refused at n={n}: {e}")

/-- Minimum of a non-empty list. -/
def minimum : List Nat → Nat
  | [] => 0
  | x :: xs => xs.foldl Nat.min x

def runCase (name : String) (n reps : Nat) (trial : Nat → IO Nat) : IO Unit := do
  for _ in [0:5] do
    let _ ← trial n
  let mut times := []
  for _ in [0:reps] do
    times := (← trial n) :: times
  let best := minimum times
  let total := times.foldl (· + ·) 0
  IO.println s!"{name},{n},{reps},{best},{total / reps}"

def main : IO Unit := do
  IO.println "implementation,n,reps,best_ns,mean_ns"
  for n in [32, 128, 256] do
    runCase "lean-array" n 200 timeNative
    runCase "uf-list" n 200 timeList
    runCase "sealed" n 200 timeSealed

end Cap.UFPerformance

def main : IO Unit := Cap.UFPerformance.main
