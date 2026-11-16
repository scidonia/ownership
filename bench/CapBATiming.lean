/-
Timing comparison of the three backends on the 64-byte fill-and-snapshot
pattern: the pure list `Backend`, the byte-array `BackendArr`
(`Cap/BackendArr.lean`), and the reference `Heap` (`Cap/Bytes.lean`).

What the numbers are: wall-clock elapsed time of these definitions as evaluated
by the toolchain's evaluator in one process on one machine. They therefore
measure the three implementations' operation sequences — the dispatch of
`Backend.write`, `BackendArr.write` and `Heap.fill?`/`Heap.snapshot?` and the
list/array operations behind them — and nothing else: not a compiled program,
not FFI, not any guarantee about a real runtime, and not an observation of Lean's
possible in-place update of a uniquely referenced `ByteArray`. Because the run is
interpreted rather than compiled to native code, the per-repetition figure
includes the evaluator's own overhead on top of each implementation's operations,
and it is environment-dependent: machine, load, toolchain build and evaluation
strategy all move it. Do not quote these numbers as a property of the
implementations; they are an observation of one run.

Run from the repository root, after the `Cap` library has been built once so its
olean files exist, so that the imports above resolve:

```
lake build Cap
lake env lean bench/CapBATiming.lean
```
-/
import Cap.BackendArr
import Cap.BackendRun
import Cap.Bytes

open Cap

namespace Cap

/-- One repetition on the byte-array backend: a fresh `n`-byte backend, the first
half filled with 1 and the second with `UInt8.ofNat i`, one `BackendArr.write`
per byte, then the final buffer read back as a list. The result is the byte sum
of that buffer, or 0 if a write failed. -/
def baRep (n i : Nat) : Nat :=
  let half := n / 2
  let done :=
    (baFill (BackendArr.empty n) 0 half (1 : UInt8)).bind
      (fun x => baFill x half (n - half) (UInt8.ofNat i))
  match done with
  | none => 0
  | some x => Heap.sum x.arr.data.toList

/-- One repetition on the pure list backend. -/
def backendRep (n i : Nat) : Nat :=
  let half := n / 2
  let done :=
    (BackendRun.fill (Backend.empty n) 0 half (1 : UInt8)).bind
      (fun b => BackendRun.fill b half n (UInt8.ofNat i))
  match done with
  | none => 0
  | some b => Heap.sum b.buf

/-- One repetition on the reference heap. -/
def referenceRep (n i : Nat) : Nat :=
  let half := n / 2
  let done :=
    ((Heap.empty.alloc ⟨0⟩ n).fill? ⟨0⟩ 0 half (1 : UInt8)).bind
      (fun h => h.fill? ⟨0⟩ half n (UInt8.ofNat i))
  match done with
  | none => 0
  | some h =>
      match h.snapshot? ⟨0⟩ with
      | none => 0
      | some xs => Heap.sum xs

/-- Run `step` at every repetition index and add its results up. -/
def runReps (reps : Nat) (step : Nat → Nat) : Nat :=
  (List.range reps).foldl (fun acc i => acc + step i) 0

/-- Time `reps` repetitions of `step` and print the totals and the checksum. -/
def timed (label : String) (reps : Nat) (step : Nat → Nat) : IO Unit := do
  let ns0 ← IO.monoNanosNow
  let checksum := runReps reps step
  let ns1 ← IO.monoNanosNow
  let totalNs := ns1 - ns0
  let perRep := if reps = 0 then 0 else totalNs / reps
  IO.println s!"{label}: reps={reps} total_ns={totalNs} ns_per_repetition={perRep} checksum={checksum}"

/-- Print the three timings on the 64-byte example. All three cover the same
number of repetitions and the same buffer size, so the checksums must agree. -/
def main : IO Unit := do
  timed "backend (list)" 10000 (backendRep 64)
  timed "backend (byte array)" 10000 (baRep 64)
  timed "reference" 10000 (referenceRep 64)

end Cap

#eval Cap.main
