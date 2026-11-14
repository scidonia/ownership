/-
A timing harness for the two pure byte models.

This file contains no theorem and makes no performance claim. It runs the same
64-byte fill-and-snapshot pattern on both models of the development and prints
how long each takes:

* the mutable-backend model of `Cap.Backend`, driven by `Cap.BackendRun.fill`,
  which performs one `Backend.write` per byte (`List.set` on a 64-element list)
  and whose snapshot is the final buffer `Backend.buf`;
* the reference heap of `Cap.Bytes`, driven by `Heap.alloc`, `Heap.fill?`
  (a `List.range`-and-`List.map` rebuild of the buffer) and `Heap.snapshot?`
  (a lookup, since the buffer is already a value).

Each repetition starts from a fresh allocation, fills offsets `[0, n/2)` with 1
and `[n/2, n)` with `UInt8.ofNat i` for the repetition index `i`, and then takes
the snapshot. The byte sum of every snapshot is accumulated into a checksum that
is printed, so the work cannot be skipped as unused, and so a run where the two
models disagree about the bytes is visible in the output.

What the numbers are: wall-clock elapsed time of these definitions as evaluated
by the toolchain's evaluator in one process on one machine. They therefore
measure the pure models' operation sequences — the dispatch of `Backend.write`
and `Heap.fill?`/`Heap.snapshot?` and the list operations behind them — and
nothing else: not an optimised array or `ByteArray` backend, not FFI, not a
compiler-emitted program's allocation or garbage collection, and not any
guarantee about a real runtime. Because the run is interpreted rather than
compiled to native code, the per-repetition figure includes the evaluator's own
overhead on top of the model's operations, and it is environment-dependent:
machine, load, toolchain build and evaluation strategy all move it. Do not quote
these numbers as a property of the models; they are an observation of one run.

Run from the repository root, after the `Cap` library has been built once so its
olean files exist, so that the imports above resolve:

```
lake build Cap
lake env lean bench/CapTiming.lean
```
-/
import Cap.BackendRun
import Cap.Bytes

open Cap

namespace Cap

/-- One repetition of the pattern on the mutable-backend model: a fresh `n`-byte
backend, the first half written with 1 and the second with `UInt8.ofNat i`, one
`Backend.write` per byte, then the final buffer. The result is the byte sum of
that buffer, or 0 if a write failed. -/
def backendRep (n i : Nat) : Nat :=
  let half := n / 2
  let done :=
    (BackendRun.fill (Backend.empty n) 0 half (1 : UInt8)).bind
      (fun b => BackendRun.fill b half n (UInt8.ofNat i))
  match done with
  | none => 0
  | some b => Heap.sum b.buf

/-- One repetition of the pattern on the reference heap: a fresh `n`-byte
allocation at index 0, the same two `Heap.fill?` calls, then `Heap.snapshot?`.
The result is the byte sum of the snapshot, or 0 if a step failed. -/
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

/-- Run `step` at every repetition index and add its results up. The index makes
each repetition's byte content different, and the sum keeps every snapshot
observable. -/
def runReps (reps : Nat) (step : Nat → Nat) : Nat :=
  (List.range reps).foldl (fun acc i => acc + step i) 0

/-- Time `reps` repetitions of `step` and print the total milliseconds, the total
nanoseconds, the nanoseconds per repetition and the checksum. -/
def timed (label : String) (reps : Nat) (step : Nat → Nat) : IO Unit := do
  let ms0 ← IO.monoMsNow
  let ns0 ← IO.monoNanosNow
  let checksum := runReps reps step
  let ns1 ← IO.monoNanosNow
  let ms1 ← IO.monoMsNow
  let totalMs := ms1 - ms0
  let totalNs := ns1 - ns0
  let perRep := if reps = 0 then 0 else totalNs / reps
  IO.println s!"{label}: reps={reps} total_ms={totalMs} total_ns={totalNs} \
ns_per_repetition={perRep} checksum={checksum}"

/-- Time `reps` full 64-byte fill-and-snapshot repetitions on the mutable-backend
model (each byte written by its own `Backend.write`). -/
def fillBackend (n : Nat) (reps : Nat) : IO Unit :=
  timed "backend" reps (fun i => backendRep n i)

/-- Time `reps` full fill-and-snapshot repetitions on the reference heap (each
half filled by one `Heap.fill?`). -/
def fillReference (n : Nat) (reps : Nat) : IO Unit :=
  timed "reference" reps (fun i => referenceRep n i)

/-- Print the two timings on the 64-byte example. Both sides cover the same
number of repetitions and the same buffer size, so the checksums must agree. -/
def main : IO Unit := do
  IO.println "backend"
  fillBackend 64 10000
  IO.println "reference"
  fillReference 64 10000

end Cap

#eval Cap.main
