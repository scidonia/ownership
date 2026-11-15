/-
A small executable interpreter over the pure backend.

This is an *interpreter over the pure `Cap.Backend` state machine for one
allocation*: a program is a list of `Instr`, where `Instr.fill lo hi v` performs one
`Backend.write` per offset of `[lo, hi)` and `Instr.snapshot` records the current
buffer. It is deliberately not the reference interpreter of `Cap.Bytes`, not an FFI
path and not a compiler guarantee: no real machine is involved, there is no
allocation beyond the one backend the program starts from, and nothing here says
anything about cost, aliasing, lifetimes or concurrent access.

What is proved here:
* `exec_fill_refines` — one in-range fill followed by a snapshot produces the same
  bytes as `Heap.fill?` at the same range and byte, on the reference heap's fresh
  64-byte allocation at index 0.
* `exec_example` — the 64-byte example program (fill `[0, 32)` with 1, fill
  `[32, 64)` with 2, snapshot) yields 32 ones followed by 32 twos.
* `exec_example_refines_heap` — the same program's observation is exactly
  `Heap.example64Buf`, the reference heap's buffer after its own run.
* `execFill_eq_BackendRun_fill` — the interpreter's fill loop is the concrete run's
  fill loop, so `Cap.BackendRun` and this interpreter agree by definition.
* `execFill_beyond` — a fill beginning past the end of the buffer fails. Unlike
  `Heap.fill?`, which ignores out-of-range offsets, the interpreter stops at the
  first failing write, so the refinement statements below cover in-range ranges
  only.
-/
import Cap.Backend
import Cap.Bytes
import Cap.BackendRun

-- The concrete `decide` checks below evaluate a 64-byte run, whose kernel
-- reduction nests deeply.
set_option maxRecDepth 10000

namespace Cap

/-- An instruction of the interpreter: fill offsets `[lo, hi)` with `v`, or record
the current buffer as the observation. -/
inductive Instr where
  | fill (lo hi : Nat) (v : UInt8)
  | snapshot

/-- Write `v` at every offset of `[lo, hi)`, one `Backend.write` per offset; stops
at the first failing write. -/
def execFill (b : Backend) (lo hi : Nat) (v : UInt8) : Option Backend :=
  (List.range (hi - lo)).foldl
    (fun acc k => acc.bind (fun b => b.write (lo + k) v)) (some b)

/-- The interpreter's fill loop is `Cap.BackendRun.fill`, by definition. -/
theorem execFill_eq_BackendRun_fill :
    execFill = BackendRun.fill := rfl

/-- Run a program from backend `b`, carrying the last recorded observation. A
`fill` keeps the observation and continues from the backend it produced; a
`snapshot` replaces the observation with the current buffer. The observation starts
empty, so a program that takes no snapshot observes `[]`. -/
def execGo : Backend → List UInt8 → List Instr → Option (Backend × List UInt8)
  | b, obs, [] => some (b, obs)
  | b, obs, Instr.fill lo hi v :: rest => (execFill b lo hi v).bind (fun b' => execGo b' obs rest)
  | b, _, Instr.snapshot :: rest => execGo b b.buf rest

/-- Run a program and return the final backend together with the last snapshot. -/
def exec (b : Backend) (p : List Instr) : Option (Backend × List UInt8) :=
  execGo b [] p

/-- A program with no instructions succeeds and observes nothing. -/
theorem exec_nil (b : Backend) : exec b [] = some (b, []) := rfl

/-- The 64-byte example program: fill `[0, 32)` with 1, fill `[32, 64)` with 2,
then snapshot. -/
def execExampleProgram : List Instr :=
  [Instr.fill 0 32 (1 : UInt8), Instr.fill 32 64 (2 : UInt8), Instr.snapshot]

/-- The example program's observed buffer is 32 ones followed by 32 twos. -/
theorem exec_example :
    (exec (Backend.empty 64) execExampleProgram).map Prod.snd =
      some (List.replicate 32 (1 : UInt8) ++ List.replicate 32 (2 : UInt8)) := by
  decide

/-- A single in-range fill followed by a snapshot observes the same bytes as
`Heap.fill?` at the same range and byte on the reference heap's fresh 64-byte
allocation at index 0. -/
theorem exec_fill_refines :
    (exec (Backend.empty 64) [Instr.fill 0 64 (7 : UInt8), Instr.snapshot]).map Prod.snd =
      (Heap.fill? (Heap.empty.alloc ⟨0⟩ 64) ⟨0⟩ 0 64 (7 : UInt8)).bind
        (fun h => h.snapshot? ⟨0⟩) := by
  decide

/-- The example program's observation is the reference heap's example buffer: the
interpreter and the reference model agree byte for byte on the one allocation. -/
theorem exec_example_refines_heap :
    (exec (Backend.empty 64) execExampleProgram).map Prod.snd = Heap.example64Buf := by
  decide

/-- A fill starting past the end of the buffer fails at its first write, whereas
`Heap.fill?` would ignore the range. -/
theorem execFill_beyond :
    execFill (Backend.empty 64) 64 65 (1 : UInt8) = none := by
  decide

end Cap
