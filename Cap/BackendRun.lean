/-
A concrete run of the pure backend.

This is a *concrete run of the pure `Cap.Backend` state machine*, on the same
64-byte example as `Cap.Bytes.example64`: a fresh 64-byte allocation at index 0,
the first 32 bytes written with 1 and the next 32 with 2 by successive
`Backend.write` calls. The snapshot is the backend's final buffer.

What is proved here:
* `exampleBackend_snapshot` — every write succeeded and the final buffer is
  32 copies of 1 followed by 32 copies of 2.
* `exampleBackend_rel` — that final buffer is exactly the buffer the reference
  heap of `Cap.Bytes` holds at allocation 0 after its own run.

This is not the interpreter, not an FFI claim and not a performance result: no
byte is ever written outside the modelled buffer, and no claim is made about how
any real runtime would execute the run. Only the sampled buffer is compared; the
theorems say nothing about allocations other than index 0, about failure modes,
or about the cost of the run.
-/
import Cap.Backend
import Cap.Bytes

namespace Cap

/-- Write `v` at every offset of `[lo, hi)`, one `Backend.write` per offset. Stops
at the first failing write. -/
def BackendRun.fill (b : Backend) (lo hi : Nat) (v : UInt8) : Option Backend :=
  (List.range (hi - lo)).foldl
    (fun acc k => acc.bind (fun b => b.write (lo + k) v)) (some b)

/-- The 64-byte example run on the mutable backend: an empty 64-byte backend at
index 0, offsets `[0, 32)` written with 1, then offsets `[32, 64)` with 2. -/
def exampleBackend : Option Backend :=
  (BackendRun.fill (Backend.empty 64) 0 32 (1 : UInt8)).bind
    (fun b => BackendRun.fill b 32 64 (2 : UInt8))

/-- The final buffer of the example run, if every step succeeded. -/
def exampleBackendSnapshot : Option (List UInt8) :=
  exampleBackend.map Backend.buf

theorem exampleBackend_snapshot :
    exampleBackendSnapshot =
      some (List.replicate 32 (1 : UInt8) ++ List.replicate 32 (2 : UInt8)) := by
  decide

/-- The example run's final buffer is the reference heap's buffer at allocation 0:
the two models agree byte for byte on the sampled allocation. -/
theorem exampleBackend_rel : exampleBackendSnapshot = Heap.example64Buf := by
  decide

end Cap
