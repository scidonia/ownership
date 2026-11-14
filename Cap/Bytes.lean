/-
A reference byte heap.

This is a *reference model only*: an allocation is a buffer of bytes, kept as a
`List UInt8` so that offsets start at 0 and index arithmetic stays small. There is
no permission ledger here: nothing in this module knows about capabilities,
lifetimes, loans, ceilings or ownership. It exists so that the ledger's invariants
can be stated against a heap whose reads and writes are ordinary list operations.

The heap is immutable. `Heap.write?` and `Heap.fill?` return a new heap and never
mutate their argument, and `Heap.snapshot?` copies the buffer out: the returned
list is a value that later writes to the heap cannot change.

What is proved here:
* `write_get` — a successful write at index `i` is visible to a read at `i`.
* `write_preserves_length` — a write leaves the buffer's length unchanged.
* `write_ne` — a write at `i` does not change a read at `j ≠ i`.
* `example64_snapshot`, `example64_left_sum` (32), `example64_right_sum` (64) and
  `right_readers_both_64` — the concrete run of the example buffer (64 zero bytes,
  the first half filled with 1, the second with 2) has the expected contents; the
  two readers of the right half each sum to 64.
* `snapshot_independent` — a snapshot taken before a write still holds the old
  bytes when read after the write.

What is not proved here: anything about allocation identity reuse, aliasing,
permissions, or failure modes other than "unknown allocation" and "index out of
range". `Heap.alloc` simply replaces any existing buffer at that `AllocId`.
-/
import Cap.Id

namespace Cap

/-- A byte heap: one buffer per allocation, as a list (offset 0 first). -/
structure Heap where
  bufs : List (AllocId × List UInt8)
deriving Repr

namespace Heap

/-- Look up an allocation's buffer; the first entry for `a` wins. -/
def lookupList? : List (AllocId × List UInt8) → AllocId → Option (List UInt8)
  | [], _ => none
  | (k, v) :: rest, a => if k = a then some v else lookupList? rest a

/-- Replace the first buffer stored for `a`, appending it if absent. -/
def updateList :
    List (AllocId × List UInt8) → AllocId → List UInt8 →
      List (AllocId × List UInt8)
  | [], a, w => [(a, w)]
  | (k, v) :: rest, a, w => if k = a then (k, w) :: rest else (k, v) :: updateList rest a w

/-- The heap with no allocations. -/
def empty : Heap := ⟨[]⟩

/-- The buffer stored for `a`, if any. -/
def lookup? (h : Heap) (a : AllocId) : Option (List UInt8) := lookupList? h.bufs a

/-- Allocate `n` zero bytes at `a`, replacing any buffer already stored there. -/
def alloc (h : Heap) (a : AllocId) (n : Nat) : Heap :=
  ⟨updateList h.bufs a (List.replicate n (0 : UInt8))⟩

/-- Read byte `i` of allocation `a`. -/
def read? (h : Heap) (a : AllocId) (i : Nat) : Option UInt8 :=
  (lookup? h a).bind (fun xs => xs[i]?)

/-- Write `v` at offset `i` of allocation `a`; fails for an unknown allocation or
an out-of-range offset. -/
def write? (h : Heap) (a : AllocId) (i : Nat) (v : UInt8) : Option Heap :=
  match lookup? h a with
  | none => none
  | some xs => if i < xs.length then some ⟨updateList h.bufs a (xs.set i v)⟩ else none

/-- A copy of allocation `a`'s bytes. Writes to the heap do not affect a snapshot
already taken. -/
def snapshot? (h : Heap) (a : AllocId) : Option (List UInt8) := lookup? h a

/-- Fill offsets `[lo, hi)` of allocation `a` with `v`. Offsets outside the buffer
are ignored, so a range past the end writes only the part that exists. -/
def fill? (h : Heap) (a : AllocId) (lo hi : Nat) (v : UInt8) : Option Heap :=
  match lookup? h a with
  | none => none
  | some xs =>
      some ⟨updateList h.bufs a
        ((List.range xs.length).map (fun k => if lo ≤ k ∧ k < hi then v else xs.getD k (0 : UInt8)))⟩

/-- Looking up a buffer after inserting one at the same key yields the inserted
buffer. -/
theorem lookupList?_updateList {a : AllocId} {w : List UInt8}
    (l : List (AllocId × List UInt8)) {xs : List UInt8}
    (h : lookupList? l a = some xs) :
    lookupList? (updateList l a w) a = some w := by
  induction l with
  | nil => simp [lookupList?] at h
  | cons p rest ih =>
      obtain ⟨k, v⟩ := p
      by_cases hk : k = a
      · simp [lookupList?, updateList, hk]
      · simp only [lookupList?, updateList, hk, ite_false] at h ⊢
        exact ih h

/-- A successful write is visible to a read at the same offset. -/
theorem write_get {h h' : Heap} {a : AllocId} {i : Nat} {v : UInt8}
    (hw : write? h a i v = some h') : read? h' a i = some v := by
  cases hl : lookup? h a with
  | none => simp [write?, hl] at hw
  | some xs =>
      by_cases hlt : i < xs.length
      · simp only [write?, hl, if_pos hlt, Option.some.injEq] at hw
        have hupd : lookupList? (updateList h.bufs a (xs.set i v)) a = some (xs.set i v) :=
          lookupList?_updateList h.bufs (xs := xs) hl
        rw [← hw]
        simp [read?, lookup?, hupd, List.getElem?_set_self hlt]
      · simp [write?, hl, hlt] at hw

/-- A write does not change the buffer's length. -/
theorem write_preserves_length {h h' : Heap} {a : AllocId} {i : Nat} {v : UInt8}
    (hw : write? h a i v = some h') :
    (lookup? h' a).map List.length = (lookup? h a).map List.length := by
  cases hl : lookup? h a with
  | none => simp [write?, hl] at hw
  | some xs =>
      by_cases hlt : i < xs.length
      · simp only [write?, hl, if_pos hlt, Option.some.injEq] at hw
        have hupd : lookupList? (updateList h.bufs a (xs.set i v)) a = some (xs.set i v) :=
          lookupList?_updateList h.bufs (xs := xs) hl
        rw [← hw]
        simp [lookup?, hupd, List.length_set]
      · simp [write?, hl, hlt] at hw

/-- A write at `i` does not change a read at any other offset `j`. -/
theorem write_ne {h h' : Heap} {a : AllocId} {i j : Nat} {v : UInt8}
    (hw : write? h a i v = some h') (hij : i ≠ j) :
    read? h' a j = read? h a j := by
  cases hl : lookup? h a with
  | none => simp [write?, hl] at hw
  | some xs =>
      by_cases hlt : i < xs.length
      · simp only [write?, hl, if_pos hlt, Option.some.injEq] at hw
        have hupd : lookupList? (updateList h.bufs a (xs.set i v)) a = some (xs.set i v) :=
          lookupList?_updateList h.bufs (xs := xs) hl
        rw [← hw]
        have hlu : lookupList? h.bufs a = some xs := hl
        simp [read?, lookup?, hupd, hlu, List.getElem?_set_ne hij]
      · simp [write?, hl, hlt] at hw

/-- The byte sum of a list. -/
def sum (xs : List UInt8) : Nat := (xs.map (fun b => b.toNat)).sum

/-- The example heap: 64 zero bytes at allocation 0, offsets `[0, 32)` set to 1 and
offsets `[32, 64)` set to 2. -/
def example64 : Option Heap :=
  ((empty.alloc ⟨0⟩ 64).fill? ⟨0⟩ 0 32 (1 : UInt8)).bind
    (fun h => h.fill? ⟨0⟩ 32 64 (2 : UInt8))

/-- The example heap's buffer, if every step succeeded. -/
def example64Buf : Option (List UInt8) := example64.bind (fun h => h.snapshot? ⟨0⟩)

/-- Sum of the example heap's first half. -/
def example64_left : Option Nat := example64Buf.map (fun xs => sum (xs.take 32))

/-- Sum of the example heap's second half. -/
def example64_right : Option Nat := example64Buf.map (fun xs => sum (xs.drop 32))

theorem example64_snapshot :
    example64Buf =
      some (List.replicate 32 (1 : UInt8) ++ List.replicate 32 (2 : UInt8)) := by
  decide

theorem example64_left_sum : example64_left = some 32 := by
  decide

theorem example64_right_sum : example64_right = some 64 := by
  decide

/-- Two readers of the *right* half each observe 64: a fractional split shares one
footprint, it does not divide the bytes. -/
def rightReaders : Option (Nat × Nat) :=
  example64Buf.map (fun xs => (sum (xs.drop 32), sum (xs.drop 32)))

theorem right_readers_both_64 : rightReaders = some (64, 64) := by
  decide

/-- A two-step run used to observe that a snapshot is a copy: fill four bytes with
7, snapshot it, write 9 at offset 0, then read the old snapshot *and* take a new one.
The tuple is (before the write, the same snapshot read again after the write, the
new heap's snapshot). -/
def snapshotRun : Option (List UInt8 × List UInt8 × List UInt8) :=
  ((empty.alloc ⟨0⟩ 4).fill? ⟨0⟩ 0 4 (7 : UInt8)).bind (fun h =>
    (h.snapshot? ⟨0⟩).bind (fun before =>
      (h.write? ⟨0⟩ 0 9).bind (fun h' =>
        (h.snapshot? ⟨0⟩).bind (fun again =>
          (h'.snapshot? ⟨0⟩).map (fun after => (before, again, after))))))

/-- The snapshot taken before the write is unchanged when read afterwards; only the
heap returned by the write sees the new byte. -/
theorem snapshot_independent :
    snapshotRun = some ([7, 7, 7, 7], [7, 7, 7, 7], [9, 7, 7, 7]) := by
  decide

end Heap

end Cap
