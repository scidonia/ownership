/-
A mutable-backend model for one allocation.

This is a *pure state machine over a buffer*, not an executable backend: there is
no FFI, no pointer, no alias and no concurrency. It exists so that the reference
heap of `Cap.Bytes` can be refined by a value whose read and write are ordinary
list operations on a length-indexed buffer. `Backend` records the buffer, its
length and a proof that the length matches, so a write can keep the length while
changing a byte.

`Backend.Rel b h a` says that `h` holds exactly `b.buf` at allocation `a`. The
refinement theorems below are stated against that relation, one allocation at a
time: they say nothing about other allocations in the heap, about capabilities or
lifetimes, and they are not a compiler guarantee.

What is proved here:
* `Backend.empty_rel` — the empty backend allocated at `a` in the empty heap
  relates to `a`.
* `Backend.read_refines` — a successful backend read is the heap's read of the
  same allocation and offset.
* `Backend.write_refines` — if the heap write at the same index succeeds, the
  updated backend relates to the updated heap; both sides write the same byte.
* `Backend.write_preserves_len` — a successful write leaves the buffer's length
  unchanged.
* `Backend.write_then_read` — a read after a successful write at that index
  returns the written byte.
* `Backend.write_buf` and `Backend.write_lt` — the two facts about `Backend.write`
  (its buffer is `List.set`, and success implies the index is in range) that the
  refinement proofs use; `Backend.write` fails exactly out of range, matching
  `Heap.write?`.
-/
import Cap.Bytes

namespace Cap

/-- A mutable backend for one allocation, as a pure state machine over its buffer. -/
structure Backend where
  buf : List UInt8
  len : Nat
  hlen : buf.length = len

/-- Equality ignores the length proof, which is proof-irrelevant. -/
instance : DecidableEq Backend := by
  intro a b
  by_cases h : a.buf = b.buf ∧ a.len = b.len
  · refine isTrue ?_
    cases a
    cases b
    simp_all
  · refine isFalse ?_
    intro hab
    apply h
    cases hab
    exact ⟨rfl, rfl⟩

/-- The reference buffer of an allocation, if present. -/
def Backend.Rel (b : Backend) (h : Heap) (a : AllocId) : Prop :=
  h.lookup? a = some b.buf

/-- The backend for a fresh allocation of `n` zero bytes. -/
def Backend.empty (n : Nat) : Backend :=
  { buf := List.replicate n (0 : UInt8), len := n, hlen := List.length_replicate }

/-- Read byte `i`, failing out of range. -/
def Backend.read (b : Backend) (i : Nat) : Option UInt8 :=
  b.buf[i]?

/-- Write `v` at offset `i`, failing out of range; the length is unchanged. -/
def Backend.write (b : Backend) (i : Nat) (v : UInt8) : Option Backend :=
  if i < b.buf.length then
    some { buf := b.buf.set i v, len := b.len,
           hlen := by rw [List.length_set]; exact b.hlen }
  else none

/-- A successful write stores `List.set` of the old buffer. -/
theorem Backend.write_buf {b b' : Backend} {i : Nat} {v : UInt8}
    (hb : b.write i v = some b') : b'.buf = b.buf.set i v := by
  have h := congrArg (fun o : Option Backend => o.map Backend.buf) hb
  unfold Backend.write at h
  split at h
  · simpa using h.symm
  · simp at h

/-- A successful write has its index in range. -/
theorem Backend.write_lt {b b' : Backend} {i : Nat} {v : UInt8}
    (hb : b.write i v = some b') : i < b.buf.length := by
  unfold Backend.write at hb
  split at hb
  · assumption
  · simp at hb

/-- The empty backend relates to the fresh allocation of `n` bytes at `a`. -/
theorem Backend.empty_rel (n : Nat) (a : AllocId) :
    (Backend.empty n).Rel (Heap.empty.alloc a n) a := by
  simp [Backend.Rel, Backend.empty, Heap.empty, Heap.alloc, Heap.lookup?, Heap.lookupList?,
    Heap.updateList]

/-- A successful backend read is the heap's read at the same allocation and offset. -/
theorem Backend.read_refines {b : Backend} {h : Heap} {a : AllocId} {i : Nat} {v : UInt8}
    (hr : b.read i = some v) (hrel : b.Rel h a) : h.read? a i = some v := by
  unfold Backend.read at hr
  unfold Backend.Rel at hrel
  unfold Heap.read?
  rw [hrel]
  simpa using hr

/-- A successful backend write and a successful heap write at the same index leave
the updated backend related to the updated heap. -/
theorem Backend.write_refines {b b' : Backend} {h h' : Heap} {a : AllocId} {i : Nat}
    {v : UInt8} (hb : b.write i v = some b') (hrel : b.Rel h a)
    (hw : h.write? a i v = some h') : b'.Rel h' a := by
  have hbuf := Backend.write_buf hb
  unfold Backend.Rel at hrel ⊢
  unfold Heap.write? at hw
  rw [hrel] at hw
  dsimp only at hw
  split at hw
  · simp only [Option.some.injEq] at hw
    subst hw
    rw [hbuf]
    exact Heap.lookupList?_updateList h.bufs (xs := b.buf) hrel
  · simp at hw

/-- A successful write leaves the buffer's length unchanged. -/
theorem Backend.write_preserves_len {b b' : Backend} {i : Nat} {v : UInt8}
    (hb : b.write i v = some b') : b'.buf.length = b.buf.length := by
  rw [Backend.write_buf hb, List.length_set]

/-- A read after a successful write at the same index returns the written byte. -/
theorem Backend.write_then_read {b b' : Backend} {i : Nat} {v : UInt8}
    (hb : b.write i v = some b') : b'.read i = some v := by
  have hlt := Backend.write_lt hb
  unfold Backend.read
  rw [Backend.write_buf hb]
  exact List.getElem?_set_self hlt

end Cap
