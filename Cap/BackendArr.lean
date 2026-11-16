/-
A byte-array-backed backend with refinement to the pure list backend.

`BackendArr` stores a `ByteArray`; `Backend` (Cap/Backend.lean) is the
specification. `BackendArr.toBackend` reads the array's data back as a byte
list, and `empty_refines`, `read_refines`, `write_refines` and the fold-level
`fills_refine` state that the implementations agree. The 64-byte two-range fill
through the byte-array route refines the pure run (`ba64_refines`), whose
snapshot is the reference bytes (`pure64_snapshot`, by `decide`: the pure backend
is kernel-computable).

Not claimed: in-place update at runtime. Lean's runtime may mutate a uniquely
referenced `ByteArray`, but that is not observable here and this file makes no
statement about it; that observation problem is the subject of the ownership
side of this repository.
-/
import Cap.Backend

namespace Cap

/-- The byte-array-backed backend. -/
structure BackendArr where
  arr : ByteArray
  len : Nat
  hlen : arr.size = len

/-- The functional reading: the array's data as a byte list of length `len`. -/
def BackendArr.toBackend (x : BackendArr) : Backend :=
  { buf := x.arr.data.toList, len := x.len,
    hlen := by rw [Array.length_toList]; exact x.hlen }

/-- The empty byte-array backend of `n` zero bytes. -/
def BackendArr.empty (n : Nat) : BackendArr :=
  { arr := ⟨Array.replicate n (0 : UInt8)⟩, len := n,
    hlen := Array.size_replicate }

/-- The empty byte-array backend refines the empty pure backend. -/
theorem BackendArr.empty_refines (n : Nat) :
    (BackendArr.empty n).toBackend = Backend.empty n := by
  unfold BackendArr.toBackend BackendArr.empty Backend.empty
  congr 1

/-- Read byte `i`, failing out of range. -/
def BackendArr.read (x : BackendArr) (i : Nat) : Option UInt8 :=
  x.arr.data.toList[i]?

/-- Reads agree with the pure backend. -/
theorem BackendArr.read_refines (x : BackendArr) (i : Nat) :
    x.read i = x.toBackend.read i := rfl

/-- Write `v` at offset `i`, failing out of range; the length is unchanged. -/
def BackendArr.write (x : BackendArr) (i : Nat) (v : UInt8) : Option BackendArr :=
  if h : i < x.arr.size then
    some { arr := ⟨x.arr.data.set i v h⟩, len := x.len,
           hlen := by
             show (x.arr.data.set i v h).size = x.len
             rw [Array.size_set]
             exact x.hlen }
  else none

/-- Writes agree with the pure backend. -/
theorem BackendArr.write_refines (x : BackendArr) (i : Nat) (v : UInt8) :
    (x.write i v).map BackendArr.toBackend = Backend.write x.toBackend i v := by
  unfold BackendArr.write Backend.write BackendArr.toBackend
  by_cases hi : i < x.arr.size
  · have hbl : i < x.arr.data.toList.length := by
      rw [Array.length_toList]
      exact hi
    simp only [hi, ↓reduceDIte, hbl, ↓reduceIte, Option.map_some]
    congr 1
  · have hbl : ¬ i < x.arr.data.toList.length := by
      rw [Array.length_toList]
      exact hi
    simp [hi, hbl]

/-- A range fill on byte-array backends. -/
def baFill (x : BackendArr) (lo n : Nat) (v : UInt8) : Option BackendArr :=
  (List.range n).foldl (fun acc k => acc.bind fun x => x.write (lo + k) v) (some x)

/-- A range fill on pure backends. -/
def pureFill (b : Backend) (lo n : Nat) (v : UInt8) : Option Backend :=
  (List.range n).foldl (fun acc k => acc.bind fun b => b.write (lo + k) v) (some b)

/-- Folding an option-binding step over the `none` accumulator stays `none`. -/
theorem List.foldl_option_bind_none {α : Type} (ks : List Nat)
    (f : Option α → Nat → Option α) (hf : ∀ k, f none k = none) :
    ks.foldl f none = none := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp [List.foldl_cons, hf k, ih]

/-- Fills agree: folding the byte-array write and reading back equals folding the
pure write. -/
theorem BackendArr.fills_refine (x : BackendArr) (lo n : Nat) (v : UInt8) :
    (baFill x lo n v).map BackendArr.toBackend = pureFill x.toBackend lo n v := by
  suffices h : ∀ ks : List Nat, ∀ xa : BackendArr, ∀ ba : Backend,
      ba = xa.toBackend →
      ((ks.foldl (fun acc k => acc.bind fun x => x.write (lo + k) v)) (some xa)).map
        BackendArr.toBackend
        = ks.foldl (fun acc k => acc.bind fun b => b.write (lo + k) v) (some ba) by
    exact h (List.range n) x x.toBackend rfl
  intro ks
  induction ks with
  | nil =>
    intro xa ba hba
    simp [hba]
  | cons k ks ih =>
    intro xa ba hba
    simp only [List.foldl_cons]
    cases hw : xa.write (lo + k) v with
    | none =>
      have hb : xa.toBackend.write (lo + k) v = none := by
        have h2 := BackendArr.write_refines xa (lo + k) v
        rw [hw] at h2
        simpa using h2.symm
      have hL : ((some xa).bind fun x => x.write (lo + k) v) = none := hw
      have hR : ((some ba).bind fun b => b.write (lo + k) v) = none := by
        rw [hba]; exact hb
      have hn1 : (ks.foldl (fun (acc : Option BackendArr) (k : Nat) =>
          acc.bind fun x => x.write (lo + k) v)) none = none :=
        List.foldl_option_bind_none ks _ (fun k => rfl)
      have hn2 : (ks.foldl (fun (acc : Option Backend) (k : Nat) =>
          acc.bind fun b => b.write (lo + k) v)) none = none :=
        List.foldl_option_bind_none ks _ (fun k => rfl)
      rw [hL, hR]
      simp only [hn1, hn2]
      rfl
    | some xa' =>
      have hb : xa.toBackend.write (lo + k) v = some xa'.toBackend := by
        have h2 := BackendArr.write_refines xa (lo + k) v
        rw [hw] at h2
        simpa using h2.symm
      have hL : ((some xa).bind fun x => x.write (lo + k) v) = some xa' := hw
      have hR : ((some ba).bind fun b => b.write (lo + k) v) = some xa'.toBackend := by
        rw [hba]; exact hb
      rw [hL, hR]
      exact ih xa' xa'.toBackend rfl

/-- The 64-byte two-range fill on byte-array backends. -/
def ba64 : Option BackendArr :=
  (baFill (BackendArr.empty 64) 0 32 1).bind fun x => baFill x 32 32 2

/-- The 64-byte two-range fill on the pure backend. -/
def pure64 : Option Backend :=
  (pureFill (Backend.empty 64) 0 32 1).bind fun b => pureFill b 32 32 2

/-- The pure run's snapshot is the reference bytes. -/
theorem pure64_snapshot :
    pure64.map Backend.buf
      = some (List.replicate 32 (1 : UInt8) ++ List.replicate 32 (2 : UInt8)) := by
  decide

/-- The byte-array run refines the pure run. -/
theorem ba64_refines : ba64.map BackendArr.toBackend = pure64 := by
  unfold ba64 pure64
  cases hF : baFill (BackendArr.empty 64) 0 32 1 with
  | none =>
    have hp : pureFill (Backend.empty 64) 0 32 1 = none := by
      have h := BackendArr.fills_refine (BackendArr.empty 64) 0 32 1
      rw [hF, BackendArr.empty_refines] at h
      simpa using h.symm
    rw [hp]
    simp
  | some x =>
    have hp : pureFill (Backend.empty 64) 0 32 1 = some x.toBackend := by
      have h := BackendArr.fills_refine (BackendArr.empty 64) 0 32 1
      rw [hF, BackendArr.empty_refines] at h
      simpa using h.symm
    rw [hp]
    exact BackendArr.fills_refine x 32 32 2

/-- The byte-array run's snapshot is the reference bytes. -/
theorem ba64_snapshot :
    (ba64.map BackendArr.toBackend).map Backend.buf
      = some (List.replicate 32 (1 : UInt8) ++ List.replicate 32 (2 : UInt8)) := by
  rw [ba64_refines]
  exact pure64_snapshot

end Cap
