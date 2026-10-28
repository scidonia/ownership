/-
A runtime model for the designated write, and the correspondence that makes its
exclusivity check return instead of aborting.

`Ownership.Heap` is a counted heap whose predicates the ownership judgment is
stated over. That heap is a *name* heap: `Ref` is a name, `exclusive?` is a
function of the stored count and persistence flag, and `dec` never frees. This
module adds a second, independent state — the shape the runtime actually
operates on — and relates the two by a structural correspondence. The point is
not a second copy of the same definitions: it is that the runtime's operations
are *defined on their own terms*, and the write's in-place disposition is then
derived from the model's invariant through the relation, rather than assumed by
the relation.

## The two states

| runtime (`Runtime.RHeap`) | model (`Ownership.Heap`) |
| --- | --- |
| `cells : Ref → Option RObj` | `cells : Ref → Option Obj` |
| `RObj.fields`, `RObj.rc`, `RObj.persistent` | `Obj.fields`, `Obj.rc`, `Obj.persistent` |
| `next : Ref` (the allocator's next name) | `next : Ref` |
| `RHeap.set` (replace one cell) | `Heap.set` |
| `RHeap.alloc` (fresh cell at count one) | `Heap.alloc` |
| `RHeap.dec` (one count decrement, no free) | `Heap.dec` |
| `RHeap.rc` (the count read off the cell) | `Heap.rc` |
| `RHeap.isExclusive` (`lean_is_exclusive`) | `Heap.exclusive?` |
| `RHeap.Exclusive` (the runtime predicate as a `Prop`) | `Heap.Exclusive` |
| `RHeap.WF` (the cursor and every name above it are vacant) | — |
| `RHeap.alloc?` (alloc at the cursor, `none` when it is occupied) | `Heap.alloc` |

The model keeps persistence in a separate flag and never lets a persistent
object be exclusive. The runtime encodes persistence in the count word (a
persistent object's count is zero, so it can never read as one), and a
thread-shared object's count is outside the single-threaded range. `isExclusive`
is the model of the runtime test for a single-threaded, non-scalar object: the
count is one and the object is not persistent. Scalar (tagged immediate) values
are not heap objects and never reach the check.

## The operations the emitted write performs

`checkExclusive` is `assertExclusiveArrayImpl`: it returns its argument
unchanged when the array is exclusive and takes the abort branch otherwise, with
no heap effect. `arraySet` is `lean_array_uset` (through
`lean_ensure_exclusive_array`): on an exclusive array it writes the selected
field and returns the same reference, leaving every count alone; on any other
array it allocates a fresh cell at count one with the updated fields and
consumes one count of the source, whose own fields are untouched. Allocation
goes through `alloc?`, which checks the cursor's cell and reports `none` when it
is occupied, so the copy path refuses rather than overwriting a live name. Both
dispositions are defined; nothing here chooses one. The field update is Lean's
`Array.set!`, which is neutral outside the array; the emitted primitive is
`lean_array_uset`, which does no bounds test of its own, so the in-bounds
premise the write theorems carry is the emitted bounds test's result (A4), and
not something `arraySet` establishes. `setAt` is the emitted composite — check,
then the write — and its non-value outcomes are the check's abort branch and a
refused allocation on the copy path.

## Well-formedness

`WF H` says every name at or above `RHeap.next` is vacant. It gives that the
cursor's own cell is vacant and that every live name is strictly below the
cursor, and it is preserved by a field update and by a count decrement at a live
name (`WF.set`, `WF.dec`), by allocation (`WF.alloc`), and by both array-write
dispositions (`arraySet_inPlace_wf`, `arraySet_copy_wf`, `WF.copy`). It therefore
makes the copy's fresh cell genuinely fresh: the source is live and hence below
the cursor, and the cell at the cursor is vacant. `alloc?` is guarded
independently of the invariant, so a heap with an occupied cursor makes the copy
path return `none`; `WF` is the condition under which the copy is a copy of a
vacant name. It is a premise of the copy-shape lemmas and is not needed by the
in-place result or by the abort-impossibility theorems.

## What is proved

Under `Corr H R` (refs, cells, counts, persistence, fields and the fresh-name
counter agree), the model's own `Heap.Exclusive H r`, and the runtime cell at `r`
the relation supplies:

* `checkExclusive` returns at `r` (`checkExclusive_returns`); the abort branch is
  not taken (`checkExclusive_no_abort`);
* `arraySet` takes the in-place disposition at the same reference and updates the
  selected field (`arraySet_inPlace`); replacing the fields leaves the count
  (`RHeap.rc_set_fields`), and the written field reads back as the replacement
  (`setAt_inPlace_field`);
* the composite writes in place (`setAt_inPlace`), never returns `none`, changes
  no count (`setAt_inPlace_matches_outcome`), and its poststate corresponds to
  the model's poststate and to `OwnershipLcnf.inPlaceOutcome` at the designated
  write — same target, same handle at both binders, no fault;
* from a concrete `EntryInv` at the checker's initializer context, the model's
  exclusivity is derived (`exclusive_of_entryInv`) and the runtime write is in
  place (`setAt_inPlace_of_entryInv`);
* the controls take the other branch: a count above one and a persistent cell
  both abort the check (`checkExclusive_of_not_exclusive` through
  `not_exclusive_of_rc_ne_one` / `not_exclusive_of_persistent`) and copy in
  `arraySet` under `WF` (`arraySet_of_not_exclusive`, `copy_*`); a heap whose
  cursor is occupied makes `alloc?` refuse, so `arraySet` reports no outcome
  instead of overwriting the live cell at the cursor.

## Residual trust

This is a model of runtime operations, not a refinement of the runtime.

* **Model fidelity (A6/A8).** `isExclusive`, `checkExclusive` and `arraySet` are
  written here from the documented meaning of `lean_is_exclusive` and
  `lean_array_uset`/`lean_ensure_exclusive_array`. No theorem relates them to
  the linked runtime, and none is derived from an executable: a divergence
  between this model and the C implementation would not be detected here.
* **A6.** The emitted check is taken to return its argument or abort, with no
  heap effect; that is the assumption the `Semantics` module names, restated
  over this state.
* **A8.** The emitted `Array.set!` is taken to have the two dispositions above;
  the element decrement `lean_array_uset` performs on the replaced slot is not
  modelled here (the designated write's replacement is a scalar, and the
  `Ownership` heap does not count elements either). `RHeap.dec` is the
  single-threaded count lowering and does not model `lean_dec`'s no-op on a
  persistent or thread-shared object: a persistent cell's count here is a model
  artifact, and the in-place result excludes persistent cells by construction.
* **Allocator freshness.** `WF` is a property of a starting heap, not something
  the model establishes for an arbitrary one, and the guard in `alloc?` is a
  refusal, not a model of the runtime allocator's ability to find fresh memory.
  A heap with an occupied cursor is outside the copy-shape lemmas; the real
  allocator's address selection is not modelled.
* **A10.** The replay identity — that the captured prefix is the backend input —
  is not a theorem here; this module says nothing about the emitted callee, the
  continuation, allocation failure, capacity, free/cascade, thread-shared count
  encodings, or address identity. No claim is made about a compiled C program,
  a linked executable, physical reference counts, or the identity of a `Ref`
  with a runtime address.

`RHeap.next` is the allocator's next *name*; `Corr.next` only says the two
states agree on it. Nothing identifies it with a runtime address.
-/
import OwnershipLcnf.Semantics

namespace OwnershipLcnf
namespace Runtime

open Ownership

/-! ## The runtime state and its operations -/

/-- A runtime object: its fields, its reference count and its persistence flag.
The model keeps persistence explicit; the runtime encodes it in the count. -/
structure RObj where
  fields : Array Val
  rc : Nat
  persistent : Bool := false
  deriving Repr

/-- The runtime object's element read at an index. -/
def RObj.field? (o : RObj) (i : Nat) : Option Val := o.fields[i]?

/-- The runtime heap: names to objects, plus the allocator's next name. -/
structure RHeap where
  cells : Ref → Option RObj
  next : Ref

namespace RHeap

def set (H : RHeap) (r : Ref) (o : RObj) : RHeap :=
  { H with cells := fun r' => if r' = r then some o else H.cells r' }

@[simp] theorem set_self (H : RHeap) (r : Ref) (o : RObj) :
    (H.set r o).cells r = some o := by
  simp [set]

@[simp] theorem set_other (H : RHeap) (r r' : Ref) (o : RObj) (h : r' ≠ r) :
    (H.set r o).cells r' = H.cells r' := by
  simp [set, h]

/-- The count read off the live cell, or zero when there is no cell. -/
def rc (H : RHeap) (r : Ref) : Nat := (H.cells r).map (·.rc) |>.getD 0

/-- The runtime's next name names a fresh cell at count one. -/
def alloc (H : RHeap) (fields : Array Val) : Ref × RHeap :=
  let r := H.next
  (r, { cells := fun r' => if r' = r then some ⟨fields, 1, false⟩ else H.cells r'
        next := r + 1 })

@[simp] theorem alloc_fst (H : RHeap) (fields : Array Val) : (H.alloc fields).1 = H.next := rfl

@[simp] theorem alloc_next (H : RHeap) (fields : Array Val) :
    (H.alloc fields).2.next = H.next + 1 := rfl

@[simp] theorem alloc_cells_self (H : RHeap) (fields : Array Val) :
    (H.alloc fields).2.cells H.next = some ⟨fields, 1, false⟩ := by
  simp [alloc]

theorem alloc_cells_other {H : RHeap} {fields : Array Val} {r' : Ref}
    (h : r' ≠ H.next) : (H.alloc fields).2.cells r' = H.cells r' := by
  simp [alloc, h]

/-- Heap well-formedness: every name at or above the allocator's cursor is
vacant. So the cursor's own cell is vacant, a live cell is strictly below the
cursor, and allocation at the cursor cannot overwrite a live object. The
property survives allocation, a field update or count decrement at a live cell,
and the in-place write. -/
def WF (H : RHeap) : Prop := ∀ r, H.next ≤ r → H.cells r = none

/-- Allocation at the cursor, refused when the cursor's cell is occupied. A
well-formed heap's cursor is vacant, so it allocates there; a dirty cursor
leaves the heap unchanged and reports no result. -/
def alloc? (H : RHeap) (fields : Array Val) : Option (Ref × RHeap) :=
  if H.cells H.next = none then some (H.alloc fields) else none

/-- The single count decrement of the runtime's `dec`. No free and no cascade:
the count is lowered, the cell stays. -/
def dec (H : RHeap) (r : Ref) (n : Nat) : RHeap :=
  match H.cells r with
  | none => H
  | some o => H.set r { o with rc := o.rc - n }

theorem dec_cells_self {H : RHeap} {r : Ref} {n : Nat} {o : RObj}
    (h : H.cells r = some o) :
    (H.dec r n).cells r = some { o with rc := o.rc - n } := by
  simp [dec, h, set]

theorem dec_next (H : RHeap) (r : Ref) (n : Nat) : (H.dec r n).next = H.next := by
  unfold RHeap.dec
  split <;> simp [RHeap.set]

namespace WF

theorem cursor_vacant {H : RHeap} (h : H.WF) : H.cells H.next = none :=
  h H.next (Nat.le_refl _)

/-- A live name is strictly below the cursor. -/
theorem lt_next {H : RHeap} (h : H.WF) {r : Ref} {o : RObj}
    (hc : H.cells r = some o) : r < H.next := by
  by_cases hlt : r < H.next
  · exact hlt
  · exfalso
    have hge : H.next ≤ r := Nat.le_of_not_lt hlt
    rw [h r hge] at hc
    simp at hc

theorem ne_next {H : RHeap} (h : H.WF) {r : Ref} {o : RObj}
    (hc : H.cells r = some o) : r ≠ H.next := by
  intro heq
  exact Nat.lt_irrefl H.next (heq ▸ h.lt_next hc)

theorem set {H : RHeap} (h : H.WF) {r : Ref} {o : RObj} (hlt : r < H.next) :
    (H.set r o).WF := by
  intro r' hr'
  have hr'' : H.next ≤ r' := hr'
  have hne : r' ≠ r := by
    intro heq
    have hle : H.next ≤ r := heq ▸ hr''
    exact Nat.lt_irrefl H.next (Nat.lt_of_le_of_lt hle hlt)
  simp [RHeap.set, hne, h r' hr'']

theorem alloc? {H : RHeap} (h : H.WF) (fields : Array Val) :
    H.alloc? fields = some (H.alloc fields) := by
  simp [RHeap.alloc?, h.cursor_vacant]

theorem alloc {H : RHeap} (h : H.WF) (fields : Array Val) :
    (H.alloc fields).2.WF := by
  intro r' hr'
  have hr'' : H.next + 1 ≤ r' := hr'
  have hne : r' ≠ H.next := by
    intro heq
    exact Nat.not_succ_le_self H.next (heq ▸ hr'')
  have hge : H.next ≤ r' := Nat.le_of_succ_le hr''
  simp [RHeap.alloc, hne, h r' hge]

theorem dec {H : RHeap} (h : H.WF) {r : Ref} {n : Nat} (hlt : r < H.next) :
    (H.dec r n).WF := by
  intro r' hr'
  have hr'' : H.next ≤ r' := by simpa [RHeap.dec_next] using hr'
  have hne : r' ≠ r := by
    intro heq
    have hle : H.next ≤ r := heq ▸ hr''
    exact Nat.lt_irrefl H.next (Nat.lt_of_le_of_lt hle hlt)
  unfold RHeap.dec
  cases hcell : H.cells r with
  | none => simpa [hcell] using h r' hr''
  | some o => simp [RHeap.set, hne, h r' hr'']

/-- The copy disposition's heap is well formed: allocation at the cursor and the
source decrement both preserve the invariant. -/
theorem copy {H : RHeap} (h : H.WF) {r : Ref} {o : RObj} {i : Nat} {v : Val}
    (hcell : H.cells r = some o) :
    ((H.alloc (o.fields.set! i v)).2.dec r 1).WF := by
  have hlt : r < H.next := h.lt_next hcell
  exact (h.alloc _).dec (by simpa using Nat.lt_succ_of_lt hlt)

end WF

/-- The runtime's exclusivity test: a live cell counted once that is not
persistent. This is `lean_is_exclusive` on the facts the model represents. -/
def isExclusive (H : RHeap) (r : Ref) : Bool :=
  match H.cells r with
  | some o => o.rc == 1 && !o.persistent
  | none => false

/-- The runtime's exclusivity predicate as a proposition. -/
def Exclusive (H : RHeap) (r : Ref) : Prop :=
  ∃ o, H.cells r = some o ∧ o.rc = 1 ∧ o.persistent = false

theorem isExclusive_eq_true {H : RHeap} {r : Ref} :
    H.isExclusive r = true ↔ H.Exclusive r := by
  unfold RHeap.isExclusive RHeap.Exclusive
  cases h : H.cells r with
  | none => simp
  | some o =>
    constructor
    · intro hh
      simp at hh
      exact ⟨o, rfl, hh.1, by simpa using hh.2⟩
    · rintro ⟨o', he, hrc, hp⟩
      simp at he
      subst he
      simp [hrc, hp]

theorem isExclusive_eq_false {H : RHeap} {r : Ref} :
    H.isExclusive r = false ↔ ¬ H.Exclusive r := by
  constructor
  · intro h he
    have := (isExclusive_eq_true (H := H) (r := r)).mpr he
    rw [h] at this
    exact Bool.false_ne_true this
  · intro h
    cases hb : H.isExclusive r with
    | false => rfl
    | true => exact absurd ((isExclusive_eq_true (H := H) (r := r)).mp hb) h

/-- Setting a cell changes the count only at that cell, and there to the new
object's count. -/
theorem rc_set (H : RHeap) (r : Ref) (o : RObj) (r' : Ref) :
    (H.set r o).rc r' = if r' = r then o.rc else H.rc r' := by
  unfold RHeap.rc RHeap.set
  by_cases h : r' = r
  · subst h; simp
  · simp [h]

/-- Replacing a cell's fields changes no count: the new object is the old one
with different fields, so it keeps the old count. -/
theorem rc_set_fields {H : RHeap} {r : Ref} {o : RObj} (hcell : H.cells r = some o)
    (i : Nat) (v : Val) (r' : Ref) :
    (H.set r { o with fields := o.fields.set! i v }).rc r' = H.rc r' := by
  rw [rc_set]
  by_cases h : r' = r
  · subst h
    simp [RHeap.rc, hcell]
  · simp [h]

end RHeap

/-! ## The check and the array write -/

/-- The check's two outcomes. `ok` is the same reference it was handed; `abort`
is the branch the emitted assertion faults on. -/
inductive CheckOutcome where
  | ok (r : Ref)
  | abort (r : Ref)
  deriving DecidableEq, Repr

/-- `assertExclusiveArrayImpl`: return the argument or take the abort branch. -/
def checkExclusive (H : RHeap) (r : Ref) : CheckOutcome :=
  if H.isExclusive r then .ok r else .abort r

/-- The array write's dispositions: in place at the same reference, or a fresh
cell with the replacement and one count consumed from the source. -/
inductive SetOutcome where
  | inPlace (H : RHeap) (r : Ref)
  | copied (H : RHeap) (r : Ref)

/-- `lean_array_uset` through `lean_ensure_exclusive_array`: the exclusive
branch writes the field in place; the other branch copies. Both are defined. -/
def arraySet (H : RHeap) (r : Ref) (i : Nat) (v : Val) : Option SetOutcome :=
  match H.cells r with
  | none => none
  | some o =>
      if H.isExclusive r then
        some (.inPlace (H.set r { o with fields := o.fields.set! i v }) r)
      else
        match H.alloc? (o.fields.set! i v) with
        | some (r', H1) => some (.copied (H1.dec r 1) r')
        | none => none

/-- The emitted composite: check, then the write. `none` is the check's abort
branch, or a refused allocation on the copy path. -/
def setAt (H : RHeap) (r : Ref) (i : Nat) (v : Val) : Option SetOutcome :=
  match checkExclusive H r with
  | .ok a => arraySet H a i v
  | .abort _ => none

/-! ## The check and write on their own terms -/

theorem checkExclusive_of_exclusive {H : RHeap} {r : Ref} (h : H.Exclusive r) :
    checkExclusive H r = .ok r := by
  simp [checkExclusive, (RHeap.isExclusive_eq_true).mpr h]

theorem checkExclusive_of_not_exclusive {H : RHeap} {r : Ref} (h : ¬ H.Exclusive r) :
    checkExclusive H r = .abort r := by
  simp [checkExclusive, (RHeap.isExclusive_eq_false).mpr h]

theorem arraySet_of_exclusive {H : RHeap} {r : Ref} {i : Nat} {v : Val} {o : RObj}
    (hcell : H.cells r = some o) (h : H.Exclusive r) :
    arraySet H r i v = some (.inPlace (H.set r { o with fields := o.fields.set! i v }) r) := by
  simp [arraySet, hcell, (RHeap.isExclusive_eq_true).mpr h]

theorem arraySet_of_not_exclusive {H : RHeap} {r : Ref} {i : Nat} {v : Val} {o : RObj}
    (hcell : H.cells r = some o) (h : ¬ H.Exclusive r) (hwf : H.WF) :
    arraySet H r i v =
      some (.copied ((H.alloc (o.fields.set! i v)).2.dec r 1)
                    (H.alloc (o.fields.set! i v)).1) := by
  have hb : H.isExclusive r = false := (RHeap.isExclusive_eq_false).mpr h
  simp only [arraySet, hcell, hb, Bool.false_eq_true, ite_false]
  rw [RHeap.WF.alloc? (fields := o.fields.set! i v) hwf]

/-- A count other than one is not exclusive. -/
theorem not_exclusive_of_rc_ne_one {H : RHeap} {r : Ref} {o : RObj}
    (hcell : H.cells r = some o) (hrc : o.rc ≠ 1) : ¬ H.Exclusive r := by
  rintro ⟨o', ho', h1, _⟩
  rw [hcell] at ho'
  injection ho' with heq
  subst heq
  exact hrc h1

/-- A persistent cell is not exclusive, whatever its count. -/
theorem not_exclusive_of_persistent {H : RHeap} {r : Ref} {o : RObj}
    (hcell : H.cells r = some o) (hp : o.persistent = true) : ¬ H.Exclusive r := by
  rintro ⟨o', ho', _, hp'⟩
  rw [hcell] at ho'
  injection ho' with heq
  subst heq
  rw [hp] at hp'
  exact Bool.false_ne_true hp'.symm

/-! ## The copy disposition's concrete shape

The facts below take heap well-formedness: `WF` makes the allocator's cursor
vacant, so the fresh cell the copy writes is genuinely fresh and the source
reference is distinct from it. Without `WF` the cursor's cell can be occupied,
and the copy path refuses through `alloc?` rather than overwriting it. The
in-place result does not need this invariant. -/

theorem copy_fresh_cell {H : RHeap} {r : Ref} {o : RObj} {i : Nat} {v : Val}
    (hcell : H.cells r = some o) (hwf : H.WF) :
    ((H.alloc (o.fields.set! i v)).2.dec r 1).cells H.next =
      some ⟨o.fields.set! i v, 1, false⟩ := by
  have hne : r ≠ H.next := hwf.ne_next hcell
  unfold RHeap.dec
  split
  · simp [RHeap.alloc]
  · rw [RHeap.set_other _ _ _ _ (fun h => hne h.symm)]
    simp [RHeap.alloc]

theorem copy_source_cell {H : RHeap} {r : Ref} {o : RObj} {i : Nat} {v : Val}
    (hcell : H.cells r = some o) (hwf : H.WF) :
    ((H.alloc (o.fields.set! i v)).2.dec r 1).cells r =
      some { o with rc := o.rc - 1 } := by
  have hne : r ≠ H.next := hwf.ne_next hcell
  have h1 : (H.alloc (o.fields.set! i v)).2.cells r = some o := by
    rw [RHeap.alloc_cells_other hne, hcell]
  exact RHeap.dec_cells_self h1

/-! ## The correspondence -/

/-- Two objects correspond when their fields, counts and persistence flags agree.
The direction of the equalities is the runtime's on the left, the model's on the
right. -/
structure ObjCorr (o : Ownership.Obj) (o' : RObj) : Prop where
  fields : o'.fields = o.fields
  rc : o'.rc = o.rc
  persistent : o'.persistent = o.persistent

/-- The heap correspondence: the fresh-name counters agree, each name is live in
one state exactly when it is live in the other, and a name that is live in both
has corresponding objects. Only these structural facts — no predicate of the
model, and in particular no exclusivity fact, is part of the relation. -/
structure Corr (H : Ownership.Heap) (R : RHeap) : Prop where
  next : R.next = H.next
  cells : ∀ r, H.cells r = none ↔ R.cells r = none
  obj : ∀ r o o', H.cells r = some o → R.cells r = some o' → ObjCorr o o'

namespace Corr

variable {H : Ownership.Heap} {R : RHeap}

/-- A name is live in the runtime state exactly when it is live in the model. -/
theorem some_iff (hc : Corr H R) (r : Ref) :
    (∃ o, H.cells r = some o) ↔ ∃ o', R.cells r = some o' := by
  constructor
  · rintro ⟨o, ho⟩
    cases hr : R.cells r with
    | none => exact absurd ((hc.cells r).mpr hr) (by simp [ho])
    | some o' => exact ⟨o', rfl⟩
  · rintro ⟨o', ho'⟩
    cases hh : H.cells r with
    | none => exact absurd ((hc.cells r).mp hh) (by simp [ho'])
    | some o => exact ⟨o, rfl⟩

theorem rc_eq (hc : Corr H R) (r : Ref) : R.rc r = H.rc r := by
  unfold RHeap.rc Ownership.Heap.rc
  cases hh : H.cells r with
  | none =>
      have hr : R.cells r = none := (hc.cells r).mp hh
      simp [hr]
  | some o =>
      obtain ⟨o', ho'⟩ := (some_iff hc r).mp ⟨o, hh⟩
      have hcorr := hc.obj r o o' hh ho'
      simp [ho', hcorr.rc]

/-- The runtime test answers exactly as the model's test does. -/
theorem isExclusive_eq (hc : Corr H R) (r : Ref) : R.isExclusive r = H.exclusive? r := by
  unfold RHeap.isExclusive Ownership.Heap.exclusive?
  cases hh : H.cells r with
  | none =>
      have hr : R.cells r = none := (hc.cells r).mp hh
      simp [hr]
  | some o =>
      obtain ⟨o', ho'⟩ := (some_iff hc r).mp ⟨o, hh⟩
      have hcorr := hc.obj r o o' hh ho'
      simp [ho', hcorr.rc, hcorr.persistent]

/-- The model's exclusivity makes the runtime test true. -/
theorem isExclusive_true (hc : Corr H R) {r : Ref}
    (hex : Ownership.Heap.Exclusive H r) : R.isExclusive r = true := by
  rw [isExclusive_eq hc, (Ownership.Heap.exclusive?_eq_true).mpr hex]

/-- The model's exclusivity is the runtime predicate. -/
theorem exclusive (hc : Corr H R) {r : Ref} (hex : Ownership.Heap.Exclusive H r) :
    R.Exclusive r :=
  (RHeap.isExclusive_eq_true).mp (isExclusive_true hc hex)

theorem set (hc : Corr H R) {r : Ref} {o : Ownership.Obj} {o' : RObj}
    (hcorr : ObjCorr o o') : Corr (H.set r o) (R.set r o') := by
  refine ⟨hc.next, ?_, ?_⟩
  · intro r'
    by_cases h : r' = r
    · subst h
      simp [Ownership.Heap.set, RHeap.set]
    · simpa [Ownership.Heap.set, RHeap.set, h] using hc.cells r'
  · intro r' o1 o2 h1 h2
    by_cases h : r' = r
    · subst h
      simp [Ownership.Heap.set, RHeap.set] at h1 h2
      cases h1
      cases h2
      exact hcorr
    · exact hc.obj r' o1 o2 (by simpa [Ownership.Heap.set, h] using h1)
        (by simpa [RHeap.set, h] using h2)

theorem alloc (hc : Corr H R) (fields : Array Val) :
    Corr (H.alloc fields).2 (R.alloc fields).2 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Ownership.Heap.alloc, RHeap.alloc, hc.next]
  · intro r'
    by_cases h : r' = R.next
    · subst h
      simp [Ownership.Heap.alloc, RHeap.alloc, hc.next]
    · have hH : r' ≠ H.next := fun hh => h (hh.trans hc.next.symm)
      simpa [Ownership.Heap.alloc, RHeap.alloc, h, hH] using hc.cells r'
  · intro r' o1 o2 h1 h2
    by_cases h : r' = R.next
    · subst h
      simp [Ownership.Heap.alloc, RHeap.alloc, hc.next] at h1 h2
      cases h1
      cases h2
      exact ⟨rfl, rfl, rfl⟩
    · have hH : r' ≠ H.next := fun hh => h (hh.trans hc.next.symm)
      exact hc.obj r' o1 o2 (by simpa [Ownership.Heap.alloc, hH] using h1)
        (by simpa [RHeap.alloc, h] using h2)

theorem dec (hc : Corr H R) (r : Ref) (n : Nat) : Corr (H.dec r n) (R.dec r n) := by
  unfold Ownership.Heap.dec RHeap.dec
  cases hh : H.cells r with
  | none =>
      have hr : R.cells r = none := (hc.cells r).mp hh
      simp only [hr]
      exact hc
  | some o =>
      obtain ⟨o', ho'⟩ := (some_iff hc r).mp ⟨o, hh⟩
      have hcorr := hc.obj r o o' hh ho'
      simp only [ho']
      exact set hc ⟨hcorr.fields, by rw [hcorr.rc], hcorr.persistent⟩

end Corr

/-! ## The write under the correspondence -/

theorem checkExclusive_returns {H : Ownership.Heap} {R : RHeap} {r : Ref}
    (hc : Corr H R) (hex : Ownership.Heap.Exclusive H r) :
    checkExclusive R r = .ok r :=
  checkExclusive_of_exclusive (Corr.exclusive hc hex)

/-- Under the correspondence and the model's exclusivity the check cannot take
the abort branch at `r`. -/
theorem checkExclusive_no_abort {H : Ownership.Heap} {R : RHeap} {r : Ref}
    (hc : Corr H R) (hex : Ownership.Heap.Exclusive H r) (r' : Ref) :
    checkExclusive R r ≠ .abort r' := by
  rw [checkExclusive_returns hc hex]
  simp

/-- Under the correspondence and the model's exclusivity the write takes the
in-place disposition at the same reference. -/
theorem arraySet_inPlace {H : Ownership.Heap} {R : RHeap} {r : Ref} {i : Nat} {v : Val}
    {o' : RObj}
    (hc : Corr H R) (ho' : R.cells r = some o')
    (hex : Ownership.Heap.Exclusive H r) :
    arraySet R r i v = some (.inPlace (R.set r { o' with fields := o'.fields.set! i v }) r) :=
  arraySet_of_exclusive ho' (Corr.exclusive hc hex)

/-- The in-place disposition preserves well-formedness; the update is at a live
cell, below the cursor, so it cannot touch the cursor's vacant name. -/
theorem arraySet_inPlace_wf {H : RHeap} {r : Ref} {i : Nat} {v : Val} {o : RObj}
    (hcell : H.cells r = some o) (hwf : H.WF) :
    (H.set r { o with fields := o.fields.set! i v }).WF :=
  hwf.set (hwf.lt_next hcell)

/-- The copy disposition's heap is well formed under the invariant. -/
theorem arraySet_copy_wf {H : RHeap} {r : Ref} {i : Nat} {v : Val} {o : RObj}
    (hcell : H.cells r = some o) (hwf : H.WF) :
    ((H.alloc (o.fields.set! i v)).2.dec r 1).WF :=
  hwf.copy hcell

/-- The emitted composite writes in place, at the same reference. -/
theorem setAt_inPlace {H : Ownership.Heap} {R : RHeap} {r : Ref} {i : Nat} {v : Val}
    {o' : RObj}
    (hc : Corr H R) (ho' : R.cells r = some o')
    (hex : Ownership.Heap.Exclusive H r) :
    setAt R r i v = some (.inPlace (R.set r { o' with fields := o'.fields.set! i v }) r) := by
  simp [setAt, checkExclusive_returns hc hex, arraySet_inPlace hc ho' hex]

/-- The composite never reports the abort branch. -/
theorem setAt_ne_none {H : Ownership.Heap} {R : RHeap} {r : Ref} {i : Nat} {v : Val}
    {o' : RObj}
    (hc : Corr H R) (ho' : R.cells r = some o')
    (hex : Ownership.Heap.Exclusive H r) :
    setAt R r i v ≠ none := by
  rw [setAt_inPlace hc ho' hex]
  simp

/-- The runtime poststate corresponds to the model's poststate at the designated
write. The replacement is a scalar, which is the value the emitted write boxes
(A7) and the value `inPlaceOutcome` stores. -/
theorem setAt_poststate_corr {H : Ownership.Heap} {R : RHeap} {r : Ref} {i : Nat}
    {vn : Nat} {o : Ownership.Obj} {o' : RObj}
    (hc : Corr H R) (hcell : H.cells r = some o) (ho' : R.cells r = some o') :
    Corr (inPlaceOutcome r i vn o H).heap
      (R.set r { o' with fields := o'.fields.set! i (.scalar vn) }) := by
  have hcorr := hc.obj r o o' hcell ho'
  have hf : (o'.fields.set! i (.scalar vn)) = (o.fields.set! i (.scalar vn)) := by
    rw [hcorr.fields]
  exact Corr.set hc ⟨hf, hcorr.rc, hcorr.persistent⟩

/-- The runtime's outcome at the designated write is the model's
`inPlaceOutcome`: the same target, the same reference at the write's result
binder and at the returned handle, the in-place disposition and no fault. -/
theorem setAt_inPlace_matches_outcome {H : Ownership.Heap} {R : RHeap} {r : Ref}
    {i : Nat} {vn : Nat} {o : Ownership.Obj} {o' : RObj}
    (hc : Corr H R) (hcell : H.cells r = some o) (ho' : R.cells r = some o')
    (hex : Ownership.Heap.Exclusive H r) :
    ∃ H', setAt R r i (.scalar vn) = some (.inPlace H' r) ∧
      (∀ r', H'.rc r' = R.rc r') ∧
      Corr (inPlaceOutcome r i vn o H).heap H' ∧
      (inPlaceOutcome r i vn o H).target = some r ∧
      (inPlaceOutcome r i vn o H).setResult = some (.ref r) ∧
      (inPlaceOutcome r i vn o H).result = some (.ref r) ∧
      (inPlaceOutcome r i vn o H).inPlace = true ∧
      (inPlaceOutcome r i vn o H).fault = none :=
  ⟨_, setAt_inPlace hc ho' hex, RHeap.rc_set_fields ho' i (.scalar vn),
    setAt_poststate_corr hc hcell ho', rfl, rfl, rfl, rfl, rfl⟩

/-- The in-place write's field at the written index is the replacement. -/
theorem set!_getElem? {xs : Array Val} {i : Nat} {v : Val} (hin : i < xs.size) :
    (xs.set! i v)[i]? = some v := by
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  simp [hin]

/-- The field read at the written index after the write. `RObj.field?` is the
runtime object's own element read. -/
theorem setAt_inPlace_field {H : Ownership.Heap} {R : RHeap} {r : Ref} {i : Nat} {v : Val}
    {o' : RObj}
    (hc : Corr H R) (ho' : R.cells r = some o')
    (hex : Ownership.Heap.Exclusive H r) (hin : i < o'.fields.size) :
    ∃ H', setAt R r i v = some (.inPlace H' r) ∧
      (H'.cells r).bind (fun o => o.field? i) = some v := by
  refine ⟨_, setAt_inPlace hc ho' hex, ?_⟩
  simp only [RHeap.set_self, Option.bind_some, RObj.field?]
  exact set!_getElem? hin

/-! ## From the entry invariant -/

/-- The model's exclusivity at the checker's initializer root, from a concrete
`EntryInv`: with `multOf 0 = 1`, `Inv.rc_eq` makes the root's count one and
`Inv.nonPersistent` clears the persistence flag. -/
theorem exclusive_of_entryInv {H : Ownership.Heap} {env : Ownership.Env}
    {root : Ref} {client : List Ref}
    (hEntry : Ownership.Entry.EntryInv H env (Ownership.Runner.initCtx root) root client) :
    Ownership.Heap.Exclusive H root := by
  have hi : Ownership.Inv H env (Ownership.Runner.initCtx root) := hEntry.toInv
  obtain ⟨r, hr, hmul⟩ :=
    Ownership.Ctx.multOf_eq_one (Ownership.Runner.initCtx_multOf_zero root)
  have hrroot : r = root := by
    have h : (Ownership.Runner.initCtx root).refOf 0 = some r := hr
    rw [Ownership.Runner.initCtx_refOf_zero] at h
    exact (Option.some.inj h).symm
  have hmul' : (Ownership.Runner.initCtx root).mult root = 1 := by
    simpa [hrroot] using hmul
  exact hi.exclusive hmul'

/-- The runtime write at the initializer root, from a concrete `EntryInv`, the
correspondence and an in-bounds index. The model's poststate and the runtime
poststate correspond, the target is the root, and the written field reads back
as the replacement. -/
theorem setAt_inPlace_of_entryInv {H : Ownership.Heap} {R : RHeap} {env : Ownership.Env}
    {root : Ref} {client : List Ref} {i : Nat} {vn : Nat} {o : Ownership.Obj} {o' : RObj}
    (hEntry : Ownership.Entry.EntryInv H env (Ownership.Runner.initCtx root) root client)
    (hc : Corr H R) (hcell : H.cells root = some o) (ho' : R.cells root = some o')
    (hin : i < o.fields.size) :
    ∃ H', setAt R root i (.scalar vn) = some (.inPlace H' root) ∧
      Corr (inPlaceOutcome root i vn o H).heap H' ∧
      (inPlaceOutcome root i vn o H).target = some root ∧
      (H'.cells root).bind (fun o => o.field? i) = some (.scalar vn) := by
  have hex : Ownership.Heap.Exclusive H root := exclusive_of_entryInv hEntry
  have hcorr := hc.obj root o o' hcell ho'
  have hin' : i < o'.fields.size := by simpa [hcorr.fields] using hin
  have hset :
      setAt R root i (.scalar vn) =
        some (.inPlace (R.set root { o' with fields := o'.fields.set! i (.scalar vn) }) root) :=
    setAt_inPlace hc ho' hex
  have hfield :
      ((R.set root { o' with fields := o'.fields.set! i (.scalar vn) }).cells root).bind
        (fun o => o.field? i) = some (.scalar vn) := by
    simp only [RHeap.set_self, Option.bind_some, RObj.field?]
    exact set!_getElem? hin'
  exact ⟨_, hset, setAt_poststate_corr hc hcell ho', rfl, hfield⟩

end Runtime
end OwnershipLcnf
