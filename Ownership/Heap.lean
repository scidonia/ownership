/-
A counted heap for the ownership core.

This is the fragment's heap, not Lean's object graph. A location is a `Ref`
(a name); a cell carries its fields, a count and a persistence flag. The
operations are the ones the ownership judgment needs: allocation, increment,
decrement, field read/write, and the exclusivity test. The runtime bridge
(`RefCount` / `RCHeap` in the sibling and the in-place harness) is a separate
link, named in `PLAN.md`; nothing here says a compiled C program mutates memory.

The heap is a function from names to cells plus a fresh-name counter, so
allocation freshness is a theorem rather than an assumption. The `dec` here is
the count-lowering operation without the free/cascade; the arm that frees is
outside this fragment's theorem, because the designated writes in A1 run at a
count of one on a live cell, and the judgment never needs a cell's death to
prove a write's exclusivity. The sibling's `CHeap` supplies the cascade for the
runtime refinement.
-/
import Std

namespace Ownership

abbrev Ref := Nat

inductive Val where
  | ref (r : Ref)
  | scalar (n : Nat)
  | erased
  deriving DecidableEq, Repr

structure Obj where
  fields : Array Val
  rc : Nat
  persistent : Bool := false
  deriving Repr

structure Heap where
  cells : Ref → Option Obj
  next : Ref

namespace Heap

def get? (H : Heap) (r : Ref) : Option Obj := H.cells r

def set (H : Heap) (r : Ref) (o : Obj) : Heap :=
  { H with cells := fun r' => if r' = r then some o else H.cells r' }

def erase (H : Heap) (r : Ref) : Heap :=
  { H with cells := fun r' => if r' = r then none else H.cells r' }

@[simp] theorem set_self (H : Heap) (r : Ref) (o : Obj) : (H.set r o).cells r = some o := by
  simp [set]

@[simp] theorem set_other (H : Heap) (r r' : Ref) (o : Obj) (h : r' ≠ r) :
    (H.set r o).cells r' = H.cells r' := by
  simp [set, h]

@[simp] theorem erase_self (H : Heap) (r : Ref) : (H.erase r).cells r = none := by
  simp [erase]

@[simp] theorem erase_other (H : Heap) (r r' : Ref) (h : r' ≠ r) :
    (H.erase r).cells r' = H.cells r' := by
  simp [erase, h]

def rc (H : Heap) (r : Ref) : Nat := (H.cells r).map (·.rc) |>.getD 0

def isPersistent (H : Heap) (r : Ref) : Bool :=
  (H.cells r).map (·.persistent) |>.getD false

def Exclusive (H : Heap) (r : Ref) : Prop :=
  ∃ o, H.cells r = some o ∧ o.rc = 1 ∧ o.persistent = false

def exclusive? (H : Heap) (r : Ref) : Bool :=
  match H.cells r with
  | some o => o.rc == 1 && !o.persistent
  | none => false

theorem exclusive?_eq_true {H : Heap} {r : Ref} :
    exclusive? H r = true ↔ Exclusive H r := by
  unfold exclusive? Exclusive
  cases h : H.cells r with
  | none => simp [h]
  | some o =>
    constructor
    · intro hh
      simp [h] at hh
      exact ⟨o, rfl, hh.1, by simpa using hh.2⟩
    · rintro ⟨o', he, hrc, hp⟩
      simp [h] at he
      subst he
      simp [h, hrc, hp]

theorem exclusive?_eq_false {H : Heap} {r : Ref} :
    exclusive? H r = false ↔ ¬ Exclusive H r := by
  constructor
  · intro h he
    have := (exclusive?_eq_true (H := H) (r := r)).mpr he
    rw [h] at this
    exact Bool.false_ne_true this
  · intro h
    cases hb : exclusive? H r with
    | false => rfl
    | true => exact absurd ((exclusive?_eq_true (H := H) (r := r)).mp hb) h

theorem exclusive_rc {H : Heap} {r : Ref} (h : Exclusive H r) : H.rc r = 1 := by
  rcases h with ⟨o, ho, hrc, _⟩
  simp [rc, ho, hrc]

theorem exclusive_not_persistent {H : Heap} {r : Ref} (h : Exclusive H r) :
    H.isPersistent r = false := by
  rcases h with ⟨o, ho, _, hp⟩
  simp [isPersistent, ho, hp]

def empty : Heap := { cells := fun _ => none, next := 0 }

@[simp] theorem empty_cells (r : Ref) : empty.cells r = none := rfl

def alloc (H : Heap) (fields : Array Val) : Ref × Heap :=
  let r := H.next
  let cells : Ref → Option Obj :=
    fun r' => if r' = r then some ⟨fields, 1, false⟩ else H.cells r'
  (r, { cells := cells, next := r + 1 })

@[simp] theorem alloc_fst (H : Heap) (fields : Array Val) : (H.alloc fields).1 = H.next := rfl

@[simp] theorem alloc_cells_self (H : Heap) (fields : Array Val) :
    (H.alloc fields).2.cells H.next = some ⟨fields, 1, false⟩ := by
  simp [alloc]

theorem alloc_cells_other {H : Heap} {fields : Array Val} {r' : Ref}
    (h : r' ≠ H.next) : (H.alloc fields).2.cells r' = H.cells r' := by
  simp [alloc, h]

theorem alloc_exclusive (H : Heap) (fields : Array Val) :
    Exclusive (H.alloc fields).2 (H.alloc fields).1 := by
  refine ⟨⟨fields, 1, false⟩, ?_, rfl, rfl⟩
  exact alloc_cells_self H fields

def inc (H : Heap) (r : Ref) (n : Nat) : Heap :=
  match H.cells r with
  | none => H
  | some o => H.set r { o with rc := o.rc + n }

/-- A saturating count decrement. This fragment does not free: the cell stays
with a count of `rc - n` (truncated at zero). The sibling's `CHeap` models the
free/cascade for the runtime refinement; the write theorem only needs the
count, and keeping the cell makes the borrow-validity invariant simple. -/
def dec (H : Heap) (r : Ref) (n : Nat) : Heap :=
  match H.cells r with
  | none => H
  | some o => H.set r { o with rc := o.rc - n }

theorem inc_rc {H : Heap} {r : Ref} {n : Nat} {o : Obj} (h : H.cells r = some o) :
    (H.inc r n).rc r = o.rc + n := by
  simp [inc, h, rc]

theorem dec_other {H : Heap} {r r' : Ref} {n : Nat} (h : r' ≠ r) :
    (H.dec r n).cells r' = H.cells r' := by
  cases hcell : H.cells r with
  | none => simp [dec, hcell]
  | some o => simp [dec, hcell, set, h]

theorem inc_other {H : Heap} {r r' : Ref} {n : Nat} (h : r' ≠ r) :
    (H.inc r n).cells r' = H.cells r' := by
  unfold inc
  split
  · rfl
  · exact set_other _ _ _ _ h

theorem dec_exclusive_other {H : Heap} {r r' : Ref} {n : Nat} (h : r' ≠ r)
    (he : Exclusive H r') : Exclusive (H.dec r n) r' := by
  rcases he with ⟨o, ho, hrc, hp⟩
  unfold dec
  split
  · exact ⟨o, ho, hrc, hp⟩
  · unfold Exclusive
    rw [set_other _ _ _ _ h]
    exact ⟨o, ho, hrc, hp⟩

theorem rc_inc_self {H : Heap} {r : Ref} {n : Nat} {o : Obj}
    (h : H.cells r = some o) : (H.inc r n).rc r = H.rc r + n := by
  simp [inc, rc, h, set]

theorem rc_inc_other {H : Heap} {r r' : Ref} {n : Nat} (h : r' ≠ r) :
    (H.inc r n).rc r' = H.rc r' := by
  cases hcell : H.cells r with
  | none => simp [inc, rc, hcell]
  | some o => simp [inc, rc, hcell, set, h]

theorem rc_set_self (H : Heap) (r : Ref) (o : Obj) : (H.set r o).rc r = o.rc := by
  simp [rc, set]

theorem rc_set_other {H : Heap} {r r' : Ref} {o : Obj} (h : r' ≠ r) :
    (H.set r o).rc r' = H.rc r' := by
  simp [rc, set, h]

theorem rc_dec_self (H : Heap) (r : Ref) (n : Nat) :
    (H.dec r n).rc r = H.rc r - n := by
  cases hcell : H.cells r with
  | none => simp [dec, rc, hcell]
  | some o => simp [dec, rc, hcell, set]

theorem rc_dec_other {H : Heap} {r r' : Ref} {n : Nat} (h : r' ≠ r) :
    (H.dec r n).rc r' = H.rc r' := by
  cases hcell : H.cells r with
  | none => simp [dec, rc, hcell]
  | some o => simp [dec, rc, hcell, set, h]

end Heap

end Ownership
