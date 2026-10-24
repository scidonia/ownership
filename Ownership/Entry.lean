/-
The entry invariant, with the two nested-state countermodels from the review:
a repeated child and a client-retained child.

`EntryInv` extends the handle/count invariant with
* `UniqueTree` — every cell in the mutable footprint has count one;
* `ClientSeparated` — no client-reachable reference is in the footprint.

The unique tree is a sufficient condition, not the only admissible one; the
point here is that the initializer must establish it (or a protocol that proves
the actual write target exclusive). The fresh-array initializer does; a state
whose two slots name the same child does not, and a client handle into the
footprint violates separation.
-/
import Ownership.Runner

namespace Ownership
namespace Entry

open Ownership.Runner

/-- The references a value names. -/
def refsOf : Val → List Ref
  | .ref r => [r]
  | _ => []

/-- The references in an object's fields. -/
def fieldRefs (o : Obj) : List Ref := o.fields.toList.flatMap refsOf

/-- The one-level mutable footprint of a root cell: the root and the refs its
fields name. -/
def footprint (H : Heap) (root : Ref) : List Ref :=
  root :: (match H.cells root with
           | some o => fieldRefs o
           | none => [])

/-- Every cell in the footprint is exclusively owned. -/
def UniqueTree (H : Heap) (root : Ref) : Prop :=
  ∀ r ∈ footprint H root, H.rc r = 1

/-- No client-reachable reference is in the footprint. -/
def ClientSeparated (H : Heap) (root : Ref) (client : List Ref) : Prop :=
  ∀ r ∈ client, r ∉ footprint H root

/-- The concrete entry condition: the handle/count invariant plus the two
footprint facts. -/
structure EntryInv (H : Heap) (env : Env) (c : Ctx) (root : Ref) (client : List Ref) : Prop
    extends Inv H env c where
  uniqueTree : UniqueTree H root
  separated : ClientSeparated H root client

/-- A state whose two slots both name the child: the outer array is exclusive,
the child's count is two. -/
def repeatedChildHeap : Heap :=
  { cells := fun r =>
      if r = 0 then some ⟨#[.scalar 0], 2, false⟩
      else if r = 1 then some ⟨#[.ref 0, .ref 0], 1, false⟩
      else none
    next := 2 }

theorem repeatedChild_mem : 0 ∈ footprint repeatedChildHeap 1 := by
  simp [footprint, repeatedChildHeap, fieldRefs, refsOf]

/-- The repeated child is **not** a unique mutable tree. -/
theorem repeatedChild_not_unique : ¬ UniqueTree repeatedChildHeap 1 := by
  intro h
  have hrc := h 0 repeatedChild_mem
  simp [repeatedChildHeap, Heap.rc] at hrc

/-- A client handle on the child violates separation. -/
theorem clientRetained_not_separated :
    ¬ ClientSeparated repeatedChildHeap 1 [0] := by
  intro h
  exact h 0 (by simp) repeatedChild_mem

/-- The fresh array's footprint is just the root, with count one. -/
theorem freshArray_unique (n : Nat) : UniqueTree (initHeap n).2 (initHeap n).1 := by
  intro r hr
  simp [footprint, initHeap, fieldRefs, refsOf] at hr
  rcases hr with rfl | ⟨a, ⟨hn, ha⟩, hmem⟩
  · simp [initHeap, Heap.rc]
  · subst a
    simp [refsOf] at hmem

/-- A fresh array has no client-reachable references, so separation is
immediate. -/
theorem freshArray_separated (n : Nat) :
    ClientSeparated (initHeap n).2 (initHeap n).1 [] := by
  intro r hr
  simp at hr

/-- The initializer establishes the concrete entry condition. -/
theorem initEntryInv (n : Nat) :
    EntryInv (initHeap n).2 (initEnv (initHeap n).1) (initCtx (initHeap n).1)
      (initHeap n).1 [] :=
  { toInv := initInv n
    uniqueTree := freshArray_unique n
    separated := freshArray_separated n }

/-- A1 under the entry condition: the measured write prefix is fault-free and
every write is exclusive. -/
theorem artifact_entry (n : Nat) :
    ∃ H' env' v ws,
      run (execSet 0 3 1 2) (initEnv (initHeap n).1) (initHeap n).2 =
        .done H' env' v ws ∧
      (∀ w ∈ ws, w.2 = true) :=
  accepted_no_fault_and_exclusive_writes
    (execSet_check (initHeap n).1) (initEntryInv n).toInv

end Entry
end Ownership
