/-
Concrete counted-pair fixtures for the extraction protocol.

`H0` is the unique entry: the parent array at `ref 0` holds the child `ref 1`
in slot `0`, both cells are non-persistent at count one, and the fresh pair name
`ref 2` is empty. `counted_pair_boundary` runs the captured take-out, the two
projection increments and the unique-pair decrement. Its positive control shows
the pair gone, both cells still live at count one, the child exclusive and the
parent's placeholder-filled cell retained; the child cell is unchanged.

The negative controls are in the same file. `no_free_control` omits the pair
decrement, leaving the pair alive and both components at count two.
`retained_alias_control` keeps one extra counted handle to the parent after
the pair is gone, again count two and not exclusive. `shared_child_control` and
`shared_parent_control` start from a component already at count two and show
the protocol does not make it exclusive. Each negative is paired with the
positive `counted_pair_boundary` above or with the protocol boundary it
contradicts.

These are concrete instances of `Ownership.CountedPair.pair_accounting` and
its negative-control theorems. They are heap calculations, not runtime or
backend claims.
-/
import Ownership.CountedPair

open Ownership
open Ownership.CountedPair

namespace OwnershipTest.CountedPair

/-! ## Concrete heaps -/

/-- The child: one scalar field, count one, non-persistent. -/
def childObj : Obj := ⟨#[.scalar 0], 1, false⟩

/-- The parent array: the selected slot `0` holds the child, count one,
non-persistent. -/
def parentObj : Obj := ⟨#[.ref 1, .scalar 0], 1, false⟩

/-- The well-formed entry heap: parent at `0`, child at `1`, fresh name `2`. -/
def H0 : Heap :=
  { cells := fun r =>
      if r = 0 then some parentObj
      else if r = 1 then some childObj
      else none
    next := 2 }

/-- The shared-child entry: the same parent, child count two. -/
def sharedChildObj : Obj := ⟨#[.scalar 0], 2, false⟩

def Hs : Heap :=
  { cells := fun r =>
      if r = 0 then some parentObj
      else if r = 1 then some sharedChildObj
      else none
    next := 2 }

/-- The shared-parent entry: parent count two, child count one. -/
def sharedParentObj : Obj := ⟨#[.ref 1, .scalar 0], 2, false⟩

def Hp : Heap :=
  { cells := fun r =>
      if r = 0 then some sharedParentObj
      else if r = 1 then some childObj
      else none
    next := 2 }

/-! ## The well-formed entry -/

theorem entry0 : WellFormedEntry H0 0 1 0 := by
  refine ⟨parentObj, childObj, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [H0, parentObj, childObj]

theorem sharedEntry : CountedEntry Hs 0 1 0 1 2 := by
  refine ⟨parentObj, sharedChildObj, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Hs, parentObj, sharedChildObj]

theorem sharedParentEntry : CountedEntry Hp 0 1 0 2 1 := by
  refine ⟨sharedParentObj, childObj, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Hp, sharedParentObj, childObj]

/-! ## The positive control -/

/-- The parent's post-take-out object: the selected slot is the model's
placeholder scalar. -/
def parentAfterObj : Obj := ⟨#[.scalar 0, .scalar 0], 1, false⟩

theorem parent_placeholder :
    parentObj.fields.setIfInBounds 0 (.scalar 0) = parentAfterObj.fields := by
  decide

/-- The complete protocol on the unique entry. The pair is gone, both
components are live at count one, the child is exclusive, the parent remains
live while the call is suspended, and the child cell is unchanged. -/
theorem counted_pair_boundary :
    (protocol H0 0 1 0).1 = 2 ∧
      (protocol H0 0 1 0).2.rc 0 = 1 ∧
      (protocol H0 0 1 0).2.rc 1 = 1 ∧
      (protocol H0 0 1 0).2.cells 0 = some parentAfterObj ∧
      (protocol H0 0 1 0).2.cells 1 = some childObj ∧
      (protocol H0 0 1 0).2.cells 2 = none ∧
      Heap.Exclusive (protocol H0 0 1 0).2 0 ∧
      Heap.Exclusive (protocol H0 0 1 0).2 1 := by
  have hb := protocol_boundary (H := H0) (p := 0) (c := 1) (i := 0)
    (op := parentObj) (oc := childObj)
    (by simp [H0]) (by simp [H0]) (by decide) (by decide) (by decide)
  dsimp only at hb
  rcases hb with ⟨_, hcellsp, hcellsc, hpair, hrcp, hrcc, hexp, hexc⟩
  have hfstb : (protocol H0 0 1 0).1 = 2 := rfl
  refine ⟨hfstb, ?_, ?_, ?_, hcellsc, ?_, ?_, ?_⟩
  · simpa [parentObj] using hrcp
  · simpa [childObj] using hrcc
  · simpa [parentObj, parentAfterObj, parent_placeholder] using hcellsp
  · rw [← hfstb]
    exact hpair
  · exact hexp.mpr (by simp [parentObj])
  · exact hexc.mpr (by simp [childObj])

theorem pair_traffic_neutral_run :
    (protocol H0 0 1 0).2.rc 0 = H0.rc 0 ∧
      (protocol H0 0 1 0).2.rc 1 = H0.rc 1 ∧
      (protocol H0 0 1 0).2.cells 1 = H0.cells 1 ∧
      (protocol H0 0 1 0).2.cells (protocol H0 0 1 0).1 = none := by
  have h := pair_traffic_neutral entry0
  dsimp only at h
  exact h

theorem boundary_correspondence_run :
    (protocol H0 0 1 0).2.rc 0 = H0.rc 0 ∧
      (protocol H0 0 1 0).2.rc 1 = H0.rc 1 ∧
      Heap.Exclusive (protocol H0 0 1 0).2 0 ∧
      Heap.Exclusive (protocol H0 0 1 0).2 1 ∧
      (protocol H0 0 1 0).2.exclusive? 0 = true ∧
      (protocol H0 0 1 0).2.exclusive? 1 = true := by
  have h := boundary_correspondence entry0
  dsimp only at h
  exact h

/-! ## Negative controls -/

/-- Omitting the pair decrement: the pair stays live and both components stay
at count two, so neither is exclusive. The positive control is
`counted_pair_boundary`. -/
theorem no_free_control :
    (protocolNoFree H0 0 1 0).2.rc 0 = 2 ∧
      (protocolNoFree H0 0 1 0).2.rc 1 = 2 ∧
      ¬ Heap.Exclusive (protocolNoFree H0 0 1 0).2 0 ∧
      ¬ Heap.Exclusive (protocolNoFree H0 0 1 0).2 1 ∧
      (protocolNoFree H0 0 1 0).2.cells 2 ≠ none := by
  have h := no_free_components_not_exclusive entry0
  dsimp only at h
  have hfst : (protocolNoFree H0 0 1 0).1 = 2 := rfl
  have hpair : (protocolNoFree H0 0 1 0).2.cells 2 ≠ none := by
    rw [← hfst]
    exact h.2.2.2.2
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, hpair⟩

/-- Retaining one extra counted parent handle after the pair is gone: the
parent is at count two and not exclusive; the child is unaffected and remains
exclusive. The positive control is `counted_pair_boundary`. -/
theorem retained_alias_control :
    ((protocol H0 0 1 0).2.inc 0 1).rc 0 = 2 ∧
      ¬ Heap.Exclusive ((protocol H0 0 1 0).2.inc 0 1) 0 ∧
      ((protocol H0 0 1 0).2.inc 0 1).rc 1 = 1 ∧
      Heap.Exclusive ((protocol H0 0 1 0).2.inc 0 1) 1 := by
  have h := retained_alias_not_exclusive entry0
  dsimp only at h
  exact h

/-- A shared child entry remains at count two and is not exclusive at the
boundary. The positive control is the count-one child in
`counted_pair_boundary`. -/
theorem shared_child_control :
    (protocol Hs 0 1 0).2.rc 1 = 2 ∧
      ¬ Heap.Exclusive (protocol Hs 0 1 0).2 1 := by
  have h := shared_child_not_exclusive sharedEntry
  dsimp only at h
  exact h

/-- A shared parent entry remains at count two and is not exclusive at the
boundary. The positive control is the count-one parent in
`counted_pair_boundary`. -/
theorem shared_parent_control :
    (protocol Hp 0 1 0).2.rc 0 = 2 ∧
      ¬ Heap.Exclusive (protocol Hp 0 1 0).2 0 := by
  have h := shared_parent_not_exclusive sharedParentEntry
  dsimp only at h
  exact h

#print axioms Ownership.CountedPair.takeOut_transfers
#print axioms pair_accounting
#print axioms pair_traffic_neutral
#print axioms boundary_correspondence
#print axioms counted_pair_boundary
#print axioms pair_traffic_neutral_run
#print axioms boundary_correspondence_run
#print axioms no_free_control
#print axioms retained_alias_control
#print axioms shared_child_control
#print axioms shared_parent_control

end OwnershipTest.CountedPair
