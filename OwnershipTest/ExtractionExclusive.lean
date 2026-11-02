/-
Extraction and restoration cell exclusivity at the concrete path.

`checkN_extraction_exclusive_of_entryInv` is instantiated on the depth-two path
certificate of `OwnershipTest.PathAgreement`: the whole program's root take-out
and the child level its call hands to the recursive summary each take out and
restore a slot whose array cell is exclusive. The `#guard` is the same checker's
positive control on the same concrete values.
-/
import OwnershipTest.PathAgreement

open Ownership
open Ownership.Nested
open Ownership.Entry
open Ownership.Path
open OwnershipTest.PathAgreement

namespace OwnershipTest.ExtractionExclusive

/-- The model-level disposition theorem on the whole path program. -/
theorem code_extractionExclusive : ExtractionExclusive H env0 code :=
  checkN_extraction_exclusive_of_entryInv entry0 agrees0 checkN_code

/-- The root take-out's array cell is exclusive. -/
theorem root_exclusive : Heap.Exclusive H 0 := by
  have h : ExtractionExclusive H env0 code := code_extractionExclusive
  unfold code build l0 l1 pathVar valueVar at h
  obtain ⟨r, o, idx, ha, hi, hcell, hex, hk⟩ := h
  have henv0 : env0 0 = some (.ref 0) := by simp [env0]
  rw [henv0] at ha
  have hr : r = 0 := (Val.ref.inj (Option.some.inj ha)).symm
  rw [hr] at hex
  exact hex

/-- The child take-out's array cell is exclusive in the heap the root's take-out
leaves. -/
theorem child_exclusive : Heap.Exclusive (blankLevel H l0) 1 := by
  have h : ExtractionExclusive H env0 code := code_extractionExclusive
  unfold code build l0 l1 pathVar valueVar at h
  obtain ⟨r, o, idx, ha, hi, hcell, hex, hk⟩ := h
  have henv0 : env0 0 = some (.ref 0) := by simp [env0]
  rw [henv0] at ha
  have hr : r = 0 := (Val.ref.inj (Option.some.inj ha)).symm
  have hcell0 : H.cells 0 = some rootObj := H_cells_zero
  rw [hr] at hcell
  have ho : o = rootObj := Option.some.inj (hcell.symm.trans hcell0)
  have henv1 : env0 1 = some (.scalar 0) := by simp [env0]
  rw [henv1] at hi
  have hidx : idx = 0 := (Val.scalar.inj (Option.some.inj hi)).symm
  rw [hr] at hk
  rw [ho] at hk
  rw [hidx] at hk
  obtain ⟨_, _, hbody, _⟩ := hk
  unfold build at hbody
  obtain ⟨r1, o1, idx1, ha1, hi1, hcell1, hex1, hk1⟩ := hbody
  have henv3 : (isolateEnv ((env0.set 2 (.ref 0)).set 3 (.ref 1)) 3 10 11) 3 =
      some (.ref 1) := by
    simp [isolateEnv, Env.set]
  rw [henv3] at ha1
  have hr1 : r1 = 1 := (Val.ref.inj (Option.some.inj ha1)).symm
  rw [hr1] at hex1
  exact hex1

/-- The root put-back's target array cell is exclusive on the heap the child
call leaves, so the restoration half of the path is covered as well. -/
theorem root_putBack_exclusive :
    ∃ H' env' v ws,
      runN innerCode env1 H1 = .done H' env' v ws ∧ Heap.Exclusive H' 0 := by
  have h : ExtractionExclusive H env0 code := code_extractionExclusive
  unfold code build l0 l1 pathVar valueVar at h
  obtain ⟨r, o, idx, ha, hi, hcell, hex, hk⟩ := h
  have henv0 : env0 0 = some (.ref 0) := by simp [env0]
  rw [henv0] at ha
  have hr : r = 0 := (Val.ref.inj (Option.some.inj ha)).symm
  have hcell0 : H.cells 0 = some rootObj := H_cells_zero
  rw [hr] at hcell
  have ho : o = rootObj := Option.some.inj (hcell.symm.trans hcell0)
  have henv1 : env0 1 = some (.scalar 0) := by simp [env0]
  rw [henv1] at hi
  have hidx : idx = 0 := (Val.scalar.inj (Option.some.inj hi)).symm
  rw [hr] at hk
  rw [ho] at hk
  rw [hidx] at hk
  obtain ⟨r2, hstate, _, hcont⟩ := hk
  have henvstate : ((env0.set 2 (.ref 0)).set 3 (.ref 1)) 3 = some (.ref 1) := by
    simp [Env.set]
  rw [henvstate] at hstate
  have hr2 : r2 = 1 := (Val.ref.inj (Option.some.inj hstate)).symm
  rw [hr2] at hcont
  obtain ⟨H', env', v, ws, hrun, -, -, -⟩ := childContract
  have hp := hcont H' env' v ws hrun
  obtain ⟨r0, re0, o0, idx0, hpa, hpe, hpi, hpc, hex0, _⟩ := hp
  have henv2 : (((env0.set 2 (.ref 0)).set 3 (.ref 1)).set 4 (.ref 1)) 2 =
      some (.ref 0) := by
    simp [Env.set]
  rw [henv2] at hpa
  have hr0 : r0 = 0 := (Val.ref.inj (Option.some.inj hpa)).symm
  rw [hr0] at hex0
  exact ⟨H', env', v, ws, hrun, hex0⟩

-- The affirmative control: the checker accepts the path program.
#guard (checkN ctx0 code).isSome

end OwnershipTest.ExtractionExclusive

#print axioms OwnershipTest.ExtractionExclusive.code_extractionExclusive
#print axioms OwnershipTest.ExtractionExclusive.root_exclusive
#print axioms OwnershipTest.ExtractionExclusive.child_exclusive
#print axioms OwnershipTest.ExtractionExclusive.root_putBack_exclusive
