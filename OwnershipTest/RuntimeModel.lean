/-
Concrete runtime fixtures for the designated write.

The positive is the initializer's array: a count-one, non-persistent cell at
`ref 0`, the same heap `Ownership.Entry.initEntryInv` describes. Its runtime
counterpart is `initRHeap n`; `corr_init` relates them, `positive_setAt` instantiates
`setAt_inPlace_of_entryInv` at the concrete entry invariant, and the written field
reads back as the replacement.

The controls change one fact each, on the same shape of heap:

* `sharedR`: the root is counted twice. `shared_not_exclusive` and
  `shared_model_not_exclusive` show the runtime and model predicates both refuse
  it, `shared_check` takes the abort branch, `shared_setAt` reports no write, and
  `shared_copy` reaches the copy disposition: a fresh cell at count one with the
  replacement, the source cell lowered to count one with its fields kept.
* `persistR`: the root is counted once but persistent. The same facts hold:
  `persistent_check` aborts, `persistent_setAt` reports no write, and
  `persistent_copy` reaches the copy disposition.
* `dirtyR`: the allocator's cursor name is occupied by a live cell. The heap is
  not well formed (`dirty_not_wf`); `alloc?` refuses (`dirty_alloc_refused`) and
  `arraySet` reports no outcome (`dirty_copy_refused`), so the copy path cannot
  silently overwrite the cell at the cursor.

The positive and the two copy controls satisfy `WF`: the cursor's name and every
name above it are vacant, which is what makes their copy a copy.

These are calculations over the runtime model of
`OwnershipLcnf.RuntimeModel`, not measurements of a linked executable. No address
identity, physical reference count, emitted callee or C-runtime behaviour is
established here.
-/
import OwnershipLcnf.RuntimeModel

open Ownership
open OwnershipLcnf
open OwnershipLcnf.Runtime

namespace OwnershipTest.Runtime

/-! ## The positive: the initializer's heap -/

def initObj (n : Nat) : Ownership.Obj := ⟨Array.replicate n (.scalar 0), 1, false⟩

def initRObj (n : Nat) : RObj := ⟨Array.replicate n (.scalar 0), 1, false⟩

def initRHeap (n : Nat) : RHeap :=
  { cells := fun r => if r = 0 then some (initRObj n) else none
    next := 1 }

theorem wf_init (n : Nat) : (initRHeap n).WF := by
  intro r hr
  have h1 : 1 ≤ r := hr
  have hne : r ≠ 0 := by
    intro heq
    rw [heq] at h1
    exact Nat.not_succ_le_zero 0 h1
  simp [initRHeap, hne]

theorem corr_init (n : Nat) : Corr (Ownership.Runner.initHeap n).2 (initRHeap n) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro r
    by_cases h : r = 0 <;> simp [initRHeap, Ownership.Runner.initHeap, h]
  · intro r o o' h1 h2
    by_cases h : r = 0
    · subst h
      simp [initRHeap, Ownership.Runner.initHeap, initObj, initRObj] at h1 h2
      cases h1
      cases h2
      exact ⟨rfl, rfl, rfl⟩
    · simp [initRHeap, Ownership.Runner.initHeap, h] at h1

theorem positive_entryInv (n : Nat) :
    Ownership.Entry.EntryInv (Ownership.Runner.initHeap n).2
      (Ownership.Runner.initEnv (Ownership.Runner.initHeap n).1)
      (Ownership.Runner.initCtx (Ownership.Runner.initHeap n).1)
      (Ownership.Runner.initHeap n).1 [] :=
  Ownership.Entry.initEntryInv n

theorem positive_check (n : Nat) : checkExclusive (initRHeap n) 0 = .ok 0 :=
  checkExclusive_returns (corr_init n) (exclusive_of_entryInv (positive_entryInv n))

theorem positive_check_not_abort (n : Nat) (r' : Ref) :
    checkExclusive (initRHeap n) 0 ≠ .abort r' :=
  checkExclusive_no_abort (corr_init n) (exclusive_of_entryInv (positive_entryInv n)) r'

/-- The concrete entry invariant supplies the exclusivity, the runtime check
returns, the write is in place at `ref 0`, and the field reads back as the
replacement. -/
theorem positive_setAt (n : Nat) (hn : 0 < n) :
    ∃ H', setAt (initRHeap n) 0 0 (.scalar 7) = some (.inPlace H' 0) ∧
      Corr (inPlaceOutcome 0 0 7 (initObj n) (Ownership.Runner.initHeap n).2).heap H' ∧
      (inPlaceOutcome 0 0 7 (initObj n) (Ownership.Runner.initHeap n).2).target = some 0 ∧
      (H'.cells 0).bind (fun o => o.field? 0) = some (.scalar 7) := by
  have hcell : (Ownership.Runner.initHeap n).2.cells 0 = some (initObj n) := by
    simp [Ownership.Runner.initHeap, initObj]
  have ho' : (initRHeap n).cells 0 = some (initRObj n) := by
    simp [initRHeap]
  have hin : 0 < (initObj n).fields.size := by simpa [initObj] using hn
  exact setAt_inPlace_of_entryInv (H := (Ownership.Runner.initHeap n).2)
    (R := initRHeap n) (root := (Ownership.Runner.initHeap n).1)
    (i := 0) (vn := 7) (o := initObj n) (o' := initRObj n)
    (positive_entryInv n) (corr_init n) hcell ho' hin

/-! ## Control: a shared root -/

def sharedObj : Ownership.Obj := ⟨#[.scalar 0], 2, false⟩

def sharedRObj : RObj := ⟨#[.scalar 0], 2, false⟩

def sharedH : Ownership.Heap :=
  { cells := fun r => if r = 0 then some sharedObj else none
    next := 1 }

def sharedR : RHeap :=
  { cells := fun r => if r = 0 then some sharedRObj else none
    next := 1 }

theorem wf_shared : sharedR.WF := by
  intro r hr
  have h1 : 1 ≤ r := hr
  have hne : r ≠ 0 := by
    intro heq
    rw [heq] at h1
    exact Nat.not_succ_le_zero 0 h1
  simp [sharedR, hne]

theorem corr_shared : Corr sharedH sharedR := by
  refine ⟨rfl, ?_, ?_⟩
  · intro r
    by_cases h : r = 0 <;> simp [sharedH, sharedR, h]
  · intro r o o' h1 h2
    by_cases h : r = 0
    · subst h
      simp [sharedH, sharedR] at h1 h2
      cases h1
      cases h2
      exact ⟨rfl, rfl, rfl⟩
    · simp [sharedH, h] at h1

/-- The model's own predicate refuses the shared root. -/
theorem shared_model_not_exclusive : ¬ Ownership.Heap.Exclusive sharedH 0 := by
  rintro ⟨o, ho, hrc, _⟩
  have h : sharedObj = o := by simpa [sharedH] using ho
  subst h
  simp [sharedObj] at hrc

theorem shared_not_exclusive : ¬ sharedR.Exclusive 0 :=
  not_exclusive_of_rc_ne_one (H := sharedR) (r := 0) (o := sharedRObj)
    (by simp [sharedR]) (by simp [sharedRObj])

theorem shared_check : checkExclusive sharedR 0 = .abort 0 :=
  checkExclusive_of_not_exclusive shared_not_exclusive

theorem shared_setAt : setAt sharedR 0 0 (.scalar 7) = none := by
  simp [setAt, shared_check]

theorem shared_copy :
    arraySet sharedR 0 0 (.scalar 7) =
      some (.copied (((sharedR.alloc (sharedRObj.fields.set! 0 (.scalar 7))).2.dec 0 1))
                    ((sharedR.alloc (sharedRObj.fields.set! 0 (.scalar 7))).1)) :=
  arraySet_of_not_exclusive (by simp [sharedR]) shared_not_exclusive wf_shared

theorem shared_fresh_ref :
    (sharedR.alloc (sharedRObj.fields.set! 0 (.scalar 7))).1 = 1 := by
  simp [sharedR]

theorem shared_fresh_cell :
    ((sharedR.alloc (sharedRObj.fields.set! 0 (.scalar 7))).2.dec 0 1).cells 1 =
      some ⟨sharedRObj.fields.set! 0 (.scalar 7), 1, false⟩ := by
  have h := copy_fresh_cell (H := sharedR) (r := 0) (o := sharedRObj) (i := 0)
    (v := .scalar 7) (by simp [sharedR]) wf_shared
  simpa [sharedR] using h

theorem shared_source_cell :
    ((sharedR.alloc (sharedRObj.fields.set! 0 (.scalar 7))).2.dec 0 1).cells 0 =
      some { sharedRObj with rc := sharedRObj.rc - 1 } :=
  copy_source_cell (by simp [sharedR]) wf_shared

/-- The source cell keeps its fields; only its count drops. -/
theorem shared_source_fields :
    ((sharedR.alloc (sharedRObj.fields.set! 0 (.scalar 7))).2.dec 0 1).cells 0 =
      some { sharedRObj with rc := 1 } := by
  rw [shared_source_cell]
  simp [sharedRObj]

theorem shared_source_rc :
    ((sharedR.alloc (sharedRObj.fields.set! 0 (.scalar 7))).2.dec 0 1).rc 0 = 1 := by
  simp only [RHeap.rc]
  rw [shared_source_cell]
  simp [sharedRObj]

/-! ## Control: a persistent root -/

def persistObj : Ownership.Obj := ⟨#[.scalar 0], 1, true⟩

def persistRObj : RObj := ⟨#[.scalar 0], 1, true⟩

def persistH : Ownership.Heap :=
  { cells := fun r => if r = 0 then some persistObj else none
    next := 1 }

def persistR : RHeap :=
  { cells := fun r => if r = 0 then some persistRObj else none
    next := 1 }

theorem wf_persistent : persistR.WF := by
  intro r hr
  have h1 : 1 ≤ r := hr
  have hne : r ≠ 0 := by
    intro heq
    rw [heq] at h1
    exact Nat.not_succ_le_zero 0 h1
  simp [persistR, hne]

theorem corr_persistent : Corr persistH persistR := by
  refine ⟨rfl, ?_, ?_⟩
  · intro r
    by_cases h : r = 0 <;> simp [persistH, persistR, h]
  · intro r o o' h1 h2
    by_cases h : r = 0
    · subst h
      simp [persistH, persistR] at h1 h2
      cases h1
      cases h2
      exact ⟨rfl, rfl, rfl⟩
    · simp [persistH, h] at h1

/-- The model's own predicate refuses the persistent root. -/
theorem persistent_model_not_exclusive : ¬ Ownership.Heap.Exclusive persistH 0 := by
  rintro ⟨o, ho, _, hp⟩
  have h : persistObj = o := by simpa [persistH] using ho
  subst h
  simp [persistObj] at hp

theorem persistent_not_exclusive : ¬ persistR.Exclusive 0 :=
  not_exclusive_of_persistent (H := persistR) (r := 0) (o := persistRObj)
    (by simp [persistR]) (by simp [persistRObj])

theorem persistent_check : checkExclusive persistR 0 = .abort 0 :=
  checkExclusive_of_not_exclusive persistent_not_exclusive

theorem persistent_setAt : setAt persistR 0 0 (.scalar 7) = none := by
  simp [setAt, persistent_check]

theorem persistent_copy :
    arraySet persistR 0 0 (.scalar 7) =
      some (.copied (((persistR.alloc (persistRObj.fields.set! 0 (.scalar 7))).2.dec 0 1))
                    ((persistR.alloc (persistRObj.fields.set! 0 (.scalar 7))).1)) :=
  arraySet_of_not_exclusive (by simp [persistR]) persistent_not_exclusive wf_persistent

theorem persistent_fresh_cell :
    ((persistR.alloc (persistRObj.fields.set! 0 (.scalar 7))).2.dec 0 1).cells 1 =
      some ⟨persistRObj.fields.set! 0 (.scalar 7), 1, false⟩ := by
  have h := copy_fresh_cell (H := persistR) (r := 0) (o := persistRObj) (i := 0)
    (v := .scalar 7) (by simp [persistR]) wf_persistent
  simpa [persistR] using h

theorem persistent_source_cell :
    ((persistR.alloc (persistRObj.fields.set! 0 (.scalar 7))).2.dec 0 1).cells 0 =
      some { persistRObj with rc := persistRObj.rc - 1 } :=
  copy_source_cell (by simp [persistR]) wf_persistent

/-! ## Control: an occupied cursor -/

def dirtyObj : RObj := ⟨#[.scalar 0], 1, false⟩

/-- The root at `0` is shared, so the write wants the copy branch; the
allocator's cursor name `1` is occupied by a live cell. -/
def dirtyR : RHeap :=
  { cells := fun r =>
      if r = 0 then some sharedRObj
      else if r = 1 then some dirtyObj
      else none
    next := 1 }

theorem dirty_cursor_occupied : dirtyR.cells 1 = some dirtyObj := by
  simp [dirtyR]

theorem dirty_root_cell : dirtyR.cells 0 = some sharedRObj := by
  simp [dirtyR]

theorem dirty_not_wf : ¬ dirtyR.WF := by
  intro hwf
  have h : dirtyR.cells dirtyR.next = none := hwf.cursor_vacant
  simp [dirtyR] at h

theorem dirty_alloc_refused : dirtyR.alloc? #[.scalar 0] = none := by
  simp [RHeap.alloc?, dirtyR]

theorem dirty_not_exclusive : ¬ dirtyR.Exclusive 0 :=
  not_exclusive_of_rc_ne_one (H := dirtyR) (r := 0) (o := sharedRObj)
    (by simp [dirtyR]) (by simp [sharedRObj])

/-- The copy path refuses: no fresh cell is written and the occupied cursor
cell is left alone. -/
theorem dirty_copy_refused : arraySet dirtyR 0 0 (.scalar 7) = none := by
  have hb : dirtyR.isExclusive 0 = false := (RHeap.isExclusive_eq_false).mpr dirty_not_exclusive
  have ha : dirtyR.alloc? (sharedRObj.fields.set! 0 (.scalar 7)) = none := by
    simp [RHeap.alloc?, dirtyR]
  simp only [arraySet, dirty_root_cell, hb, Bool.false_eq_true, ite_false, ha]

/-! ## The two predicates agree on the fixtures -/

theorem positive_tests_agree (n : Nat) :
    (initRHeap n).isExclusive 0 =
      (Ownership.Runner.initHeap n).2.exclusive? 0 :=
  Corr.isExclusive_eq (corr_init n) 0

theorem shared_tests_agree : sharedR.isExclusive 0 = sharedH.exclusive? 0 :=
  Corr.isExclusive_eq corr_shared 0

theorem persistent_tests_agree : persistR.isExclusive 0 = persistH.exclusive? 0 :=
  Corr.isExclusive_eq corr_persistent 0

/-! ## Axiom footprint of the headline results -/

#print axioms OwnershipLcnf.Runtime.RHeap.isExclusive_eq_true
#print axioms OwnershipLcnf.Runtime.Corr.rc_eq
#print axioms OwnershipLcnf.Runtime.Corr.isExclusive_eq
#print axioms OwnershipLcnf.Runtime.Corr.isExclusive_true
#print axioms OwnershipLcnf.Runtime.Corr.set
#print axioms OwnershipLcnf.Runtime.Corr.alloc
#print axioms OwnershipLcnf.Runtime.Corr.dec
#print axioms OwnershipLcnf.Runtime.checkExclusive_returns
#print axioms OwnershipLcnf.Runtime.checkExclusive_no_abort
#print axioms OwnershipLcnf.Runtime.arraySet_inPlace
#print axioms OwnershipLcnf.Runtime.setAt_inPlace
#print axioms OwnershipLcnf.Runtime.setAt_ne_none
#print axioms OwnershipLcnf.Runtime.setAt_poststate_corr
#print axioms OwnershipLcnf.Runtime.setAt_inPlace_matches_outcome
#print axioms OwnershipLcnf.Runtime.setAt_inPlace_field
#print axioms OwnershipLcnf.Runtime.exclusive_of_entryInv
#print axioms OwnershipLcnf.Runtime.setAt_inPlace_of_entryInv
#print axioms OwnershipLcnf.Runtime.checkExclusive_of_not_exclusive
#print axioms OwnershipLcnf.Runtime.arraySet_of_not_exclusive
#print axioms OwnershipLcnf.Runtime.copy_fresh_cell
#print axioms OwnershipLcnf.Runtime.copy_source_cell
#print axioms OwnershipLcnf.Runtime.RHeap.rc_set_fields
#print axioms OwnershipLcnf.Runtime.RHeap.WF.cursor_vacant
#print axioms OwnershipLcnf.Runtime.RHeap.WF.lt_next
#print axioms OwnershipLcnf.Runtime.RHeap.WF.set
#print axioms OwnershipLcnf.Runtime.RHeap.WF.alloc
#print axioms OwnershipLcnf.Runtime.RHeap.WF.dec
#print axioms OwnershipLcnf.Runtime.RHeap.WF.alloc?
#print axioms OwnershipLcnf.Runtime.RHeap.WF.copy
#print axioms OwnershipLcnf.Runtime.arraySet_inPlace_wf
#print axioms OwnershipLcnf.Runtime.arraySet_copy_wf
#print axioms OwnershipTest.Runtime.positive_setAt
#print axioms OwnershipTest.Runtime.positive_check
#print axioms OwnershipTest.Runtime.shared_setAt
#print axioms OwnershipTest.Runtime.shared_copy
#print axioms OwnershipTest.Runtime.persistent_setAt
#print axioms OwnershipTest.Runtime.persistent_copy
#print axioms OwnershipTest.Runtime.wf_init
#print axioms OwnershipTest.Runtime.wf_shared
#print axioms OwnershipTest.Runtime.wf_persistent
#print axioms OwnershipTest.Runtime.dirty_not_wf
#print axioms OwnershipTest.Runtime.dirty_alloc_refused
#print axioms OwnershipTest.Runtime.dirty_copy_refused

end OwnershipTest.Runtime
