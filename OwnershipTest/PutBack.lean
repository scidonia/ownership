/-
Concrete put-back fixtures with a positive beside each control.

`B` is the heap `OwnershipTest.CountedPair.H0`'s protocol run reaches: the parent
at `ref 0` holds the take-out's placeholder in slot `0`, the child at `ref 1` is
live at count one, and the temporary pair is gone. `childCall0` instantiates the
call boundary: the body is admitted, checked from the isolated context, runs from
`Nested.isolateEnv` — where the caller's parent variable is dead — with the
invariant on the isolated environment, and the parent outside the child's mutable
footprint. `ChildCall.parent` derives the parent's cell preservation from those
facts via `Entry.callAt_frame_confined`; it is not a field. `exclusive_restoration`
is the positive: the put-back on the heap that call leaves takes the mutate
branch, returns `ref 0` itself, writes the child into slot `0`, and leaves both
counts at one. `functional_restoration_run` and `counts_run` are the two halves,
and `restored_cell`, `child_write_survives` read the concrete slots.

The controls are on the same parent cell with one fact changed, each beside the
positive above.

* `shared_control`: the parent at count two. The put-back copies: the result is
  the fresh name, the fresh cell is at count one with the child in the selected
  slot, and the alias keeps its fields and drops to count one.
* `retaining_body_run`, `retaining_body_parent`, `retaining_body_not_admitted`,
  `retaining_body_excluded`: a child body that increments a variable bound to
  the parent. It leaves exactly the shared control's parent cell, and it is
  outside the supported interface the contract names (`CountFree` forbids the
  increment), so no heap makes it a `ChildCall`.
* `putBack_retaining_positive`: a `.putBack`-shaped retaining body with the
  parent at variable `6`. On the caller's own environment it runs to `done`, puts
  the parent reference in the child's slot, and moves no count — the retention
  case `CountFree` alone admits. Beside it, `putBack_retaining_operands` and
  `putBack_retaining_faults` show that under the isolated environment the array
  operand and the index are bound and only the parent's variable is dead, so the
  body cannot complete (`putBack_retaining_no_outcome`,
  `putBack_retaining_excluded`); `putBack_parent_faults` shows the same dead
  variable named as `.badVar 6` when it sits in the arm's label position.
* `retained_parent_excluded`: a heap whose child slot holds the parent. A body
  could then reach the parent through a reference write, which is exactly why
  the boundary carries the separation premise; no `ChildCall` exists there.
* `persistent_control`: the same parent fields with the persistence flag set.
  The only branch is copy.
* `unique_pair_positive`: the same heap with the flag cleared and the count one
  is the mutate branch.

These are heap calculations over the model, not runtime or backend claims: no
address identity, no physical reference count, and no emitted callee is
established here.
-/
import Ownership.PutBack
import OwnershipTest.CountedPair

open Ownership
open Ownership.PutBack

namespace OwnershipTest.PutBack

/-! ## The boundary and the child call -/

/-- The counted entry's protocol boundary. -/
def B : Heap := (Ownership.CountedPair.protocol OwnershipTest.CountedPair.H0 0 1 0).2

/-- The entry's parent and child cells. -/
abbrev parentObj : Obj := OwnershipTest.CountedPair.parentObj
abbrev childObj : Obj := OwnershipTest.CountedPair.childObj

/-- The restoration boundary on the protocol run. -/
theorem boundary0 : Boundary B 0 1 0 parentObj childObj := by
  have h : Boundary
      (Ownership.CountedPair.protocol OwnershipTest.CountedPair.H0 0 1 0).2 0 1 0
      OwnershipTest.CountedPair.parentObj OwnershipTest.CountedPair.childObj :=
    restorationBoundary_of_entry
      (H := OwnershipTest.CountedPair.H0) (p := 0) (c := 1) (i := 0)
      (op := OwnershipTest.CountedPair.parentObj) (oc := OwnershipTest.CountedPair.childObj)
      (by simp [OwnershipTest.CountedPair.H0])
      (by simp [OwnershipTest.CountedPair.H0])
      rfl rfl rfl rfl
      (by simp [OwnershipTest.CountedPair.parentObj])
      (by decide) (by decide) (by decide)
  simpa [B, parentObj, childObj] using h

/-- The caller's context. Only its multiplicity map reaches the call, and
`Inv.rc_eq` makes it the boundary heap's own counts. -/
def childCtx : Ctx :=
  { us := fun _ => .dead, refOf := fun _ => none, mult := fun r => B.rc r }

/-- The child call's environment: the state variable holds the extracted child,
the body's own slot index and a replacement scalar. -/
def cenv : Env :=
  fun z =>
    if z = 4 then some (.ref 1)
    else if z = 10 then some (.scalar 0)
    else if z = 11 then some (.scalar 7)
    else none

/-- The admitted child body: one designated write on the child's own slot `0`. -/
def body : Nested.NCode := .base (.setArr 4 10 11 (.ret 4))

/-- The child cell after the body's write: slot `0` holds the scalar `7`. -/
def childAfter : Obj := { childObj with fields := childObj.fields.setIfInBounds 0 (.scalar 7) }

/-- The heap the child call leaves. -/
def Hc : Heap := B.set 1 childAfter

theorem body_admitted : Nested.CountFree body = true := rfl

/-- The boundary child is live at count one. -/
theorem B_rc_1 : B.rc 1 = 1 := by
  rw [CountedPair.rc_of_cells (H := B) (r := 1) (o := childObj) boundary0.child]
  rfl

/-- The boundary heap has no live cell besides the parent and the child. -/
theorem B_cells_none {r : Ref} (h0 : r ≠ 0) (h1 : r ≠ 1) : B.cells r = none := by
  by_cases h2 : r = 2
  · subst h2
    obtain ⟨-, -, -, -, -, hpair, -, -⟩ := OwnershipTest.CountedPair.counted_pair_boundary
    simpa [B] using hpair
  · have hB : B = Ownership.CountedPair.pairTraffic
        (Ownership.CountedPair.takeOut OwnershipTest.CountedPair.H0 0 1 0).2
        OwnershipTest.CountedPair.H0.next := rfl
    have htraffic : B.cells r =
        (Ownership.CountedPair.pairFree
          (Ownership.CountedPair.pairInc
            (Ownership.CountedPair.takeOut OwnershipTest.CountedPair.H0 0 1 0).2 0 1)
          0 1 OwnershipTest.CountedPair.H0.next).cells r := by
      rw [hB, Ownership.CountedPair.pairTraffic_takeOut (H := OwnershipTest.CountedPair.H0)
        (p := 0) (c := 1) (i := 0) (by decide) (by decide)]
    rw [htraffic,
      Ownership.CountedPair.pairFree_inc_cells_other
        (pair := OwnershipTest.CountedPair.H0.next) h0 h1
        (by rw [show OwnershipTest.CountedPair.H0.next = 2 from rfl]; exact h2)]
    have htake : (Ownership.CountedPair.takeOut OwnershipTest.CountedPair.H0 0 1 0).2.cells r
        = OwnershipTest.CountedPair.H0.cells r := by
      show (Ownership.CountedPair.setPlaceholder
        (Ownership.CountedPair.allocPair OwnershipTest.CountedPair.H0 0 1) 0 0).cells r = _
      rw [Ownership.CountedPair.setPlaceholder_cells_other h0,
        Ownership.CountedPair.allocPair_cells_other
          (by rw [show OwnershipTest.CountedPair.H0.next = 2 from rfl]; exact h2)]
    rw [htake]
    simp [OwnershipTest.CountedPair.H0, h0, h1]

/-- Every live boundary cell is non-persistent, which is the invariant's
persistence field. -/
theorem B_nonPersistent : ∀ r o, B.cells r = some o → o.persistent = false := by
  intro r o h
  by_cases h0 : r = 0
  · subst h0
    rw [boundary0.parent] at h
    simp only [Option.some.injEq] at h
    subst h
    rfl
  · by_cases h1 : r = 1
    · subst h1
      rw [boundary0.child] at h
      simp only [Option.some.injEq] at h
      subst h
      rfl
    · rw [B_cells_none h0 h1] at h
      simp at h

/-- The child object has no reference field, so its footprint has no step. -/
theorem childObj_fieldRefs : Entry.fieldRefs childObj = [] := by
  simp [Entry.fieldRefs, Entry.refsOf, childObj, OwnershipTest.CountedPair.childObj]

/-- The child's mutable footprint is the child alone: its cell holds a scalar, so
no step leaves it. -/
theorem childFootprint : ∀ q, Ownership.Entry.MutableFootprint B 1 q → q = 1 := by
  intro q h
  induction h with
  | root => rfl
  | step hr hcell hpers hmem hcell' hpers' ih =>
      subst ih
      rw [boundary0.child] at hcell
      simp only [Option.some.injEq] at hcell
      subst hcell
      rw [childObj_fieldRefs] at hmem
      simp at hmem

/-- The parent is outside the child's mutable footprint: the separation premise
the call boundary carries. -/
theorem childSeparated : ¬ Ownership.Entry.MutableFootprint B 1 0 := by
  intro h
  have hq := childFootprint 0 h
  exact absurd hq (by decide)

/-- The caller's invariant on the isolated environment. -/
theorem childInv : Inv B (Nested.isolateEnv cenv 4 10 11) (Nested.isolatedCtx childCtx 4 10 11 1) where
  rc_eq := by intro r; rfl
  owned := by
    intro z r hz hr
    by_cases h4 : z = 4
    · subst h4
      have hr' : (1 : Ref) = r := by simpa [Nested.isolatedCtx] using hr
      subst hr'
      refine ⟨by simp [Nested.isolateEnv, cenv], ?_⟩
      rw [show (Nested.isolatedCtx childCtx 4 10 11 1).mult 1 = B.rc 1 from rfl, B_rc_1]
      decide
    · by_cases h10 : z = 10
      · subst h10
        simp [Nested.isolatedCtx, h4] at hz
      · by_cases h11 : z = 11
        · subst h11
          simp [Nested.isolatedCtx, h4, h10] at hz
        · simp [Nested.isolatedCtx, h4, h10, h11] at hz
  borrow := by
    intro z r hz hr
    by_cases h4 : z = 4
    · subst h4
      simp [Nested.isolatedCtx] at hz
    · by_cases h10 : z = 10
      · subst h10
        simp [Nested.isolatedCtx, h4] at hz
      · by_cases h11 : z = 11
        · subst h11
          simp [Nested.isolatedCtx, h4, h10] at hz
        · simp [Nested.isolatedCtx, h4, h10, h11] at hz
  scalar := by
    intro z hz
    by_cases h4 : z = 4
    · subst h4
      simp [Nested.isolatedCtx] at hz
    · by_cases h10 : z = 10
      · subst h10
        exact ⟨0, by simp [Nested.isolateEnv, cenv]⟩
      · by_cases h11 : z = 11
        · subst h11
          exact ⟨7, by simp [Nested.isolateEnv, cenv]⟩
        · simp [Nested.isolatedCtx, h4, h10, h11] at hz
  nonPersistent := B_nonPersistent

/-- The checker admits the body from the isolated context. -/
theorem childChecked :
    ∃ cb, Nested.checkNF (Nested.isolatedCtx childCtx 4 10 11 1) [] body = some cb ∧
      ∃ y, Nested.retVar body = some y ∧ cb.us y = .owned ∧ cb.refOf y = some 1 := by
  refine ⟨Nested.isolatedCtx childCtx 4 10 11 1, ?_, 4, rfl, ?_, ?_⟩
  · simp [body, Nested.checkNF, Ownership.check, Nested.isolatedCtx, childCtx,
      Ownership.Ctx.multOf, B_rc_1]
  · simp [Nested.isolatedCtx]
  · simp [Nested.isolatedCtx]

/-- The body runs from the isolated environment the call hands it. -/
theorem body_runs_isolated :
    Nested.runN body (Nested.isolateEnv cenv 4 10 11) B =
      .done Hc ((Nested.isolateEnv cenv 4 10 11).set 4 (.ref 1)) (.ref 1) [(1, true)] := by
  have hcell : B.cells 1 = some childObj := boundary0.child
  have hex : B.exclusive? 1 = true :=
    (Heap.exclusive?_eq_true).mpr ⟨childObj, hcell, by rfl, by rfl⟩
  have h4 : Nested.isolateEnv cenv 4 10 11 4 = some (.ref 1) := by
    simp [Nested.isolateEnv, cenv]
  have h10 : Nested.isolateEnv cenv 4 10 11 10 = some (.scalar 0) := by
    simp [Nested.isolateEnv, cenv]
  have h11 : Nested.isolateEnv cenv 4 10 11 11 = some (.scalar 7) := by
    simp [Nested.isolateEnv, cenv]
  simp only [body, Nested.runN, Ownership.run, h4, h10, h11]
  rw [hcell]
  simp [hex, Hc, childAfter, Ownership.Res.addWrite]

/-- The child-call boundary, concretely: admitted, checked from the isolated
context, run from `isolateEnv`, invariant-carrying, annotated, extraction-safe
and separated from the parent. The parent's cell preservation is derived from
these (`ChildCall.parent`), not stated. -/
theorem childCall0 : ChildCall B Hc cenv childCtx 4 10 11 body 0 1 where
  admitted := body_admitted
  checked := childChecked
  inv := childInv
  annotations := trivial
  extraction := trivial
  separated := childSeparated
  outcome := ⟨(Nested.isolateEnv cenv 4 10 11).set 4 (.ref 1), [(1, true)],
    body_runs_isolated⟩
  child_rc := by
    show Hc.rc 1 = B.rc 1
    rw [Hc, Heap.rc_set_self]
    rw [CountedPair.rc_of_cells (H := B) (r := 1) (o := childObj) boundary0.child]
    rfl
  child_persistent := by
    show Hc.isPersistent 1 = B.isPersistent 1
    rw [Hc,
      isPersistent_of_cells (H := B.set 1 childAfter) (r := 1) (o := childAfter)
        (Heap.set_self B 1 childAfter),
      isPersistent_of_cells (H := B) (r := 1) (o := childObj) boundary0.child]
    rfl

/-! ## The positive: exclusive restoration -/

/-- The put-back on the heap the child call leaves takes the mutate branch,
returns the parent's own reference, restores the child into the selected slot,
and leaves both counts at one. -/
theorem exclusive_restoration :
    let H' := mutate Hc 0 (parentAfter parentObj 0) 0 1
    disposition? Hc 0 0 = some .mutate ∧
      putBack Hc 0 0 1 = some (0, H') ∧
      ((parentAfter parentObj 0).fields.setIfInBounds 0 (.ref 1))[0]? = some (.ref 1) ∧
      H'.rc 0 = 1 ∧ H'.rc 1 = 1 ∧
      H'.cells 0 ≠ none ∧ H'.cells 1 ≠ none ∧
      Heap.Exclusive H' 0 ∧ Heap.Exclusive H' 1 :=
  putBack_exclusive boundary0 childCall0

/-- The same restoration from the `CountedPair` well-formed entry: the entry's
protocol boundary and the child-call contract alone select the mutate branch and
leave both counts at one. -/
theorem exclusive_restoration_from_entry :
    ∃ op, putBack Hc 0 0 1 = some (0, mutate Hc 0 (parentAfter op 0) 0 1) ∧
      (mutate Hc 0 (parentAfter op 0) 0 1).rc 0 = 1 ∧
      (mutate Hc 0 (parentAfter op 0) 0 1).rc 1 = 1 ∧
      Heap.Exclusive (mutate Hc 0 (parentAfter op 0) 0 1) 0 ∧
      Heap.Exclusive (mutate Hc 0 (parentAfter op 0) 0 1) 1 :=
  putBack_exclusive_of_wellFormed OwnershipTest.CountedPair.entry0 childCall0

/-- Functional restoration: the result is the parent's reference, the child's
cell is untouched, and nothing is allocated. -/
theorem functional_restoration_run :
    (mutate Hc 0 (parentAfter parentObj 0) 0 1).cells 0 =
        some { parentAfter parentObj 0 with
          fields := (parentAfter parentObj 0).fields.setIfInBounds 0 (.ref 1) } ∧
      (mutate Hc 0 (parentAfter parentObj 0) 0 1).cells 1 = Hc.cells 1 ∧
      (mutate Hc 0 (parentAfter parentObj 0) 0 1).next = Hc.next := by
  have h := restoration_functional boundary0 childCall0
  dsimp only at h
  obtain ⟨-, hcell, -, -, -, hchild, hnext⟩ := h
  exact ⟨hcell, hchild, hnext⟩

/-- Reference-count preservation: the boundary counts are one and the restore
leaves them one. -/
theorem counts_run :
    Hc.rc 0 = 1 ∧ Hc.rc 1 = 1 ∧
      (mutate Hc 0 (parentAfter parentObj 0) 0 1).rc 0 = 1 ∧
      (mutate Hc 0 (parentAfter parentObj 0) 0 1).rc 1 = 1 := by
  have h := restoration_counts boundary0 childCall0
  dsimp only at h
  obtain ⟨h1, h2, h3, h4, -, -, -, -⟩ := h
  exact ⟨h1, h2, h3, h4⟩

/-- The restored cell: slot `0` holds the child handle, slot `1` still holds the
model's placeholder. -/
theorem restored_cell :
    ((parentAfter parentObj 0).fields.setIfInBounds 0 (.ref 1))[0]? = some (.ref 1) ∧
      ((parentAfter parentObj 0).fields.setIfInBounds 0 (.ref 1))[1]? = some (.scalar 0) := by
  have hsize : 0 < (parentAfter parentObj 0).fields.size := by
    simp [parentAfter, parentObj, OwnershipTest.CountedPair.parentObj]
  refine ⟨Array.getElem?_setIfInBounds_self_of_lt hsize, ?_⟩
  rw [Array.getElem?_setIfInBounds_ne (by decide : (0 : Nat) ≠ 1)]
  rfl

/-- The child's own write survives the restoration: its cell is the one the body
wrote, and the restoration does not touch it. -/
theorem child_write_survives :
    (mutate Hc 0 (parentAfter parentObj 0) 0 1).cells 1 = some childAfter := by
  have h := functional_restoration_run
  rw [h.2.1]
  show Hc.cells 1 = some childAfter
  exact Heap.set_self B 1 childAfter

/-! ## The shared parent control -/

/-- The boundary parent cell carried by a retained alias: count two, the same
fields. -/
def sharedObj : Obj := { parentAfter parentObj 0 with rc := 2 }

/-- The shared-parent heap: the count-two parent at `0`, the child at `1`, fresh
name `2`. -/
def Hsh : Heap :=
  { cells := fun r =>
      if r = 0 then some sharedObj else if r = 1 then some childObj else none
    next := 2 }

/-- A count-two parent selects the copy branch: the result is the fresh name, the
fresh cell is at count one with the child in the selected slot, and the alias
drops to count one. Beside `exclusive_restoration`. -/
theorem shared_control :
    disposition? Hsh 0 0 = some .copy ∧
      putBack Hsh 0 0 1 = some (copy Hsh 0 sharedObj 0 1) ∧
      (copy Hsh 0 sharedObj 0 1).1 = Hsh.next ∧
      (copy Hsh 0 sharedObj 0 1).2.cells Hsh.next =
        some ⟨sharedObj.fields.setIfInBounds 0 (.ref 1), 1, false⟩ ∧
      (copy Hsh 0 sharedObj 0 1).2.cells 0 = some { sharedObj with rc := 1 } := by
  have hcell : Hsh.cells 0 = some sharedObj := by simp [Hsh]
  have hlt : 0 < sharedObj.fields.size := by
    simp [sharedObj, parentAfter, parentObj, OwnershipTest.CountedPair.parentObj]
  have hrc : sharedObj.rc = 2 := rfl
  have hpn : (0 : Ref) ≠ Hsh.next := by decide
  exact shared_parent_copies hcell hlt hrc hpn

/-- The copy leaves the old parent's fields alone: the old cell keeps the same
contents and only its count moves. -/
theorem shared_old_parent_contents :
    ∃ o, (copy Hsh 0 sharedObj 0 1).2.cells 0 = some o ∧ o.fields = sharedObj.fields := by
  obtain ⟨-, -, -, -, hold⟩ := shared_control
  exact ⟨_, hold, rfl⟩

/-- The copy's fresh cell is a different reference from the alias and carries the
child in the selected slot. -/
theorem shared_fresh_is_new :
    (copy Hsh 0 sharedObj 0 1).1 ≠ 0 ∧
      (copy Hsh 0 sharedObj 0 1).2.cells (copy Hsh 0 sharedObj 0 1).1 =
        some ⟨sharedObj.fields.setIfInBounds 0 (.ref 1), 1, false⟩ ∧
      (sharedObj.fields.setIfInBounds 0 (.ref 1))[0]? = some (.ref 1) := by
  obtain ⟨-, -, hfresh, hnew, -⟩ := shared_control
  have hsize : 0 < sharedObj.fields.size := by
    simp [sharedObj, parentAfter, parentObj, OwnershipTest.CountedPair.parentObj]
  refine ⟨by rw [hfresh]; decide, by rw [hfresh]; exact hnew, ?_⟩
  exact Array.getElem?_setIfInBounds_self_of_lt hsize

/-! ## The retaining child body control -/

/-- The retaining child body: it increments a variable bound to the parent. -/
def retainingBody : Nested.NCode := .base (.inc 6 1 (.ret 4))

/-- The caller's environment, which binds the child, the parent and the put-back's
index scalar. The parent sits at variable `6`, which the isolated environment
does not expose. -/
def retainingEnv : Env :=
  fun z =>
    if z = 4 then some (.ref 1)
    else if z = 6 then some (.ref 0)
    else if z = 10 then some (.scalar 0)
    else none

/-- The isolated environment the call hands its body leaves the parent's variable
dead, so the body cannot name the parent even by a reference. -/
theorem retained_var_dead : Nested.isolateEnv retainingEnv 4 10 11 6 = none := by
  simp [Nested.isolateEnv]

/-- If a body could reach the parent, the increment would leave it at count two:
the run on the caller's own environment. -/
theorem retaining_body_run :
    Nested.runN retainingBody retainingEnv B =
      .done (B.inc 0 1) retainingEnv (.ref 1) [] := by
  simp [retainingBody, Nested.runN, Ownership.run, retainingEnv]

/-- The retaining body leaves exactly the shared control's parent cell. -/
theorem retaining_body_parent :
    (B.inc 0 1).cells 0 = some sharedObj := by
  have h := CountedPair.inc_cells_self (H := B) (r := 0) (n := 1) boundary0.parent
  simpa [sharedObj, parentAfter, parentObj, OwnershipTest.CountedPair.parentObj] using h

/-- The retaining body is outside the supported interface: `CountFree` refuses the
increment, which is the checker's premise on a call body. -/
theorem retaining_body_not_admitted : Nested.CountFree retainingBody = false := rfl

/-- The retaining body is excluded by the stated interface premise: no heap, no
environment and no context make it a child call. Beside `childCall0`. -/
theorem retaining_body_excluded (Hout : Heap) (env : Env) (ctx : Ctx)
    (state path x : Var) :
    ¬ ChildCall B Hout env ctx state path x retainingBody 0 1 :=
  not_childCall_of_not_countFree retaining_body_not_admitted

/-- A put-back-shaped retaining body: it stores the reference held by variable
`6` — the parent, in the caller's environment — into the child's slot, with no
increment. `CountFree` admits `.putBack`. -/
def putBackRetainingBody : Nested.NCode := .putBack 4 6 10 12 (.ret 4)

theorem putBack_retaining_admitted : Nested.CountFree putBackRetainingBody = true := rfl

/-- The child cell after the retention write: slot `0` holds the parent
reference. -/
def childRetained : Obj := { childObj with fields := childObj.fields.setIfInBounds 0 (.ref 0) }

/-- The caller-side execution: with the parent bound at variable `6` and the index
at variable `10`, the body runs to `done` and stores the parent reference in the
child's selected slot. Only `.putBack`'s reference write happens — no increment,
so the counts are untouched. -/
theorem putBack_retaining_run :
    Nested.runN putBackRetainingBody retainingEnv B =
      .done (B.set 1 childRetained) (retainingEnv.set 12 (.ref 1)) (.ref 1) [] := by
  have hcell : B.cells 1 = some childObj := boundary0.child
  have h4 : retainingEnv 4 = some (.ref 1) := by simp [retainingEnv]
  have h6 : retainingEnv 6 = some (.ref 0) := by simp [retainingEnv]
  have h10 : retainingEnv 10 = some (.scalar 0) := by simp [retainingEnv]
  simp only [putBackRetainingBody, Nested.runN, h4, h6, h10]
  rw [hcell]
  simp [childRetained, Env.set_other, h4]

/-- The write's slot: the child's field `0` is the parent reference. -/
theorem putBack_retaining_slot : childRetained.fields[0]? = some (.ref 0) :=
  Array.getElem?_setIfInBounds_self_of_lt
    (by simp [childObj, OwnershipTest.CountedPair.childObj])

/-- The write changes no count: the parent and the child are at their boundary
counts after the retention. -/
theorem putBack_retaining_counts :
    (B.set 1 childRetained).rc 0 = B.rc 0 ∧ (B.set 1 childRetained).rc 1 = B.rc 1 := by
  refine ⟨?_, ?_⟩
  · rw [Heap.rc_set_other (H := B) (r := 1) (r' := 0) (o := childRetained) (by decide)]
  · rw [Heap.rc_set_self (H := B) (r := 1) (o := childRetained),
      CountedPair.rc_of_cells (H := B) (r := 1) (o := childObj) boundary0.child]
    rfl

/-- The retention case the contract has to exclude: the body is admitted, it runs
to `done` on the caller's environment, the child's slot holds the parent
reference, and no count moves. Beside `childCall0`. -/
theorem putBack_retaining_positive :
    Nested.runN putBackRetainingBody retainingEnv B =
        .done (B.set 1 childRetained) (retainingEnv.set 12 (.ref 1)) (.ref 1) [] ∧
      (B.set 1 childRetained).cells 1 = some childRetained ∧
      childRetained.fields[0]? = some (.ref 0) ∧
      (B.set 1 childRetained).rc 0 = B.rc 0 ∧
      (B.set 1 childRetained).rc 1 = B.rc 1 :=
  ⟨putBack_retaining_run, Heap.set_self B 1 childRetained, putBack_retaining_slot,
    putBack_retaining_counts.1, putBack_retaining_counts.2⟩

/-- The operands the isolated environment hands this body: the child at the array
variable, the index scalar at variable `10`, and the parent's variable `6` dead.
The index is therefore not the missing operand. -/
theorem putBack_retaining_operands :
    (Nested.isolateEnv retainingEnv 4 10 11) 4 = some (.ref 1) ∧
      (Nested.isolateEnv retainingEnv 4 10 11) 6 = none ∧
      (Nested.isolateEnv retainingEnv 4 10 11) 10 = some (.scalar 0) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [Nested.isolateEnv, retainingEnv]

/-- Under the isolated environment the retention body cannot run. The model's
put-back arm labels any missing operand with its first operand, so the fault term
is `.badVar 4`; `putBack_retaining_operands` shows that the array operand and the
index are both bound and that only the value operand — the parent's variable `6`
— is dead, so the retention is stopped by the parent reference being
unnameable. -/
theorem putBack_retaining_faults :
    Nested.runN putBackRetainingBody (Nested.isolateEnv retainingEnv 4 10 11) B =
      .fault B (Nested.isolateEnv retainingEnv 4 10 11) (.badVar 4) [] := by
  obtain ⟨h4, h6, h10⟩ := putBack_retaining_operands
  simp only [putBackRetainingBody, Nested.runN, h4, h6, h10]

/-- The retention body produces no outcome at all, so it cannot satisfy the call
boundary's `outcome` field. -/
theorem putBack_retaining_no_outcome (Hout : Heap) :
    ¬ ∃ envb ws,
      Nested.runN putBackRetainingBody (Nested.isolateEnv retainingEnv 4 10 11) B =
        .done Hout envb (.ref 1) ws := by
  rintro ⟨envb, ws, hrun⟩
  rw [putBack_retaining_faults] at hrun
  cases hrun

/-- A put-back-shaped body whose destination operand is the parent's variable: it
would write into the parent's own cell. -/
def putBackParentBody : Nested.NCode := .putBack 6 4 10 12 (.ret 4)

/-- Its operands under the isolated environment: the destination (variable `6`,
the parent) is dead, while the value and the index are bound. -/
theorem putBack_parent_operands :
    (Nested.isolateEnv retainingEnv 4 10 11) 6 = none ∧
      (Nested.isolateEnv retainingEnv 4 10 11) 4 = some (.ref 1) ∧
      (Nested.isolateEnv retainingEnv 4 10 11) 10 = some (.scalar 0) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [Nested.isolateEnv, retainingEnv]

/-- With the dead parent variable as the first operand, the model's put-back fault
names it: `.badVar 6`. This is the same dead variable as the retention body's
value operand, seen from the arm's labelling position. -/
theorem putBack_parent_faults :
    Nested.runN putBackParentBody (Nested.isolateEnv retainingEnv 4 10 11) B =
      .fault B (Nested.isolateEnv retainingEnv 4 10 11) (.badVar 6) [] := by
  obtain ⟨h6, h4, h10⟩ := putBack_parent_operands
  simp only [putBackParentBody, Nested.runN, h6, h4, h10]

/-- A body that stores the parent reference into the child's slot is excluded by
the call boundary itself: the boundary requires a successful run from the
isolated environment, and this body has none. -/
theorem putBack_retaining_excluded (Hout : Heap) (ctx : Ctx) :
    ¬ ChildCall B Hout retainingEnv ctx 4 10 11 putBackRetainingBody 0 1 := by
  intro h
  exact putBack_retaining_no_outcome Hout h.runs

/-- A child cell that holds the parent reference: a body could reach the parent
through a reference write, which no increment-free check would catch. -/
def retainedChildObj : Obj := ⟨#[.ref 0, .scalar 0], 1, false⟩

/-- The retaining heap: the boundary parent at `0`, the child at `1` whose slot
names the parent. -/
def Hret : Heap :=
  { cells := fun r =>
      if r = 0 then some (parentAfter parentObj 0)
      else if r = 1 then some retainedChildObj
      else none
    next := 2 }

theorem Hret_cells_zero : Hret.cells 0 = some (parentAfter parentObj 0) := by simp [Hret]

theorem Hret_cells_one : Hret.cells 1 = some retainedChildObj := by simp [Hret]

theorem retained_child_not_persistent : retainedChildObj.persistent = false := rfl

theorem retained_parent_not_persistent :
    (parentAfter parentObj 0).persistent = false := by
  simp [parentAfter, parentObj, OwnershipTest.CountedPair.parentObj]

/-- The parent is inside the child's mutable footprint. -/
theorem retained_mem : Ownership.Entry.MutableFootprint Hret 1 0 :=
  Ownership.Entry.MutableFootprint.step (r := 1) (o := retainedChildObj) (r' := 0)
    (o' := parentAfter parentObj 0)
    (Ownership.Entry.MutableFootprint.root Hret_cells_one retained_child_not_persistent)
    Hret_cells_one retained_child_not_persistent
    (by simp [Entry.fieldRefs, Entry.refsOf, retainedChildObj])
    Hret_cells_zero retained_parent_not_persistent

/-- A heap where the parent is reachable from the child has no call boundary: the
separation premise fails, so the reference-write retention is excluded by the
contract rather than by the increment check. Beside `childCall0`. -/
theorem retained_parent_excluded (Hout : Heap) (env : Env) (ctx : Ctx)
    (state path x : Var) :
    ¬ ChildCall Hret Hout env ctx state path x putBackRetainingBody 0 1 :=
  retention_separation_fails retained_mem

/-! ## The persistent parent control -/

/-- The boundary parent fields with the persistence flag set: never exclusive. -/
def persistentObj : Obj := { parentAfter parentObj 0 with persistent := true, rc := 2 }

/-- The persistent-parent heap with fresh name `2`. -/
def Hps : Heap :=
  { cells := fun r =>
      if r = 0 then some persistentObj else if r = 1 then some childObj else none
    next := 2 }

/-- A persistent parent has no in-place branch: it copies, leaving the alias's
contents and one fewer reference. Beside `exclusive_restoration`. -/
theorem persistent_control :
    disposition? Hps 0 0 = some .copy ∧
      putBack Hps 0 0 1 = some (copy Hps 0 persistentObj 0 1) ∧
      (copy Hps 0 persistentObj 0 1).1 = Hps.next ∧
      (copy Hps 0 persistentObj 0 1).2.cells 0 = some { persistentObj with rc := 1 } := by
  have hcell : Hps.cells 0 = some persistentObj := by simp [Hps]
  have hlt : 0 < persistentObj.fields.size := by
    simp [persistentObj, parentAfter, parentObj, OwnershipTest.CountedPair.parentObj]
  have hpers : persistentObj.persistent = true := rfl
  have hpn : (0 : Ref) ≠ Hps.next := by decide
  exact persistent_parent_copies hcell hlt hpers hpn

/-- The same parent fields at count one with the flag cleared: the mutate branch.
Only the count and the flag separate this from `persistent_control`. -/
def Huniq : Heap :=
  { cells := fun r =>
      if r = 0 then some (parentAfter parentObj 0)
      else if r = 1 then some childObj
      else none
    next := 2 }

theorem unique_pair_positive : disposition? Huniq 0 0 = some .mutate := by
  have hcell : Huniq.cells 0 = some (parentAfter parentObj 0) := by simp [Huniq]
  have hlt : 0 < (parentAfter parentObj 0).fields.size := by
    simp [parentAfter, parentObj, OwnershipTest.CountedPair.parentObj]
  exact disposition_mutate_of_inPlace
    (inPlace_of_exclusive hcell rfl rfl hlt)

#print axioms Ownership.PutBack.inPlace?_eq_true
#print axioms Ownership.PutBack.disposition_mutate_of_inPlace
#print axioms Ownership.PutBack.disposition_copy_of_not_inPlace
#print axioms Ownership.PutBack.putBack_eq_mutate
#print axioms Ownership.PutBack.putBack_eq_copy
#print axioms Ownership.PutBack.restorationBoundary_of_entry
#print axioms Ownership.PutBack.restorationBoundary_of_wellFormed
#print axioms Ownership.PutBack.putBack_mutate_of_boundary
#print axioms Ownership.PutBack.restoration_functional
#print axioms Ownership.PutBack.restoration_counts
#print axioms Ownership.PutBack.putBack_exclusive
#print axioms Ownership.PutBack.putBack_exclusive_of_wellFormed
#print axioms Ownership.PutBack.copy_result
#print axioms Ownership.PutBack.shared_parent_copies
#print axioms Ownership.PutBack.persistent_parent_copies
#print axioms Ownership.PutBack.retained_parent_copies
#print axioms Ownership.PutBack.mutate_eq_model
#print axioms Ownership.PutBack.ChildCall.confined
#print axioms Ownership.PutBack.ChildCall.parent
#print axioms Ownership.PutBack.ChildCall.writes_exclusive
#print axioms Ownership.PutBack.ChildCall.parent_live
#print axioms Ownership.PutBack.ChildCall.parent_rc
#print axioms Ownership.PutBack.retention_separation_fails
#print axioms Ownership.PutBack.not_childCall_of_not_countFree
#print axioms OwnershipTest.PutBack.boundary0
#print axioms OwnershipTest.PutBack.body_runs_isolated
#print axioms OwnershipTest.PutBack.childChecked
#print axioms OwnershipTest.PutBack.childInv
#print axioms OwnershipTest.PutBack.childCall0
#print axioms OwnershipTest.PutBack.putBack_retaining_positive
#print axioms OwnershipTest.PutBack.putBack_retaining_run
#print axioms OwnershipTest.PutBack.putBack_retaining_operands
#print axioms OwnershipTest.PutBack.putBack_retaining_faults
#print axioms OwnershipTest.PutBack.putBack_parent_faults
#print axioms OwnershipTest.PutBack.putBack_retaining_no_outcome
#print axioms OwnershipTest.PutBack.putBack_retaining_excluded
#print axioms OwnershipTest.PutBack.retained_parent_excluded
#print axioms OwnershipTest.PutBack.exclusive_restoration
#print axioms OwnershipTest.PutBack.exclusive_restoration_from_entry
#print axioms OwnershipTest.PutBack.shared_control
#print axioms OwnershipTest.PutBack.persistent_control

end OwnershipTest.PutBack
