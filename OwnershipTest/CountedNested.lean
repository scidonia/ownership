/-
Concrete fixtures for the counted extraction/call/restoration chain.

`H0` is `OwnershipTest.CountedPair`'s unique entry: the parent array at `ref 0`
holds the child `ref 1` in slot `0`, both cells are non-persistent at count one,
and the fresh name `ref 2` is empty. The caller's context is the one the
checker's take-out rule produces: the array's handle moves to variable `2`, the
extracted element's handle is bound as an owned variable `3`, and the
environment binds those variables to `ref 0` and `ref 1`.

The controls are ordered affirmative first:

* `entryAccounted` accounts the entry;
* `boundary_cells` asserts the boundary's heap facts: the pair cell is absent,
  the cursor advanced to `3`, both components are live at count one, and the
  parent's selected slot holds the placeholder;
* `pairPhase_refused` is the kernel refusal that the pair-live state is not
  accounted at the run's own take-out context, which is why the boundary
  formulation is forced rather than chosen;
* `counted_retained_copies` runs the copy branch at the counted level on a
  parent at count two, beside `boundary_cells`' mutate positive.

These are heap calculations, not runtime or backend claims.
-/
import Ownership.CountedNested
import OwnershipTest.CountedPair
import OwnershipTest.PutBack

open Ownership
open Ownership.CountedPair

namespace OwnershipTest.CountedNested

abbrev parentObj : Obj := OwnershipTest.CountedPair.parentObj
abbrev childObj : Obj := OwnershipTest.CountedPair.childObj
abbrev H0 : Heap := OwnershipTest.CountedPair.H0
abbrev parentAfterObj : Obj := OwnershipTest.CountedPair.parentAfterObj

/-! ## Computable heap guards, affirmative first -/

-- the boundary: the pair cell is released and the cursor advanced
#guard ((protocol H0 0 1 0).2.cells 2).isNone
#guard (protocol H0 0 1 0).2.next == 3
#guard (protocol H0 0 1 0).2.rc 0 == 1
#guard (protocol H0 0 1 0).2.rc 1 == 1
-- the omitted release: the pair cell is still live at the entry's fresh name
#guard ((protocolNoFree H0 0 1 0).2.cells 2).isSome

theorem H0_cells_0 : H0.cells 0 = some parentObj := by
  simp [H0, OwnershipTest.CountedPair.H0]

theorem H0_cells_1 : H0.cells 1 = some childObj := by
  simp [H0, OwnershipTest.CountedPair.H0]

theorem H0_cells_other {r : Ref} (h0 : r ≠ 0) (h1 : r ≠ 1) : H0.cells r = none := by
  simp [H0, OwnershipTest.CountedPair.H0, h0, h1]

theorem H0_rc_0 : H0.rc 0 = 1 := by
  rw [rc_of_cells H0_cells_0]
  rfl

theorem H0_rc_1 : H0.rc 1 = 1 := by
  rw [rc_of_cells H0_cells_1]
  rfl

/-! ## The boundary's heap facts -/

/-- The protocol boundary on `H0`: the pair is gone, the cursor advanced, both
components are live at count one, and the parent's slot holds the placeholder.
The positive control for the copy branch below. -/
theorem boundary_cells :
    (protocol H0 0 1 0).2.cells 2 = none ∧
      (protocol H0 0 1 0).2.next = 3 ∧
      (protocol H0 0 1 0).2.rc 0 = 1 ∧
      (protocol H0 0 1 0).2.rc 1 = 1 ∧
      (protocol H0 0 1 0).2.cells 0 = some parentAfterObj ∧
      (protocol H0 0 1 0).2.cells 1 = some childObj := by
  have hb := OwnershipTest.CountedPair.counted_pair_boundary
  obtain ⟨-, hrc0, hrc1, hcell0, hcell1, hpair, -, -⟩ := hb
  have hnext : (protocol H0 0 1 0).2.next = 3 := by
    rw [protocol_next (H := H0) (p := 0) (c := 1) (i := 0) (by decide) (by decide)]
    rfl
  exact ⟨hpair, hnext, hrc0, hrc1, hcell0, hcell1⟩

/-- The boundary's accounting, at the take-out context the checker produces: two
owning variables, one per component, each at count one with no heap edge into it
(the selected slot holds the placeholder). -/
theorem boundary_parent_cell :
    (protocol H0 0 1 0).2.cells 0 =
      some { parentObj with fields := parentObj.fields.setIfInBounds 0 (.scalar 0) } :=
  boundary_cells.2.2.2.2.1

/-! ## The entry's incoming-edge counts -/

/-- The entry's edge count at the parent is zero. -/
theorem incoming_H0_zero : IncomingCount H0 0 = 0 := by
  rw [IncomingCount_eq_edges]
  decide

/-- The entry's edge count at the child is the parent's selected slot. -/
theorem incoming_H0_one : IncomingCount H0 1 = 1 := by
  rw [IncomingCount_eq_edges]
  decide

/-- Every other reference has no incoming edge at the entry. -/
theorem incoming_H0_other {r : Ref} (h0 : r ≠ 0) (h1 : r ≠ 1) :
    IncomingCount H0 r = 0 := by
  rw [IncomingCount_eq_edges]
  have hparent : RefCount parentObj.fields r = 0 := by
    unfold RefCount
    rw [show parentObj.fields.toList = [.ref 1, .scalar 0] from rfl]
    simp [Val.ref.injEq]
    exact fun hh => h1 hh.symm
  have hchild : RefCount childObj.fields r = 0 := by
    unfold RefCount
    rw [show childObj.fields.toList = [.scalar 0] from rfl]
    simp
  simp [List.range_succ, EdgeAt, H0, OwnershipTest.CountedPair.H0, hparent, hchild, h0, h1]

/-- The caller's context: the array's handle is at variable `0`. -/
def entryCtx : Ctx :=
  { us := fun x => if x = 0 then .owned else .dead
    refOf := fun x => if x = 0 then some 0 else none
    mult := fun r => H0.rc r }

/-- The caller's environment: variable `0` denotes the array, and the child
call's path and value arguments are scalars. -/
def entryEnv : Env :=
  fun x => if x = 0 then some (.ref 0)
           else if x = 10 then some (.scalar 0)
           else if x = 11 then some (.scalar 7)
           else none

/-! ## The entry is accounted -/

/-- The caller's invariant: the array's variable is the only owning one. -/
theorem entryInv : Inv H0 entryEnv entryCtx where
  rc_eq r := rfl
  owned := by
    intro x r hx hr
    by_cases hx0 : x = 0
    · subst hx0
      have hr0 : (0 : Ref) = r := Option.some.inj (by simpa [entryCtx] using hr)
      subst hr0
      refine ⟨by simp [entryEnv], ?_⟩
      show 1 ≤ H0.rc 0
      rw [H0_rc_0]
      decide
    · simp [entryCtx, hx0] at hx
  borrow := by
    intro x r hx _
    by_cases hx0 : x = 0
    · subst hx0
      simp [entryCtx] at hx
    · simp [entryCtx, hx0] at hx
  scalar := by
    intro x hx
    by_cases hx0 : x = 0
    · subst hx0
      simp [entryCtx] at hx
    · simp [entryCtx, hx0] at hx
  nonPersistent := by
    intro r o hc
    by_cases hr0 : r = 0
    · subst hr0; rw [H0_cells_0] at hc; injection hc with h; subst h; rfl
    · by_cases hr1 : r = 1
      · subst hr1; rw [H0_cells_1] at hc; injection hc with h; subst h; rfl
      · rw [H0_cells_other hr0 hr1] at hc; exact absurd hc (by simp)

theorem envOwner_zero : EnvOwnerCount entryCtx [0] 0 = 1 := by
  simp [EnvOwnerCount, entryCtx]

theorem envOwner_one : EnvOwnerCount entryCtx [0] 1 = 0 := by
  simp [EnvOwnerCount, entryCtx]

theorem envOwner_other {r : Ref} (h0 : r ≠ 0) :
    EnvOwnerCount entryCtx [0] r = 0 := by
  simp [EnvOwnerCount, entryCtx]
  exact fun hh => h0 hh.symm

/-- The entry is accounted: one owning variable and one heap edge into the
child. -/
theorem entryAccounted : Accounted [0] H0 entryEnv entryCtx := by
  refine
    { inv := entryInv
      support_nodup := List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩
      support_sound := ?_
      support_complete := ?_
      support_bound := ?_
      domain := ?_
      count := ?_ }
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    simp [entryCtx]
  · intro x hx
    by_cases hx0 : x = 0
    · subst hx0; simp
    · simp [entryCtx, hx0] at hx
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    exact ⟨0, by simp [entryCtx]⟩
  · intro r o hc
    by_cases hr0 : r = 0
    · subst hr0; rw [H0_cells_0] at hc; injection hc with h; subst h; decide
    · by_cases hr1 : r = 1
      · subst hr1; rw [H0_cells_1] at hc; injection hc with h; subst h; decide
      · rw [H0_cells_other hr0 hr1] at hc; exact absurd hc (by simp)
  · intro r
    by_cases hr0 : r = 0
    · subst hr0
      rw [H0_rc_0, incoming_H0_zero, envOwner_zero]
    · by_cases hr1 : r = 1
      · subst hr1
        rw [H0_rc_1, incoming_H0_one, envOwner_one]
      · have hz : H0.rc r = 0 := by
          rw [Heap.rc, H0_cells_other hr0 hr1]
          rfl
        rw [hz, incoming_H0_other hr0 hr1, envOwner_other hr0]

/-- The caller's boundary environment: the extracted handles. -/
def boundaryEnv : Env := (entryEnv.set 2 (.ref 0)).set 3 (.ref 1)

/-- The caller's boundary context: the checker's take-out rule's context. -/
def boundaryCtx : Ctx := (entryCtx.move 0 2).bindOwned 3 1

/-- The boundary is accounted, derived from the entry's accounting by the counted
take-out (`counted_takeOut`), not recomputed. -/
theorem boundaryAccounted :
    Accounted [3, 2] (protocol H0 0 1 0).2 boundaryEnv boundaryCtx := by
  have h := counted_takeOut (h := entryAccounted) (a := 0) (fst := 2) (snd := 3) (e := 1)
    (r := 0) (o := parentObj) (idx := 0)
    (by simp [entryCtx])
    (by simp [Ctx.multOf, entryCtx, H0_rc_0])
    (by simp [entryCtx])
    (by simpa [entryCtx] using H0_rc_1)
    (by simp [entryCtx])
    (by simp [entryCtx])
    (by decide) (by decide) H0_cells_0 (by decide)
  simpa [boundaryEnv, boundaryCtx, replaceVar] using h.1

/-! ## The accounting after the child call's leaf write -/

/-- The caller's accounting at the heap the child call leaves, computed directly:
the body's write is an in-place scalar store in the child's own cell, so
`Accounted.setFieldsScalar` carries the boundary's accounting across it. The
derived route is `countedBoundaryCall_accounted`, which reaches the same fact
from the boundary accounting and the call's edge effect. -/
theorem calledAccounted :
    Accounted [3, 2] OwnershipTest.PutBack.Hc boundaryEnv boundaryCtx := by
  have h := Accounted.setFieldsScalar (h := boundaryAccounted)
    (r := 1) (o := childObj) (idx := 0) (old := 0) (w := 7)
    (by simpa using boundary_cells.2.2.2.2.2) (by decide)
  simpa [OwnershipTest.PutBack.Hc, OwnershipTest.PutBack.B, OwnershipTest.PutBack.childAfter,
    Array.set!, childObj, parentObj] using h

/-- The call's edge effect at the boundary: the body rewrites the child's own
cell and the rewrite replaces a scalar with a scalar, so no `.ref` occurrence at
any name changes. -/
theorem boundaryEdges :
    EdgePreserved (protocol H0 0 1 0).2 OwnershipTest.PutBack.Hc :=
  EdgePreserved.set (H := (protocol H0 0 1 0).2) (r := 1) (o := childObj)
    (o' := OwnershipTest.PutBack.childAfter)
    (by simpa using boundary_cells.2.2.2.2.2)
    (fun q => by
      simpa [OwnershipTest.PutBack.childAfter] using
        (RefCount_setIfInBounds_scalar_scalar (fields := childObj.fields) (i := 0)
          (old := 0) (w := 7) (q := q) (by decide)).symm)

/-! ## The boundary heap's cells and counts -/

/-- The boundary's cells outside the entry's two live names are empty: the pair
cell is erased and every other cell is the entry's. -/
theorem B_cells_none {r : Ref} (h0 : r ≠ 0) (h1 : r ≠ 1) :
    (protocol H0 0 1 0).2.cells r = none := by
  by_cases h2 : r = 2
  · subst h2
    exact boundary_cells.1
  · have htraffic : (protocol H0 0 1 0).2 =
        pairFree (pairInc (takeOut H0 0 1 0).2 0 1) 0 1 2 := by
      show pairTraffic (takeOut H0 0 1 0).2 2 = _
      exact pairTraffic_takeOut (H := H0) (p := 0) (c := 1) (i := 0)
        (by decide) (by decide)
    rw [htraffic, pairFree_inc_cells_other h0 h1 h2]
    show (setPlaceholder (allocPair H0 0 1) 0 0).cells r = none
    rw [setPlaceholder_cells_other h0, allocPair_cells_other h2,
      H0_cells_other h0 h1]

/-- The boundary's stored counts are the entry's: the pair traffic is neutral. -/
theorem B_rc_eq (r : Ref) : (protocol H0 0 1 0).2.rc r = H0.rc r := by
  by_cases h0 : r = 0
  · subst h0
    rw [boundary_cells.2.2.1, H0_rc_0]
  · by_cases h1 : r = 1
    · subst h1
      rw [boundary_cells.2.2.2.1, H0_rc_1]
    · rw [Heap.rc, B_cells_none h0 h1, Heap.rc, H0_cells_other h0 h1]

/-! ## The pair-live state is not accounted -/

/-- The state just after the take-out, at the context the run's own take-out rule
produces, is not accounted at any support: the pair cell holds `.ref 0`, so the
parent has an incoming edge, while the caller's variable `2` is an owning handle
for that same reference — the count equation reads one = one plus one. The
positive control is `boundary_cells`: after the pair's release the counts match
again. -/
theorem pairPhase_refused (support : List Var) :
    ¬ Accounted support (takeOut H0 0 1 0).2
        ((entryEnv.set 2 (.ref 0)).set 3 (.ref 1)) ((entryCtx.move 0 2).bindOwned 3 1) := by
  intro h
  -- the pair cell is live and its first slot holds the parent's reference
  have hpair : (takeOut H0 0 1 0).2.cells 2 = some ⟨pairFields 0 1, 1, false⟩ :=
    takeOut_cells_pair (H := H0) (p := 0) (c := 1) (i := 0) (by decide)
  have hslot : (⟨pairFields 0 1, 1, false⟩ : Obj).fields[0]? = some (.ref 0) := by
    simp [pairFields]
  -- so the parent has at least one incoming edge
  have hinc : 1 ≤ IncomingCount (takeOut H0 0 1 0).2 0 :=
    h.IncomingCount_pos_of_slot hpair hslot
  -- and the caller's variable 2 is an owning handle for it
  have hus2 : ((entryCtx.move 0 2).bindOwned 3 1).us 2 = .owned := by
    rw [Ctx.bindOwned_us_other (c := entryCtx.move 0 2) (x := 3) (z := 2) (r := 1) (h := by decide),
      Ctx.move_us_y]
    simp [entryCtx]
  have href2 : ((entryCtx.move 0 2).bindOwned 3 1).refOf 2 = some 0 := by
    rw [Ctx.bindOwned_refOf_other (c := entryCtx.move 0 2) (x := 3) (z := 2) (r := 1) (h := by decide)]
    rw [Ctx.move_refOf_y]
    simp [entryCtx]
  have hmem : 2 ∈ support := h.support_complete 2 hus2
  have hfil : 2 ∈ support.filter (fun z =>
      (((entryCtx.move 0 2).bindOwned 3 1).us z = .owned ∧
        ((entryCtx.move 0 2).bindOwned 3 1).refOf z = some 0)) := by
    rw [List.mem_filter]
    exact ⟨hmem, by simp [entryCtx]⟩
  have hpos : 1 ≤ EnvOwnerCount ((entryCtx.move 0 2).bindOwned 3 1) support 0 :=
    List.length_pos_iff_exists_mem.mpr ⟨2, hfil⟩
  -- the parent's stored count is still one
  have hrc : (takeOut H0 0 1 0).2.rc 0 = 1 := by
    rw [rc_of_cells (takeOut_cells_parent (H := H0) (p := 0) (c := 1) (i := 0)
      (o := parentObj) H0_cells_0 (by decide))]
    rfl
  have hcount := h.count 0
  rw [hrc] at hcount
  omega

/-! ## The copy branch at the counted level -/

/-- A parent at count two is not exclusive, so the restoration copies: the result
is the fresh name and the old parent keeps its contents at one fewer reference.
The positive control is `boundary_cells`' count-one restoration. -/
theorem counted_retained_copies :
    PutBack.disposition? (H0.inc 0 1) 0 0 = some .copy ∧
      (PutBack.copy (H0.inc 0 1) 0 { parentObj with rc := 2 } 0 1).1 = 2 ∧
      (PutBack.copy (H0.inc 0 1) 0 { parentObj with rc := 2 } 0 1).2.cells 1 =
        some childObj := by
  have hcell : (H0.inc 0 1).cells 0 = some { parentObj with rc := 2 } :=
    inc_cells_self (H := H0) (r := 0) (n := 1) (o := parentObj) H0_cells_0
  have hnext : (H0.inc 0 1).next = 2 := by
    rw [PutBack.inc_next]
    rfl
  obtain ⟨hdisp, -, hfresh, -, -⟩ :=
    PutBack.shared_parent_copies (H := H0.inc 0 1) (p := 0) (c := 1) (i := 0)
      (o := { parentObj with rc := 2 }) hcell (by decide) rfl
      (by rw [hnext]; decide)
  refine ⟨hdisp, ?_, ?_⟩
  · rw [hfresh, hnext]
  · obtain ⟨-, -, -, hother, -, -⟩ :=
      PutBack.copy_result (H := H0.inc 0 1) (p := 0) (c := 1) (i := 0)
        (o := { parentObj with rc := 2 }) hcell (by rw [hnext]; decide)
    rw [hother 1 (by decide) (by rw [hnext]; decide)]
    exact H0_cells_1

/-! ## The boundary child call and the counted contract -/

/-- The child body in the chain's variable layout: the state is the extracted
child variable `3`, and the body writes the child's own slot `0`. -/
def boundaryBody : Nested.NCode := .base (.setArr 3 10 11 (.ret 3))

theorem boundaryBody_admitted : Nested.CountFree boundaryBody = true := rfl

theorem boundaryBody_retVar : Nested.retVar boundaryBody = some 3 := rfl

/-- The child's mutable footprint is the child alone, so the parent is outside
it (`OwnershipTest/PutBack.lean`'s proof, at this context's state). -/
theorem boundarySeparated : ¬ Entry.MutableFootprint (protocol H0 0 1 0).2 1 0 :=
  OwnershipTest.PutBack.childSeparated

/-- The caller's invariant on the isolated environment at the boundary. -/
theorem boundaryInv :
    Inv (protocol H0 0 1 0).2 (Nested.isolateEnv boundaryEnv 3 10 11)
      (Nested.isolatedCtx boundaryCtx 3 10 11 1) where
  rc_eq r := B_rc_eq r
  owned := by
    intro x r hx hr
    have hx3 : x = 3 := by
      by_cases h3 : x = 3
      · exact h3
      · by_cases h10 : x = 10
        · subst h10; simp [Nested.isolatedCtx, h3] at hx
        · by_cases h11 : x = 11
          · subst h11; simp [Nested.isolatedCtx, h3, h10] at hx
          · simp [Nested.isolatedCtx, h3, h10, h11] at hx
    subst hx3
    have hr1 : (1 : Ref) = r := Option.some.inj (by simpa [Nested.isolatedCtx] using hr)
    subst hr1
    refine ⟨by simp [Nested.isolateEnv, boundaryEnv, entryEnv], ?_⟩
    show 1 ≤ H0.rc 1
    rw [H0_rc_1]
    decide
  borrow := by
    intro x r hx _
    by_cases h3 : x = 3
    · subst h3; simp [Nested.isolatedCtx] at hx
    · by_cases h10 : x = 10
      · subst h10; simp [Nested.isolatedCtx, h3] at hx
      · by_cases h11 : x = 11
        · subst h11; simp [Nested.isolatedCtx, h3, h10] at hx
        · simp [Nested.isolatedCtx, h3, h10, h11] at hx
  scalar := by
    intro x hx
    by_cases h3 : x = 3
    · subst h3; simp [Nested.isolatedCtx] at hx
    · by_cases h10 : x = 10
      · subst h10
        exact ⟨0, by simp [Nested.isolateEnv, boundaryEnv, entryEnv]⟩
      · by_cases h11 : x = 11
        · subst h11
          exact ⟨7, by simp [Nested.isolateEnv, boundaryEnv, entryEnv]⟩
        · simp [Nested.isolatedCtx, h3, h10, h11] at hx
  nonPersistent := by
    intro r o hc
    by_cases h0 : r = 0
    · subst h0
      rw [boundary_cells.2.2.2.2.1] at hc
      injection hc with h; subst h; rfl
    · by_cases h1 : r = 1
      · subst h1
        rw [boundary_cells.2.2.2.2.2] at hc
        injection hc with h; subst h; rfl
      · rw [B_cells_none h0 h1] at hc
        exact absurd hc (by simp)

/-- The checker admits the body from the boundary's isolated context. -/
theorem boundaryChecked :
    ∃ cb, Nested.checkNF (Nested.isolatedCtx boundaryCtx 3 10 11 1) [] boundaryBody = some cb ∧
      ∃ y, Nested.retVar boundaryBody = some y ∧ cb.us y = .owned ∧
        cb.refOf y = some 1 := by
  refine ⟨Nested.isolatedCtx boundaryCtx 3 10 11 1, ?_, 3, rfl, ?_, ?_⟩
  · simp [boundaryBody, Nested.checkNF, Ownership.check, Nested.isolatedCtx,
      Ownership.Ctx.multOf]
    show H0.rc 1 = 1
    rw [H0_rc_1]
  · simp [Nested.isolatedCtx]
  · simp [Nested.isolatedCtx]

/-- The body runs from the isolated environment on the boundary heap. -/
theorem boundaryBody_runs :
    Nested.runN boundaryBody (Nested.isolateEnv boundaryEnv 3 10 11)
        (protocol H0 0 1 0).2 =
      .done OwnershipTest.PutBack.Hc
        ((Nested.isolateEnv boundaryEnv 3 10 11).set 3 (.ref 1)) (.ref 1) [(1, true)] := by
  have hcell : (protocol H0 0 1 0).2.cells 1 = some childObj := boundary_cells.2.2.2.2.2
  have hex : (protocol H0 0 1 0).2.exclusive? 1 = true :=
    (Heap.exclusive?_eq_true).mpr ⟨childObj, hcell, rfl, rfl⟩
  have h3 : Nested.isolateEnv boundaryEnv 3 10 11 3 = some (.ref 1) := by
    simp [Nested.isolateEnv, boundaryEnv, entryEnv]
  have h10 : Nested.isolateEnv boundaryEnv 3 10 11 10 = some (.scalar 0) := by
    simp [Nested.isolateEnv, boundaryEnv, entryEnv]
  have h11 : Nested.isolateEnv boundaryEnv 3 10 11 11 = some (.scalar 7) := by
    simp [Nested.isolateEnv, boundaryEnv, entryEnv]
  simp only [boundaryBody, Nested.runN, Ownership.run, h3, h10, h11]
  rw [hcell]
  simp [hex, OwnershipTest.PutBack.Hc, OwnershipTest.PutBack.B,
    OwnershipTest.PutBack.childAfter, Ownership.Res.addWrite, Array.set!]

/-- The child-call boundary at the caller's boundary environment and context. -/
theorem boundaryCall :
    PutBack.ChildCall (protocol H0 0 1 0).2 OwnershipTest.PutBack.Hc boundaryEnv
      boundaryCtx 3 10 11 boundaryBody 0 1 where
  admitted := boundaryBody_admitted
  checked := boundaryChecked
  inv := boundaryInv
  annotations := trivial
  extraction := trivial
  separated := boundarySeparated
  outcome := ⟨(Nested.isolateEnv boundaryEnv 3 10 11).set 3 (.ref 1), [(1, true)],
    boundaryBody_runs⟩
  child_rc := by
    show OwnershipTest.PutBack.Hc.rc 1 = (protocol H0 0 1 0).2.rc 1
    rw [OwnershipTest.PutBack.Hc, Heap.rc_set_self]
    rw [rc_of_cells boundary_cells.2.2.2.2.2]
    rfl
  child_persistent := by
    show OwnershipTest.PutBack.Hc.isPersistent 1 = (protocol H0 0 1 0).2.isPersistent 1
    rw [OwnershipTest.PutBack.Hc, OwnershipTest.PutBack.B,
      PutBack.isPersistent_of_cells (H := (protocol H0 0 1 0).2.set 1 OwnershipTest.PutBack.childAfter)
        (r := 1) (o := OwnershipTest.PutBack.childAfter) (Heap.set_self _ _ _),
      PutBack.isPersistent_of_cells (H := (protocol H0 0 1 0).2) (r := 1) (o := childObj)
        boundary_cells.2.2.2.2.2]
    rfl

/-- The counted child-call contract at the boundary: the boundary's call and the
call's edge effect. This is the witness that `counted_nested_chain`'s `hcall` is
inhabited. -/
theorem countedBoundaryCall :
    CountedChildCall (protocol H0 0 1 0).2 OwnershipTest.PutBack.Hc boundaryEnv
      boundaryCtx 3 10 11 boundaryBody 0 1 [3, 2] where
  call := boundaryCall
  edges := boundaryEdges

/-- The caller's accounting at the body's return, derived from the boundary
accounting and the call's edge effect. Its type is `calledAccounted`'s, whose
direct proof is the independent computation of the same fact. -/
theorem countedBoundaryCall_accounted :
    Accounted [3, 2] OwnershipTest.PutBack.Hc boundaryEnv boundaryCtx :=
  countedBoundaryCall.accounted_of boundaryAccounted

/-- The contract's result binding at the boundary: the state's handle moves to
the result variable and the accounting follows it. -/
theorem countedBoundaryCall_move :
    Accounted (replaceVar [3, 2] 3 12) OwnershipTest.PutBack.Hc
      (boundaryEnv.set 12 (.ref 1)) (boundaryCtx.move 3 12) :=
  countedBoundaryCall.move boundaryAccounted (result := 12)
    (by simp [boundaryCtx, Ctx.bindOwned]) (by simp [boundaryCtx, Ctx.bindOwned])
    (by simp [boundaryCtx, Ctx.bindOwned, entryCtx])

/-! ## The edge effect is not a consequence of the call boundary -/

/-- The same-shaped child cell whose selected slot holds a reference to a cell
the caller owns at count two. -/
def leakyChild : Obj := ⟨#[.ref 2, .scalar 0], 1, false⟩

/-- The child cell after the body's scalar write over that reference slot. -/
def leakyAfter : Obj := { leakyChild with fields := leakyChild.fields.setIfInBounds 0 (.scalar 7) }

/-- The entry heap: the child cell at `1` and the referenced cell at `2`. -/
def leakyHin : Heap :=
  { cells := fun r =>
      if r = 1 then some leakyChild
      else if r = 2 then some ⟨#[.scalar 0], 2, false⟩
      else none
    next := 3 }

/-- The heap after the scalar-over-reference store. -/
def leakyHout : Heap := leakyHin.set 1 leakyAfter

theorem leaky_incoming : IncomingCount leakyHin 2 = 1 := by
  rw [IncomingCount_eq_edges]; decide

theorem leaky_incoming_after : IncomingCount leakyHout 2 = 0 := by
  rw [IncomingCount_eq_edges]; decide

/-- The scalar-over-reference store is not edge-preserving: the caller-owned
cell at `2` loses its only incoming edge. This is the negative control beside
`boundaryEdges`, and the reason `CountedChildCall` carries the edge effect rather
than deriving it from the boundary: the store is in the child's own cell, inside
its mutable footprint, and changes no stored count. -/
theorem leaky_not_edgePreserved : ¬ EdgePreserved leakyHin leakyHout := by
  intro h
  have hin := h.incoming 2
  rw [leaky_incoming_after, leaky_incoming] at hin
  exact absurd hin (by decide)

#print axioms Ownership.counted_takeOut
#print axioms Ownership.Accounted.of_compat
#print axioms Ownership.HeapCompat.IncomingCount
#print axioms Ownership.runN_compat
#print axioms Ownership.counted_nested_chain
#print axioms Ownership.counted_restore
#print axioms Ownership.restorationBoundary_of_accounted
#print axioms boundary_cells
#print axioms boundary_parent_cell
#print axioms pairPhase_refused
#print axioms entryAccounted
#print axioms boundaryAccounted
#print axioms calledAccounted
#print axioms boundaryCall
#print axioms boundaryEdges
#print axioms countedBoundaryCall
#print axioms countedBoundaryCall_accounted
#print axioms countedBoundaryCall_move
#print axioms leaky_not_edgePreserved
#print axioms counted_retained_copies

end OwnershipTest.CountedNested
