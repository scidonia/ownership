/-
The counted family of one-level take-out / child call / restoration instances.

The family's entry heap `famHeap n i` has two live non-persistent cells at count
one and the fresh name `2`: the parent at `ref 0` is an `n`-slot array whose slot
`i` holds the child, and the child at `ref 1` is an `n`-slot array of scalars.
The caller's context owns the parent through variable `0`; the parent's index
argument is variable `10` holding the outer slot `i`, the leaf's index argument
is variable `14` holding the leaf slot `j`, and the value argument is variable
`11` holding `w`. The child body is the single designated write
`.base (.setArr 3 14 11 (.ret 3))`: it writes the child's own slot `j` with
`.scalar w` and returns the child handle.

What is proved, for every outer slot `i` with `i < n`, leaf slot `j` with
`j < n`, and written value `w`:

* the entry is accounted (`entryAccounted`);
* the protocol boundary's cells, cursor, counts and accounting
  (`boundary_cells`, `boundary_accounted`);
* the child-call contract with the caller's accounting at the body's return
  (`countedBoundaryCall`);
* the whole counted chain, `Ownership.counted_nested_chain`, at the family's
  data (`family_chain`), with five of its conjuncts also named by their own
  projection theorems, and the statement formed from the chain's conclusion
  conjunct for conjunct;
* the chain's net entry-to-output edge effect,
  `Ownership.counted_nested_chain_edges`, at the same data (`family_chain_edges`),
  with `IncomingCount_fam_final_one` reading the identity off at the extracted
  child. This is the `edges` field an enclosing call would consume.

`family_chain` is the length-`n` version and `family_chain_two` its `n := 2`
application: the parent's and the child's field arrays then both have length two,
and the parameters are the outer slot, the leaf slot and the written value. The
bound hypotheses `i < n` and `j < n` are the only length facts the proof uses:
the slot facts are `Array.getElem?_setIfInBounds_self_of_lt`, and the count
equation combines the take-out's edge-fill lemmas (`IncomingCount_set_fill`,
`IncomingCount_set_fill_ne`) with the base heap's zero edge count
(`IncomingCount_baseHeap`), which follows from `Accounted.RefCount_initFields` at
every `n`, so nothing depends on the value of `n` beyond those bounds.

What is not claimed: no runtime or backend statement, no emitted callee, and no
heap equality against an abstract run — the chain's own `HeapCompat` conjunct is
carried, not an equality. The controls above the proofs are computable heap
calculations: the affirmative guards read the boundary state and the child's
unwritten slot, and the one refusal guard reads the slot the leaf writes.

The controls are ordered affirmative first.
-/
import Ownership.CountedNested

open Ownership
open Ownership.CountedPair

namespace OwnershipTest.CountedFamily

/-! ## The family's field arrays and cells -/

/-- The all-scalar field array of length `n`. -/
def baseFields (n : Nat) : Array Val := Array.replicate n (.scalar 0)

/-- The parent's field array: the all-scalar array with slot `i` holding the child. -/
def parentFields (n i : Nat) : Array Val := (baseFields n).setIfInBounds i (.ref 1)

/-- The all-scalar cell the base heap is built from. -/
def scalarObj (n : Nat) : Obj := ⟨baseFields n, 1, false⟩

/-- The parent cell: the all-scalar cell whose slot `i` holds the child. -/
def parentObj (n i : Nat) : Obj := { scalarObj n with fields := parentFields n i }

/-- The child cell at the entry: every slot is a scalar. -/
abbrev childObj (n : Nat) : Obj := scalarObj n

/-- The all-scalar heap the family is built from: the two cells at count one and
the fresh name `2`. -/
def baseHeap (n : Nat) : Heap :=
  { cells := fun r =>
      if r = 0 then some (scalarObj n) else if r = 1 then some (scalarObj n) else none
    next := 2 }

/-- The family's entry heap: the base heap with the parent's slot `i` filled by
the child handle. -/
def famHeap (n i : Nat) : Heap := (baseHeap n).set 0 (parentObj n i)

/-- The child cell after the leaf's write of the slot `j` with `w`. -/
def childAfter (n j w : Nat) : Obj :=
  { childObj n with fields := (childObj n).fields.setIfInBounds j (.scalar w) }

/-- The protocol boundary heap of the family's take-out. -/
def B (n i : Nat) : Heap := (CountedPair.protocol (famHeap n i) 0 1 i).2

/-- The heap the child call leaves. -/
def Hc (n i j w : Nat) : Heap := (B n i).set 1 (childAfter n j w)

/-! ## The family's variables and program -/

/-- The parent's owning variable. -/
def parentVar : Var := 0
/-- The parent's take-out index variable. -/
def idxVar : Var := 10
/-- The leaf's index variable. -/
def leafIdxVar : Var := 14
/-- The leaf's value variable. -/
def valueVar : Var := 11
/-- The take-out's array target. -/
def fstVar : Var := 2
/-- The take-out's element target, the child call's state. -/
def childVar : Var := 3
/-- The child call's result variable. -/
def resultVar : Var := 12
/-- The put-back's restored-array variable. -/
def restoredVar : Var := 13

/-- The child body: one designated write of the child's own slot `j` with `w`,
returning the child handle. -/
def body : Nested.NCode := .base (.setArr childVar leafIdxVar valueVar (.ret childVar))

/-- The caller's entry environment. -/
def famEnv (i j w : Nat) : Env :=
  fun x =>
    if x = parentVar then some (.ref 0)
    else if x = idxVar then some (.scalar i)
    else if x = leafIdxVar then some (.scalar j)
    else if x = valueVar then some (.scalar w)
    else none

/-- The caller's entry context: the parent is owned, the three scalar arguments
are scalars, and the multiplicities are the entry heap's own counts. -/
def famCtx (n i : Nat) : Ctx :=
  { us := fun x =>
      if x = parentVar then .owned
      else if x = idxVar then .scalar
      else if x = leafIdxVar then .scalar
      else if x = valueVar then .scalar
      else .dead
    refOf := fun x => if x = parentVar then some 0 else none
    mult := fun r => (famHeap n i).rc r }

/-- The caller's boundary environment: the take-out's two targets. -/
def boundaryEnv (i j w : Nat) : Env :=
  ((famEnv i j w).set fstVar (.ref 0)).set childVar (.ref 1)

/-- The caller's boundary context: the take-out's move and owned bind. -/
def boundaryCtx (n i : Nat) : Ctx := ((famCtx n i).move parentVar fstVar).bindOwned childVar 1

/-- The context after the child call's result binding. -/
def callCtx (n i : Nat) : Ctx := (boundaryCtx n i).move childVar resultVar

/-- The context the whole chain's check produces. -/
def famFinalCtx (n i : Nat) : Ctx := ((callCtx n i).move fstVar restoredVar).setUs resultVar .dead

/-- The chain the family instantiates. -/
def famChain : Nested.NCode :=
  chain parentVar idxVar fstVar childVar 1 leafIdxVar valueVar resultVar restoredVar body

/-! ## Computable controls, affirmative first -/

/-- A slot holds the scalar zero. -/
def isZeroScalar : Option Val → Bool
  | some (.scalar 0) => true
  | _ => false

-- the boundary at the outer slot 1: the pair cell is released, the cursor advanced
#guard ((B 2 1).cells 2).isNone
-- the omitted release leaves that same cell live: the positive counterpart
#guard ((protocolNoFree (famHeap 2 1) 0 1 1).2.cells 2).isSome
#guard (B 2 1).next == 3
#guard (B 2 1).rc 0 == 1
#guard (B 2 1).rc 1 == 1
-- the placeholder write lands in the parent's selected slot
#guard isZeroScalar (((B 2 1).cells 0).bind (fun o => o.fields[1]?))
-- the child's own cell survives the take-out; unchangedness is `boundary_child_cell`
#guard ((B 2 1).cells 1).isSome
-- the leaf writes the slot it is given, and no other
#guard isZeroScalar (childAfter 2 1 7).fields[0]?
#guard (isZeroScalar (childAfter 2 1 7).fields[1]?) == false

/-! ## Cell, slot and edge facts -/

theorem fam_next (n i : Nat) : (famHeap n i).next = 2 := rfl

theorem fam_cells_zero (n i : Nat) : (famHeap n i).cells 0 = some (parentObj n i) := by
  simp [famHeap]

theorem fam_cells_one (n i : Nat) : (famHeap n i).cells 1 = some (scalarObj n) := by
  unfold famHeap
  rw [Heap.set_other (H := baseHeap n) (r := 0) (r' := 1) (o := parentObj n i)
    (by decide : (1 : Ref) ≠ 0)]
  simp [baseHeap]

theorem fam_cells_other (n i : Nat) {r : Ref} (h0 : r ≠ 0) (h1 : r ≠ 1) :
    (famHeap n i).cells r = none := by
  unfold famHeap
  rw [Heap.set_other (H := baseHeap n) (r := 0) (r' := r) (o := parentObj n i) h0]
  simp [baseHeap, h0, h1]

theorem fam_rc_zero (n i : Nat) : (famHeap n i).rc 0 = 1 := by
  rw [Heap.rc, fam_cells_zero]
  rfl

theorem fam_rc_one (n i : Nat) : (famHeap n i).rc 1 = 1 := by
  rw [Heap.rc, fam_cells_one]
  rfl

theorem parentSlot (n i : Nat) (hi : i < n) : (parentObj n i).fields[i]? = some (.ref 1) := by
  have h : i < (baseFields n).size := by simpa [baseFields] using hi
  simpa [parentObj, parentFields] using
    (Array.getElem?_setIfInBounds_self_of_lt (xs := baseFields n) (i := i) (a := Val.ref 1) h)

theorem childSlot (n j : Nat) (hj : j < n) : (childObj n).fields[j]? = some (.scalar 0) := by
  simp [childObj, scalarObj, baseFields, hj]

theorem IncomingCount_baseHeap (n : Nat) (q : Ref) : IncomingCount (baseHeap n) q = 0 := by
  have h0 : EdgeAt (baseHeap n) 0 q = 0 := by
    simp [EdgeAt, baseHeap, baseFields, scalarObj, Accounted.RefCount_initFields]
  have h1 : EdgeAt (baseHeap n) 1 q = 0 := by
    simp [EdgeAt, baseHeap, baseFields, scalarObj, Accounted.RefCount_initFields]
  rw [IncomingCount_eq_edges]
  have hnext : (baseHeap n).next = 2 := rfl
  rw [hnext]
  simp [List.range_succ, h0, h1]

/-- The take-out's fill of the parent's slot `i` raises the child's incoming
count to one: the slot was a scalar slot of the base cell, and the pair traffic
is neutral on the parent's own cell. -/
theorem IncomingCount_fam_one (n i : Nat) (hi : i < n) :
    IncomingCount (famHeap n i) 1 = 1 := by
  have hcell : (baseHeap n).cells 0 = some (scalarObj n) := by simp [baseHeap]
  have hnext : (0 : Ref) < (baseHeap n).next := by
    show (0 : Nat) < 2
    decide
  have h := IncomingCount_set_fill (H := baseHeap n) (r := 0) (re := 1) (o := scalarObj n)
    (idx := i) (old := 0) hcell hnext (childSlot n i hi)
  rw [IncomingCount_baseHeap] at h
  simpa [famHeap, parentObj, parentFields, scalarObj, Array.set!] using h

/-- No slot besides `i` is filled, so the parent has no edge into any other
reference. -/
theorem IncomingCount_fam_zero (n i : Nat) (hi : i < n) :
    IncomingCount (famHeap n i) 0 = 0 := by
  have hcell : (baseHeap n).cells 0 = some (scalarObj n) := by simp [baseHeap]
  have hnext : (0 : Ref) < (baseHeap n).next := by
    show (0 : Nat) < 2
    decide
  have h := IncomingCount_set_fill_ne (H := baseHeap n) (r := 0) (re := 1) (o := scalarObj n)
    (idx := i) (old := 0) hcell hnext (childSlot n i hi) (by decide : (0 : Ref) ≠ 1)
  rw [IncomingCount_baseHeap] at h
  simpa [famHeap, parentObj, parentFields, scalarObj, Array.set!] using h

theorem IncomingCount_fam_other (n i : Nat) (hi : i < n) {q : Ref} (hq : q ≠ 1) :
    IncomingCount (famHeap n i) q = 0 := by
  have hcell : (baseHeap n).cells 0 = some (scalarObj n) := by simp [baseHeap]
  have hnext : (0 : Ref) < (baseHeap n).next := by
    show (0 : Nat) < 2
    decide
  have h := IncomingCount_set_fill_ne (H := baseHeap n) (r := 0) (re := 1) (o := scalarObj n)
    (idx := i) (old := 0) hcell hnext (childSlot n i hi) hq
  rw [IncomingCount_baseHeap] at h
  simpa [famHeap, parentObj, parentFields, scalarObj, Array.set!] using h

/-! ## The entry's accounting -/

theorem fam_us_owned (n i x : Var) : (famCtx n i).us x = .owned ↔ x = parentVar := by
  unfold famCtx parentVar idxVar leafIdxVar valueVar
  by_cases h0 : x = 0 <;> by_cases h1 : x = 10 <;> by_cases h2 : x = 14 <;>
    by_cases h3 : x = 11 <;> simp [h0, h1, h2, h3]

theorem fam_us_ne_borrow (n i x : Var) : (famCtx n i).us x ≠ .borrow := by
  unfold famCtx parentVar idxVar leafIdxVar valueVar
  by_cases h0 : x = 0 <;> by_cases h1 : x = 10 <;> by_cases h2 : x = 14 <;>
    by_cases h3 : x = 11 <;> simp [h0, h1, h2, h3]

theorem fam_refOf (n i x : Var) (r : Ref) :
    (famCtx n i).refOf x = some r ↔ x = parentVar ∧ r = 0 := by
  unfold famCtx parentVar
  by_cases h0 : x = 0
  · subst h0
    simp [eq_comm]
  · simp [h0]

theorem fam_envOwner_zero (n i : Nat) : EnvOwnerCount (famCtx n i) [parentVar] 0 = 1 := by
  simp [EnvOwnerCount, famCtx, parentVar]

theorem fam_envOwner_one (n i : Nat) : EnvOwnerCount (famCtx n i) [parentVar] 1 = 0 := by
  simp [EnvOwnerCount, famCtx, parentVar]

theorem fam_envOwner_other (n i : Nat) {r : Ref} (h0 : r ≠ 0) :
    EnvOwnerCount (famCtx n i) [parentVar] r = 0 := by
  simp [EnvOwnerCount, famCtx, parentVar]
  exact fun hh => h0 hh.symm

theorem entryInv (n i j w : Nat) : Inv (famHeap n i) (famEnv i j w) (famCtx n i) where
  rc_eq r := rfl
  owned := by
    intro x r hx hr
    have hx0 : x = parentVar := (fam_us_owned n i x).mp hx
    subst hx0
    have hr0 : (0 : Ref) = r := ((fam_refOf n i parentVar r).mp hr).2.symm
    subst hr0
    refine ⟨by simp [famEnv, parentVar], ?_⟩
    show 1 ≤ (famHeap n i).rc 0
    rw [fam_rc_zero]
    decide
  borrow := by
    intro x r hx _
    exact absurd hx (fam_us_ne_borrow n i x)
  scalar := by
    intro x hx
    by_cases h0 : x = 0
    · subst h0
      simp [famCtx, parentVar] at hx
    · by_cases h1 : x = 10
      · subst h1
        exact ⟨i, by simp [famEnv, parentVar, idxVar]⟩
      · by_cases h2 : x = 14
        · subst h2
          exact ⟨j, by simp [famEnv, parentVar, idxVar, leafIdxVar]⟩
        · by_cases h3 : x = 11
          · subst h3
            exact ⟨w, by simp [famEnv, parentVar, idxVar, leafIdxVar, valueVar]⟩
          · simp [famCtx, parentVar, idxVar, leafIdxVar, valueVar, h0, h1, h2, h3] at hx
  nonPersistent := by
    intro r o hc
    by_cases h0 : r = 0
    · subst h0
      rw [fam_cells_zero] at hc
      injection hc with h
      subst h
      rfl
    · by_cases h1 : r = 1
      · subst h1
        rw [fam_cells_one] at hc
        injection hc with h
        subst h
        rfl
      · rw [fam_cells_other n i h0 h1] at hc
        exact absurd hc (by simp)

theorem entryAccounted (n i j w : Nat) (hi : i < n) :
    Accounted [parentVar] (famHeap n i) (famEnv i j w) (famCtx n i) := by
  refine
    { inv := entryInv n i j w
      support_nodup := List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩
      support_sound := ?_
      support_complete := ?_
      support_bound := ?_
      domain := ?_
      count := ?_ }
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    simp [famCtx, parentVar]
  · intro x hx
    exact List.mem_singleton.mpr ((fam_us_owned n i x).mp hx)
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    exact ⟨0, by simp [famCtx, parentVar]⟩
  · intro r o hc
    rw [fam_next]
    by_cases h0 : r = 0
    · subst h0; rw [fam_cells_zero] at hc; injection hc with h; subst h; decide
    · by_cases h1 : r = 1
      · subst h1; rw [fam_cells_one] at hc; injection hc with h; subst h; decide
      · rw [fam_cells_other n i h0 h1] at hc
        exact absurd hc (by simp)
  · intro r
    by_cases h0 : r = 0
    · subst h0
      rw [fam_rc_zero, IncomingCount_fam_zero n i hi, fam_envOwner_zero]
    · by_cases h1 : r = 1
      · subst h1
        rw [fam_rc_one, IncomingCount_fam_one n i hi, fam_envOwner_one]
      · have hz : (famHeap n i).rc r = 0 := by
          simp [Heap.rc, fam_cells_other n i h0 h1]
        rw [hz, IncomingCount_fam_other n i hi h1, fam_envOwner_other n i h0]

/-! ## The protocol boundary's facts -/

theorem boundary_cells (n i : Nat) :
    (B n i).cells 2 = none ∧ (B n i).next = 3 ∧ (B n i).rc 0 = 1 ∧
      (B n i).rc 1 = 1 ∧
      (B n i).cells 0 = some (PutBack.parentAfter (parentObj n i) i) ∧
      (B n i).cells 1 = some (scalarObj n) := by
  have hpn : (0 : Ref) ≠ (famHeap n i).next := by rw [fam_next]; decide
  have hcn : (1 : Ref) ≠ (famHeap n i).next := by rw [fam_next]; decide
  obtain ⟨-, hcellp, hcellc, hpair, hrcp, hrcc, -, -⟩ :=
    protocol_boundary (H := famHeap n i) (p := 0) (c := 1) (i := i)
      (op := parentObj n i) (oc := scalarObj n) (fam_cells_zero n i) (fam_cells_one n i)
      (by decide) hpn hcn
  have hnext : (B n i).next = 3 := by
    rw [B, protocol_next (H := famHeap n i) (p := 0) (c := 1) (i := i) hpn hcn, fam_next]
  refine ⟨?_, hnext, ?_, ?_, ?_, ?_⟩
  · exact hpair
  · simpa [B, parentObj, scalarObj] using hrcp
  · simpa [B, scalarObj] using hrcc
  · simpa [B, PutBack.parentAfter] using hcellp
  · simpa [B, scalarObj] using hcellc

theorem boundary_parent_cell (n i : Nat) :
    (B n i).cells 0 = some (PutBack.parentAfter (parentObj n i) i) :=
  (boundary_cells n i).2.2.2.2.1

theorem boundary_child_cell (n i : Nat) :
    (B n i).cells 1 = some (scalarObj n) :=
  (boundary_cells n i).2.2.2.2.2

/-- The boundary heap has no live cell besides the parent and the child. -/
theorem B_cells_none (n i : Nat) {r : Ref} (h0 : r ≠ 0) (h1 : r ≠ 1) :
    (B n i).cells r = none := by
  by_cases h2 : r = 2
  · subst h2
    exact (boundary_cells n i).1
  · have htraffic : (B n i) =
        pairFree (pairInc (takeOut (famHeap n i) 0 1 i).2 0 1) 0 1 (famHeap n i).next := by
      show pairTraffic (takeOut (famHeap n i) 0 1 i).2 (famHeap n i).next = _
      exact pairTraffic_takeOut (H := famHeap n i) (p := 0) (c := 1) (i := i)
        (by rw [fam_next]; decide) (by rw [fam_next]; decide)
    rw [htraffic, pairFree_inc_cells_other h0 h1 (by rw [fam_next]; exact h2)]
    show (setPlaceholder (allocPair (famHeap n i) 0 1) 0 i).cells r = none
    rw [setPlaceholder_cells_other h0,
      allocPair_cells_other (by rw [fam_next]; exact h2), fam_cells_other n i h0 h1]

theorem childFieldRefs (n : Nat) : Entry.fieldRefs (childObj n) = [] := by
  unfold Entry.fieldRefs childObj scalarObj baseFields
  rw [Array.toList_replicate]
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ]
      simp [Entry.refsOf, ih]

/-- The child call's boundary accounting, derived by the counted take-out from
the entry's accounting rather than recomputed. -/
theorem boundary_accounted (n i j w : Nat) (hi : i < n) :
    Accounted [childVar, fstVar] (B n i) (boundaryEnv i j w) (boundaryCtx n i) ∧
      HeapCompat (B n i) ((famHeap n i).set 0 (PutBack.parentAfter (parentObj n i) i)) := by
  have h := counted_takeOut (h := entryAccounted n i j w hi) (a := parentVar) (fst := fstVar)
    (snd := childVar) (e := 1) (r := 0) (o := parentObj n i) (idx := i)
    (by simp [famCtx, parentVar])
    (by simp [Ctx.multOf, famCtx, parentVar, fam_rc_zero])
    (by simp [famCtx, parentVar])
    (by simpa [famCtx] using fam_rc_one n i)
    (by simp [famCtx, fstVar, parentVar, idxVar, leafIdxVar, valueVar])
    (by simp [famCtx, childVar, parentVar, idxVar, leafIdxVar, valueVar])
    (by decide) (by decide) (fam_cells_zero n i) (parentSlot n i hi)
  refine ⟨?_, ?_⟩
  · simpa [B, boundaryEnv, boundaryCtx, replaceVar, parentVar, fstVar, childVar] using h.1
  · simpa [B, parentObj, PutBack.parentAfter] using h.2.1

theorem boundary_rc_eq (n i j w : Nat) (hi : i < n) (r : Ref) :
    (B n i).rc r = (famHeap n i).rc r := by
  rw [(boundary_accounted n i j w hi).2.rc r]
  by_cases h0 : r = 0
  · subst h0
    rw [Heap.rc_set_self, fam_rc_zero]
    rfl
  · rw [Heap.rc_set_other h0]

/-! ## The child call's boundary -/

theorem body_admitted : Nested.CountFree body = true := rfl

theorem bodyChecked (n i : Nat) :
    ∃ cb,
      Nested.checkNF (Nested.isolatedCtx (boundaryCtx n i) childVar leafIdxVar valueVar 1) [] body =
        some cb ∧
      ∃ y, Nested.retVar body = some y ∧ cb.us y = .owned ∧ cb.refOf y = some 1 := by
  refine ⟨Nested.isolatedCtx (boundaryCtx n i) childVar leafIdxVar valueVar 1, ?_,
    childVar, rfl, ?_, ?_⟩
  · simp [body, Nested.checkNF, Ownership.check, Nested.isolatedCtx, childVar, idxVar,
      leafIdxVar, valueVar, boundaryCtx, famCtx, parentVar, fstVar, Ctx.multOf]
    show (famHeap n i).rc 1 = 1
    rw [fam_rc_one]
  · simp [Nested.isolatedCtx, childVar]
  · simp [Nested.isolatedCtx, childVar]

theorem boundaryInv (n i j w : Nat) (hi : i < n) :
    Inv (B n i) (Nested.isolateEnv (boundaryEnv i j w) childVar leafIdxVar valueVar)
      (Nested.isolatedCtx (boundaryCtx n i) childVar leafIdxVar valueVar 1) where
  rc_eq r := by
    simpa [Nested.isolatedCtx, boundaryCtx, famCtx] using boundary_rc_eq n i j w hi r
  owned := by
    intro x r hx hr
    have hx3 : x = childVar := Nested.isolatedCtx_us_owned.mp hx
    subst hx3
    have hr1 : (1 : Ref) = r :=
      Option.some.inj (by simpa [Nested.isolatedCtx, childVar] using hr)
    subst hr1
    refine ⟨by simp [Nested.isolateEnv, boundaryEnv, Env.set, childVar], ?_⟩
    show 1 ≤ (famHeap n i).rc 1
    rw [fam_rc_one]
    decide
  borrow := by
    intro x r hx _
    exact absurd hx Nested.isolatedCtx_us_ne_borrow
  scalar := by
    intro x hx
    by_cases h : x = 3
    · subst h
      simp [Nested.isolatedCtx, childVar] at hx
    · by_cases h14 : x = 14
      · subst h14
        exact ⟨j, by
          simp [Nested.isolateEnv, boundaryEnv, famEnv, Env.set, parentVar, idxVar, leafIdxVar,
            childVar, fstVar]⟩
      · by_cases h11 : x = 11
        · subst h11
          exact ⟨w, by
            simp [Nested.isolateEnv, boundaryEnv, famEnv, Env.set, parentVar, idxVar, leafIdxVar,
              valueVar, childVar, fstVar]⟩
        · simp [Nested.isolatedCtx, childVar, leafIdxVar, valueVar, h, h14, h11] at hx
  nonPersistent := by
    intro r o hc
    by_cases h0 : r = 0
    · subst h0
      rw [boundary_parent_cell n i] at hc
      injection hc with h
      subst h
      rfl
    · by_cases h1 : r = 1
      · subst h1
        rw [boundary_child_cell n i] at hc
        injection hc with h
        subst h
        rfl
      · rw [B_cells_none n i h0 h1] at hc
        exact absurd hc (by simp)

theorem childFootprint (n i : Nat) :
    ∀ q, Entry.MutableFootprint (B n i) 1 q → q = 1 := by
  intro q h
  induction h with
  | root => rfl
  | step hr hcell hpers hmem hcell' hpers' ih =>
      subst ih
      rw [boundary_child_cell n i] at hcell
      injection hcell with heq
      subst heq
      rw [childFieldRefs] at hmem
      simp at hmem

theorem childSeparated (n i : Nat) :
    ¬ Entry.MutableFootprint (B n i) 1 0 := by
  intro h
  have hq := childFootprint n i 0 h
  exact absurd hq (by decide)

theorem body_runs (n i j w : Nat) :
    Nested.runN body (Nested.isolateEnv (boundaryEnv i j w) childVar leafIdxVar valueVar)
        (B n i) =
      .done (Hc n i j w)
        ((Nested.isolateEnv (boundaryEnv i j w) childVar leafIdxVar valueVar).set childVar
          (.ref 1)) (.ref 1) [(1, true)] := by
  have hcell : (B n i).cells 1 = some (scalarObj n) := boundary_child_cell n i
  have hex : (B n i).exclusive? 1 = true :=
    (Heap.exclusive?_eq_true).mpr ⟨scalarObj n, hcell, rfl, rfl⟩
  have h3 : Nested.isolateEnv (boundaryEnv i j w) childVar leafIdxVar valueVar childVar =
      some (.ref 1) := by
    simp [Nested.isolateEnv, boundaryEnv, Env.set, childVar]
  have h14 : Nested.isolateEnv (boundaryEnv i j w) childVar leafIdxVar valueVar leafIdxVar =
      some (.scalar j) := by
    simp [Nested.isolateEnv, boundaryEnv, famEnv, Env.set, parentVar, idxVar, leafIdxVar,
      childVar, fstVar]
  have h11 : Nested.isolateEnv (boundaryEnv i j w) childVar leafIdxVar valueVar valueVar =
      some (.scalar w) := by
    simp [Nested.isolateEnv, boundaryEnv, famEnv, Env.set, parentVar, idxVar, leafIdxVar, valueVar,
      childVar, fstVar]
  simp only [body, Nested.runN, Ownership.run, h3, h14, h11]
  rw [hcell]
  simp [hex, Hc, childAfter, Ownership.Res.addWrite, Array.set!]

theorem childCall (n i j w : Nat) (hi : i < n) :
    PutBack.ChildCall (B n i) (Hc n i j w) (boundaryEnv i j w) (boundaryCtx n i)
      childVar leafIdxVar valueVar body 0 1 where
  admitted := body_admitted
  checked := bodyChecked n i
  inv := boundaryInv n i j w hi
  annotations := trivial
  extraction := trivial
  separated := childSeparated n i
  outcome :=
    ⟨(Nested.isolateEnv (boundaryEnv i j w) childVar leafIdxVar valueVar).set childVar
        (.ref 1), [(1, true)], body_runs n i j w⟩
  child_rc := by
    show (Hc n i j w).rc 1 = (B n i).rc 1
    rw [Hc, Heap.rc_set_self, rc_of_cells (boundary_child_cell n i)]
    rfl
  child_persistent := by
    show (Hc n i j w).isPersistent 1 = (B n i).isPersistent 1
    rw [Hc,
      PutBack.isPersistent_of_cells (H := (B n i).set 1 (childAfter n j w)) (r := 1)
        (o := childAfter n j w) (Heap.set_self _ _ _),
      PutBack.isPersistent_of_cells (H := B n i) (r := 1) (o := scalarObj n)
        (boundary_child_cell n i)]
    rfl

/-- The caller's accounting at the body's return: the leaf's store is an
in-place scalar rewrite of the child's own slot, so `Accounted.setFieldsScalar`
carries the boundary's accounting across it. -/
theorem calledAccounted (n i j w : Nat) (hi : i < n) (hj : j < n) :
    Accounted [childVar, fstVar] (Hc n i j w) (boundaryEnv i j w) (boundaryCtx n i) := by
  have h := Accounted.setFieldsScalar (h := (boundary_accounted n i j w hi).1) (r := 1)
    (o := scalarObj n) (idx := j) (old := 0) (w := w)
    (boundary_child_cell n i) (childSlot n j hj)
  simpa [Hc, childAfter, Array.set!, B, boundaryEnv, boundaryCtx, childVar, fstVar] using h

/-- The call's edge effect at the family boundary: the leaf's write replaces a
scalar slot of the all-scalar child cell with a scalar, so no `.ref` occurrence
at any name changes. -/
theorem B_edges (n i j w : Nat) (hi : i < n) (hj : j < n) :
    EdgePreserved (B n i) (Hc n i j w) :=
  EdgePreserved.set (H := B n i) (r := 1) (o := scalarObj n) (o' := childAfter n j w)
    (boundary_child_cell n i)
    (fun q => by
      simpa [childAfter] using
        (RefCount_setIfInBounds_scalar_scalar (fields := (scalarObj n).fields) (i := j)
          (old := 0) (w := w) (q := q) (childSlot n j hj)).symm)

theorem countedBoundaryCall (n i j w : Nat) (hi : i < n) (hj : j < n) :
    CountedChildCall (B n i) (Hc n i j w) (boundaryEnv i j w) (boundaryCtx n i)
      childVar leafIdxVar valueVar body 0 1 [childVar, fstVar] where
  call := childCall n i j w hi
  edges := B_edges n i j w hi hj

/-- The caller's accounting at the body's return, derived from the boundary
accounting and the call's edge effect; its type is `calledAccounted`'s. -/
theorem countedBoundaryCall_accounted (n i j w : Nat) (hi : i < n) (hj : j < n) :
    Accounted [childVar, fstVar] (Hc n i j w) (boundaryEnv i j w) (boundaryCtx n i) :=
  (countedBoundaryCall n i j w hi hj).accounted_of (boundary_accounted n i j w hi).1

/-! ## The chain's own check -/

theorem famChecked (n i : Nat) :
    Nested.checkN (famCtx n i) famChain = some (famFinalCtx n i) := by
  simp [Nested.checkN, famChain, Ownership.chain, famCtx, fam_rc_zero, fam_rc_one,
    Nested.checkNF, Ownership.check, boundaryCtx, callCtx, famFinalCtx, childVar, idxVar,
    leafIdxVar, valueVar, fstVar, parentVar, resultVar, restoredVar, body, Nested.isolatedCtx,
    Ctx.move, Ctx.bindOwned, Ctx.setUs, Ctx.multOf, Nested.openRef, Nested.CountFree,
    Nested.countFreeCode, Nested.retVar, Nested.codeRetVar]
  funext y
  rfl

/-! ## The family's chain -/

/-- The counted extraction / child call / restoration chain at the family's data:
the child body writes the child's own slot `j` with `w` and the chain returns the
restored parent. Every conjunct of `Ownership.counted_nested_chain` is stated at
the family's parameters, conjunct for conjunct. -/
theorem family_chain (n i j w : Nat) (hi : i < n) (hj : j < n) :
    ∃ Hf Hm envm ws,
      Accounted [childVar, fstVar] (B n i) (boundaryEnv i j w) (boundaryCtx n i) ∧
      HeapCompat (B n i) ((famHeap n i).set 0 (PutBack.parentAfter (parentObj n i) i)) ∧
      (B n i).cells 2 = none ∧
      (B n i).next = 3 ∧
      Heap.Exclusive (B n i) 0 ∧
      Heap.Exclusive (B n i) 1 ∧
      PutBack.disposition? (Hc n i j w) 0 i = some .mutate ∧
      PutBack.putBack (Hc n i j w) 0 i 1 = some (0, Hf) ∧
      Hf = PutBack.mutate (Hc n i j w) 0 (PutBack.parentAfter (parentObj n i) i) i 1 ∧
      Accounted
        ((replaceVar (replaceVar [childVar, fstVar] childVar resultVar) fstVar restoredVar).erase
          resultVar) Hf
        (((boundaryEnv i j w).set resultVar (.ref 1)).set restoredVar (.ref 0))
        (famFinalCtx n i) ∧
      Nested.runN famChain (famEnv i j w) (famHeap n i) = .done Hm envm (.ref 0) ws ∧
      (∃ envb,
        Nested.runN body (Nested.isolateEnv (boundaryEnv i j w) childVar leafIdxVar valueVar)
            (B n i) = .done (Hc n i j w) envb (.ref 1) ws) ∧
      (∀ ws' ∈ ws, ws'.2 = true) ∧
      HeapCompat Hf Hm := by
  obtain ⟨Hf, Hm, envm, ws, haccB, hcompat, hpair, hnext, hexclP, hexclC, hdisp, hpb, hfm,
    haccF, hrun, hrunBody, hws', hcompF⟩ :=
    counted_nested_chain (support := [parentVar]) (H := famHeap n i) (env := famEnv i j w)
      (c := famCtx n i) (a := parentVar) (i := idxVar) (fst := fstVar) (snd := childVar)
      (path := leafIdxVar) (x := valueVar) (result := resultVar) (restored := restoredVar)
      (r := 0) (eR := 1) (o := parentObj n i) (idx := i) (body := body)
      (Hout := Hc n i j w) (ctx' := famFinalCtx n i)
      (entryAccounted n i j w hi) (famChecked n i)
      (by simp [famCtx, parentVar]) (fam_cells_zero n i) (parentSlot n i hi)
      (by show (famEnv i j w) idxVar = some (.scalar i); simp [famEnv, parentVar, idxVar])
      (countedBoundaryCall n i j w hi hj)
  refine ⟨Hf, Hm, envm, ws, ?_, ?_, ?_, ?_, hexclP, hexclC, hdisp, hpb, hfm, haccF, hrun,
    hrunBody, hws', hcompF⟩
  · simpa [replaceVar, parentVar, fstVar, childVar, B, boundaryEnv, boundaryCtx] using haccB
  · simpa [B, parentObj, PutBack.parentAfter] using hcompat
  · exact hpair
  · exact hnext

/-- The length-two instance: both field arrays have length two, and the family is
the outer slot `i < 2`, the leaf slot `j < 2` and the value `w`. -/
theorem family_chain_two (i j w : Nat) (hi : i < 2) (hj : j < 2) :
    ∃ Hf Hm envm ws,
      Accounted [childVar, fstVar] (B 2 i) (boundaryEnv i j w) (boundaryCtx 2 i) ∧
      HeapCompat (B 2 i) ((famHeap 2 i).set 0 (PutBack.parentAfter (parentObj 2 i) i)) ∧
      (B 2 i).cells 2 = none ∧
      (B 2 i).next = 3 ∧
      Heap.Exclusive (B 2 i) 0 ∧
      Heap.Exclusive (B 2 i) 1 ∧
      PutBack.disposition? (Hc 2 i j w) 0 i = some .mutate ∧
      PutBack.putBack (Hc 2 i j w) 0 i 1 = some (0, Hf) ∧
      Hf = PutBack.mutate (Hc 2 i j w) 0 (PutBack.parentAfter (parentObj 2 i) i) i 1 ∧
      Accounted
        ((replaceVar (replaceVar [childVar, fstVar] childVar resultVar) fstVar restoredVar).erase
          resultVar) Hf
        (((boundaryEnv i j w).set resultVar (.ref 1)).set restoredVar (.ref 0))
        (famFinalCtx 2 i) ∧
      Nested.runN famChain (famEnv i j w) (famHeap 2 i) = .done Hm envm (.ref 0) ws ∧
      (∃ envb,
        Nested.runN body (Nested.isolateEnv (boundaryEnv i j w) childVar leafIdxVar valueVar)
            (B 2 i) = .done (Hc 2 i j w) envb (.ref 1) ws) ∧
      (∀ ws' ∈ ws, ws'.2 = true) ∧
      HeapCompat Hf Hm :=
  family_chain 2 i j w hi hj

/-- The family's chain has a net entry-to-output edge effect, not merely the
final-state `HeapCompat` that `family_chain` carries: the whole
take-out/call/restore run at the family's data leaves every name's incoming-edge
count where the entry had it. This is the instance of
`Ownership.counted_nested_chain_edges` that an enclosing call consumes as its
`edges` field. -/
theorem family_chain_edges (n i j w : Nat) (hi : i < n) (hj : j < n) :
    EdgePreserved (famHeap n i)
      (PutBack.mutate (Hc n i j w) 0 (PutBack.parentAfter (parentObj n i) i) i 1) :=
  counted_nested_chain_edges (support := [parentVar]) (H := famHeap n i) (env := famEnv i j w)
    (c := famCtx n i) (a := parentVar) (i := idxVar) (fst := fstVar) (snd := childVar)
    (path := leafIdxVar) (x := valueVar) (result := resultVar) (restored := restoredVar)
    (r := 0) (eR := 1) (o := parentObj n i) (idx := i) (body := body)
    (Hout := Hc n i j w) (ctx' := famFinalCtx n i)
    (entryAccounted n i j w hi) (famChecked n i)
    (by simp [famCtx, parentVar]) (fam_cells_zero n i) (parentSlot n i hi)
    (by show (famEnv i j w) idxVar = some (.scalar i); simp [famEnv, parentVar, idxVar])
    (countedBoundaryCall n i j w hi hj)

/-! ## The chain's parts, named -/

theorem family_pair_cell_absent (n i j w : Nat) (hi : i < n) (hj : j < n) :
    (B n i).cells 2 = none := by
  obtain ⟨-, -, -, -, -, -, h, -, -, -, -, -, -, -, -, -, -⟩ := family_chain n i j w hi hj
  exact h

theorem family_cursor (n i j w : Nat) (hi : i < n) (hj : j < n) :
    (B n i).next = 3 := by
  obtain ⟨-, -, -, -, -, -, -, h, -, -, -, -, -, -, -, -, -⟩ := family_chain n i j w hi hj
  exact h

theorem family_extraction_exclusive (n i j w : Nat) (hi : i < n) (hj : j < n) :
    Heap.Exclusive (B n i) 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, h, -, -, -, -, -, -, -, -⟩ := family_chain n i j w hi hj
  exact h

theorem family_child_exclusive (n i j w : Nat) (hi : i < n) (hj : j < n) :
    Heap.Exclusive (B n i) 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h, -, -, -, -, -, -, -, -⟩ := family_chain n i j w hi hj
  exact h

theorem family_restoration_mutate (n i j w : Nat) (hi : i < n) (hj : j < n) :
    PutBack.disposition? (Hc n i j w) 0 i = some .mutate := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h, -, -, -, -, -, -⟩ := family_chain n i j w hi hj
  exact h

/-- The child cell at the body's return: the child's own slot `j` holds the
written scalar and the cell is still live at count one. -/
theorem family_child_after (n i j w : Nat) (hj : j < n) :
    (Hc n i j w).cells 1 = some (childAfter n j w) ∧
      (childAfter n j w).fields[j]? = some (.scalar w) ∧
      (Hc n i j w).rc 1 = 1 := by
  have hsize : (childObj n).fields.size = n := by
    simp [childObj, scalarObj, baseFields]
  have hlt : j < (childObj n).fields.size := by rw [hsize]; exact hj
  refine ⟨by simp [Hc], ?_, ?_⟩
  · simpa [childAfter] using
      (Array.getElem?_setIfInBounds_self_of_lt (xs := (childObj n).fields) (i := j)
        (a := Val.scalar w) hlt)
  · rw [Hc, Heap.rc_set_self]
    rfl

#print axioms entryAccounted
#print axioms boundary_cells
#print axioms boundary_accounted
#print axioms calledAccounted
#print axioms B_edges
#print axioms countedBoundaryCall
#print axioms countedBoundaryCall_accounted
#print axioms famChecked
#print axioms family_chain
/-- The countable content of `family_chain_edges` at the family's data: the net
run's final heap has the same incoming-edge count at the extracted child that the
entry has. The take-out removes the parent's slot edge and the restoration puts it
back, so this is the identity the net statement records, read off at a name. -/
theorem IncomingCount_fam_final_one (n i j w : Nat) (hi : i < n) (hj : j < n) :
    IncomingCount
      (PutBack.mutate (Hc n i j w) 0 (PutBack.parentAfter (parentObj n i) i) i 1) 1 = 1 := by
  have h := (family_chain_edges n i j w hi hj).incoming 1
  rw [h, IncomingCount_fam_one n i hi]

#print axioms family_chain_two
#print axioms family_pair_cell_absent
#print axioms family_cursor
#print axioms family_extraction_exclusive
#print axioms family_child_exclusive
#print axioms family_restoration_mutate
#print axioms family_child_after
#print axioms family_chain_edges
#print axioms IncomingCount_fam_final_one

end OwnershipTest.CountedFamily
