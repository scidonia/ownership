/-
Focused checks for preservation through accepted execution.

The computable guards come affirmative first: the measured write runs and records
exactly one exclusive write; the increment arm's run aborts. The kernel-checked
theorems then state the two refusals the fragment's premises exclude — a stale
alias target, and a store whose slot holds a reference — each beside its positive
control in this file, plus the initializer instances of the entry record, the
measured write, and the store's own pre- and post-state. `#print axioms` closes
the file.
-/
import Ownership.Preservation

open Ownership

namespace OwnershipTest.Preservation

/-! ## Computable guards -/

-- The measured write runs fault-free and records one exclusive write.
#guard (run (Runner.execSet 0 3 1 2) (Runner.initEnv 0) (Runner.initHeap 3).2).writes
  = [(0, true)]

-- The increment arm's run aborts at the exclusivity check.
#guard (run (Runner.aliasSet 0 3 1 2) (Runner.initEnv 0) (Runner.initHeap 3).2).ok = false

/-! ## The measured write and the entry record -/

/-- The measured write prefix, through the preservation theorem at the size-three
initializer: fault-free, one exclusive write, accounted at the moved support. -/
theorem measured_write :
    ∃ H' env' v ws,
      run (Runner.execSet 0 3 1 2) (Runner.initEnv 0) (Runner.initHeap 3).2 =
        .done H' env' v ws ∧
      (∀ w ∈ ws, w.2 = true) ∧
      Accounted [3] H' env' ((Runner.initCtx 0).move 0 3) ∧
      Heap.Exclusive (Runner.initHeap 3).2 (Runner.initHeap 3).1 := by
  have h := Runner.store_exclusive (n := 3) (by decide)
  rwa [storeSupport_eq] at h

/-- The support the measured write ends at, asserted rather than left implicit. -/
theorem measured_support :
    resultSupport (Runner.execSet 0 3 1 2) [0] = [3] :=
  storeSupport_eq

/-- The initializer's two entry facts, packaged. -/
theorem initial_entry :
    AccountedEntry [0] (Runner.initHeap 3).2 (Runner.initEnv (Runner.initHeap 3).1)
      (Runner.initCtx (Runner.initHeap 3).1) (Runner.initHeap 3).1 [] :=
  Entry.initAccounted 3

/-- The entry condition at a configuration no support accounts, at the size-three
initializer: the alias witness has the fresh array's footprint and completeness
while its two owners share one count. -/
theorem alias_entry_inv :
    Entry.EntryInv (aliasHeap 3) (aliasEnv 3) (aliasCtx 3) (Runner.initHeap 3).1 [] ∧
      ∀ support, ¬ Accounted support (aliasHeap 3) (aliasEnv 3) (aliasCtx 3) :=
  aliasEntryInv 3

/-- The count relation at a state with no entry condition: the two-cell witness is
accounted, but its root has count two, so footprint uniqueness fails. -/
theorem accounted_not_entry_inv :
    Accounted [0, 1] inRangeHeap witnessEnv witnessCtx ∧
      ¬ Entry.EntryInv inRangeHeap witnessEnv witnessCtx 0 [] :=
  accountedNotEntryInv

/-- The initializer's store slots at the measured write. -/
theorem initial_slots :
    StoreSlots (Runner.initHeap 3).2 (Runner.initEnv 0) (Runner.execSet 0 3 1 2) :=
  storeSlots_init (by decide)

/-- The same at the smallest initializer that has the write's index slot: a
one-element array whose only slot is the store's target. -/
theorem initial_slots_one :
    StoreSlots (Runner.initHeap 1).2 (Runner.initEnv 0) (Runner.execSet 0 3 1 2) :=
  storeSlots_init (by decide)

/-! ## Owner counts from the context alone -/

/-- The owner count at `r` is zero when no owning variable names `r`. -/
theorem EnvOwnerCount_eq_zero {c : Ctx} {support : List Var} {r : Ref}
    (hnone : ∀ z, c.us z = .owned → c.refOf z ≠ some r) :
    EnvOwnerCount c support r = 0 := by
  unfold EnvOwnerCount
  have hnil : support.filter (fun z => c.us z = .owned ∧ c.refOf z = some r) = [] := by
    rw [List.filter_eq_nil_iff]
    intro z _ hp
    exact hnone z (of_decide_eq_true hp).1 (of_decide_eq_true hp).2
  rw [hnil]
  rfl

/-! ## Refusal: a stale alias target -/

/-- In the moved witness context only variable `0` is an owning variable, and it
names the reference the alias source named. -/
theorem movedCtx_us_owned {z : Var} :
    (witnessCtx.move 1 0).us z = .owned → z = 0 := by
  by_cases hz0 : z = 0
  · exact fun _ => hz0
  · by_cases hz1 : z = 1
    · subst hz1
      simp [Ctx.move, witnessCtx]
    · simp [Ctx.move, witnessCtx, hz0, hz1]

/-- The alias destination's freshness is load-bearing. `check` accepts the alias
at the accounted two-cell witness and the source is the count-one handle, yet the
move overwrites an already-owning destination and destroys the obligation that
named the other cell, so no support accounts the post-state: the count equation
fails at cell `0`. -/
theorem staleAlias_destroys :
    check witnessCtx (.let 0 (.checkAlias 1) (.ret 0)) = some (witnessCtx.move 1 0) ∧
      Accounted [0, 1] inRangeHeap witnessEnv witnessCtx ∧
      witnessCtx.multOf 1 = 1 ∧
      ∀ support, ¬ Accounted support inRangeHeap (witnessEnv.set 0 (.ref 1))
        (witnessCtx.move 1 0) := by
  refine ⟨?_, outOfRange_accepted, ?_, ?_⟩
  · simp [check, witnessCtx, Ctx.multOf, Ctx.move]
  · simp [Ctx.multOf, witnessCtx]
  · intro support h
    have hI : IncomingCount inRangeHeap 0 = 1 := by decide
    have hrc : Heap.rc inRangeHeap 0 = 2 := by decide
    have hcount := h.count 0
    rw [hI, hrc] at hcount
    have hE : EnvOwnerCount (witnessCtx.move 1 0) support 0 = 0 := by
      refine EnvOwnerCount_eq_zero ?_
      intro z hz hzr
      have hz0 : z = 0 := movedCtx_us_owned hz
      rw [hz0] at hzr
      simp [Ctx.move, witnessCtx] at hzr
    rw [hE] at hcount
    omega

/-! ## Refusal: a reference-valued store slot -/

/-- The accounted state whose exclusive array slot holds a reference: cell `0` is
a one-field array with `.ref 1` at index `0`, owned by variable `0` at count one;
cell `1` is live with count one, held by the edge. Variables `2` and `3` carry
the store's index and replacement. -/
def refSlotObj : Obj := ⟨#[Val.ref 1], 1, false⟩

def refSlotHeap : Heap :=
  { cells := fun r' => if r' = 0 then some refSlotObj
      else if r' = 1 then some ⟨#[Val.scalar 0], 1, false⟩ else none
    next := 2 }

def refSlotEnv : Env :=
  fun x => if x = 0 then some (Val.ref 0) else if x = 2 then some (Val.scalar 0)
    else if x = 3 then some (Val.scalar 0) else none

def refSlotCtx : Ctx :=
  { us := fun x => if x = 0 then .owned else if x = 2 then .scalar
      else if x = 3 then .scalar else .dead
    refOf := fun x => if x = 0 then some 0 else none
    mult := fun r' => if r' = 0 then 1 else if r' = 1 then 1 else 0 }

theorem refSlot_inv : Inv refSlotHeap refSlotEnv refSlotCtx := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r
    by_cases h0 : r = 0
    · subst h0
      decide
    · by_cases h1 : r = 1
      · subst h1
        decide
      · have hr : Heap.rc refSlotHeap r = 0 := by simp [Heap.rc, refSlotHeap, h0, h1]
        have hm : refSlotCtx.mult r = 0 := by simp [refSlotCtx, h0, h1]
        rw [hr, hm]
  · intro x r hx hr
    by_cases hx0 : x = 0
    · subst hx0
      have hs : some (0 : Ref) = some r := by simpa [refSlotCtx] using hr
      have hr0 : r = 0 := (Option.some.inj hs).symm
      subst hr0
      exact ⟨by decide, by decide⟩
    · by_cases hx2 : x = 2
      · rw [hx2] at hx
        simp [refSlotCtx] at hx
      · by_cases hx3 : x = 3
        · rw [hx3] at hx
          simp [refSlotCtx] at hx
        · rw [show refSlotCtx.us x = U.dead from by simp [refSlotCtx, hx0, hx2, hx3]] at hx
          exact absurd hx (by decide)
  · intro x r hx hr
    by_cases hx0 : x = 0
    · rw [hx0] at hx
      simp [refSlotCtx] at hx
    · by_cases hx2 : x = 2
      · rw [hx2] at hx
        simp [refSlotCtx] at hx
      · by_cases hx3 : x = 3
        · rw [hx3] at hx
          simp [refSlotCtx] at hx
        · rw [show refSlotCtx.us x = U.dead from by simp [refSlotCtx, hx0, hx2, hx3]] at hx
          exact absurd hx (by decide)
  · intro x hx
    by_cases hx0 : x = 0
    · rw [hx0] at hx
      simp [refSlotCtx] at hx
    · by_cases hx2 : x = 2
      · subst hx2
        exact ⟨0, by decide⟩
      · by_cases hx3 : x = 3
        · subst hx3
          exact ⟨0, by decide⟩
        · rw [show refSlotCtx.us x = U.dead from by simp [refSlotCtx, hx0, hx2, hx3]] at hx
          exact absurd hx (by decide)
  · intro r o hc
    by_cases h0 : r = 0
    · rw [h0] at hc
      simp [refSlotHeap] at hc
      subst hc
      rfl
    · by_cases h1 : r = 1
      · rw [h1] at hc
        simp [refSlotHeap] at hc
        subst hc
        rfl
      · simp [refSlotHeap, h0, h1] at hc

theorem refSlot_accounted : Accounted [0] refSlotHeap refSlotEnv refSlotCtx := by
  refine ⟨refSlot_inv, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    simp [refSlotCtx]
  · intro x hx
    by_cases h0 : x = 0
    · rw [h0]
      simp
    · by_cases h2 : x = 2
      · rw [h2] at hx
        simp [refSlotCtx] at hx
      · by_cases h3 : x = 3
        · rw [h3] at hx
          simp [refSlotCtx] at hx
        · rw [show refSlotCtx.us x = U.dead from by simp [refSlotCtx, h0, h2, h3]] at hx
          exact absurd hx (by decide)
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    exact ⟨0, by simp [refSlotCtx]⟩
  · intro r o hc
    by_cases h0 : r = 0
    · rw [h0]
      decide
    · by_cases h1 : r = 1
      · rw [h1]
        decide
      · rw [show refSlotHeap.cells r = none from by simp [refSlotHeap, h0, h1]] at hc
        exact absurd hc (by simp)
  · intro r
    by_cases h0 : r = 0
    · rw [h0]
      decide
    · by_cases h1 : r = 1
      · rw [h1]
        decide
      · have h0' : (0 : Ref) ≠ r := fun hh => h0 hh.symm
        have h1' : (1 : Ref) ≠ r := fun hh => h1 hh.symm
        have hrc : Heap.rc refSlotHeap r = 0 := by simp [Heap.rc, refSlotHeap, h0, h1]
        have hI : IncomingCount refSlotHeap r = 0 := by
          rw [IncomingCount_eq_edges]
          simp [List.range_succ, EdgeAt, refSlotHeap, refSlotObj, RefCount, h1']
        have hE : EnvOwnerCount refSlotCtx [0] r = 0 := by
          simp [EnvOwnerCount, refSlotCtx, h0']
        rw [hrc, hI, hE]

/-- The store-slot premise is load-bearing. The state is accounted with an
exclusive target, the run takes the mutate branch — it never inspects the slot —
and the post-state is unaccounted: the write drops cell `1`'s only incoming
edge without releasing its count. -/
theorem nonScalarStore_rejected :
    Accounted [0] refSlotHeap refSlotEnv refSlotCtx ∧
      Heap.Exclusive refSlotHeap 0 ∧
      refSlotObj.fields[0]? = some (.ref 1) ∧
      (run (.setArr 0 2 3 (.ret 0)) refSlotEnv refSlotHeap).writes = [(0, true)] ∧
      ∀ support, ¬ Accounted support
        (refSlotHeap.set 0 { refSlotObj with fields := refSlotObj.fields.set! 0 (.scalar 0) })
        (refSlotEnv.set 0 (.ref 0)) refSlotCtx := by
  refine ⟨refSlot_accounted, ⟨refSlotObj, rfl, rfl, rfl⟩, by decide, by decide, ?_⟩
  intro support h
  have hrc : Heap.rc
      (refSlotHeap.set 0 { refSlotObj with fields := refSlotObj.fields.set! 0 (.scalar 0) }) 1
      = 1 := by decide
  have hI : IncomingCount
      (refSlotHeap.set 0 { refSlotObj with fields := refSlotObj.fields.set! 0 (.scalar 0) }) 1
      = 0 := by decide
  have hE : EnvOwnerCount refSlotCtx support 1 = 0 := by
    refine EnvOwnerCount_eq_zero ?_
    intro z hz hzr
    by_cases hz0 : z = 0
    · rw [hz0] at hzr
      simp [refSlotCtx] at hzr
    · by_cases hz2 : z = 2
      · rw [hz2] at hz
        simp [refSlotCtx] at hz
      · by_cases hz3 : z = 3
        · rw [hz3] at hz
          simp [refSlotCtx] at hz
        · rw [show refSlotCtx.us z = U.dead from by simp [refSlotCtx, hz0, hz2, hz3]] at hz
          exact absurd hz (by decide)
  have hcount := h.count 1
  rw [hrc, hI, hE] at hcount
  omega

/-- The positive control for the slot premise: the same store shape with a
`scalar` slot is accounted after the write. -/
def scalarSlotObj : Obj := ⟨#[Val.scalar 0], 1, false⟩

def scalarSlotHeap : Heap :=
  { cells := fun r' => if r' = 0 then some scalarSlotObj else none
    next := 1 }

def scalarSlotCtx : Ctx :=
  { us := fun x => if x = 0 then .owned else if x = 2 then .scalar
      else if x = 3 then .scalar else .dead
    refOf := fun x => if x = 0 then some 0 else none
    mult := fun r' => if r' = 0 then 1 else 0 }

theorem scalarSlot_inv : Inv scalarSlotHeap refSlotEnv scalarSlotCtx := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r
    by_cases h0 : r = 0
    · subst h0
      decide
    · have hr : Heap.rc scalarSlotHeap r = 0 := by simp [Heap.rc, scalarSlotHeap, h0]
      have hm : scalarSlotCtx.mult r = 0 := by simp [scalarSlotCtx, h0]
      rw [hr, hm]
  · intro x r hx hr
    by_cases hx0 : x = 0
    · subst hx0
      have hs : some (0 : Ref) = some r := by simpa [scalarSlotCtx] using hr
      have hr0 : r = 0 := (Option.some.inj hs).symm
      subst hr0
      exact ⟨by decide, by decide⟩
    · by_cases hx2 : x = 2
      · rw [hx2] at hx
        simp [scalarSlotCtx] at hx
      · by_cases hx3 : x = 3
        · rw [hx3] at hx
          simp [scalarSlotCtx] at hx
        · rw [show scalarSlotCtx.us x = U.dead from by
            simp [scalarSlotCtx, hx0, hx2, hx3]] at hx
          exact absurd hx (by decide)
  · intro x r hx hr
    by_cases hx0 : x = 0
    · rw [hx0] at hx
      simp [scalarSlotCtx] at hx
    · by_cases hx2 : x = 2
      · rw [hx2] at hx
        simp [scalarSlotCtx] at hx
      · by_cases hx3 : x = 3
        · rw [hx3] at hx
          simp [scalarSlotCtx] at hx
        · rw [show scalarSlotCtx.us x = U.dead from by
            simp [scalarSlotCtx, hx0, hx2, hx3]] at hx
          exact absurd hx (by decide)
  · intro x hx
    by_cases hx0 : x = 0
    · rw [hx0] at hx
      simp [scalarSlotCtx] at hx
    · by_cases hx2 : x = 2
      · subst hx2
        exact ⟨0, by decide⟩
      · by_cases hx3 : x = 3
        · subst hx3
          exact ⟨0, by decide⟩
        · rw [show scalarSlotCtx.us x = U.dead from by
            simp [scalarSlotCtx, hx0, hx2, hx3]] at hx
          exact absurd hx (by decide)
  · intro r o hc
    by_cases h0 : r = 0
    · rw [h0] at hc
      simp [scalarSlotHeap] at hc
      subst hc
      rfl
    · rw [show scalarSlotHeap.cells r = none from by simp [scalarSlotHeap, h0]] at hc
      exact absurd hc (by simp)

theorem scalarSlot_accounted : Accounted [0] scalarSlotHeap refSlotEnv scalarSlotCtx := by
  refine ⟨scalarSlot_inv, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    simp [scalarSlotCtx]
  · intro x hx
    by_cases h0 : x = 0
    · rw [h0]
      simp
    · by_cases h2 : x = 2
      · rw [h2] at hx
        simp [scalarSlotCtx] at hx
      · by_cases h3 : x = 3
        · rw [h3] at hx
          simp [scalarSlotCtx] at hx
        · rw [show scalarSlotCtx.us x = U.dead from by simp [scalarSlotCtx, h0, h2, h3]] at hx
          exact absurd hx (by decide)
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    exact ⟨0, by simp [scalarSlotCtx]⟩
  · intro r o hc
    by_cases h0 : r = 0
    · rw [h0]
      decide
    · rw [show scalarSlotHeap.cells r = none from by simp [scalarSlotHeap, h0]] at hc
      exact absurd hc (by simp)
  · intro r
    by_cases h0 : r = 0
    · rw [h0]
      decide
    · have h0' : (0 : Ref) ≠ r := fun hh => h0 hh.symm
      have hrc : Heap.rc scalarSlotHeap r = 0 := by simp [Heap.rc, scalarSlotHeap, h0]
      have hI : IncomingCount scalarSlotHeap r = 0 := by
        rw [IncomingCount_eq_edges]
        simp [EdgeAt, scalarSlotHeap, scalarSlotObj, RefCount]
      have hE : EnvOwnerCount scalarSlotCtx [0] r = 0 := by
        simp [EnvOwnerCount, scalarSlotCtx, h0']
      rw [hrc, hI, hE]

/-- The same store with a scalar slot: the write's post-state is accounted. -/
theorem exclusive_store_positive :
    Accounted [0] scalarSlotHeap refSlotEnv scalarSlotCtx ∧
      Heap.Exclusive scalarSlotHeap 0 ∧
      (run (.setArr 0 2 3 (.ret 0)) refSlotEnv scalarSlotHeap).writes = [(0, true)] ∧
      Accounted [0]
        (scalarSlotHeap.set 0
          { scalarSlotObj with fields := scalarSlotObj.fields.set! 0 (.scalar 0) })
        (refSlotEnv.set 0 (.ref 0)) scalarSlotCtx := by
  refine ⟨scalarSlot_accounted, ⟨scalarSlotObj, rfl, rfl, rfl⟩, by decide, ?_⟩
  exact Accounted.setArrInPlace (h := scalarSlot_accounted) (x := 0) (r := 0)
    (o := scalarSlotObj) (idx := 0) (old := 0) (val := 0)
    (by decide) (by decide) (by simp [scalarSlotHeap]) (by simp [scalarSlotObj])

/-! ## Axiom audit -/

#print axioms measured_write
#print axioms measured_support
#print axioms initial_entry
#print axioms alias_entry_inv
#print axioms accounted_not_entry_inv
#print axioms initial_slots
#print axioms initial_slots_one
#print axioms EnvOwnerCount_eq_zero
#print axioms staleAlias_destroys
#print axioms movedCtx_us_owned
#print axioms refSlot_accounted
#print axioms nonScalarStore_rejected
#print axioms scalarSlot_accounted
#print axioms exclusive_store_positive

end OwnershipTest.Preservation
