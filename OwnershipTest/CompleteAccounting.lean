/-
Focused checks for the complete accounting relation.

The computable guards are the context arithmetic; the four `Supported` controls
come affirmative first (the certified program and the count-one decrement), then
the refusals (the increment and the decrement whose continuation returns the
deadened handle). The controls at the decremented context are the ones a
pre-state continuation index cannot pass in either direction.

The remaining theorems instantiate the relation: the initializer's dichotomy,
the take-out's no-owner side condition on a one-edge state, and the state
witnesses of `Ownership/CompleteAccounting.lean`. `#print axioms` closes the file.
-/
import Ownership.CompleteAccounting
import Ownership.Runner

open Ownership

namespace OwnershipTest.CompleteAccounting

/-! ## Computable counts -/

#guard (Runner.initCtx 0).mult 0 == 1
#guard (Runner.initCtx 0).mult 1 == 0
#guard ((Runner.initCtx 0).move 0 3).us 3 == U.owned
#guard ((Runner.initCtx 0).move 0 3).us 0 == U.dead
#guard ((Runner.initCtx 0).inc 0 1).mult 0 == 2
#guard (((Runner.initCtx 0).inc 0 1).dec 0 1).mult 0 == 1
#guard (check (Runner.initCtx 0) (Runner.execSet 0 3 1 2)).isSome
#guard (check (Runner.initCtx 0) (Runner.aliasSet 0 3 1 2)).isNone

/-! ## The four `Supported` controls -/

/-- The certified flat model is supported from the initializer. The alias source
is the count-one owned handle at slot 0; the write's four premises hold at the
moved context, where slot 3 carries that handle and slots 1 and 2 are the
scalar index and replacement. -/
theorem supported_execSet : Supported (Runner.initCtx 0) (Runner.execSet 0 3 1 2) := by
  unfold Runner.execSet
  refine Supported.bindAlias (c := Runner.initCtx 0) (x := 0) (y := 3)
    (k := .setArr 3 1 2 (.ret 3)) ?_ ?_ ?_ ?_
  · exact Runner.initCtx_us_zero 0
  · exact Runner.initCtx_multOf_zero 0
  · simp [Runner.initCtx]
  · refine Supported.setArr ((Runner.initCtx 0).move 0 3) 3 1 2 (.ret 3)
      ?_ ?_ ?_ ?_ ?_
    · simp [Ctx.move_us_y, Runner.initCtx]
    · simp [Ctx.multOf, Ctx.move_refOf_y, Runner.initCtx]
    · simp [Ctx.move_us_other, Runner.initCtx]
    · simp [Ctx.move_us_other, Runner.initCtx]
    · refine Supported.ret _ _ ?_
      simp [Ctx.move_us_y, Runner.initCtx]

/-- A second handle to the same array (count two) makes the write
non-exclusive, so the program is outside the fragment. -/
theorem not_supported_aliasSet :
    ¬ Supported (Runner.initCtx 0) (Runner.aliasSet 0 3 1 2) := by
  intro h
  cases h

/-- The count-one decrement is supported, and its continuation is checked at the
checker's post-state: variable 0 is dead there, so the rebinding is admitted. -/
theorem supported_decOne :
    Supported ((Runner.initCtx 0).inc 0 1) (.dec 0 1 (.let 0 (.lit 5) (.ret 0))) := by
  refine Supported.decOne (c := (Runner.initCtx 0).inc 0 1) (x := 0) (r := 0)
    (k := .let 0 (.lit 5) (.ret 0)) ?_ ?_ ?_ ?_
  · simp [Runner.initCtx, Ctx.inc]
  · simp [Runner.initCtx, Ctx.inc]
  · simp [Runner.initCtx, Ctx.inc]
  · refine Supported.bindLit _ 0 5 _ ?_ ?_
    · simp [Ctx.dec, Ctx.setUs]
    · refine Supported.ret _ 0 ?_
      simp [Ctx.dec, Ctx.setUs]

/-- The same decrement whose continuation returns the deadened handle is refused
at the same context: only the continuation's index distinguishes the two. -/
theorem not_supported_decOne_ret :
    ¬ Supported ((Runner.initCtx 0).inc 0 1) (.dec 0 1 (.ret 0)) := by
  intro h
  cases h with
  | decOne c x r k hx hr hlt hk =>
    cases hk with
    | ret c' x' h =>
      simp [Ctx.dec, Ctx.setUs] at h

/-! ## The initializer and the uniqueness fact -/

/-- The count-one dichotomy at the initializer. -/
theorem dichotomy_initCtx (n : Nat) :
    (EnvOwnerCount (Runner.initCtx (Runner.initHeap n).1) [0]
          (Runner.initHeap n).1 = 1 ∧
        IncomingCount (Runner.initHeap n).2 (Runner.initHeap n).1 = 0) ∨
      (EnvOwnerCount (Runner.initCtx (Runner.initHeap n).1) [0]
            (Runner.initHeap n).1 = 0 ∧
          IncomingCount (Runner.initHeap n).2 (Runner.initHeap n).1 = 1) :=
  (Accounted.initCtx n).count_one_dichotomy (by simp [Runner.initCtx])

/-- The initializer has at most one owner of its reference. -/
theorem at_most_one_initCtx (n : Nat) {x y : Var}
    (hx : (Runner.initCtx (Runner.initHeap n).1).us x = .owned)
    (hy : (Runner.initCtx (Runner.initHeap n).1).us y = .owned)
    (hrx : (Runner.initCtx (Runner.initHeap n).1).refOf x = some (Runner.initHeap n).1)
    (hry : (Runner.initCtx (Runner.initHeap n).1).refOf y = some (Runner.initHeap n).1) :
    x = y :=
  (Accounted.initCtx n).at_most_one_owner (by simp [Runner.initCtx]) hx hy hrx hry

/-! ## The take-out side condition -/

/-- A one-edge state: cell 0 holds an edge into the child at 1, and no owning
variable names the child. -/
def childHeap : Heap :=
  { cells := fun r' => if r' = 0 then some ⟨#[.ref 1], 1, false⟩
      else if r' = 1 then some ⟨#[.scalar 0], 1, false⟩ else none
    next := 2 }

def childEnv : Env := fun x => if x = 0 then some (.ref 0) else none

def childCtx : Ctx :=
  { us := fun x => if x = 0 then .owned else .dead
    refOf := fun x => if x = 0 then some 0 else none
    mult := fun r' => if r' = 0 then 1 else if r' = 1 then 1 else 0 }

theorem child_inv : Inv childHeap childEnv childCtx := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r
    by_cases h0 : r = 0
    · subst h0
      decide
    · by_cases h1 : r = 1
      · subst h1
        decide
      · rw [show Heap.rc childHeap r = 0 from by simp [Heap.rc, childHeap, h0, h1],
            show childCtx.mult r = 0 from by simp [childCtx, h0, h1]]
  · intro x r hx hr
    by_cases hx0 : x = 0
    · subst hx0
      have hs : some (0 : Ref) = some r := by simpa [childCtx] using hr
      have hr0 : r = 0 := (Option.some.inj hs).symm
      subst hr0
      exact ⟨by decide, by decide⟩
    · rw [show childCtx.us x = U.dead from by simp [childCtx, hx0]] at hx
      exact absurd hx (by decide)
  · intro x r hx hr
    by_cases hx0 : x = 0
    · rw [hx0] at hx
      simp [childCtx] at hx
    · rw [show childCtx.us x = U.dead from by simp [childCtx, hx0]] at hx
      exact absurd hx (by decide)
  · intro x hx
    by_cases hx0 : x = 0
    · rw [hx0] at hx
      simp [childCtx] at hx
    · rw [show childCtx.us x = U.dead from by simp [childCtx, hx0]] at hx
      exact absurd hx (by decide)
  · intro r o hc
    by_cases h0 : r = 0
    · rw [h0] at hc
      simp [childHeap] at hc
      subst hc
      rfl
    · by_cases h1 : r = 1
      · rw [h1] at hc
        simp [childHeap, h0] at hc
        subst hc
        rfl
      · simp [childHeap, h0, h1] at hc

theorem child_accounted : Accounted [0] childHeap childEnv childCtx := by
  refine ⟨child_inv, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    simp [childCtx]
  · intro x hx
    by_cases h0 : x = 0
    · rw [h0]
      simp
    · rw [show childCtx.us x = U.dead from by simp [childCtx, h0]] at hx
      exact absurd hx (by decide)
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    exact ⟨0, by simp [childCtx]⟩
  · intro r o hc
    by_cases h0 : r = 0
    · rw [h0]
      decide
    · by_cases h1 : r = 1
      · rw [h1]
        decide
      · rw [show childHeap.cells r = none from by simp [childHeap, h0, h1]] at hc
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
        have hrc : Heap.rc childHeap r = 0 := by
          simp [Heap.rc, childHeap, h0, h1]
        have hI : IncomingCount childHeap r = 0 := by
          rw [IncomingCount_eq_edges]
          simp [List.range_succ, EdgeAt, childHeap, RefCount, h1']
        have hE : EnvOwnerCount childCtx [0] r = 0 := by
          simp [EnvOwnerCount, childCtx, h0, h0']
        rw [hrc, hI, hE]

/-- The extracted child has no owning variable: the take-out's side condition,
from the relation plus one incoming edge. -/
theorem child_no_owner :
    ∀ y, childCtx.us y = .owned → childCtx.refOf y = some 1 → False :=
  Accounted.noOwnerOfSingleEdge child_accounted (by decide) (by decide)

/-! ## The state witnesses -/

theorem alias_state_refused (n : Nat) :
    ∀ support, ¬ Accounted support (aliasHeap n) (aliasEnv n) (aliasCtx n) :=
  (alias_rejected n).2

theorem inc_state_refused (n : Nat) :
    ∀ support, ¬ Accounted support ((aliasHeap n).inc (Runner.initHeap n).1 1)
      (Runner.initEnv (Runner.initHeap n).1)
      ((Runner.initCtx (Runner.initHeap n).1).inc (Runner.initHeap n).1 1) :=
  (inc_rejected n).2

theorem outOfRange_state_refused :
    ∀ support, ¬ Accounted support outOfRangeHeap witnessEnv witnessCtx :=
  outOfRange_rejected.2

theorem outOfRange_state_accepted : Accounted [0, 1] inRangeHeap witnessEnv witnessCtx :=
  outOfRange_accepted

theorem bindAlone_state_refused :
    ∀ support, ¬ Accounted support bindAloneHeap (bindAloneEnv.set 1 (.ref 1))
      (bindAloneCtx.bindOwned 1 1) :=
  bindAlone_rejected.2

theorem scalarOverwrite_state_refused (n : Nat) :
    ∀ support, ¬ Accounted support (Runner.initHeap n).2
      ((Runner.initEnv (Runner.initHeap n).1).set 0 (.scalar 0))
      ((Runner.initCtx (Runner.initHeap n).1).setUs 0 .scalar) :=
  (scalarOverwrite_rejected n).2

theorem dupSupport_counts (n : Nat) :
    EnvOwnerCount (Runner.initCtx (Runner.initHeap n).1) [0, 0] (Runner.initHeap n).1
      = 2 :=
  (dupSupport_witness n).1

theorem unbound_root_counts {c : Ctx} {r : Ref} (hx : c.us 7 = .owned)
    (hr : c.refOf 7 = none) : EnvOwnerCount c [7] r = 0 :=
  unboundRoot_witness hx hr

/-! ## Axiom audit -/

#print axioms supported_execSet
#print axioms not_supported_aliasSet
#print axioms supported_decOne
#print axioms not_supported_decOne_ret
#print axioms dichotomy_initCtx
#print axioms at_most_one_initCtx
#print axioms child_accounted
#print axioms child_no_owner
#print axioms alias_state_refused
#print axioms inc_state_refused
#print axioms outOfRange_state_refused
#print axioms outOfRange_state_accepted
#print axioms bindAlone_state_refused
#print axioms scalarOverwrite_state_refused
#print axioms dupSupport_counts
#print axioms unbound_root_counts
#print axioms Accounted
#print axioms Accounted.initCtx
#print axioms Accounted.takeOut
#print axioms Supported

end OwnershipTest.CompleteAccounting
