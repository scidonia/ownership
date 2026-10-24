/-
The runner model: a fresh session array, one owned handle, and the executor's
designated write step.

This is the entry-invariant part of the plan. `initInv` is the concrete
`EntryInv` for the initializer (`Array.replicate` allocated at run time, one
owned handle, no borrows, no client-visible alias because the array is fresh).
`execSet` is the measured write prefix of `execP`: an exclusivity check, then
the element write, then the return. `artifact` composes the checker's
soundness with the entry invariant.

The client-separation and full `execP` recursion are not modelled here; the
exact emitted LCNF is the M1 measurement in `scripts/dump_executor.lean`, and
the plan keeps those as the next links rather than hiding them.
-/
import Ownership.Soundness

namespace Ownership
namespace Runner

/-- The initializer's heap: a fresh scalar array of size `n`. -/
def initHeap (n : Nat) : Ref × Heap :=
  (0, { cells := fun r' =>
          if r' = 0 then some ⟨Array.replicate n (Val.scalar 0), 1, false⟩ else none
        next := 1 })

/-- The initializer's context: variable 0 is the owned array, variables 1 and 2
are the scalars the measured write path uses. -/
def initCtx (r : Ref) : Ctx :=
  { us := fun x =>
      if x = 0 then .owned
      else if x = 1 then .scalar
      else if x = 2 then .scalar
      else .dead
    refOf := fun x => if x = 0 then some r else none
    mult := fun r' => if r' = r then 1 else 0 }

/-- The initializer's environment. -/
def initEnv (r : Ref) : Env :=
  fun x =>
    if x = 0 then some (.ref r)
    else if x = 1 then some (.scalar 0)
    else if x = 2 then some (.scalar 0)
    else none

/-- The measured write prefix: bind the exclusivity check's result, write through
it, return it. This mirrors the emitted `execP` shape
(`_x.12 := assertExclusiveArrayImpl a; Array.set! _x.12 ...`). -/
def execSet (x y i v : Var) : Code :=
  .let y (.checkAlias x) (.setArr y i v (.ret y))

theorem initCtx_us_zero (r : Ref) : (initCtx r).us 0 = .owned := by
  simp [initCtx]

theorem initCtx_us_one (r : Ref) : (initCtx r).us 1 = .scalar := by
  simp [initCtx]

theorem initCtx_us_two (r : Ref) : (initCtx r).us 2 = .scalar := by
  simp [initCtx]

theorem initCtx_refOf_zero (r : Ref) : (initCtx r).refOf 0 = some r := by
  simp [initCtx]

theorem initCtx_multOf_zero (r : Ref) : (initCtx r).multOf 0 = 1 := by
  simp [initCtx, Ctx.multOf, initCtx_refOf_zero]

theorem initEnv_zero (r : Ref) : initEnv r 0 = some (.ref r) := by
  simp [initEnv]

theorem initEnv_one (r : Ref) : initEnv r 1 = some (.scalar 0) := by
  simp [initEnv]

theorem initEnv_two (r : Ref) : initEnv r 2 = some (.scalar 0) := by
  simp [initEnv]

/-- The concrete entry invariant. -/
theorem initInv (n : Nat) :
    Inv (initHeap n).2 (initEnv (initHeap n).1) (initCtx (initHeap n).1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r'
    by_cases h : r' = 0
    · subst h
      simp [initHeap, initCtx, Heap.rc]
    · simp [initHeap, initCtx, Heap.rc, h]
  · intro x r hx hr
    by_cases hx0 : x = 0
    · subst hx0
      have hfst : (initHeap n).fst = 0 := by simp [initHeap]
      have hr' : (initHeap n).fst = r := by simpa [initCtx] using hr
      have hr0 : r = 0 := by rw [← hr', hfst]
      subst hr0
      constructor
      · simp [initEnv, hfst]
      · simp [initCtx, hfst]
    · by_cases hx1 : x = 1
      · simp [initCtx, hx0, hx1] at hx
      · by_cases hx2 : x = 2
        · simp [initCtx, hx0, hx1, hx2] at hx
        · simp [initCtx, hx0, hx1, hx2] at hx
  · intro x r hx hr
    by_cases hx0 : x = 0
    · subst hx0; simp [initCtx] at hx
    · by_cases hx1 : x = 1
      · subst hx1; simp [initCtx] at hx
      · by_cases hx2 : x = 2
        · subst hx2; simp [initCtx] at hx
        · simp [initCtx, hx0, hx1, hx2] at hx
  · intro x hx
    by_cases hx0 : x = 0
    · subst hx0; simp [initCtx] at hx
    · by_cases hx1 : x = 1
      · subst hx1
        exact ⟨0, by simp [initEnv]⟩
      · by_cases hx2 : x = 2
        · subst hx2
          exact ⟨0, by simp [initEnv]⟩
        · simp [initCtx, hx0, hx1, hx2] at hx
  · intro r' o' hcell
    by_cases h : r' = 0
    · subst h
      simp [initHeap] at hcell
      subst hcell
      rfl
    · simp [initHeap, h] at hcell

/-- The checker accepts the measured write prefix from the entry context. -/
theorem execSet_check (r : Ref) :
    check (initCtx r) (execSet 0 3 1 2) = some ((initCtx r).move 0 3) := by
  simp [execSet, check, initCtx, Ctx.multOf, Ctx.move]

/-- A1 for the measured write prefix: from the concrete entry invariant, the
run is fault-free and every write in its trace is exclusive. -/
theorem artifact (n : Nat) :
    ∃ H' env' v ws,
      run (execSet 0 3 1 2) (initEnv (initHeap n).1) (initHeap n).2 =
        .done H' env' v ws ∧
      (∀ w ∈ ws, w.2 = true) := by
  exact accepted_no_fault_and_exclusive_writes
    (execSet_check (initHeap n).1) (initInv n)

/-- The alias countermodel: duplicating the array's handle makes the exclusivity
check fail, so the write is not accepted. -/
def aliasSet (x y i v : Var) : Code :=
  .inc x 1 (execSet x y i v)

theorem aliasSet_rejected (r : Ref) :
    check (initCtx r) (aliasSet 0 3 1 2) = none := by
  simp [aliasSet, execSet, check, initCtx, Ctx.multOf, Ctx.inc]

end Runner
end Ownership
