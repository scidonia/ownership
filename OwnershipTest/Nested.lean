/-
The nested artifact: the measured `setAt` Path.index order, as an `NCode`
take-out → element check → recursive summary → put-back, with the concrete
heap premises.

The take-out element is the array's selected field (`ref 1`); both the array
and the element start at count one. The recursive summary records the write at
the element; the put-back restores the array's slot. The theorem says the whole
nested run is fault-free and every write is exclusive.
-/
import Ownership.Nested

open Ownership
open Ownership.Nested

namespace OwnershipTest.Nested

def arrayObj : Obj := ⟨#[.ref 1], 1, false⟩
def elemObj : Obj := ⟨#[], 1, false⟩

def H : Heap :=
  { cells := fun r =>
      if r = 0 then some arrayObj
      else if r = 1 then some elemObj
      else none
    next := 2 }

def env0 : Env :=
  fun x =>
    if x = 0 then some (.ref 0)
    else if x = 1 then some (.scalar 0)
    else if x = 5 then some (.scalar 0)
    else if x = 6 then some (.scalar 0)
    else none

def ctx0 : Ctx :=
  { us := fun x =>
      if x = 0 then .owned
      else if x = 1 then .scalar
      else if x = 5 then .scalar
      else if x = 6 then .scalar
      else .dead
    refOf := fun x => if x = 0 then some 0 else none
    mult := fun r => if r = 0 then 1 else if r = 1 then 1 else 0 }

/-- The measured order: take-out, check the extracted element, recursive write,
put-back. -/
def code : NCode :=
  .takeOut 0 1 2 3 1
    (.callAt 3 5 6 4
      (.putBack 2 4 1 7 (.ret 7)))

def ctx1 : Ctx :=
  (((ctx0.move 0 2).bindOwned 3 1).move 3 4 |>.move 2 7).setUs 4 .dead

theorem checkN_code : checkN ctx0 code = some ctx1 := by
  simp [checkN, checkNF, code, ctx0, ctx1, Ctx.multOf, openRef]

theorem inv0 : Inv H env0 ctx0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r
    by_cases h0 : r = 0
    · subst h0; simp [H, ctx0, Heap.rc]; rfl
    · by_cases h1 : r = 1
      · subst h1; simp [H, ctx0, Heap.rc, h0]; rfl
      · simp [H, ctx0, Heap.rc, h0, h1]
  · intro x r hx hr
    by_cases hx0 : x = 0
    · subst hx0
      have hr0 : r = 0 := by simpa [ctx0] using hr.symm
      subst hr0
      exact ⟨by simp [env0], by simp [ctx0]⟩
    · by_cases hx1 : x = 1
      · subst hx1; simp [ctx0, hx0] at hx
      · by_cases hx5 : x = 5
        · subst hx5; simp [ctx0, hx0, hx1] at hx
        · by_cases hx6 : x = 6
          · subst hx6; simp [ctx0, hx0, hx1, hx5] at hx
          · simp [ctx0, hx0, hx1, hx5, hx6] at hx
  · intro x r hx hr
    by_cases hx0 : x = 0
    · subst hx0; simp [ctx0] at hx
    · by_cases hx1 : x = 1
      · subst hx1; simp [ctx0, hx0] at hx
      · by_cases hx5 : x = 5
        · subst hx5; simp [ctx0, hx0, hx1] at hx
        · by_cases hx6 : x = 6
          · subst hx6; simp [ctx0, hx0, hx1, hx5] at hx
          · simp [ctx0, hx0, hx1, hx5, hx6] at hx
  · intro x hx
    by_cases hx0 : x = 0
    · subst hx0; simp [ctx0] at hx
    · by_cases hx1 : x = 1
      · subst hx1; exact ⟨0, by simp [env0]⟩
      · by_cases hx5 : x = 5
        · subst hx5; exact ⟨0, by simp [env0]⟩
        · by_cases hx6 : x = 6
          · subst hx6; exact ⟨0, by simp [env0]⟩
          · simp [ctx0, hx0, hx1, hx5, hx6] at hx
  · intro r o hcell
    by_cases h0 : r = 0
    · subst h0
      simp [H] at hcell
      subst hcell
      rfl
    · by_cases h1 : r = 1
      · subst h1
        simp [H, h0] at hcell
        subst hcell
        rfl
      · simp [H, h0, h1] at hcell

theorem hok0 : TakeOutsOK H env0 code := by
  refine ⟨0, arrayObj, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [env0]
  · simp [env0]
  · simp [H]
  · simp [H, arrayObj]
  · decide
  · refine ⟨1, ?_, ?_, ?_⟩
    · simp [env0, Env.set]
    · simp [Heap.exclusive?, H, Heap.set, arrayObj, elemObj]
    · refine ⟨0, 1, { arrayObj with fields := arrayObj.fields.setIfInBounds 0 (.scalar 0) }, 0,
        ?_, ?_, ?_, ?_, trivial⟩
      · simp [env0, Env.set]
      · simp [env0, Env.set]
      · simp [env0, Env.set]
      · simp [Heap.set]

/-- The nested artifact certificate. -/
theorem artifact :
    ∃ H' env' v ws, runN code env0 H = .done H' env' v ws ∧
      (∀ w ∈ ws, w.2 = true) := by
  obtain ⟨H', env', v, ws, hrun, hws, _⟩ := checkN_sound checkN_code inv0 hok0
  exact ⟨H', env', v, ws, hrun, hws⟩

/-- The held-pair/alias shape: the element's count is two, so the take-out's
`mult e = 1` rule rejects it. -/
def heldCtx : Ctx := { ctx0 with mult := fun r => if r = 0 then 1 else if r = 1 then 2 else 0 }

/-- The same element/array after the take-out is rejected when the element is
still named twice. -/
def heldCode : NCode := .takeOut 0 1 2 3 1 (.ret 7)

example : checkN heldCtx heldCode = none := by
  simp [checkN, checkNF, heldCode, heldCtx, ctx0, Ctx.multOf, openRef]

#print axioms Ownership.Nested.checkN_sound
#print axioms artifact

end OwnershipTest.Nested
