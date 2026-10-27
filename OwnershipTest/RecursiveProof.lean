/-
The two-level recursive extraction artifact, and the nested refusals the frame
checker must enforce.

The safe heap is a root array whose slot 0 holds a child array whose slot 0
holds a leaf object; each cell is counted once. The program extracts the child
from the root, extracts the leaf from the child, runs the recursive write
summary on the leaf, and restores both slots in reverse order. `artifact`
proves the run is fault-free, records one exclusive write at the leaf, and
leaves both slots holding their original elements again.

The countermodels are the programs the checker must refuse, each paired with the
same-checker positive control: reopening an array whose slot is already open (a
stale slot), extracting a child that two parent slots name (count two), and
extracting after an `inc` duplicated the handle. The checker's other
client-boundary refusals — a put-back into a different array, returning the
emptied parent while its frame is open, and aliased take-out binders — are
asserted by the executable fixtures this module imports, so building the test
library elaborates them with these theorems.
-/
import Ownership.Nested
import OwnershipTest.Recursive
import OwnershipTest.WrongFrame
import OwnershipTest.OpenFrameReturn
import OwnershipTest.DistinctBinders
import OwnershipTest.RecursiveFrame

open Ownership
open Ownership.Nested

namespace OwnershipTest.RecursiveProof

/-! ## The safe two-level path -/

/-- The root array: slot 0 holds the child array `ref 1`. -/
def rootObj : Obj := ⟨#[.ref 1], 1, false⟩

/-- The child array: slot 0 holds the leaf `ref 2`; slot 1 is the slot the
recursive body's designated write targets. -/
def childObj : Obj := ⟨#[.ref 2, .scalar 9], 1, false⟩

/-- The leaf the recursive body extracts and restores. -/
def leafObj : Obj := ⟨#[.scalar 0], 1, false⟩

/-- Root → child → leaf, each live cell counted once. -/
def H : Heap :=
  { cells := fun r =>
      if r = 0 then some rootObj
      else if r = 1 then some childObj
      else if r = 2 then some leafObj
      else none
    next := 3 }

/-- Variable 0 names the root, 1 names the root's slot, and 7 and 8 name the
recursive call's scalar path and replacement arguments. -/
def env0 : Env :=
  fun x =>
    if x = 0 then some (.ref 0)
    else if x = 1 then some (.scalar 0)
    else if x = 7 then some (.scalar 0)
    else if x = 8 then some (.scalar 1)
    else none

def ctx0 : Ctx :=
  { us := fun x =>
      if x = 0 then .owned
      else if x = 1 then .scalar
      else if x = 7 then .scalar
      else if x = 8 then .scalar
      else .dead
    refOf := fun x => if x = 0 then some 0 else none
    mult := fun r => if r = 0 then 1 else if r = 1 then 1 else if r = 2 then 1 else 0 }

/-- Extract the child from the root, then call the recursive program on it. The
body takes the leaf out of the child, restores it, and performs the designated
write in the child's other slot; the outer continuation restores the root's
slot. -/
def code : NCode :=
  .takeOut 0 1 2 3 1
    (.callAt 3 7 8 9
      (.takeOut 3 7 5 6 2
        (.putBack 5 6 7 10
          (.base (.let 11 (.checkAlias 10) (.setArr 11 8 7 (.ret 11))))))
      (.putBack 2 9 1 12 (.ret 12)))

def ctx1 : Ctx := (ctx0.move 0 2).bindOwned 3 1
def ctx2 : Ctx := ctx1.move 3 9
def ctx3 : Ctx := (ctx2.move 2 12).setUs 9 .dead

theorem checkN_code : checkN ctx0 code = some ctx3 := by
  simp [checkN, checkNF, code, ctx0, ctx1, ctx2, ctx3, Ctx.multOf, openRef,
    CountFree, countFreeCode, retVar, codeRetVar, isolatedCtx, check, Ctx.setUs,
    Ctx.bindOwned, Ctx.move, Env.set]

theorem inv0 : Inv H env0 ctx0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r
    by_cases h0 : r = 0
    · subst h0; simp [H, ctx0, Heap.rc, rootObj]
    · by_cases h1 : r = 1
      · subst h1; simp [H, ctx0, Heap.rc, h0, childObj]
      · by_cases h2 : r = 2
        · subst h2; simp [H, ctx0, Heap.rc, h0, h1, leafObj]
        · simp [H, ctx0, Heap.rc, h0, h1, h2]
  · intro x r hx hr
    by_cases hx0 : x = 0
    · subst hx0
      have hr0 : r = 0 := by simpa [ctx0] using hr.symm
      subst hr0
      exact ⟨by simp [env0], by simp [ctx0]⟩
    · by_cases hx1 : x = 1
      · subst hx1; simp [ctx0, hx0] at hx
      · by_cases hx7 : x = 7
        · subst hx7; simp [ctx0, hx0, hx1] at hx
        · by_cases hx8 : x = 8
          · subst hx8; simp [ctx0, hx0, hx1, hx7] at hx
          · simp [ctx0, hx0, hx1, hx7, hx8] at hx
  · intro x r hx hr
    by_cases hx0 : x = 0
    · subst hx0; simp [ctx0] at hx
    · by_cases hx1 : x = 1
      · subst hx1; simp [ctx0, hx0] at hx
      · by_cases hx7 : x = 7
        · subst hx7; simp [ctx0, hx0, hx1] at hx
        · by_cases hx8 : x = 8
          · subst hx8; simp [ctx0, hx0, hx1, hx7] at hx
          · simp [ctx0, hx0, hx1, hx7, hx8] at hx
  · intro x hx
    by_cases hx0 : x = 0
    · subst hx0; simp [ctx0] at hx
    · by_cases hx1 : x = 1
      · subst hx1; exact ⟨0, by simp [env0]⟩
      · by_cases hx7 : x = 7
        · subst hx7; exact ⟨0, by simp [env0]⟩
        · by_cases hx8 : x = 8
          · subst hx8; exact ⟨1, by simp [env0]⟩
          · simp [ctx0, hx0, hx1, hx7, hx8] at hx
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
      · by_cases h2 : r = 2
        · subst h2
          simp [H, h0, h1] at hcell
          subst hcell
          rfl
        · simp [H, h0, h1, h2] at hcell

/-- The state-indexed premise at the concrete two-level heap: the root's slot
holds the child, the child's slot 0 holds the leaf, the body's designated write
runs on the heap the body's own extraction left, and the outer continuation runs
on whatever heap the body leaves. -/
theorem hok0 : TakeOutsOK H env0 code := by
  refine ⟨0, rootObj, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [env0]
  · simp [env0]
  · simp [H]
  · simp [H, rootObj]
  · decide
  · refine ⟨1, ?_, ?_, ?_, ?_⟩
    · simp [env0, Env.set]
    · simp [Heap.exclusive?, Heap.set, H, rootObj, childObj]
    · -- the body: take the leaf out of the child, restore it, write
      refine ⟨1, childObj, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rfl
      · rfl
      · simp [Heap.set, H, rootObj]
      · simp [childObj]
      · decide
      · refine ⟨1, 2, { childObj with fields := childObj.fields.setIfInBounds 0 (.scalar 0) }, 0,
          ?_, ?_, ?_, ?_, trivial⟩
        · simp [Env.set, isolateEnv, env0]
        · simp [Env.set, isolateEnv, env0]
        · simp [Env.set, isolateEnv, env0]
        · simp [Heap.set]
    · -- the continuation: restore the root's slot on the heap the body leaves
      intro H' envb vb wsb hb
      simp [runN, isolateEnv, env0, Env.set, H, Heap.set, Heap.exclusive?, rootObj,
        childObj, leafObj, Res.addWrite, addWrites, run] at hb
      obtain ⟨rfl, -, -, -⟩ := hb
      refine ⟨0, 1, { rootObj with fields := rootObj.fields.setIfInBounds 0 (.scalar 0) }, 0,
        ?_, ?_, ?_, ?_, trivial⟩
      · simp [env0, Env.set]
      · simp [env0, Env.set]
      · simp [env0, Env.set]
      · simp [Heap.set, rootObj]

/-- The two-level artifact certificate: the run is fault-free, its only write is
the body's exclusive write inside the extracted child, both extracted slots are
restored to their original elements, and the designated write changed the
child's other slot. -/
theorem artifact :
    ∃ H' env' v ws, runN code env0 H = .done H' env' v ws ∧
      (∀ w ∈ ws, w.2 = true) ∧
      H'.cells 0 = some rootObj ∧
      H'.cells 1 = some ⟨#[.ref 2, .scalar 0], 1, false⟩ ∧
      ws = [(1, true)] := by
  obtain ⟨H', env', v, ws, hrun, hws, _⟩ := checkN_sound checkN_code inv0 hok0
  have hred := hrun
  simp only [runN, code, env0, Env.set, H, Heap.set, rootObj, childObj, leafObj,
    Heap.exclusive?, Res.addWrite, addWrites, isolateEnv, run] at hred
  injection hred with hH henv hv hws'
  exact ⟨H', env', v, ws, hrun, hws, by rw [← hH]; rfl, by rw [← hH]; rfl, hws'.symm⟩

#print axioms Ownership.Nested.checkN_sound
#print axioms Ownership.Nested.callAt_frame_sound
#print axioms artifact

/-! ## Refusals with same-checker positive controls -/

/-- One extraction and return: admissible on the unique-count context. -/
def oneLevelCode : NCode := .takeOut 0 1 2 3 1 (.ret 3)

theorem oneLevel_accepted :
    checkN ctx0 oneLevelCode = some ((ctx0.move 0 2).bindOwned 3 1) := by
  simp [checkN, checkNF, oneLevelCode, ctx0, Ctx.multOf, openRef]

/-- The stale-slot countermodel: the root's slot 0 is open, and the program
extracts from the same array before restoring it. -/
def staleCode : NCode := .takeOut 0 1 2 3 1 (.takeOut 2 1 4 5 1 (.ret 5))

theorem stale_rejected : checkN ctx0 staleCode = none := by
  simp [checkN, checkNF, staleCode, ctx0, Ctx.multOf, openRef]

theorem stale_control : ∃ c, checkN ctx0 oneLevelCode = some c :=
  ⟨_, oneLevel_accepted⟩

/-- A root whose two slots both name the child; the child is counted twice. -/
def sharedObj : Obj := ⟨#[.ref 1, .ref 1], 1, false⟩

def sharedH : Heap :=
  { cells := fun r =>
      if r = 0 then some sharedObj
      else if r = 1 then some childObj
      else if r = 2 then some leafObj
      else none
    next := 3 }

/-- Two slots name the child, so its handle count is two. -/
def sharedCtx : Ctx :=
  { ctx0 with
      mult := fun r => if r = 0 then 1 else if r = 1 then 2 else if r = 2 then 1 else 0 }

/-- Both root slots hold the same child, which is why the count is two. -/
theorem shared_slots : sharedH.cells 0 = some sharedObj ∧
    sharedObj.fields[0]? = some (.ref 1) ∧ sharedObj.fields[1]? = some (.ref 1) :=
  ⟨rfl, rfl, rfl⟩

theorem shared_rejected : checkN sharedCtx oneLevelCode = none := by
  simp [checkN, checkNF, oneLevelCode, sharedCtx, ctx0, Ctx.multOf, openRef]

theorem shared_control : ∃ c, checkN ctx0 oneLevelCode = some c :=
  ⟨_, oneLevel_accepted⟩

/-- `inc` duplicates the child's handle: the same extraction is refused. -/
theorem incShared_rejected : checkN (ctx0.inc 1 1) oneLevelCode = none := by
  simp [checkN, checkNF, oneLevelCode, Ctx.inc, ctx0, Ctx.multOf, openRef]

theorem incShared_control : ∃ c, checkN ctx0 oneLevelCode = some c :=
  ⟨_, oneLevel_accepted⟩

end OwnershipTest.RecursiveProof
