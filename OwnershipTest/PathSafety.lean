/-
The depth-three certificate for path-depth safety and client retention.

The heap is a three-level chain — root array `ref 0` → child `ref 1` →
grandchild `ref 2` → tip `ref 3` → leaf `ref 40` — plus a client-only chain the
program never touches: `ref 50` (the client's handle) → `ref 51` → `ref 52`.
Every cell is counted once and every array's second slot holds an unrelated
scalar, so the writes the program performs are visible against untouched
siblings.

The program is `Ownership.Path.build` at this path: each level extracts its
selected slot and hands the child to the recursive call; the innermost call runs
the admitted body, which takes the leaf out of the tip, restores it, and writes
the nonzero scalar `7` into the tip's other slot; the three extractions are then
restored in reverse order. `checkN` accepts it from the entry context, and the
entry condition `entry0` is the concrete one.

The certificate uses the general theorems rather than restating them:

* `path_run_separated` gives the fault-free, exclusively-writing run, the
  preserved invariant, the untouched cells outside the root's mutable footprint,
  and — through `client_retention` — that no reference the client can reach lies
  in the entry footprint.
* `level_call_confined` supplies the per-level call contract (the `.callAt`
  steps), which discharges `ChildConfined`'s preservation halves; the innermost
  call is `callAt_frame_confined` applied to the leaf body.
* `footprint_within` and `clientSeparated_preserved` turn the entry condition's
  `ClientSeparated` into the post heap's: the footprint did not grow, so the
  client's own chain — still reachable, since no cell outside the footprint
  moved — cannot have acquired a reference into it.

What this does not certify: the emitted recursive callee's body is not captured,
so the innermost `Agrees` is a premise about the admitted model body and the
callee/prefix correspondence is the separate conditional result in
`OwnershipLcnf/NestedSemantics.lean`. Callbacks and joins are outside the
recognized fragment. The emitted continuation's retention (contract A2) remains
a named runtime obligation: treating node/continuation reference-count traffic as
disjoint from the state is conditional on real separation, which these theorems
connect to the model's `ClientSeparated` but do not establish at runtime. No
physical reference count, allocation policy or linked executable is claimed.
-/
import Ownership.PathSafety

open Ownership
open Ownership.Nested
open Ownership.Entry
open Ownership.Path
open Ownership.PathSafety

namespace OwnershipTest.PathSafety

/-! ## The object tree -/

/-- The root array: slot 0 holds the child, slot 1 an unrelated sibling scalar. -/
def rootObj : Obj := ⟨#[.ref 1, .scalar 5], 1, false⟩

/-- The child array: slot 0 holds the grandchild, slot 1 an unrelated scalar. -/
def childObj : Obj := ⟨#[.ref 2, .scalar 3], 1, false⟩

/-- The grandchild array: slot 0 holds the tip, slot 1 an unrelated scalar. -/
def grandObj : Obj := ⟨#[.ref 3, .scalar 4], 1, false⟩

/-- The tip array: slot 0 holds the extracted leaf, slot 1 the scalar the body
overwrites. -/
def tipObj : Obj := ⟨#[.ref 40, .scalar 6], 1, false⟩

/-- The leaf the body extracts and restores. -/
def leafObj : Obj := ⟨#[.scalar 0], 1, false⟩

/-- The client's own handle: an object outside the root's tree. -/
def clientWrap : Obj := ⟨#[.ref 51], 1, false⟩

/-- The client's intermediate cell. -/
def clientMid : Obj := ⟨#[.ref 52], 1, false⟩

/-- The client's own leaf. -/
def clientLeaf : Obj := ⟨#[.scalar 0], 1, false⟩

/-- Root → child → grandchild → tip → leaf, the client's three cells, each live
cell counted once. -/
def H : Heap :=
  { cells := fun r =>
      if r = 0 then some rootObj
      else if r = 1 then some childObj
      else if r = 2 then some grandObj
      else if r = 3 then some tipObj
      else if r = 40 then some leafObj
      else if r = 50 then some clientWrap
      else if r = 51 then some clientMid
      else if r = 52 then some clientLeaf
      else none
    next := 53 }

/-- The client's handles. -/
def client : List Ref := [50]

/-! ## The path -/

/-- The root level: extract slot 0 of `ref 0` into variables 2 and 3. -/
def l0 : Level :=
  { arr := 0, obj := rootObj, idx := 0, child := 1
    arrayVar := 0, indexVar := 1, parentVar := 2, childVar := 3
    resultVar := 4, restoredVar := 5 }

/-- The child level: extract slot 0 of `ref 1` — reached through the child
variable 3 — into variables 6 and 8. Its index is the call's path variable 10. -/
def l1 : Level :=
  { arr := 1, obj := childObj, idx := 0, child := 2
    arrayVar := 3, indexVar := 10, parentVar := 6, childVar := 8
    resultVar := 12, restoredVar := 13 }

/-- The grandchild level: extract slot 0 of `ref 2` — reached through the child
variable 8 — into variables 14 and 16, handing the tip `ref 3` to the innermost
call. -/
def l2 : Level :=
  { arr := 2, obj := grandObj, idx := 0, child := 3
    arrayVar := 8, indexVar := 10, parentVar := 14, childVar := 16
    resultVar := 20, restoredVar := 21 }

/-- The call's path scalar. -/
def pathVar : Var := 10

/-- The call's value scalar; its value is the index the body writes. -/
def valueVar : Var := 11

/-- The initial environment: the root handle, the root's selected index, and the
call's path and value scalars. -/
def env0 : Env :=
  fun x =>
    if x = 0 then some (.ref 0)
    else if x = 1 then some (.scalar 0)
    else if x = 10 then some (.scalar 0)
    else if x = 11 then some (.scalar 1)
    else none

/-- The admitted model body: extract the leaf from the tip at the path index,
restore it, then write the nonzero scalar `7` into the tip at the value index. -/
def body : NCode :=
  .takeOut 16 10 22 23 40
    (.putBack 22 23 10 24
      (.base
        (.let 25 (.checkAlias 24)
          (.let 26 (.lit 7)
            (.setArr 25 11 26 (.ret 25))))))

/-- The built program: extract three levels, run the body on the tip, restore
all three slots in reverse order. -/
def code : NCode := build pathVar valueVar body [l0, l1, l2]

/-! ## The checker state -/

def ctx0 : Ctx :=
  { us := fun x =>
      if x = 0 then .owned
      else if x = 1 then .scalar
      else if x = 10 then .scalar
      else if x = 11 then .scalar
      else .dead
    refOf := fun x => if x = 0 then some 0 else none
    mult := fun r => if r = 0 then 1 else if r = 1 then 1 else if r = 2 then 1
      else if r = 3 then 1 else if r = 40 then 1
      else if r = 50 then 1 else if r = 51 then 1 else if r = 52 then 1 else 0 }

def ctx1 : Ctx := (ctx0.move 0 2).bindOwned 3 1
def ctxIso0 : Ctx := isolatedCtx ctx1 3 pathVar valueVar 1
def ctxI1 : Ctx := (ctxIso0.move 3 6).bindOwned 8 2
def ctxIso1 : Ctx := isolatedCtx ctxI1 8 pathVar valueVar 2
def ctxI4 : Ctx := (ctxIso1.move 8 14).bindOwned 16 3
def ctxIso2 : Ctx := isolatedCtx ctxI4 16 pathVar valueVar 3
def ctxB1 : Ctx := (ctxIso2.move 16 22).bindOwned 23 40
def ctxB2 : Ctx := (ctxB1.move 22 24).setUs 23 .dead
def ctxBody : Ctx := (ctxB2.move 24 25).setUs 26 .scalar
def ctxI5 : Ctx := ctxI4.move 16 20
def ctxInner1 : Ctx := (ctxI5.move 14 21).setUs 20 .dead
def ctxI2 : Ctx := ctxI1.move 8 12
def ctxInner0 : Ctx := (ctxI2.move 6 13).setUs 12 .dead
def ctx2 : Ctx := ctx1.move 3 4
def ctxF : Ctx := (ctx2.move 2 5).setUs 4 .dead

theorem checkN_code : checkN ctx0 code = some ctxF := rfl

theorem checkNF_body : checkNF ctxIso2 [] body = some ctxBody := rfl

theorem checkNF_inner1 :
    checkNF ctxIso1 [] (build pathVar valueVar body [l2]) = some ctxInner1 := rfl

theorem checkNF_inner0 :
    checkNF ctxIso0 [] (build pathVar valueVar body [l1, l2]) = some ctxInner0 := rfl

/-! ## The take-out heaps and their environments -/

abbrev H1 : Heap := blankLevel H l0
abbrev H2 : Heap := blankLevel H1 l1
abbrev H3 : Heap := blankLevel H2 l2
abbrev env1 : Env := isolateEnv (bindLevel env0 l0) 3 pathVar valueVar
abbrev env2 : Env := isolateEnv (bindLevel env1 l1) 8 pathVar valueVar
abbrev env3 : Env := isolateEnv (bindLevel env2 l2) 16 pathVar valueVar

def blankRoot : Obj := { rootObj with fields := rootObj.fields.setIfInBounds 0 (.scalar 0) }
def blankChild : Obj := { childObj with fields := childObj.fields.setIfInBounds 0 (.scalar 0) }
def blankGrand : Obj := { grandObj with fields := grandObj.fields.setIfInBounds 0 (.scalar 0) }
def blankTip : Obj := { tipObj with fields := tipObj.fields.setIfInBounds 0 (.scalar 0) }

/-- The root after its slot is restored from the call's result. -/
def restoredRoot : Obj := { blankRoot with fields := blankRoot.fields.set! 0 (.ref 1) }

/-- The child after its slot is restored from the call's result. -/
def restoredChild : Obj := { blankChild with fields := blankChild.fields.set! 0 (.ref 2) }

/-- The grandchild after its slot is restored from the call's result. -/
def restoredGrand : Obj := { blankGrand with fields := blankGrand.fields.set! 0 (.ref 3) }

/-- The tip after the body's take-out restores its selected slot. -/
def fixedTip : Obj := { blankTip with fields := blankTip.fields.set! 0 (.ref 40) }

/-- The tip after the body's designated write: the leaf is in slot 0, the
replacement scalar `7` in slot 1. -/
def finalTip : Obj := { fixedTip with fields := fixedTip.fields.set! 1 (.scalar 7) }

/-! ## The entry heap's cells -/

theorem H_cells_zero : H.cells 0 = some rootObj := by simp [H]
theorem H_cells_one : H.cells 1 = some childObj := by simp [H]
theorem H_cells_two : H.cells 2 = some grandObj := by simp [H]
theorem H_cells_three : H.cells 3 = some tipObj := by simp [H]
theorem H_cells_leaf : H.cells 40 = some leafObj := by simp [H]
theorem H_cells_50 : H.cells 50 = some clientWrap := by simp [H]
theorem H_cells_51 : H.cells 51 = some clientMid := by simp [H]
theorem H_cells_52 : H.cells 52 = some clientLeaf := by simp [H]

/-- Object equality from the three fields. -/
theorem some_obj_eq {o o' : Obj} (hf : o.fields = o'.fields) (hrc : o.rc = o'.rc)
    (hp : o.persistent = o'.persistent) : some o = (some o' : Option Obj) := by
  have ho : o = o' := by cases o; cases o'; simp_all
  rw [ho]

/-! ## The object tree is the entry condition's unique tree -/

/-- The root's mutable footprint is exactly the five cells the path and the body
walk. -/
theorem H_footprint {q : Ref} (h : MutableFootprint H 0 q) :
    q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 40 := by
  induction h with
  | root _ _ => exact Or.inl rfl
  | step hr hcell hp hmem hcell' hp' ih =>
      rcases ih with rfl | rfl | rfl | rfl | rfl
      · rw [H_cells_zero] at hcell
        have ho : rootObj = _ := Option.some.inj hcell
        subst ho
        simp [fieldRefs, refsOf, rootObj] at hmem
        exact Or.inr (Or.inl hmem)
      · rw [H_cells_one] at hcell
        have ho : childObj = _ := Option.some.inj hcell
        subst ho
        simp [fieldRefs, refsOf, childObj] at hmem
        exact Or.inr (Or.inr (Or.inl hmem))
      · rw [H_cells_two] at hcell
        have ho : grandObj = _ := Option.some.inj hcell
        subst ho
        simp [fieldRefs, refsOf, grandObj] at hmem
        exact Or.inr (Or.inr (Or.inr (Or.inl hmem)))
      · rw [H_cells_three] at hcell
        have ho : tipObj = _ := Option.some.inj hcell
        subst ho
        simp [fieldRefs, refsOf, tipObj] at hmem
        exact Or.inr (Or.inr (Or.inr (Or.inr hmem)))
      · rw [H_cells_leaf] at hcell
        have ho : leafObj = _ := Option.some.inj hcell
        subst ho
        simp [fieldRefs, refsOf, leafObj] at hmem

/-- The positive controls: each cell of the path is in the root's footprint. -/
theorem H_fp1 : MutableFootprint H 0 1 :=
  MutableFootprint.step_of_slot (i := 0)
    (MutableFootprint.root H_cells_zero (by simp [rootObj])) H_cells_zero
    (by simp [rootObj]) (by decide) H_cells_one (by simp [childObj])

theorem H_fp2 : MutableFootprint H 0 2 :=
  MutableFootprint.step_of_slot (i := 0) H_fp1 H_cells_one (by simp [childObj])
    (by decide) H_cells_two (by simp [grandObj])

theorem H_fp3 : MutableFootprint H 0 3 :=
  MutableFootprint.step_of_slot (i := 0) H_fp2 H_cells_two (by simp [grandObj])
    (by decide) H_cells_three (by simp [tipObj])

theorem H_fp40 : MutableFootprint H 0 40 :=
  MutableFootprint.step_of_slot (i := 0) H_fp3 H_cells_three (by simp [tipObj])
    (by decide) H_cells_leaf (by simp [leafObj])

/-- The client's reachability at the entry heap stays inside its own three cells. -/
theorem H_client_reachable {q : Ref} (h : ClientReachable H client q) :
    q = 50 ∨ q = 51 ∨ q = 52 := by
  induction h with
  | direct h =>
      simp only [client, List.mem_singleton] at h
      exact Or.inl h
  | step hr hcell hmem ih =>
      rename_i r o r'
      rcases ih with rfl | rfl | rfl
      · rw [H_cells_50] at hcell
        have ho : clientWrap = o := Option.some.inj hcell
        subst ho
        simp [fieldRefs, refsOf, clientWrap] at hmem
        exact Or.inr (Or.inl hmem)
      · rw [H_cells_51] at hcell
        have ho : clientMid = o := Option.some.inj hcell
        subst ho
        simp [fieldRefs, refsOf, clientMid] at hmem
        exact Or.inr (Or.inr hmem)
      · rw [H_cells_52] at hcell
        have ho : clientLeaf = o := Option.some.inj hcell
        subst ho
        simp [fieldRefs, refsOf, clientLeaf] at hmem

theorem inv0 : Inv H env0 ctx0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r
    by_cases h0 : r = 0
    · subst h0; simp [H, ctx0, Heap.rc, rootObj]
    · by_cases h1 : r = 1
      · subst h1; simp [H, ctx0, Heap.rc, h0, childObj]
      · by_cases h2 : r = 2
        · subst h2; simp [H, ctx0, Heap.rc, h0, h1, grandObj]
        · by_cases h3 : r = 3
          · subst h3; simp [H, ctx0, Heap.rc, h0, h1, h2, tipObj]
          · by_cases h40 : r = 40
            · subst h40; simp [H, ctx0, Heap.rc, h0, h1, h2, h3, leafObj]
            · by_cases h50 : r = 50
              · subst h50
                simp [H, ctx0, Heap.rc, h0, h1, h2, h3, h40, clientWrap]
              · by_cases h51 : r = 51
                · subst h51
                  simp [H, ctx0, Heap.rc, h0, h1, h2, h3, h40, h50, clientMid]
                · by_cases h52 : r = 52
                  · subst h52
                    simp [H, ctx0, Heap.rc, h0, h1, h2, h3, h40, h50, h51, clientLeaf]
                  · simp [H, ctx0, Heap.rc, h0, h1, h2, h3, h40, h50, h51, h52]
  · intro x r hx hr
    by_cases hx0 : x = 0
    · subst hx0
      have hr0 : r = 0 := by simpa [ctx0] using hr.symm
      subst hr0
      exact ⟨by simp [env0], by simp [ctx0]⟩
    · by_cases hx1 : x = 1
      · subst hx1; simp [ctx0, hx0] at hx
      · by_cases hx10 : x = 10
        · subst hx10; simp [ctx0, hx0, hx1] at hx
        · by_cases hx11 : x = 11
          · subst hx11; simp [ctx0, hx0, hx1, hx10] at hx
          · simp [ctx0, hx0, hx1, hx10, hx11] at hx
  · intro x r hx hr
    by_cases hx0 : x = 0
    · subst hx0; simp [ctx0] at hx
    · by_cases hx1 : x = 1
      · subst hx1; simp [ctx0, hx0] at hx
      · by_cases hx10 : x = 10
        · subst hx10; simp [ctx0, hx0, hx1] at hx
        · by_cases hx11 : x = 11
          · subst hx11; simp [ctx0, hx0, hx1, hx10] at hx
          · simp [ctx0, hx0, hx1, hx10, hx11] at hx
  · intro x hx
    by_cases hx0 : x = 0
    · subst hx0; simp [ctx0] at hx
    · by_cases hx1 : x = 1
      · subst hx1; exact ⟨0, by simp [env0]⟩
      · by_cases hx10 : x = 10
        · subst hx10; exact ⟨0, by simp [env0, hx1]⟩
        · by_cases hx11 : x = 11
          · subst hx11; exact ⟨1, by simp [env0, hx1, hx10]⟩
          · simp [ctx0, hx0, hx1, hx10, hx11] at hx
  · intro r o hcell
    by_cases h0 : r = 0
    · subst h0
      rw [show H.cells 0 = some rootObj by simp [H]] at hcell
      have ho : rootObj = o := Option.some.inj hcell
      subst ho; rfl
    · by_cases h1 : r = 1
      · subst h1
        rw [show H.cells 1 = some childObj by simp [H, h0]] at hcell
        have ho : childObj = o := Option.some.inj hcell
        subst ho; rfl
      · by_cases h2 : r = 2
        · subst h2
          rw [show H.cells 2 = some grandObj by simp [H, h0, h1]] at hcell
          have ho : grandObj = o := Option.some.inj hcell
          subst ho; rfl
        · by_cases h3 : r = 3
          · subst h3
            rw [show H.cells 3 = some tipObj by simp [H, h0, h1, h2]] at hcell
            have ho : tipObj = o := Option.some.inj hcell
            subst ho; rfl
          · by_cases h40 : r = 40
            · subst h40
              rw [show H.cells 40 = some leafObj by simp [H, h0, h1, h2, h3]] at hcell
              have ho : leafObj = o := Option.some.inj hcell
              subst ho; rfl
            · by_cases h50 : r = 50
              · subst h50
                rw [show H.cells 50 = some clientWrap by
                  simp [H, h0, h1, h2, h3, h40]] at hcell
                have ho : clientWrap = o := Option.some.inj hcell
                subst ho; rfl
              · by_cases h51 : r = 51
                · subst h51
                  rw [show H.cells 51 = some clientMid by
                    simp [H, h0, h1, h2, h3, h40, h50]] at hcell
                  have ho : clientMid = o := Option.some.inj hcell
                  subst ho; rfl
                · by_cases h52 : r = 52
                  · subst h52
                    rw [show H.cells 52 = some clientLeaf by
                      simp [H, h0, h1, h2, h3, h40, h50, h51]] at hcell
                    have ho : clientLeaf = o := Option.some.inj hcell
                    subst ho; rfl
                  · rw [show H.cells r = none by
                      simp [H, h0, h1, h2, h3, h40, h50, h51, h52]] at hcell
                    exact absurd hcell (by simp)

/-- The concrete entry condition at the depth-three heap. -/
theorem entry0 : EntryInv H env0 ctx0 0 client := by
  refine ⟨inv0, ?_, ?_, ?_⟩
  · intro q hq
    rcases H_footprint hq with rfl | rfl | rfl | rfl | rfl <;>
      simp [Heap.rc, H_cells_zero, H_cells_one, H_cells_two, H_cells_three,
        H_cells_leaf, rootObj, childObj, grandObj, tipObj, leafObj]
  · intro q hq hfp
    rcases H_client_reachable hq with rfl | rfl | rfl <;>
      rcases H_footprint hfp with g | g | g | g | g <;> simp_all
  · intro x r hx hr
    have hx0 : x = 0 := by
      by_cases h0 : x = 0
      · exact h0
      · exfalso
        by_cases h1 : x = 1 <;> by_cases h10 : x = 10 <;> by_cases h11 : x = 11 <;>
          simp [ctx0, h0, h1, h10, h11] at hx
    subst hx0
    have hr0 : r = 0 := by simpa [ctx0] using hr.symm
    subst hr0
    exact MutableFootprint.root H_cells_zero (by simp [rootObj])

/-! ## The take-out heaps' cells -/

theorem H1_cells_one : H1.cells 1 = some childObj := by
  simp [H1, blankLevel, l0, H, Heap.set]

theorem H1_cells_two : H1.cells 2 = some grandObj := by
  simp [H1, blankLevel, l0, H, Heap.set]

theorem H1_cells_three : H1.cells 3 = some tipObj := by
  simp [H1, blankLevel, l0, H, Heap.set]

theorem H1_cells_leaf : H1.cells 40 = some leafObj := by
  simp [H1, blankLevel, l0, H, Heap.set]

theorem H2_cells_two : H2.cells 2 = some grandObj := by
  simp [H2, H1, blankLevel, l0, l1, H, Heap.set]

theorem H2_cells_three : H2.cells 3 = some tipObj := by
  simp [H2, H1, blankLevel, l0, l1, H, Heap.set]

theorem H2_cells_leaf : H2.cells 40 = some leafObj := by
  simp [H2, H1, blankLevel, l0, l1, H, Heap.set]

theorem H3_cells_three : H3.cells 3 = some tipObj := by
  simp [H3, H2, H1, blankLevel, l0, l1, l2, H, Heap.set]

theorem H3_cells_leaf : H3.cells 40 = some leafObj := by
  simp [H3, H2, H1, blankLevel, l0, l1, l2, H, Heap.set]

/-! ## Footprints of the take-out heaps -/

/-- The extracted child's footprint at the root's take-out heap. -/
theorem H1_footprint {q : Ref} (h : MutableFootprint H1 1 q) :
    q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 40 := by
  induction h with
  | root _ _ => exact Or.inl rfl
  | step hr hcell hp hmem hcell' hp' ih =>
      rcases ih with rfl | rfl | rfl | rfl
      · rw [H1_cells_one] at hcell
        have ho : childObj = _ := Option.some.inj hcell
        subst ho
        simp [fieldRefs, refsOf, childObj] at hmem
        exact Or.inr (Or.inl hmem)
      · rw [H1_cells_two] at hcell
        have ho : grandObj = _ := Option.some.inj hcell
        subst ho
        simp [fieldRefs, refsOf, grandObj] at hmem
        exact Or.inr (Or.inr (Or.inl hmem))
      · rw [H1_cells_three] at hcell
        have ho : tipObj = _ := Option.some.inj hcell
        subst ho
        simp [fieldRefs, refsOf, tipObj] at hmem
        exact Or.inr (Or.inr (Or.inr hmem))
      · rw [H1_cells_leaf] at hcell
        have ho : leafObj = _ := Option.some.inj hcell
        subst ho
        simp [fieldRefs, refsOf, leafObj] at hmem

/-- The tip's footprint at the child level's take-out heap. -/
theorem H2_footprint {q : Ref} (h : MutableFootprint H2 2 q) :
    q = 2 ∨ q = 3 ∨ q = 40 := by
  induction h with
  | root _ _ => exact Or.inl rfl
  | step hr hcell hp hmem hcell' hp' ih =>
      rcases ih with rfl | rfl | rfl
      · rw [H2_cells_two] at hcell
        have ho : grandObj = _ := Option.some.inj hcell
        subst ho
        simp [fieldRefs, refsOf, grandObj] at hmem
        exact Or.inr (Or.inl hmem)
      · rw [H2_cells_three] at hcell
        have ho : tipObj = _ := Option.some.inj hcell
        subst ho
        simp [fieldRefs, refsOf, tipObj] at hmem
        exact Or.inr (Or.inr hmem)
      · rw [H2_cells_leaf] at hcell
        have ho : leafObj = _ := Option.some.inj hcell
        subst ho
        simp [fieldRefs, refsOf, leafObj] at hmem

/-- The leaf's footprint at the grandchild level's take-out heap. -/
theorem H3_footprint {q : Ref} (h : MutableFootprint H3 3 q) :
    q = 3 ∨ q = 40 := by
  induction h with
  | root _ _ => exact Or.inl rfl
  | step hr hcell hp hmem hcell' hp' ih =>
      rcases ih with rfl | rfl
      · rw [H3_cells_three] at hcell
        have ho : tipObj = _ := Option.some.inj hcell
        subst ho
        simp [fieldRefs, refsOf, tipObj] at hmem
        exact Or.inr hmem
      · rw [H3_cells_leaf] at hcell
        have ho : leafObj = _ := Option.some.inj hcell
        subst ho
        simp [fieldRefs, refsOf, leafObj] at hmem

/-- The parent array is outside the extracted child's mutable footprint. -/
theorem sepRoot : ¬ MutableFootprint H1 1 0 := by
  intro h
  rcases H1_footprint h with g | g | g | g <;> simp_all

theorem sepChild : ¬ MutableFootprint H2 2 1 := by
  intro h
  rcases H2_footprint h with g | g | g | g <;> simp_all

theorem sepGrand : ¬ MutableFootprint H3 3 2 := by
  intro h
  rcases H3_footprint h with g | g <;> simp_all

/-! ## The path premises -/

theorem slots : Slots H [l0, l1, l2] := by
  intro l hl
  simp at hl
  rcases hl with rfl | rfl | rfl
  · exact ⟨H_cells_zero, by decide, by simp [l0, rootObj]⟩
  · exact ⟨H_cells_one, by decide, by simp [l1, childObj]⟩
  · exact ⟨H_cells_two, by decide, by simp [l2, grandObj]⟩

theorem slotsH1 : Slots H1 [l1, l2] := by
  intro l hl
  simp at hl
  rcases hl with rfl | rfl
  · exact ⟨H1_cells_one, by decide, by simp [l1, childObj]⟩
  · exact ⟨H1_cells_two, by decide, by simp [l2, grandObj]⟩

theorem slotsH2Tail : Slots H2 [l2] := by
  intro l hl
  simp at hl
  subst hl
  exact ⟨H2_cells_two, by decide, by simp [l2, grandObj]⟩

theorem chained : Chained [l0, l1, l2] := ⟨rfl, rfl, rfl, rfl, trivial⟩

theorem distinct : DistinctArrays [l0, l1, l2] := by
  refine ⟨?_, ?_, ?_, trivial⟩
  · intro m hm
    simp at hm
    rcases hm with rfl | rfl <;> simp [l0, l1, l2]
  · intro m hm
    simp at hm
    subst hm
    simp [l1, l2]
  · intro m hm
    simp at hm

/-- A one-level tail's distinctness is vacuous but not definitionally `True`. -/
theorem distinctL2 : DistinctArrays [l2] := ⟨by intro m hm; simp at hm, trivial⟩

theorem levelEnv0 : LevelEnv pathVar valueVar env0 l0 := by
  refine ⟨?_, ?_, ⟨0, ?_⟩, ⟨1, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [l0, env0, pathVar, valueVar]

theorem levelEnv1 : LevelEnv pathVar valueVar env1 l1 := by
  refine ⟨?_, ?_, ⟨0, ?_⟩, ⟨1, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [l1, l0, env1, env0, pathVar, valueVar, bindLevel, isolateEnv, Env.set]

theorem levelEnv2 : LevelEnv pathVar valueVar env2 l2 := by
  refine ⟨?_, ?_, ⟨0, ?_⟩, ⟨1, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [l2, l1, l0, env2, env1, env0, pathVar, valueVar, bindLevel, isolateEnv, Env.set]

theorem envok : EnvOK pathVar valueVar env0 [l0, l1, l2] :=
  ⟨levelEnv0, levelEnv1, levelEnv2, trivial⟩

theorem endsAtAll : EndsAt 3 [l0, l1, l2] := by simp [EndsAt, l2]

theorem endsAtH1 : EndsAt 3 [l1, l2] := by simp [EndsAt, l2]

theorem endsAtH2 : EndsAt 3 [l2] := by simp [EndsAt, l2]

theorem liveTip : Live H 3 := ⟨tipObj, H_cells_three, by simp [tipObj]⟩

theorem liveTipH1 : Live H1 3 := ⟨tipObj, H1_cells_three, by simp [tipObj]⟩

theorem liveTipH2 : Live H2 3 := ⟨tipObj, H2_cells_three, by simp [tipObj]⟩

/-- The leaf is in the root's footprint at the entry heap: the body's only
extraction annotation. -/
theorem annBody : AnnotationsIn H 3 body := by
  refine ⟨?_, trivial⟩
  exact MutableFootprint.step_of_slot (i := 0)
    (MutableFootprint.root H_cells_three (by simp [tipObj])) H_cells_three
    (by simp [tipObj]) (by decide) H_cells_leaf (by simp [leafObj])

theorem annBodyH1 : AnnotationsIn H1 3 body := by
  refine ⟨?_, trivial⟩
  exact MutableFootprint.step_of_slot (i := 0)
    (MutableFootprint.root H1_cells_three (by simp [tipObj])) H1_cells_three
    (by simp [tipObj]) (by decide) H1_cells_leaf (by simp [leafObj])

theorem annBodyH2 : AnnotationsIn H2 3 body := by
  refine ⟨?_, trivial⟩
  exact MutableFootprint.step_of_slot (i := 0)
    (MutableFootprint.root H2_cells_three (by simp [tipObj])) H2_cells_three
    (by simp [tipObj]) (by decide) H2_cells_leaf (by simp [leafObj])

theorem annBodyH3 : AnnotationsIn H3 3 body := by
  refine ⟨?_, trivial⟩
  exact MutableFootprint.step_of_slot (i := 0)
    (MutableFootprint.root H3_cells_three (by simp [tipObj])) H3_cells_three
    (by simp [tipObj]) (by decide) H3_cells_leaf (by simp [leafObj])

/-! ## The leaf body's agreement and the isolated invariants -/

/-- The admitted body's own agreement at the state the innermost call hands it.
This is the one premise the path theory assumes: the emitted recursive callee's
body is not captured, so its agreement is a hypothesis about the model body the
certificate admits, not a fact about the compiled declaration. -/
theorem leafBody : Agrees H3 env3 body := by
  refine ⟨3, tipObj, 0, ?_, ?_, H3_cells_three, by decide, ?_⟩
  · simp [env3, isolateEnv, bindLevel, Env.set, l2]
  · simp [env3, env2, env1, env0, isolateEnv, bindLevel, Env.set, l0, l1, l2, pathVar]
  · refine ⟨3, 40, { tipObj with fields := tipObj.fields.setIfInBounds 0 (.scalar 0) }, 0,
      ?_, ?_, ?_, ?_, trivial⟩
    · simp [Env.set]
    · simp [Env.set]
    · simp [env3, env2, env1, env0, isolateEnv, bindLevel, Env.set, l0, l1, l2, pathVar]
    · exact Heap.set_self _ _ _

/-- The caller's invariant after the root's take-out. -/
theorem invCall0 : Inv H1 (bindLevel env0 l0) ctx1 :=
  inv_after_takeOut (H := H) (env := env0) (c := ctx0) (l := l0)
    inv0 (by rfl) (by rfl) (by rfl) H_cells_zero

/-- The caller's invariant at the isolated context the root's call body is
checked from. -/
theorem invIso0 : Inv H1 env1 ctxIso0 :=
  inv_isolated (H := H1) (env := bindLevel env0 l0) (c := ctx1) (state := 3)
    (path := pathVar) (x := valueVar) (r := 1) invCall0 (by rfl) (by rfl) (by rfl) (by rfl)

/-- The caller's invariant after the child level's take-out. -/
theorem invCall1 : Inv H2 (bindLevel env1 l1) ctxI1 :=
  inv_after_takeOut (H := H1) (env := env1) (c := ctxIso0) (l := l1)
    invIso0 (by rfl) (by rfl) (by rfl) H1_cells_one

/-- The caller's invariant at the isolated context the child's call body is
checked from. -/
theorem invIso1 : Inv H2 env2 ctxIso1 :=
  inv_isolated (H := H2) (env := bindLevel env1 l1) (c := ctxI1) (state := 8)
    (path := pathVar) (x := valueVar) (r := 2) invCall1 (by rfl) (by rfl) (by rfl) (by rfl)

/-- The caller's invariant after the grandchild level's take-out. -/
theorem invCall2 : Inv H3 (bindLevel env2 l2) ctxI4 :=
  inv_after_takeOut (H := H2) (env := env2) (c := ctxIso1) (l := l2)
    invIso1 (by rfl) (by rfl) (by rfl) H2_cells_two

/-- The caller's invariant at the isolated context the leaf body is checked
from. -/
theorem invIso2 : Inv H3 env3 ctxIso2 :=
  inv_isolated (H := H3) (env := bindLevel env2 l2) (c := ctxI4) (state := 16)
    (path := pathVar) (x := valueVar) (r := 3) invCall2 (by rfl) (by rfl) (by rfl) (by rfl)

/-- The state-indexed heap premise of the leaf body, derived from its invariant,
its agreement and the checker's acceptance. -/
theorem takeOutsOKBody : TakeOutsOK H3 env3 body :=
  takeOutsOK_of_inv invIso2 leafBody checkNF_body

/-! ## The call contracts, bottom up -/

/-- The innermost call: the admitted body, through `callAt_frame_confined`. -/
theorem contractL2 :
    ∃ H' env' v ws,
      runN body env3 H3 = .done H' env' v ws ∧ (∀ w ∈ ws, w.2 = true) ∧
        v = .ref 3 ∧
        (∀ q, ¬ MutableFootprint H3 3 q → H'.cells q = H3.cells q) :=
  callAt_frame_confined (c := ctxI4) (state := 16) (path := pathVar) (x := valueVar)
    (r := 3) (body := body) (H := H3) (env := env3) (cb := ctxBody)
    annBodyH3 checkNF_body ⟨25, rfl, rfl, rfl⟩ invIso2 takeOutsOKBody

/-- The frame preservation the grandchild level's call obligation needs, read
off that call contract. -/
theorem preservedL2 {H' : Heap} {envb : Env} {vb : Val} {wsb : List Write}
    (hrun : runN body env3 H3 = .done H' envb vb wsb) :
    ∀ q, ¬ MutableFootprint H3 3 q → H'.cells q = H3.cells q := by
  obtain ⟨Hc, envc, vc, wsc, hc, -, -, hconf⟩ := contractL2
  rw [hc] at hrun
  injection hrun with hH _ _ _
  subst hH
  exact hconf

/-- The grandchild level's child-call contract. -/
theorem confinedAt2 : ChildConfined pathVar valueVar body H2 env2 [l2] :=
  ⟨sepGrand, fun _ _ _ _ hrun => preservedL2 hrun, trivial⟩

/-- The child level's call: the remaining path through `level_call_confined`. -/
theorem contractL1 :
    ∃ H' env' v ws,
      runN (build pathVar valueVar body [l2]) env2 H2 = .done H' env' v ws ∧
        (∀ w ∈ ws, w.2 = true) ∧ v = .ref 2 ∧
        (∀ q, ¬ MutableFootprint H2 2 q → H'.cells q = H2.cells q) :=
  level_call_confined (rest' := []) (m := l2) (l := l1) (tip := 3)
    (H := H1) (env := env1) (c := ctxI1) (cb := ctxInner1)
    slotsH2Tail trivial rfl distinctL2 envok.2.2 leafBody confinedAt2 invCall1
    (by rfl) (by rfl) (by rfl) (by rfl) checkNF_inner1 ⟨21, rfl, rfl, rfl⟩
    endsAtH2 liveTipH2 annBodyH2

/-- The frame preservation the child level's call obligation needs. -/
theorem preservedL1 {H' : Heap} {envb : Env} {vb : Val} {wsb : List Write}
    (hrun : runN (build pathVar valueVar body [l2]) env2 H2 = .done H' envb vb wsb) :
    ∀ q, ¬ MutableFootprint H2 2 q → H'.cells q = H2.cells q := by
  obtain ⟨Hc, envc, vc, wsc, hc, -, -, hconf⟩ := contractL1
  rw [hc] at hrun
  injection hrun with hH _ _ _
  subst hH
  exact hconf

/-- The child level's child-call contract. -/
theorem confinedAt1 : ChildConfined pathVar valueVar body H1 env1 [l1, l2] :=
  ⟨sepChild, fun _ _ _ _ hrun => preservedL1 hrun, confinedAt2⟩

/-- The root level's call: the remaining path through `level_call_confined`. -/
theorem contractL0 :
    ∃ H' env' v ws,
      runN (build pathVar valueVar body [l1, l2]) env1 H1 = .done H' env' v ws ∧
        (∀ w ∈ ws, w.2 = true) ∧ v = .ref 1 ∧
        (∀ q, ¬ MutableFootprint H1 1 q → H'.cells q = H1.cells q) :=
  level_call_confined (rest' := [l2]) (m := l1) (l := l0) (tip := 3)
    (H := H) (env := env0) (c := ctx1) (cb := ctxInner0)
    slotsH1 chained.2.2 rfl distinct.2 envok.2 leafBody confinedAt1 invCall0
    (by rfl) (by rfl) (by rfl) (by rfl) checkNF_inner0 ⟨13, rfl, rfl, rfl⟩
    endsAtH1 liveTipH1 annBodyH1

/-- The frame preservation the root level's call obligation needs. -/
theorem preservedL0 {H' : Heap} {envb : Env} {vb : Val} {wsb : List Write}
    (hrun : runN (build pathVar valueVar body [l1, l2]) env1 H1 =
      .done H' envb vb wsb) :
    ∀ q, ¬ MutableFootprint H1 1 q → H'.cells q = H1.cells q := by
  obtain ⟨Hc, envc, vc, wsc, hc, -, -, hconf⟩ := contractL0
  rw [hc] at hrun
  injection hrun with hH _ _ _
  subst hH
  exact hconf

/-- The child-call contract at every level of the concrete path. -/
theorem confined : ChildConfined pathVar valueVar body H env0 [l0, l1, l2] :=
  ⟨sepRoot, fun _ _ _ _ hrun => preservedL0 hrun, confinedAt1⟩

/-! ## The path theory's derived premises -/

/-- The whole program's agreement, derived from the path: the certificate
supplies no `Agrees` of `code` directly. -/
theorem agrees0 : Agrees H env0 code :=
  agrees_of_path (rest := [l1, l2]) (l := l0) (H := H) (env := env0)
    (path := pathVar) (value := valueVar) (body := body)
    slots chained distinct envok leafBody confined

/-- Every reference the program extracts is in the root's footprint. -/
theorem annotationsIn0 : AnnotationsIn H 0 code :=
  annotationsIn_of_path (rest := [l1, l2]) (l := l0) (root := 0) (tip := 3)
    (body := body) (path := pathVar) (value := valueVar)
    slots chained rfl endsAtAll liveTip annBody

/-- The entry context has no borrowed handle. -/
theorem hnoBorrow : ∀ z r, ctx0.us z = .borrow → ctx0.refOf z = some r → False := by
  intro z r hz _
  by_cases h0 : z = 0 <;> by_cases h1 : z = 1 <;> by_cases h10 : z = 10 <;>
    by_cases h11 : z = 11 <;> simp [ctx0, h0, h1, h10, h11] at hz

/-! ## The certificate -/

/-- The depth-three certificate.

`path_run_separated` supplies the fault-free, exclusively-writing run, the
invariant at the output context, the untouched cells outside the root's
footprint, and that nothing the client can reach lies in that footprint; the
heap is then read cell by cell to show the body's write landed, the three
extractions were restored, and the client's own chain is intact. `footprint_within`
and `clientSeparated_preserved` carry the entry condition's separation to the
post heap, where the client still reaches its own leaf and that leaf is still
outside the state's footprint. -/
theorem certificate :
    ∃ H' env' ws,
      runN code env0 H = .done H' env' (.ref 0) ws ∧
        (∀ w ∈ ws, w.2 = true) ∧ ws = [(3, true)] ∧
        Inv H' env' ctxF ∧ Outside H' H 0 ∧
        (∀ r, ClientReachable H' client r → ¬ MutableFootprint H 0 r) ∧
        (∀ r, MutableFootprint H' 0 r → MutableFootprint H 0 r) ∧
        ClientSeparated H' 0 client ∧
        ClientReachable H' client 52 ∧ ¬ MutableFootprint H' 0 52 ∧
        H'.cells 3 = some finalTip ∧ H'.cells 0 = some restoredRoot ∧
        H'.cells 1 = some restoredChild ∧ H'.cells 2 = some restoredGrand ∧
        H'.cells 40 = some leafObj ∧ H'.cells 50 = some clientWrap ∧
        H'.cells 51 = some clientMid ∧ H'.cells 52 = some clientLeaf := by
  obtain ⟨H', env', v, ws, hrun, hws, hinv, hout, hreach⟩ :=
    path_run_separated (rest := [l1, l2]) (l := l0) (body := body) (H := H)
      (env := env0) (c := ctx0) (root := 0) (client := client) (ctx' := ctxF) (tip := 3)
      slots chained distinct envok leafBody confined entry0 rfl endsAtAll liveTip
      annBody hnoBorrow checkN_code
  have hred := hrun
  simp [build, runN, body, env0, isolateEnv, Env.set, l0, l1, l2, H,
    Heap.exclusive?, rootObj, childObj, grandObj, tipObj, leafObj, clientWrap,
    clientMid, clientLeaf, Res.addWrite, addWrites, run] at hred
  injection hred with hH henv hv hws'
  simp only [List.append_nil] at hws'
  rw [← hv] at hrun
  have h3 : H'.cells 3 = some finalTip := by
    rw [← hH]
    rw [Heap.set_other _ 0 3 _ (by decide), Heap.set_other _ 1 3 _ (by decide),
      Heap.set_other _ 2 3 _ (by decide), Heap.set_self]
    exact some_obj_eq (by decide) (by decide) (by decide)
  have h0 : H'.cells 0 = some restoredRoot := by
    rw [← hH]
    rw [Heap.set_self]
    exact some_obj_eq (by decide) (by decide) (by decide)
  have h1 : H'.cells 1 = some restoredChild := by
    rw [← hH]
    rw [Heap.set_other _ 0 1 _ (by decide), Heap.set_self]
    exact some_obj_eq (by decide) (by decide) (by decide)
  have h2 : H'.cells 2 = some restoredGrand := by
    rw [← hH]
    rw [Heap.set_other _ 0 2 _ (by decide), Heap.set_other _ 1 2 _ (by decide),
      Heap.set_self]
    exact some_obj_eq (by decide) (by decide) (by decide)
  have h40 : H'.cells 40 = some leafObj := by
    rw [← hH]
    rw [Heap.set_other _ 0 40 _ (by decide), Heap.set_other _ 1 40 _ (by decide),
      Heap.set_other _ 2 40 _ (by decide), Heap.set_other _ 3 40 _ (by decide),
      Heap.set_other _ 3 40 _ (by decide), Heap.set_other _ 3 40 _ (by decide),
      Heap.set_other _ 2 40 _ (by decide), Heap.set_other _ 1 40 _ (by decide),
      Heap.set_other _ 0 40 _ (by decide)]
    exact H_cells_leaf
  have h50 : H'.cells 50 = some clientWrap := by
    rw [← hH]
    rw [Heap.set_other _ 0 50 _ (by decide), Heap.set_other _ 1 50 _ (by decide),
      Heap.set_other _ 2 50 _ (by decide), Heap.set_other _ 3 50 _ (by decide),
      Heap.set_other _ 3 50 _ (by decide), Heap.set_other _ 3 50 _ (by decide),
      Heap.set_other _ 2 50 _ (by decide), Heap.set_other _ 1 50 _ (by decide),
      Heap.set_other _ 0 50 _ (by decide)]
    exact H_cells_50
  have h51 : H'.cells 51 = some clientMid := by
    rw [← hH]
    rw [Heap.set_other _ 0 51 _ (by decide), Heap.set_other _ 1 51 _ (by decide),
      Heap.set_other _ 2 51 _ (by decide), Heap.set_other _ 3 51 _ (by decide),
      Heap.set_other _ 3 51 _ (by decide), Heap.set_other _ 3 51 _ (by decide),
      Heap.set_other _ 2 51 _ (by decide), Heap.set_other _ 1 51 _ (by decide),
      Heap.set_other _ 0 51 _ (by decide)]
    exact H_cells_51
  have h52 : H'.cells 52 = some clientLeaf := by
    rw [← hH]
    rw [Heap.set_other _ 0 52 _ (by decide), Heap.set_other _ 1 52 _ (by decide),
      Heap.set_other _ 2 52 _ (by decide), Heap.set_other _ 3 52 _ (by decide),
      Heap.set_other _ 3 52 _ (by decide), Heap.set_other _ 3 52 _ (by decide),
      Heap.set_other _ 2 52 _ (by decide), Heap.set_other _ 1 52 _ (by decide),
      Heap.set_other _ 0 52 _ (by decide)]
    exact H_cells_52
  -- The run added no cell the entry heap lacked.
  have hmono : ∀ q, H.cells q = none → H'.cells q = none := by
    intro q hq
    have hq0 : q ≠ 0 := by
      intro h; subst h; rw [H_cells_zero] at hq; exact absurd hq (by simp)
    have hq1 : q ≠ 1 := by
      intro h; subst h; rw [H_cells_one] at hq; exact absurd hq (by simp)
    have hq2 : q ≠ 2 := by
      intro h; subst h; rw [H_cells_two] at hq; exact absurd hq (by simp)
    have hq3 : q ≠ 3 := by
      intro h; subst h; rw [H_cells_three] at hq; exact absurd hq (by simp)
    rw [← hH]
    rw [Heap.set_other _ 0 q _ hq0, Heap.set_other _ 1 q _ hq1,
      Heap.set_other _ 2 q _ hq2, Heap.set_other _ 3 q _ hq3,
      Heap.set_other _ 3 q _ hq3, Heap.set_other _ 3 q _ hq3,
      Heap.set_other _ 2 q _ hq2, Heap.set_other _ 1 q _ hq1,
      Heap.set_other _ 0 q _ hq0]
    exact hq
  -- Every field reference of a post-heap footprint cell was in the entry
  -- footprint: the only reference-valued write is the leaf the body restores,
  -- and the only changed cell is the tip, whose reference slots did not move.
  have hrefs : ∀ q, MutableFootprint H 0 q → ∀ z,
      (∃ o o', H.cells q = some o ∧ H'.cells q = some o' ∧ z ∈ fieldRefs o') →
        MutableFootprint H 0 z := by
    intro q hq z h
    obtain ⟨o, o', hcell, hcell', hz⟩ := h
    rcases H_footprint hq with rfl | rfl | rfl | rfl | rfl
    · have ho : o' = restoredRoot := by
        rw [h0] at hcell'
        exact (Option.some.inj hcell').symm
      subst ho
      have hz1 : z = 1 := by
        have hl : fieldRefs restoredRoot = [1] := by decide
        rw [hl] at hz
        simpa using hz
      subst hz1
      exact H_fp1
    · have ho : o' = restoredChild := by
        rw [h1] at hcell'
        exact (Option.some.inj hcell').symm
      subst ho
      have hz2 : z = 2 := by
        have hl : fieldRefs restoredChild = [2] := by decide
        rw [hl] at hz
        simpa using hz
      subst hz2
      exact H_fp2
    · have ho : o' = restoredGrand := by
        rw [h2] at hcell'
        exact (Option.some.inj hcell').symm
      subst ho
      have hz3 : z = 3 := by
        have hl : fieldRefs restoredGrand = [3] := by decide
        rw [hl] at hz
        simpa using hz
      subst hz3
      exact H_fp3
    · have ho : o' = finalTip := by
        rw [h3] at hcell'
        exact (Option.some.inj hcell').symm
      subst ho
      have hz40 : z = 40 := by
        have hl : fieldRefs finalTip = [40] := by decide
        rw [hl] at hz
        simpa using hz
      subst hz40
      exact H_fp40
    · have ho : o' = leafObj := by
        rw [h40] at hcell'
        exact (Option.some.inj hcell').symm
      subst ho
      have hl : fieldRefs leafObj = [] := by decide
      rw [hl] at hz
      simp at hz
  have hwithin : ∀ r, MutableFootprint H' 0 r → MutableFootprint H 0 r :=
    footprint_within (H := H) (H' := H') (root := 0) hmono
      entry0.toInv.nonPersistent hrefs
  have hsep : ClientSeparated H' 0 client :=
    clientSeparated_preserved entry0.separated hout hwithin
  have hmem1 : (51 : Ref) ∈ fieldRefs clientWrap := by
    simp [fieldRefs, refsOf, clientWrap]
  have hmem2 : (52 : Ref) ∈ fieldRefs clientMid := by
    simp [fieldRefs, refsOf, clientMid]
  have reach : ClientReachable H' client 52 :=
    ClientReachable.step
      (ClientReachable.step (ClientReachable.direct (by simp [client])) h50 hmem1)
      h51 hmem2
  exact ⟨H', env', ws, hrun, hws, hws'.symm, hinv, hout, hreach, hwithin, hsep,
    reach, hsep 52 reach, h3, h0, h1, h2, h40, h50, h51, h52⟩

/-- The observed tip after the run: the body's write landed in slot 1 and the
extracted leaf is back in slot 0. This is the heap-changing positive example. -/
theorem finalTip_slots :
    finalTip.fields[0]? = some (.ref 40) ∧ finalTip.fields[1]? = some (.scalar 7) :=
  ⟨by decide, by decide⟩

/-- The replacement is nonzero and changes the slot the body wrote. -/
theorem finalTip_nontrivial : tipObj.fields[1]? ≠ finalTip.fields[1]? := by decide

#print axioms Ownership.PathSafety.path_run_safe
#print axioms Ownership.PathSafety.path_run_confined
#print axioms Ownership.PathSafety.path_run_separated
#print axioms Ownership.PathSafety.level_call_confined
#print axioms Ownership.PathSafety.client_retention
#print axioms Ownership.PathSafety.ClientReachable.of_outside
#print axioms Ownership.PathSafety.footprint_within
#print axioms Ownership.PathSafety.clientSeparated_preserved
#print axioms OwnershipTest.PathSafety.entry0
#print axioms OwnershipTest.PathSafety.agrees0
#print axioms OwnershipTest.PathSafety.annotationsIn0
#print axioms OwnershipTest.PathSafety.contractL2
#print axioms OwnershipTest.PathSafety.contractL1
#print axioms OwnershipTest.PathSafety.contractL0
#print axioms OwnershipTest.PathSafety.confined
#print axioms OwnershipTest.PathSafety.certificate

end OwnershipTest.PathSafety
