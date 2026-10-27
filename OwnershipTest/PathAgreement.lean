/-
The path theory on a concrete two-level heap.

The heap is a root array (ref 0) whose slot 0 holds the child array (ref 1),
whose slot 0 holds the tip array (ref 2), whose slot 0 holds the extracted leaf
(ref 20). Every cell is counted once and each array's other slot holds an
unrelated scalar.

The program is `Ownership.Path.build` at this path: the root slot is extracted and
the child handed to the recursive call; the child slot is extracted and the tip
handed to the innermost call; the opaque body takes the leaf out of the tip,
restores it, and writes the nonzero scalar `7` into the tip's other slot; the
two extractions are then restored in reverse order.

`checkN_code` accepts it, `entry0` is the entry condition, and the path premises
(`slots`, `chained`, `distinct`, `envok`, `leaf`, `confined`) are the concrete
ones. `agrees0` and `annotationsIn0` are *derived* by
`Ownership.Path.agrees_of_path` and `Ownership.Path.annotationsIn_of_path` — the
certificate supplies no `Agrees` and no `AnnotationsIn` of the built program
directly. The run is then discharged by `checkN_sound_of_entryInv`, and
`callAt_frame_confined` is invoked on the admitted model body the outer call runs
with the derived annotation premise.

The innermost body's own agreement is the one premise the path theory assumes
(`leaf`): the emitted recursive callee's body is not captured, so its agreement is
a hypothesis about the admitted model body, not a derived fact.

The emitted correspondence's `NestedAgrees` is not derivable from the path
theory. `nestedAgrees_modelFields` derives the part that is: its four model
environment fields (`array_model`, `index_model`, `value_model`, `path_model`) are
this path's environment facts read through the recognizer's binder layout. The
remaining fields are machine facts the path theory has no vocabulary for: the
`NestedMachine`'s heap (`heap`), its array and value slots (`array_machine`,
`value_machine`), the scalar it hands the callee as the continuation path
(`callPath`), the model variable it keeps the extracted child in (`childVar`),
the reified `Path.index` node's index field (`nodes`), and the recorded write
trace (`writes`). Each is a fact about the reified recognizer operand or about
the extraction machine, not about the model heap, the path's slots or the
extraction annotations; supplying them needs the recognizer's operand identities
(`NestedLayout`) and the reified artifact, which this theory does not mention.
-/
import Ownership.Path
import Ownership.Entry
import OwnershipLcnf.NestedSemantics

open Ownership
open Ownership.Nested
open Ownership.Entry
open Ownership.Path

namespace OwnershipTest.PathAgreement

/-! ## The object tree -/

/-- The root array: slot 0 holds the child, slot 1 an unrelated sibling scalar. -/
def rootObj : Obj := ⟨#[.ref 1, .scalar 5], 1, false⟩

/-- The child array: slot 0 holds the tip, slot 1 an unrelated scalar. -/
def childObj : Obj := ⟨#[.ref 2, .scalar 3], 1, false⟩

/-- The tip array: slot 0 holds the extracted leaf, slot 1 the scalar the body
overwrites. -/
def tipObj : Obj := ⟨#[.ref 20, .scalar 4], 1, false⟩

/-- The tip after the body's designated write. -/
def writtenTip : Obj := ⟨#[.ref 20, .scalar 7], 1, false⟩

/-- The leaf the body extracts and restores. -/
def leafObj : Obj := ⟨#[.scalar 0], 1, false⟩

/-- Root → child → tip → leaf, each live cell counted once. -/
def H : Heap :=
  { cells := fun r =>
      if r = 0 then some rootObj
      else if r = 1 then some childObj
      else if r = 2 then some tipObj
      else if r = 20 then some leafObj
      else none
    next := 21 }

/-! ## The path -/

/-- The root level: extract slot 0 of `ref 0` into variables 2 and 3. -/
def l0 : Level :=
  { arr := 0, obj := rootObj, idx := 0, child := 1
    arrayVar := 0, indexVar := 1, parentVar := 2, childVar := 3
    resultVar := 4, restoredVar := 5 }

/-- The child level: extract slot 0 of `ref 1` — reached through the child
variable 3 — into variables 6 and 8. Its index is the call's path variable 10, the
only index the isolated environment exposes to the level's body. -/
def l1 : Level :=
  { arr := 1, obj := childObj, idx := 0, child := 2
    arrayVar := 3, indexVar := 10, parentVar := 6, childVar := 8
    resultVar := 12, restoredVar := 13 }

/-- The call's path scalar. -/
def pathVar : Var := 10

/-- The call's value scalar. -/
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
  .takeOut 8 10 14 15 20
    (.putBack 14 15 10 16
      (.base (.let 17 (.checkAlias 16) (.let 18 (.lit 7) (.setArr 17 11 18 (.ret 17))))))

/-- The built program: extract both levels, run the body on the tip, restore both
slots. -/
def code : NCode := build pathVar valueVar body [l0, l1]

/-! ## The checker state -/

/-- The caller's context: the root handle owned, the root index and the call's
scalars visible, and the counted heap's multiplicities. -/
def ctx0 : Ctx :=
  { us := fun x =>
      if x = 0 then .owned
      else if x = 1 then .scalar
      else if x = 10 then .scalar
      else if x = 11 then .scalar
      else .dead
    refOf := fun x => if x = 0 then some 0 else none
    mult := fun r => if r = 0 then 1 else if r = 1 then 1 else if r = 2 then 1
      else if r = 20 then 1 else 0 }

/-- The context after the root's take-out. -/
def ctx1 : Ctx := (ctx0.move 0 2).bindOwned 3 1

/-- The context the child call's body is checked from. -/
def ctxIso : Ctx := isolatedCtx ctx0 3 10 11 1

/-- The context the child call's body is checked to. -/
def ctxInner : Ctx :=
  ((ctxIso.move 3 6).bindOwned 8 2).move 8 12 |>.move 6 13 |>.setUs 12 .dead

/-- The caller's context once the child call returns. -/
def ctx2 : Ctx := ctx1.move 3 4

/-- The caller's context after the root's put-back. -/
def ctxF : Ctx := (ctx2.move 2 5).setUs 4 .dead

/-- The heap the root's take-out leaves. -/
abbrev H1 : Heap := blankLevel H l0

/-- The heap the child's take-out leaves. -/
abbrev H2 : Heap := blankLevel H1 l1

/-! ## Checker acceptance -/

/-- The inner code: the child level's program, whose innermost call runs the
admitted body. -/
def innerCode : NCode := build pathVar valueVar body [l1]

theorem checkNF_inner : checkNF ctxIso [] innerCode = some ctxInner := rfl

theorem checkN_code : checkN ctx0 code = some ctxF := rfl

/-! ## The take-out heaps -/

/-- The root after its take-out: the selected slot holds the placeholder. -/
def blankRoot : Obj := { rootObj with fields := rootObj.fields.setIfInBounds 0 (.scalar 0) }

/-- The child after its take-out. -/
def blankChild : Obj := { childObj with fields := childObj.fields.setIfInBounds 0 (.scalar 0) }

theorem H1_cells_zero : H1.cells 0 = some blankRoot := by simp [H1, blankLevel, l0, blankRoot]

theorem H1_cells_one : H1.cells 1 = some childObj := by simp [H1, blankLevel, l0, H, Heap.set]

theorem H1_cells_two : H1.cells 2 = some tipObj := by simp [H1, blankLevel, l0, H, Heap.set]

theorem H1_cells_leaf : H1.cells 20 = some leafObj := by simp [H1, blankLevel, l0, H, Heap.set]

theorem H2_cells_two : H2.cells 2 = some tipObj := by
  simp [H2, H1, blankLevel, l0, l1, H, Heap.set]

theorem H2_cells_leaf : H2.cells 20 = some leafObj := by
  simp [H2, H1, blankLevel, l0, l1, H, Heap.set]

/-! ## The invariant and the entry condition -/

theorem inv0 : Inv H env0 ctx0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r
    by_cases h0 : r = 0
    · subst h0; simp [H, ctx0, Heap.rc, rootObj]
    · by_cases h1 : r = 1
      · subst h1; simp [H, ctx0, Heap.rc, h0, childObj]
      · by_cases h2 : r = 2
        · subst h2; simp [H, ctx0, Heap.rc, h0, h1, tipObj]
        · by_cases h20 : r = 20
          · subst h20; simp [H, ctx0, Heap.rc, h0, h1, h2, leafObj]
          · simp [H, ctx0, Heap.rc, h0, h1, h2, h20]
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
          rw [show H.cells 2 = some tipObj by simp [H, h0, h1]] at hcell
          have ho : tipObj = o := Option.some.inj hcell
          subst ho; rfl
        · by_cases h20 : r = 20
          · subst h20
            rw [show H.cells 20 = some leafObj by simp [H, h0, h1, h2]] at hcell
            have ho : leafObj = o := Option.some.inj hcell
            subst ho; rfl
          · rw [show H.cells r = none by simp [H, h0, h1, h2, h20]] at hcell
            exact absurd hcell (by simp)

/-- Emptying the root's slot leaves the caller's invariant intact: the cell is
still live, still counted once, still non-persistent, and no other cell moved. -/
theorem invH1 : Inv H1 env0 ctx0 := by
  refine inv_of_rc_cells (H := H) (Hb := H1) inv0 ?_ ?_ ?_
  · intro q
    by_cases h0 : q = 0
    · subst h0
      simp [Heap.rc, H1_cells_zero, blankRoot, rootObj, ctx0]
    · have hrc : H1.rc q = H.rc q := by
        simp [Heap.rc, blankLevel_cells_ne (l := l0) (H := H) h0]
      rw [hrc]
      exact inv0.rc_eq q
  · intro q hq
    by_cases h0 : q = 0
    · subst h0
      rw [H1_cells_zero] at hq
      exact absurd hq (by simp)
    · rw [blankLevel_cells_ne (l := l0) h0] at hq
      exact hq
  · intro q o hcell
    by_cases h0 : q = 0
    · subst h0
      rw [H1_cells_zero] at hcell
      have ho : blankRoot = o := Option.some.inj hcell
      subst ho
      rfl
    · rw [blankLevel_cells_ne (l := l0) h0] at hcell
      exact inv0.nonPersistent q o hcell

/-! ## The entry condition -/

theorem H_cells_zero : H.cells 0 = some rootObj := by simp [H]

theorem H_cells_one : H.cells 1 = some childObj := by simp [H]

theorem H_cells_two : H.cells 2 = some tipObj := by simp [H]

theorem H_cells_leaf : H.cells 20 = some leafObj := by simp [H]

/-- The root's mutable footprint is exactly the four cells the path walks. -/
theorem H_footprint {q : Ref} (h : MutableFootprint H 0 q) :
    q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 20 := by
  induction h with
  | root _ _ => exact Or.inl rfl
  | step hr hcell hp hmem hc' hp' ih =>
      rcases ih with h | h | h | h
      · subst h
        rw [H_cells_zero] at hcell
        have ho : rootObj = _ := Option.some.inj hcell
        subst ho
        simp [fieldRefs, refsOf, rootObj] at hmem
        exact Or.inr (Or.inl hmem)
      · subst h
        rw [H_cells_one] at hcell
        have ho : childObj = _ := Option.some.inj hcell
        subst ho
        simp [fieldRefs, refsOf, childObj] at hmem
        exact Or.inr (Or.inr (Or.inl hmem))
      · subst h
        rw [H_cells_two] at hcell
        have ho : tipObj = _ := Option.some.inj hcell
        subst ho
        simp [fieldRefs, refsOf, tipObj] at hmem
        exact Or.inr (Or.inr (Or.inr hmem))
      · subst h
        rw [H_cells_leaf] at hcell
        have ho : leafObj = _ := Option.some.inj hcell
        subst ho
        simp [fieldRefs, refsOf, leafObj] at hmem

/-- The path's four cells are the entry condition's unique tree. -/
theorem entry0 : EntryInv H env0 ctx0 0 [] := by
  refine ⟨inv0, ?_, ?_, ?_⟩
  · intro q hq
    rcases H_footprint hq with rfl | rfl | rfl | rfl <;>
      simp [Heap.rc, H_cells_zero, H_cells_one, H_cells_two, H_cells_leaf, rootObj,
        childObj, tipObj, leafObj]
  · intro q hq _
    exact ClientReachable.isEmpty hq
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

/-! ## The path premises -/

theorem slots : Slots H [l0, l1] := by
  intro l hl
  rcases List.mem_cons.mp hl with rfl | hl
  · exact ⟨H_cells_zero, by decide, by simp [l0, rootObj]⟩
  · rw [List.mem_singleton] at hl
    subst hl
    exact ⟨H_cells_one, by decide, by simp [l1, childObj]⟩

theorem slotsTail : Slots H [l1] := by
  intro l hl
  rw [List.mem_singleton] at hl
  subst hl
  exact ⟨H_cells_one, by decide, by simp [l1, childObj]⟩

theorem chained : Chained [l0, l1] := by
  refine ⟨rfl, rfl, trivial⟩

theorem distinct : DistinctArrays [l0, l1] := by
  simp [DistinctArrays, l0, l1]

theorem distinctTail : DistinctArrays [l1] := by
  simp [DistinctArrays]

theorem envok : EnvOK pathVar valueVar env0 [l0, l1] := by
  refine ⟨?_, ?_, trivial⟩
  · refine ⟨?_, ?_, ⟨0, ?_⟩, ⟨1, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [l0, env0, pathVar, valueVar]
  · refine ⟨?_, ?_, ⟨0, ?_⟩, ⟨1, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [l0, l1, env0, pathVar, valueVar, bindLevel, isolateEnv, Env.set]

theorem liveTip : Live H 2 := ⟨tipObj, H_cells_two, by simp [tipObj]⟩

/-- The opaque body's own extraction annotation: the leaf is in the tip's mutable
footprint. -/
theorem annBody : AnnotationsIn H 2 body := by
  refine ⟨?_, trivial⟩
  exact MutableFootprint.step_of_slot (i := 0)
    (MutableFootprint.root H_cells_two (by simp [tipObj])) H_cells_two (by simp [tipObj])
    (by decide) H_cells_leaf (by simp [leafObj])

/-! ## The leaf body's agreement (assumed) and the child-call contract -/

/-- The environment the root's call exposes to its body. -/
abbrev env1 : Env := isolateEnv (bindLevel env0 l0) 3 10 11

/-- The environment the child's call exposes to the innermost body. -/
abbrev env2 : Env := isolateEnv (bindLevel env1 l1) 8 10 11

/-- The opaque body's own agreement at the state the innermost call hands it.
This is the premise the path theory assumes: the emitted recursive callee's body
is not captured, so its agreement is a hypothesis about the admitted model body. -/
theorem leaf : leafAgrees pathVar valueVar body H1 env1 [l1] := by
  show Agrees H2 env2 body
  refine ⟨2, tipObj, 0, ?_, ?_, H2_cells_two, by decide, ?_⟩
  · simp [isolateEnv, bindLevel, Env.set, l1]
  · simp [env0, isolateEnv, bindLevel, Env.set, l0, l1]
  · refine ⟨2, 20, { tipObj with fields := tipObj.fields.setIfInBounds 0 (.scalar 0) }, 0,
      ?_, ?_, ?_, ?_, trivial⟩
    · simp [Env.set]
    · simp [Env.set]
    · simp [env0, isolateEnv, bindLevel, Env.set, l0, l1]
    · exact Heap.set_self _ _ _

theorem H1_footprint {q : Ref} (h : MutableFootprint H1 1 q) : q = 1 ∨ q = 2 ∨ q = 20 := by
  induction h with
  | root _ _ => exact Or.inl rfl
  | step hr hcell hp hmem hc' hp' ih =>
      rcases ih with h | h | h
      · subst h
        rw [H1_cells_one] at hcell
        have ho : childObj = _ := Option.some.inj hcell
        subst ho
        simp [fieldRefs, refsOf, childObj] at hmem
        exact Or.inr (Or.inl hmem)
      · subst h
        rw [H1_cells_two] at hcell
        have ho : tipObj = _ := Option.some.inj hcell
        subst ho
        simp [fieldRefs, refsOf, tipObj] at hmem
        exact Or.inr (Or.inr hmem)
      · subst h
        rw [H1_cells_leaf] at hcell
        have ho : leafObj = _ := Option.some.inj hcell
        subst ho
        simp [fieldRefs, refsOf, leafObj] at hmem

theorem H2_footprint {q : Ref} (h : MutableFootprint H2 2 q) : q = 2 ∨ q = 20 := by
  induction h with
  | root _ _ => exact Or.inl rfl
  | step hr hcell hp hmem hc' hp' ih =>
      rcases ih with h | h
      · subst h
        rw [H2_cells_two] at hcell
        have ho : tipObj = _ := Option.some.inj hcell
        subst ho
        simp [fieldRefs, refsOf, tipObj] at hmem
        exact Or.inr hmem
      · subst h
        rw [H2_cells_leaf] at hcell
        have ho : leafObj = _ := Option.some.inj hcell
        subst ho
        simp [fieldRefs, refsOf, leafObj] at hmem

/-- The parent array is outside the extracted child's mutable footprint. -/
theorem sepRoot : ¬ MutableFootprint H1 1 0 := by
  intro h
  rcases H1_footprint h with h | h | h <;> simp at h

/-- The child array is outside the tip's mutable footprint. -/
theorem sepChild : ¬ MutableFootprint H2 2 1 := by
  intro h
  rcases H2_footprint h with h | h <;> simp at h

/-- The innermost body's run leaves every cell outside the tip's footprint where
the take-out left it. -/
theorem body_preserved {H' : Heap} {envb : Env} {vb : Val} {wsb : List Write}
    (hrun : runN body env2 H2 = .done H' envb vb wsb) :
    ∀ q, ¬ MutableFootprint H2 2 q → H'.cells q = H2.cells q := by
  have hred := hrun
  simp [body, runN, env2, env1, isolateEnv, bindLevel, Env.set, blankLevel, l0, l1,
    H, Heap.exclusive?, tipObj, childObj, rootObj, leafObj, Res.addWrite,
    run] at hred
  injection hred with hH _ _ _
  intro q hq
  have hq2 : q ≠ 2 := by
    intro h
    subst h
    exact hq (MutableFootprint.root H2_cells_two (by simp [tipObj]))
  have hq20 : q ≠ 20 := by
    intro h
    subst h
    exact hq (MutableFootprint.step_of_slot (i := 0) (r' := 20)
      (MutableFootprint.root H2_cells_two (by simp [tipObj])) H2_cells_two
      (by simp [tipObj]) (by decide) H2_cells_leaf (by simp [leafObj]))
  rw [← hH]
  rw [Heap.set_other _ _ _ _ hq2, Heap.set_other _ _ _ _ hq2, Heap.set_other _ _ _ _ hq2]
  rfl

/-- The child level's run leaves every cell outside the child's footprint where
the root's take-out left it. -/
theorem inner_preserved {H' : Heap} {envb : Env} {vb : Val} {wsb : List Write}
    (hrun : runN innerCode env1 H1 = .done H' envb vb wsb) :
    ∀ q, ¬ MutableFootprint H1 1 q → H'.cells q = H1.cells q := by
  have hred := hrun
  simp [innerCode, build, runN, body, env1, isolateEnv, bindLevel, Env.set,
    blankLevel, l0, l1, H, Heap.exclusive?, tipObj, childObj, rootObj, leafObj,
    Res.addWrite, addWrites, run] at hred
  injection hred with hH _ _ _
  intro q hq
  have hq1 : q ≠ 1 := by
    intro h
    subst h
    exact hq (MutableFootprint.root H1_cells_one (by simp [childObj]))
  have hq2 : q ≠ 2 := by
    intro h
    subst h
    exact hq (MutableFootprint.step_of_slot (i := 0) (r' := 2)
      (MutableFootprint.root H1_cells_one (by simp [childObj])) H1_cells_one
      (by simp [childObj]) (by decide) H1_cells_two (by simp [tipObj]))
  rw [← hH]
  rw [Heap.set_other _ _ _ _ hq1, Heap.set_other _ _ _ _ hq2, Heap.set_other _ _ _ _ hq2,
    Heap.set_other _ _ _ _ hq2, Heap.set_other _ _ _ _ hq1]
  rfl

/-- The child-call contract at every level of the concrete path. -/
theorem confined : ChildConfined pathVar valueVar body H env0 [l0, l1] := by
  refine ⟨sepRoot, ?_, sepChild, ?_, trivial⟩
  · intro H' envb vb wsb hrun
    exact inner_preserved hrun
  · intro H' envb vb wsb hrun
    exact body_preserved hrun

/-- The child level's own annotations: the leaf is in the child array's mutable
footprint at the take-out heap. -/
theorem annBodyH1 : AnnotationsIn H1 2 body := by
  refine ⟨?_, trivial⟩
  exact MutableFootprint.step_of_slot (i := 0)
    (MutableFootprint.root H1_cells_two (by simp [tipObj])) H1_cells_two (by simp [tipObj])
    (by decide) H1_cells_leaf (by simp [leafObj])

/-- The extracted child's extractions are in the child array's footprint. -/
theorem annotationsIn1 : AnnotationsIn H1 1 innerCode :=
  annotationsIn_of_path (rest := []) (l := l1) (root := 1) (tip := 2) (body := body)
    (path := pathVar) (value := valueVar)
    (Slots.blank (l := l0) (ls := [l1]) slotsTail distinct.1) chained.2.2 rfl rfl
    ⟨tipObj, H1_cells_two, by simp [tipObj]⟩ annBodyH1

/-- The path theory's agreement at the child level, at the take-out heap and in
the environment the root's call exposes. -/
theorem agreesInner : Agrees H1 env1 innerCode :=
  Path.agrees_of_path (rest := []) (l := l1) (H := H1) (env := env1)
    (path := pathVar) (value := valueVar) (body := body)
    (Slots.blank (l := l0) (ls := [l1]) slotsTail distinct.1) chained.2.2 distinctTail
    ⟨envok.2.1, trivial⟩ leaf confined.2.2

/-- The caller's invariant after the root's take-out: the extracted array and the
extracted child are bound. -/
theorem invCall : Inv H1 (bindLevel env0 l0) ctx1 :=
  Inv.setFields (H := H) (env := (env0.set 2 (.ref 0)).set 3 (.ref 1))
    (c := (ctx0.move 0 2).bindOwned 3 1) (r := 0) (o := rootObj)
    (fields := rootObj.fields.setIfInBounds 0 (.scalar 0))
    (Inv.bindOwned (Inv.move inv0 (by rfl) (by rfl)) (by rfl)) H_cells_zero

/-- The caller's invariant at the isolated context the child call's body is
checked from. -/
theorem invIso : Inv H1 env1 ctxIso :=
  inv_isolated (H := H1) (env := bindLevel env0 l0) (c := ctx1) (state := 3)
    (path := pathVar) (x := valueVar) (r := 1) invCall
    (by rfl) (by rfl) (by rfl) (by rfl)

/-- The state-indexed premise at the isolated context, derived from the invariant,
the agreement and the checker's acceptance. -/
theorem takeOutsOKInner : TakeOutsOK H1 env1 innerCode :=
  takeOutsOK_of_inv (c := ctxIso) (fs := []) invIso agreesInner checkNF_inner

/-! ## Agreement and annotation reachability of the built program -/

/-- The path theory's agreement for the whole built program: the certificate
supplies no `Agrees` of `code` directly. -/
theorem agrees0 : Agrees H env0 code :=
  Path.agrees_of_path (rest := [l1]) (l := l0) (H := H) (env := env0)
    (path := pathVar) (value := valueVar) (body := body)
    slots chained distinct envok leaf confined

/-- The path theory's annotation reachability for the whole built program: every
extracted reference is in the root's mutable footprint. -/
theorem annotationsIn0 : AnnotationsIn H 0 code :=
  Path.annotationsIn_of_path (rest := [l1]) (l := l0) (root := 0) (tip := 2) (body := body)
    (path := pathVar) (value := valueVar)
    slots chained rfl rfl liveTip annBody

/-- The state-indexed heap premise of the whole program, derived from the entry
condition, the agreement and acceptance. -/
theorem takeOutsOK0 : TakeOutsOK H env0 code :=
  takeOutsOK_of_entryInv entry0 agrees0 checkN_code

/-! ## The child-call contract on the admitted body -/

/-- `callAt_frame_confined` on the model body the root's call runs, with the
annotation premise and the state-indexed premise both derived above. -/
theorem childContract :
    ∃ H' env' v ws,
      runN innerCode env1 H1 = .done H' env' v ws ∧
        (∀ w ∈ ws, w.2 = true) ∧ v = .ref 1 ∧
        (∀ q, ¬ MutableFootprint H1 1 q → H'.cells q = H1.cells q) :=
  callAt_frame_confined (c := ctx0) (state := 3) (path := pathVar) (x := valueVar)
    (r := 1) (body := innerCode) (H := H1) (env := env1) (cb := ctxInner)
    annotationsIn1 checkNF_inner ⟨13, rfl, rfl, rfl⟩ invIso takeOutsOKInner

/-! ## The run -/

/-- Cell equality for the observed objects: structure equality from the three
fields. -/
theorem some_obj_eq {o o' : Obj} (hf : o.fields = o'.fields) (hrc : o.rc = o'.rc)
    (hp : o.persistent = o'.persistent) : some o = (some o' : Option Obj) := by
  have ho : o = o' := by
    cases o
    cases o'
    simp_all
  rw [ho]

/-- The built program's run: fault-free, one exclusive write, both extracted slots
restored, and the innermost body's designated write in the tip's other slot. -/
theorem run_code :
    ∃ H' env' ws,
      runN code env0 H = .done H' env' (.ref 0) ws ∧
        (∀ w ∈ ws, w.2 = true) ∧ ws = [(2, true)] ∧
        H'.cells 0 = some rootObj ∧ H'.cells 1 = some childObj ∧
        H'.cells 2 = some writtenTip ∧ H'.cells 20 = some leafObj := by
  obtain ⟨H', env', v, ws, hrun, hws, -⟩ :=
    checkN_sound_of_entryInv entry0 agrees0 checkN_code
  have hred := hrun
  simp [code, build, runN, body, env0, isolateEnv, Env.set, l0, l1, H,
    Heap.exclusive?, tipObj, childObj, rootObj, leafObj, Res.addWrite, addWrites,
    run] at hred
  injection hred with hH henv hv hws'
  subst hH
  subst hv
  subst hws'
  refine ⟨_, _, _, rfl, hws, rfl, ?_, ?_, ?_, ?_⟩
  · simp only [l0, l1]
    rw [Heap.set_self]
    exact some_obj_eq (by decide) (by decide) (by decide)
  · simp only [l0, l1]
    rw [Heap.set_other _ 0 1 _ (by decide), Heap.set_self]
    exact some_obj_eq (by decide) (by decide) (by decide)
  · simp only [l0, l1]
    rw [Heap.set_other _ 0 2 _ (by decide), Heap.set_other _ 1 2 _ (by decide),
      Heap.set_self]
    exact some_obj_eq (by decide) (by decide) (by decide)
  · simp only [l0, l1]
    rw [Heap.set_other _ 0 20 _ (by decide), Heap.set_other _ 1 20 _ (by decide),
      Heap.set_other _ 2 20 _ (by decide), Heap.set_other _ 2 20 _ (by decide),
      Heap.set_other _ 2 20 _ (by decide), Heap.set_other _ 1 20 _ (by decide),
      Heap.set_other _ 0 20 _ (by decide)]
    exact H_cells_leaf

/-! ## What the emitted correspondence still needs -/

/-- The part of the emitted correspondence's `NestedAgrees` that the path theory
determines: once the recognizer's binders are the path's, its four
model-environment fields are exactly this level's environment facts. -/
theorem nestedAgrees_modelFields {assign : Lean.FVarId → Var}
    {p : OwnershipLcnf.NestedPrefix} {env : Env} {l : Level} {path value : Var}
    (harr : assign p.array = l.arrayVar) (hidx : assign p.index = l.indexVar)
    (hvalue : assign p.value = value) (hpath : assign p.path = path)
    (henv : LevelEnv path value env l) :
    env (assign p.array) = some (.ref l.arr) ∧
      env (assign p.index) = some (.scalar l.idx) ∧
      (∃ v, env (assign p.value) = some (.scalar v)) ∧
      (∃ pv, env (assign p.path) = some (.scalar pv)) := by
  obtain ⟨ha, hi, hv, hp, -⟩ := henv
  exact ⟨by rwa [harr], by rwa [hidx], by simpa [hvalue] using hp,
    by simpa [hpath] using hv⟩

end OwnershipTest.PathAgreement

#print axioms Ownership.Entry.MutableFootprint.trans
#print axioms Ownership.Entry.ClientReachable.trans
#print axioms Ownership.Entry.AnnotationsIn.trans
#print axioms Ownership.Path.agrees_of_path
#print axioms Ownership.Path.annotationsIn_of_path
#print axioms OwnershipTest.PathAgreement.agrees0
#print axioms OwnershipTest.PathAgreement.annotationsIn0
#print axioms OwnershipTest.PathAgreement.agreesInner
#print axioms OwnershipTest.PathAgreement.childContract
#print axioms OwnershipTest.PathAgreement.run_code
#print axioms OwnershipTest.PathAgreement.nestedAgrees_modelFields
