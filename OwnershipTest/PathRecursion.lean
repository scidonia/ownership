/-
The depth-two finite path whose child-call contract is derived, not supplied.

The path is `Ownership.Path.build` at two levels, with the levels' variables at
the recognized prefix's own model variables: the root array `ref 0` extracts its
child `ref 1` from slot 1 into the call's state variable `4`, the child array
`ref 1` extracts the tip `ref 3` from slot 1 into `9`, and the innermost call runs
the leaf body — write the value scalar into the state it was handed at the call's
path scalar — then the two slots are restored in reverse order.

The innermost call's index is the call's path scalar `5` at the second level,
which is what the model's level discipline requires: a callee is handed only its
state, its path and its value, so the index it takes out at is one of those two
scalars (`Ownership.Path.LevelShape`). The leaf body's contract is concrete: its
agreement is trivial (a straight-line block), its checker acceptance is the
innermost isolated context, its exit is the state variable `9` it writes through,
it is count-free, and its annotation is empty.

`contract` is the `PathContract` the level list supplies; `childContracts` is the
derived contract at every level — `childContract_l0` for the call the first level
emits, and `childContract_l1` for the innermost call, whose body is the leaf. No
`ChildContract` is assumed anywhere: the first level's call body is the remaining
levels' build, and `childContracts_of_path` proves its contract from the level
data and the leaf. `simulates` is the correspondence at this path, `model_run`
computes the model run the derived contract describes — the leaf's single
exclusive write, both slots restored, the root handle returned — and `exec`
reports the corresponding executed outcome.

What this does not certify: the emitted recursive callee's body is not captured,
so the call's meaning remains the N10 contract — the model body the call is
assumed to run. Depth is the list's syntax, not a data-dependent runtime depth.
-/
import OwnershipLcnf.PathRecursion

open Ownership
open Ownership.Nested
open Ownership.Entry
open Ownership.Path
open Ownership.PathConsolidation
open OwnershipLcnf

namespace OwnershipTest.PathRecursion

/-! ## The object tree -/

/-- The root array: slot 0 an unrelated scalar, slot 1 the child array `ref 1`. -/
def rootObj : Obj := ⟨#[.scalar 5, .ref 1], 1, false⟩

/-- The child array: slot 0 an unrelated scalar, slot 1 the tip `ref 3`. -/
def childObj : Obj := ⟨#[.scalar 3, .ref 3], 1, false⟩

/-- The tip the leaf body writes: slot 0 the extracted leaf `ref 40`, slot 1 the
scalar the body writes over. -/
def tipObj : Obj := ⟨#[.ref 40, .scalar 6], 1, false⟩

/-- The leaf the tip holds. -/
def leafObj : Obj := ⟨#[.scalar 0], 1, false⟩

/-- Root → child → tip → leaf, each live cell counted once. -/
def H : Heap :=
  { cells := fun r =>
      if r = 0 then some rootObj
      else if r = 1 then some childObj
      else if r = 3 then some tipObj
      else if r = 40 then some leafObj
      else none
    next := 41 }

/-! ## The recognized prefix and the layout -/

/-- The recognized prefix's binder identities, as concrete names. -/
def p : NestedPrefix :=
  { node := ⟨`path.node⟩
    array := ⟨`path.array⟩
    value := ⟨`path.value⟩
    childArray := ⟨`path.childArray⟩
    index := ⟨`path.index⟩
    path := ⟨`path.path⟩
    sizeResult := ⟨`path.sizeResult⟩
    bound := ⟨`path.bound⟩
    arraySite := ⟨`path.site0⟩
    arrayCheck := ⟨`path.arrayCheck⟩
    dflt := ⟨`path.dflt⟩
    pair := ⟨`path.pair⟩
    parent := ⟨`path.parent⟩
    child := ⟨`path.child⟩
    childSite := ⟨`path.site1⟩
    childCheck := ⟨`path.childCheck⟩
    recursive := ⟨`path.recursive⟩
    restored := ⟨`path.restored⟩
    indexDec := ⟨`path.indexDec⟩ }

/-- The layout: the model's variables take slots `0`–`7`, the auxiliary binders
`8`–`18`. -/
def assign (f : Lean.FVarId) : Var :=
  if f.name = `path.array then 0
  else if f.name = `path.index then 1
  else if f.name = `path.value then 2
  else if f.name = `path.parent then 3
  else if f.name = `path.child then 4
  else if f.name = `path.path then 5
  else if f.name = `path.recursive then 6
  else if f.name = `path.restored then 7
  else if f.name = `path.node then 8
  else if f.name = `path.childArray then 9
  else if f.name = `path.sizeResult then 10
  else if f.name = `path.bound then 11
  else if f.name = `path.site0 then 12
  else if f.name = `path.arrayCheck then 13
  else if f.name = `path.dflt then 14
  else if f.name = `path.pair then 15
  else if f.name = `path.site1 then 16
  else if f.name = `path.childCheck then 17
  else if f.name = `path.indexDec then 18
  else 0

theorem layout : NestedLayout assign p := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [assign, p]

/-! ## The path -/

/-- The call's path scalar. -/
def pathVar : Var := 5

/-- The call's value scalar. -/
def valueVar : Var := 2

/-- The first level: extract slot 1 of `ref 0` into the parent `3` and the state
`4`, restoring through `6` and `7`. -/
def l0 : Level :=
  { arr := 0, obj := rootObj, idx := 1, child := 1
    arrayVar := 0, indexVar := 1, parentVar := 3, childVar := 4
    resultVar := 6, restoredVar := 7 }

/-- The second level: extract slot 1 of `ref 1` — reached through the call's
state variable `4` — into the parent `8` and the state `9`, taking out at the
call's path scalar `5` and restoring through `10` and `11`. -/
def l1 : Level :=
  { arr := 1, obj := childObj, idx := 1, child := 3
    arrayVar := 4, indexVar := 5, parentVar := 8, childVar := 9
    resultVar := 10, restoredVar := 11 }

/-- The initial environment: the root handle, the root's selected index, and the
call's value and path scalars. -/
def env0 : Env :=
  fun x =>
    if x = 0 then some (.ref 0)
    else if x = 1 then some (.scalar 1)
    else if x = 2 then some (.scalar 1)
    else if x = 5 then some (.scalar 1)
    else none

/-- The leaf body: write the value scalar into the state it was handed at the
call's path scalar. -/
def body : NCode := .base (.setArr 9 5 2 (.ret 9))

/-! ## The checker state -/

/-- The entry context: the root handle owned at its count, the index and the two
call scalars scalar, the variables the first level writes dead. -/
def ctx0 : Ctx :=
  { us := fun x =>
      if x = 0 then .owned
      else if x = 1 then .scalar
      else if x = 5 then .scalar
      else if x = 2 then .scalar
      else .dead
    refOf := fun x => if x = 0 then some 0 else none
    mult := fun r =>
      if r = 0 then 1 else if r = 1 then 1 else if r = 3 then 1
      else if r = 40 then 1 else 0 }

/-- The context the innermost call hands the leaf body. -/
def bodyCtxTail : Ctx := tailCtx pathVar valueVar ctx0 [l0, l1]

/-- The leaf body's exit context. -/
def ctxBody : Ctx := bodyCtxTail

theorem checkBody : checkNF bodyCtxTail [] body = some ctxBody := rfl

/-! ## The level list's own data -/

theorem H_cells_zero : H.cells 0 = some rootObj := by simp [H]
theorem H_cells_one : H.cells 1 = some childObj := by simp [H]
theorem H_cells_three : H.cells 3 = some tipObj := by simp [H]
theorem H_cells_leaf : H.cells 40 = some leafObj := by simp [H]

theorem root_slot : rootObj.fields[1]? = some (.ref 1) := by decide
theorem child_slot : childObj.fields[1]? = some (.ref 3) := by decide

/-- The root after its selected slot is emptied. -/
abbrev blankRoot : Obj := { rootObj with fields := rootObj.fields.setIfInBounds 1 (.scalar 0) }

/-- The child after its selected slot is emptied. -/
abbrev blankChild : Obj := { childObj with fields := childObj.fields.setIfInBounds 1 (.scalar 0) }

/-- The child after its selected slot is restored from the call's result. -/
abbrev restoredChild : Obj := { blankChild with fields := blankChild.fields.set! 1 (.ref 3) }

/-- The root after its selected slot is restored from the call's result. -/
abbrev restoredRoot : Obj := { blankRoot with fields := blankRoot.fields.set! 1 (.ref 1) }

/-- The tip after the leaf body's write. -/
abbrev finalTip : Obj := { tipObj with fields := tipObj.fields.set! 1 (.scalar 1) }

theorem H1_cells_zero : (blankLevel H l0).cells 0 = some blankRoot := by
  simp [blankLevel, l0, H, blankRoot, Heap.set]

theorem H1_cells_one : (blankLevel H l0).cells 1 = some childObj := by
  simp [blankLevel, l0, H, Heap.set]

theorem H1_cells_three : (blankLevel H l0).cells 3 = some tipObj := by
  simp [blankLevel, l0, H, Heap.set]

theorem H1_cells_leaf : (blankLevel H l0).cells 40 = some leafObj := by
  simp [blankLevel, l0, H, Heap.set]

theorem H2_cells_zero : (blankLevel (blankLevel H l0) l1).cells 0 = some blankRoot := by
  simp [blankLevel, l0, l1, H, blankRoot, Heap.set]

theorem H2_cells_one : (blankLevel (blankLevel H l0) l1).cells 1 = some blankChild := by
  simp [blankLevel, l0, l1, H, blankChild, Heap.set]

theorem H2_cells_three : (blankLevel (blankLevel H l0) l1).cells 3 = some tipObj := by
  simp [blankLevel, l0, l1, H, Heap.set]

theorem H2_cells_leaf : (blankLevel (blankLevel H l0) l1).cells 40 = some leafObj := by
  simp [blankLevel, l0, l1, H, Heap.set]

/-- The root and child slots the path reads. -/
theorem slots : Slots H [l0, l1] := by
  intro l hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · exact ⟨H_cells_zero, by decide, rfl⟩
  · exact ⟨H_cells_one, by decide, rfl⟩

theorem chained : Chained [l0, l1] := ⟨rfl, rfl, trivial⟩

theorem distinct : DistinctArrays [l0, l1] :=
  ⟨by intro m hm; simp at hm; subst hm; decide, ⟨by simp, trivial⟩⟩

/-! ## The environments the levels read -/

/-- The environment the first level's call exposes. -/
abbrev envCall0 : Env := bindLevel env0 l0

/-- The environment the first level's call exposes to its body. -/
abbrev env1 : Env := isolateEnv envCall0 l0.childVar pathVar valueVar

/-- The environment the second level's call exposes. -/
abbrev envTake1 : Env := bindLevel env1 l1

/-- The environment the second level's call exposes to the leaf. -/
abbrev env3 : Env := isolateEnv envTake1 l1.childVar pathVar valueVar

theorem levelEnv0 : LevelEnv pathVar valueVar env0 l0 :=
  ⟨by rfl, by rfl, ⟨1, by rfl⟩, ⟨1, by rfl⟩, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩

theorem levelEnv1 : LevelEnv pathVar valueVar env1 l1 :=
  ⟨by rfl, by rfl, ⟨1, by rfl⟩, ⟨1, by rfl⟩, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩

theorem envok : EnvOK pathVar valueVar env0 [l0, l1] := ⟨levelEnv0, levelEnv1, trivial⟩

/-! ## The heap shape -/

/-- At any heap whose cells `3` and `40` are the tip and the leaf, the tip's
mutable footprint is those two cells. -/
theorem tip_footprint {Ht : Heap} {q : Ref} (h3 : Ht.cells 3 = some tipObj)
    (h40 : Ht.cells 40 = some leafObj) (h : MutableFootprint Ht 3 q) :
    q = 3 ∨ q = 40 := by
  induction h with
  | root _ _ => exact Or.inl rfl
  | step hr hcell hpers hmem hcell' hpers' ih =>
      rcases ih with rfl | rfl
      · rw [h3] at hcell
        have ho : tipObj = _ := Option.some.inj hcell
        subst ho
        simp [fieldRefs, refsOf, tipObj] at hmem
        exact Or.inr hmem
      · rw [h40] at hcell
        have ho : leafObj = _ := Option.some.inj hcell
        subst ho
        simp [fieldRefs, refsOf, leafObj] at hmem

/-- At any heap whose cells `1`, `3` and `40` are the child, the tip and the
leaf, the child's mutable footprint is those three cells. -/
theorem child_footprint {Ht : Heap} {q : Ref} (h1 : Ht.cells 1 = some childObj)
    (h3 : Ht.cells 3 = some tipObj) (h40 : Ht.cells 40 = some leafObj)
    (h : MutableFootprint Ht 1 q) : q = 1 ∨ q = 3 ∨ q = 40 := by
  induction h with
  | root _ _ => exact Or.inl rfl
  | step hr hcell hpers hmem hcell' hpers' ih =>
      rcases ih with rfl | rfl | rfl
      · rw [h1] at hcell
        have ho : childObj = _ := Option.some.inj hcell
        subst ho
        simp [fieldRefs, refsOf, childObj] at hmem
        exact Or.inr (Or.inl hmem)
      · rw [h3] at hcell
        have ho : tipObj = _ := Option.some.inj hcell
        subst ho
        simp [fieldRefs, refsOf, tipObj] at hmem
        exact Or.inr (Or.inr hmem)
      · rw [h40] at hcell
        have ho : leafObj = _ := Option.some.inj hcell
        subst ho
        simp [fieldRefs, refsOf, leafObj] at hmem

/-- The tip cannot reach back up to the root the first take-out emptied. -/
theorem noBack0 : ¬ MutableFootprint H 3 0 := by
  intro h
  rcases tip_footprint H_cells_three H_cells_leaf h with h | h <;> simp_all

/-- The extracted child cannot reach the suspended root array. -/
theorem sep0 : ¬ MutableFootprint (blankLevel H l0) 1 0 := by
  intro h
  rcases child_footprint H1_cells_one H1_cells_three H1_cells_leaf h with g | g | g <;>
    simp_all

/-- The tip cannot reach the child array the second take-out emptied. -/
theorem noBack1 : ¬ MutableFootprint (blankLevel H l0) 3 1 := by
  intro h
  rcases tip_footprint H1_cells_three H1_cells_leaf h with g | g <;> simp_all

/-- The tip cannot reach the suspended child array from the second take-out
heap. -/
theorem sep1 : ¬ MutableFootprint (blankLevel (blankLevel H l0) l1) 3 1 := by
  intro h
  rcases tip_footprint H2_cells_three H2_cells_leaf h with g | g <;> simp_all

theorem acyclic : Acyclic 3 H [l0, l1] :=
  ⟨sep0, noBack0, sep1, noBack1, trivial⟩

theorem live : Live H 3 := ⟨tipObj, H_cells_three, rfl⟩

/-! ## The levels' contexts -/

theorem vars0 : Vars pathVar valueVar l0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem vars1 : Vars pathVar valueVar l1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem levelCtx0 : LevelCtx pathVar valueVar ctx0 l0 :=
  ⟨vars0, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩

theorem shape1 : LevelShape pathVar valueVar l1 := ⟨vars1, Or.inl rfl⟩

theorem shapes : Shapes pathVar valueVar [l1] := ⟨shape1, trivial⟩

theorem counts : Counts ctx0.mult [l1] := ⟨by decide, by decide, trivial⟩

/-! ## The entry invariant -/

theorem inv0 : Inv H env0 ctx0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r
    by_cases h0 : r = 0
    · subst h0; simp [H, ctx0, Heap.rc, rootObj]
    · by_cases h1 : r = 1
      · subst h1; simp [H, ctx0, Heap.rc, h0, childObj]
      · by_cases h3 : r = 3
        · subst h3; simp [H, ctx0, Heap.rc, h0, h1, tipObj]
        · by_cases h40 : r = 40
          · subst h40; simp [H, ctx0, Heap.rc, h0, h1, h3, leafObj]
          · simp [H, ctx0, Heap.rc, h0, h1, h3, h40]
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
        · by_cases hx2 : x = 2
          · subst hx2; simp [ctx0, hx0, hx1, hx5] at hx
          · simp [ctx0, hx0, hx1, hx5, hx2] at hx
  · intro x r hx hr
    by_cases hx0 : x = 0
    · subst hx0; simp [ctx0] at hx
    · by_cases hx1 : x = 1
      · subst hx1; simp [ctx0, hx0] at hx
      · by_cases hx5 : x = 5
        · subst hx5; simp [ctx0, hx0, hx1] at hx
        · by_cases hx2 : x = 2
          · subst hx2; simp [ctx0, hx0, hx1, hx5] at hx
          · simp [ctx0, hx0, hx1, hx5, hx2] at hx
  · intro x hx
    by_cases hx0 : x = 0
    · subst hx0; simp [ctx0] at hx
    · by_cases hx1 : x = 1
      · subst hx1; exact ⟨1, by simp [env0, hx0]⟩
      · by_cases hx5 : x = 5
        · subst hx5; exact ⟨1, by simp [env0, hx0, hx1]⟩
        · by_cases hx2 : x = 2
          · subst hx2; exact ⟨1, by simp [env0, hx0, hx1]⟩
          · simp [ctx0, hx0, hx1, hx5, hx2] at hx
  · intro r o hcell
    by_cases h0 : r = 0
    · subst h0
      rw [H_cells_zero] at hcell
      have ho : rootObj = o := Option.some.inj hcell
      subst ho; rfl
    · by_cases h1 : r = 1
      · subst h1
        rw [show H.cells 1 = some childObj by simp [H, h0]] at hcell
        have ho : childObj = o := Option.some.inj hcell
        subst ho; rfl
      · by_cases h3 : r = 3
        · subst h3
          rw [show H.cells 3 = some tipObj by simp [H, h0, h1]] at hcell
          have ho : tipObj = o := Option.some.inj hcell
          subst ho; rfl
        · by_cases h40 : r = 40
          · subst h40
            rw [show H.cells 40 = some leafObj by simp [H, h0, h1, h3]] at hcell
            have ho : leafObj = o := Option.some.inj hcell
            subst ho; rfl
          · rw [show H.cells r = none by simp [H, h0, h1, h3, h40]] at hcell
            exact absurd hcell (by simp)

/-! ## The leaf body's contract -/

theorem leafAgreesH : leafAgrees pathVar valueVar body (blankLevel H l0) env1 [l1] := by
  show Agrees (blankLevel (blankLevel H l0) l1)
    (isolateEnv (bindLevel env1 l1) l1.childVar pathVar valueVar) body
  exact trivial

theorem retBody : retVar body = some 9 := rfl

theorem retOwned : ctxBody.us 9 = .owned := rfl

theorem retRef : ctxBody.refOf 9 = some 3 := rfl

theorem countFree : CountFree body = true := rfl

theorem annot : AnnotationsIn H 3 body := trivial

theorem endsAt : EndsAt 3 [l0, l1] := rfl

/-! ## The level list's contract -/

theorem contract : PathContract pathVar valueVar body 3 l0 [l1] H env0 ctx0 ctxBody 9 :=
  { slots := slots
    chained := chained
    distinct := distinct
    envok := envok
    leaf := leafAgreesH
    levelCtx := levelCtx0
    shapes := shapes
    counts := counts
    acyclic := acyclic
    live := live
    annot := annot
    checkBody := checkBody
    retBody := retBody
    retOwned := retOwned
    retRef := retRef
    endsAt := endsAt
    countFree := countFree
    inv := inv0 }

/-- The derived contract at every level, with no supplied `ChildContract`. -/
theorem childContracts : ChildContracts pathVar valueVar body H env0 [l0, l1] :=
  childContracts_of_path [l1] l0 contract

/-- The contract of the call the first level emits: its body is the remaining
levels' build. -/
theorem childContract_l0 : ChildContract (blankLevel H l0) env1
    (build pathVar valueVar body [l1]) l0.child :=
  childContracts.head

/-- The contract at the innermost call, whose body is the leaf: the induction's
base case, at the second level's own take-out heap. -/
theorem childContract_l1 :
    ChildContract (blankLevel (blankLevel H l0) l1) env3 body l1.child :=
  childContracts.second

/-! ## The machine and the agreement -/

/-- The fragment's starting machine. -/
def machine : NestedMachine :=
  { heap := H
    env := fun x =>
      if x = 0 then some (.ref 0)
      else if x = 2 then some (.scalar 1)
      else none
    nodes := fun _ => { index := .scalar 1 }
    callPath := 1
    childVar := 4
    pairs := fun _ => none
    writes := [] }

theorem agrees : NestedAgrees assign p machine env0 H 0 1 1 1 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [machine, env0, assign, p]

theorem levelMatch : LevelMatch assign p l0 pathVar valueVar 0 rootObj 1 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [assign, p, l0, pathVar, valueVar]

/-! ## The correspondence at this path -/

/-- The recognized prefix at this path reports the model run of the whole path:
the child contract at the first level is derived above, not supplied. -/
theorem simulates :
    NestedOutcome.ofExec assign p
        (execNested assign (build pathVar valueVar body [l1]) p.fragment machine) =
        some (NestedOutcome.ofModel
          (runN (build pathVar valueVar body [l0, l1]) env0 H)) ∧
      (∃ H' env' ws,
        runN (build pathVar valueVar body [l0, l1]) env0 H =
          .done H' env' (.ref 0) ws ∧ (∀ w ∈ ws, w.2 = true)) :=
  index_path_fragment_simulates_model assign p layout pathVar valueVar body [l1] l0 machine
    env0 H 0 rootObj 1 1 1 1 levelMatch agrees ctx0 3 ctxBody 9 contract

/-! ## The model run's states -/

/-- The heap after the first level's take-out. -/
abbrev H1 : Heap := blankLevel H l0

/-- The heap after the second level's take-out. -/
abbrev H2 : Heap := blankLevel H1 l1

/-- The heap after the leaf body's write. -/
abbrev H3 : Heap := H2.set 3 finalTip

/-- The heap after the second level's put-back. -/
abbrev H4 : Heap := H3.set 1 restoredChild

/-- The heap after the first level's put-back. -/
abbrev H5 : Heap := H4.set 0 restoredRoot

/-- The environment the run leaves. -/
abbrev envfin : Env := (envCall0.set 6 (.ref 1)).set 7 (.ref 0)

/-- The environment the second level's continuation runs in. -/
abbrev envE5 : Env := (envTake1.set 10 (.ref 3)).set 11 (.ref 1)

theorem H2_exclusive : H2.exclusive? 3 = true := by
  simp [Heap.exclusive?, show H2.cells 3 = some tipObj from H2_cells_three, tipObj]

theorem H1_exclusive : H1.exclusive? 1 = true := by
  simp [Heap.exclusive?, show H1.cells 1 = some childObj from H1_cells_one, childObj]

theorem H3_cells_one : H3.cells 1 = some blankChild := by
  rw [show H3.cells 1 = H2.cells 1 by simp [H3, Heap.set]]
  exact H2_cells_one

theorem H4_cells_zero : H4.cells 0 = some blankRoot := by
  rw [show H4.cells 0 = H3.cells 0 by simp [H4, Heap.set]]
  rw [show H3.cells 0 = H2.cells 0 by simp [H3, Heap.set]]
  exact H2_cells_zero

/-- Object equality from its three components. -/
theorem obj_eq {o o' : Obj} (hf : o.fields = o'.fields) (hr : o.rc = o'.rc)
    (hp : o.persistent = o'.persistent) : o = o' := by
  cases o
  cases o'
  simp_all

theorem restoredChild_eq : restoredChild = childObj :=
  obj_eq (by decide) (by decide) (by decide)

theorem restoredRoot_eq : restoredRoot = rootObj :=
  obj_eq (by decide) (by decide) (by decide)

/-! ## The model's step rules, as equations -/

/-- The model's take-out step. -/
theorem runN_takeOut {a i fst snd : Var} {e : Ref} {k : NCode} {env : Env} {Ht : Heap}
    {r : Ref} {o : Obj} {idx : Nat}
    (ha : env a = some (.ref r)) (hi : env i = some (.scalar idx))
    (hcell : Ht.cells r = some o) (hslot : o.fields[idx]? = some (.ref e)) :
    runN (.takeOut a i fst snd e k) env Ht =
      runN k ((env.set fst (.ref r)).set snd (.ref e))
        (Ht.set r { o with fields := o.fields.setIfInBounds idx (.scalar 0) }) := by
  simp [runN, ha, hi, hcell, hslot]

/-- The model's put-back step. -/
theorem runN_putBack {a e i result : Var} {k : NCode} {env : Env} {Ht : Heap}
    {r re : Ref} {o : Obj} {idx : Nat}
    (ha : env a = some (.ref r)) (he : env e = some (.ref re))
    (hi : env i = some (.scalar idx)) (hcell : Ht.cells r = some o) :
    runN (.putBack a e i result k) env Ht =
      runN k (env.set result (.ref r))
        (Ht.set r { o with fields := o.fields.set! idx (.ref re) }) := by
  simp [runN, ha, he, hi, hcell]

/-- The model's recursive call step, given the body's own outcome. -/
theorem runN_callAt {state path x result : Var} {body k : NCode} {env : Env}
    {Ht H' : Heap} {envb : Env} {v : Val} {ws : List Write} {r : Ref} {pv xv : Nat}
    (hs : env state = some (.ref r)) (hp : env path = some (.scalar pv))
    (hx : env x = some (.scalar xv)) (hex : Ht.exclusive? r = true)
    (hb : runN body (isolateEnv env state path x) Ht = .done H' envb v ws) :
    runN (.callAt state path x result body k) env Ht =
      addWrites (runN k (env.set result (.ref r)) H') ws := by
  simp [runN, hs, hp, hx, hex, hb]

/-- The straight-line write's exclusive branch. -/
theorem run_setArr {x i v : Var} {k : Code} {env : Env} {Ht : Heap} {r : Ref} {o : Obj}
    {idx val : Nat}
    (hx : env x = some (.ref r)) (hi : env i = some (.scalar idx))
    (hv : env v = some (.scalar val)) (hcell : Ht.cells r = some o)
    (hex : Ht.exclusive? r = true) :
    run (.setArr x i v k) env Ht =
      (run k (env.set x (.ref r))
        (Ht.set r { o with fields := o.fields.set! idx (.scalar val) })).addWrite (r, true) := by
  simp [run, hx, hi, hv, hcell, hex]

/-- The straight-line return. -/
theorem run_ret (x : Var) (env : Env) (Ht : Heap) :
    run (.ret x) env Ht = .done Ht env (env x |>.getD .erased) [] := rfl

/-! ## The environments the run reads -/

theorem envCall0_3 : envCall0 3 = some (.ref 0) := rfl

theorem envCall0_5 : envCall0 5 = some (.scalar 1) := rfl

theorem envCall0_2 : envCall0 2 = some (.scalar 1) := rfl

theorem envCall0_4 : envCall0 4 = some (.ref 1) := rfl

theorem envCall0_1 : envCall0 1 = some (.scalar 1) := rfl

theorem env1_4 : env1 4 = some (.ref 1) := rfl

theorem env1_5 : env1 5 = some (.scalar 1) := rfl

theorem envTake1_8 : envTake1 8 = some (.ref 1) := rfl

theorem envTake1_9 : envTake1 9 = some (.ref 3) := rfl

theorem envTake1_5 : envTake1 5 = some (.scalar 1) := rfl

theorem envTake1_2 : envTake1 2 = some (.scalar 1) := rfl

theorem env3_9 : env3 9 = some (.ref 3) := rfl

theorem env3_5 : env3 5 = some (.scalar 1) := rfl

theorem env3_2 : env3 2 = some (.scalar 1) := rfl

theorem envfin_3 : envfin 3 = some (.ref 0) := rfl

theorem envfin_1 : envfin 1 = some (.scalar 1) := rfl

theorem envfin_7 : envfin 7 = some (.ref 0) := rfl

/-! ## The run, step by step -/

/-- The leaf body's run: the tip's slot 1 takes the value scalar, and the body
returns the state it was handed. -/
theorem leafRun :
    runN body env3 H2 = .done H3 (env3.set 9 (.ref 3)) (.ref 3) [(3, true)] := by
  rw [show body = .base (.setArr 9 5 2 (.ret 9)) from rfl]
  rw [show runN (.base (.setArr 9 5 2 (.ret 9))) env3 H2 =
    run (.setArr 9 5 2 (.ret 9)) env3 H2 from rfl]
  rw [run_setArr (env := env3) (Ht := H2) (r := 3) (o := tipObj) (idx := 1) (val := 1)
    env3_9 env3_5 env3_2 H2_cells_three H2_exclusive]
  rw [run_ret]
  rfl

/-- The second level's continuation: the extracted child's slot is restored from
the call's result and the restored handle returned. -/
theorem innerTail :
    runN (.putBack 8 10 5 11 (.ret 11)) (envTake1.set 10 (.ref 3)) H3 =
      .done H4 envE5 (.ref 1) [] := by
  have ha : (envTake1.set 10 (.ref 3)) 8 = some (.ref 1) := by
    rw [Env.set_other _ _ _ _ (by decide : (8 : Var) ≠ 10), envTake1_8]
  have he : (envTake1.set 10 (.ref 3)) 10 = some (.ref 3) := Env.set_self _ _ _
  have hi : (envTake1.set 10 (.ref 3)) 5 = some (.scalar 1) := by
    rw [Env.set_other _ _ _ _ (by decide : (5 : Var) ≠ 10), envTake1_5]
  rw [runN_putBack (env := envTake1.set 10 (.ref 3)) (Ht := H3) (r := 1) (re := 3)
    (o := blankChild) (idx := 1) ha he hi H3_cells_one]
  rw [show runN (.ret 11) envE5 H4 = .done H4 envE5 (.ref 1) [] from rfl]

/-- The second level's call: the leaf's write, then the second level's put-back. -/
theorem innerCall : runN (.callAt 9 5 2 10 body (.putBack 8 10 5 11 (.ret 11)))
    envTake1 H2 = .done H4 envE5 (.ref 1) [(3, true)] := by
  rw [runN_callAt envTake1_9 envTake1_5 envTake1_2 H2_exclusive
    (show runN body (isolateEnv envTake1 9 5 2) H2 =
      .done H3 (env3.set 9 (.ref 3)) (.ref 3) [(3, true)] from leafRun)]
  rw [innerTail]
  simp [Ownership.Nested.addWrites]

/-- The second level's take-out: the child's slot is emptied and the tip handed to
the call. -/
theorem takeOut1 :
    runN (build pathVar valueVar body [l1]) env1 H1 = runN (.callAt 9 5 2 10 body
      (.putBack 8 10 5 11 (.ret 11))) envTake1 H2 := by
  rw [show build pathVar valueVar body [l1] =
    .takeOut 4 5 8 9 3 (.callAt 9 5 2 10 body (.putBack 8 10 5 11 (.ret 11))) from rfl]
  rw [runN_takeOut (env := env1) (Ht := H1) (r := 1) (o := childObj) (idx := 1) (e := 3)
    (fst := 8) (snd := 9) env1_4 env1_5 H1_cells_one child_slot]
  rfl

/-- The remaining levels' build, run at the first level's call. -/
theorem innerBuild :
    runN (build pathVar valueVar body [l1]) env1 H1 =
      .done H4 envE5 (.ref 1) [(3, true)] := by
  rw [takeOut1, innerCall]

/-- The first level's continuation: the root's slot is restored from the call's
result and the root handle returned. -/
theorem outerTail :
    runN (.putBack 3 6 1 7 (.ret 7)) (envCall0.set 6 (.ref 1)) H4 =
      .done H5 envfin (.ref 0) [] := by
  have ha : (envCall0.set 6 (.ref 1)) 3 = some (.ref 0) := by
    rw [Env.set_other _ _ _ _ (by decide : (3 : Var) ≠ 6), envCall0_3]
  have he : (envCall0.set 6 (.ref 1)) 6 = some (.ref 1) := Env.set_self _ _ _
  have hi : (envCall0.set 6 (.ref 1)) 1 = some (.scalar 1) := by
    rw [Env.set_other _ _ _ _ (by decide : (1 : Var) ≠ 6), envCall0_1]
  rw [runN_putBack (env := envCall0.set 6 (.ref 1)) (Ht := H4) (r := 0) (re := 1)
    (o := blankRoot) (idx := 1) ha he hi H4_cells_zero]
  rw [show runN (.ret 7) envfin H5 = .done H5 envfin (.ref 0) [] from rfl]

/-- The first level's call: the remaining levels' build, then the first level's
put-back. -/
theorem outerCall : runN (.callAt 4 5 2 6 (build pathVar valueVar body [l1])
    (.putBack 3 6 1 7 (.ret 7))) envCall0 H1 =
      .done H5 envfin (.ref 0) [(3, true)] := by
  rw [runN_callAt envCall0_4 envCall0_5 envCall0_2 H1_exclusive
    (show runN (build pathVar valueVar body [l1]) (isolateEnv envCall0 4 5 2) H1 =
      .done H4 envE5 (.ref 1) [(3, true)] from innerBuild)]
  rw [outerTail]
  simp [Ownership.Nested.addWrites]

/-- The first level's take-out. -/
theorem takeOut0 :
    runN (build pathVar valueVar body [l0, l1]) env0 H =
      runN (.callAt 4 5 2 6 (build pathVar valueVar body [l1])
        (.putBack 3 6 1 7 (.ret 7))) envCall0 H1 := by
  rw [show build pathVar valueVar body [l0, l1] =
    .takeOut 0 1 3 4 1 (.callAt 4 5 2 6 (build pathVar valueVar body [l1])
      (.putBack 3 6 1 7 (.ret 7))) from rfl]
  rw [runN_takeOut (env := env0) (Ht := H) (r := 0) (o := rootObj) (idx := 1) (e := 1)
    (fst := 3) (snd := 4)
    (by simp [env0]) (by simp [env0]) H_cells_zero root_slot]
  rfl

/-- The model run of the built path: the leaf's single exclusive write, the tip
restored into the child's slot, the child restored into the root's slot, and the
root handle returned. -/
theorem model_run :
    runN (build pathVar valueVar body [l0, l1]) env0 H =
      .done H5 envfin (.ref 0) [(3, true)] := by
  rw [takeOut0, outerCall]

/-! ## The executed outcome -/

/-- The executed recognized trace's own outcome: the final heap, the returned root
handle, no fault, and the leaf's single exclusive write. -/
theorem exec :
    NestedOutcome.ofExec assign p
        (execNested assign (build pathVar valueVar body [l1]) p.fragment machine) =
      some { heap := H5, result := some (.ref 0), fault := none,
             writes := [(3, true)] } := by
  obtain ⟨hout, -⟩ := simulates
  rw [hout, model_run]
  rfl

/-! ## The final heap -/

theorem H5_cells_zero : H5.cells 0 = some rootObj := by
  rw [show H5.cells 0 = some restoredRoot from Heap.set_self _ _ _]
  rw [restoredRoot_eq]

theorem H5_cells_one : H5.cells 1 = some childObj := by
  rw [Heap.set_other _ _ _ _ (by decide : (1 : Ref) ≠ 0)]
  rw [show H4.cells 1 = some restoredChild from Heap.set_self _ _ _]
  rw [restoredChild_eq]

theorem H5_cells_three : H5.cells 3 = some finalTip := by
  rw [Heap.set_other _ _ _ _ (by decide : (3 : Ref) ≠ 0)]
  rw [Heap.set_other _ _ _ _ (by decide : (3 : Ref) ≠ 1)]
  exact Heap.set_self _ _ _

theorem finalTip_slot_one : finalTip.fields[1]? = some (.scalar 1) := by decide

theorem finalTip_slot_zero : finalTip.fields[0]? = some (.ref 40) := by decide

#print axioms childContracts
#print axioms childContract_l0
#print axioms childContract_l1
#print axioms simulates
#print axioms model_run
#print axioms exec

end OwnershipTest.PathRecursion
