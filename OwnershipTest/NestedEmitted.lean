/-
The concrete nested `setAt` instance, at the recognizer's own operand binders.

The tree is a root array with two slots: slot 0 holds the scalar sibling `5`,
and slot 1 — a nontrivial child index — holds the child array `ref 1`. The child
array's slot 1 holds `4`; the child body the recursive call runs checks the child
it was handed and performs the designated write of the nonzero replacement `7`
into that slot.

The model program is `indexModelTerm` at the recognizer's operands: the take-out
from the root at the child index, the recursive call on the extracted child with
the call's path scalar and value parameter, the put-back of the recursive result
into the extracted parent at the same index, and the return. `nestedIndex_exec`
is the correspondence instantiated on this instance: the executed recognized
trace reports the same heap, returned value, fault status and write trace as the
model. `nestedIndex_boundary` states the boundary
`docs/notes/OWNERSHIP_NESTED_THEOREM_BOUNDARY.md` fixes: the designated write
landed, the extracted child's slot is restored, the scalar sibling is untouched,
cells outside the root's mutable footprint did not move, the parent and child
references are retained by their variables, and the caller's `EntryInv` is
re-established.

The cell the designated write changes is the child array's selected slot, not a
separate leaf cell the body would have extracted. That is not a narrowing: the
nested checker admits a straight-line block only with no open extraction frame
(`checkNF`'s `.base` rule), and a restored element is dead in the context a
put-back leaves, so a body cannot write into a cell it extracted; the deepest
cell an admissible child body can write is an array handle it owns, which here
is the child the call was handed.

The emitted recursive callee's body is not captured by the recognizer. The
child-call contract below is discharged for the admitted model body this file
writes down (`body`); that is not a statement about the emitted `setAt`
declaration.
-/
import OwnershipLcnf.NestedSemantics

open Lean
open Lean.Compiler.LCNF

namespace OwnershipTest.NestedEmitted

open Ownership
open OwnershipLcnf

/-! ## The object tree -/

/-- The root array: slot 0 holds the scalar sibling `5`, slot 1 holds the child
array `ref 1` — the slot the take-out empties and the put-back restores. -/
def rootObj : Ownership.Obj := ⟨#[.scalar 5, .ref 1], 1, false⟩

/-- The child array: slot 0 holds `3`, slot 1 holds `4` — the slot the child
body's designated write targets. -/
def childObj : Ownership.Obj := ⟨#[.scalar 3, .scalar 4], 1, false⟩

/-- The child after the designated write: its slot 1 holds the replacement. -/
def childWritten : Ownership.Obj := ⟨#[.scalar 3, .scalar 7], 1, false⟩

/-- Root → child, each live cell counted once. -/
def H : Ownership.Heap :=
  { cells := fun r =>
      if r = 0 then some rootObj
      else if r = 1 then some childObj
      else none
    next := 2 }

/-! ## The recognized operands and the model program -/

/-- The recognized prefix's binder identities. Every field is an identity the
walk reads; here they are concrete names, which is what makes the trace's
operands concrete. -/
def p : NestedPrefix :=
  { node := ⟨`nested.node⟩
    array := ⟨`nested.array⟩
    value := ⟨`nested.value⟩
    childArray := ⟨`nested.childArray⟩
    index := ⟨`nested.index⟩
    path := ⟨`nested.path⟩
    sizeResult := ⟨`nested.sizeResult⟩
    bound := ⟨`nested.bound⟩
    arraySite := ⟨`nested.site0⟩
    arrayCheck := ⟨`nested.arrayCheck⟩
    dflt := ⟨`nested.dflt⟩
    pair := ⟨`nested.pair⟩
    parent := ⟨`nested.parent⟩
    child := ⟨`nested.child⟩
    childSite := ⟨`nested.site1⟩
    childCheck := ⟨`nested.childCheck⟩
    recursive := ⟨`nested.recursive⟩
    restored := ⟨`nested.restored⟩
    indexDec := ⟨`nested.indexDec⟩ }

/-- The layout: the model's variables take slots `0`–`7`, the auxiliary binders
`8`–`18`. -/
def assign (f : FVarId) : Ownership.Var :=
  if f.name = `nested.array then 0
  else if f.name = `nested.index then 1
  else if f.name = `nested.value then 2
  else if f.name = `nested.parent then 3
  else if f.name = `nested.child then 4
  else if f.name = `nested.path then 5
  else if f.name = `nested.recursive then 6
  else if f.name = `nested.restored then 7
  else if f.name = `nested.node then 8
  else if f.name = `nested.childArray then 9
  else if f.name = `nested.sizeResult then 10
  else if f.name = `nested.bound then 11
  else if f.name = `nested.site0 then 12
  else if f.name = `nested.arrayCheck then 13
  else if f.name = `nested.dflt then 14
  else if f.name = `nested.pair then 15
  else if f.name = `nested.site1 then 16
  else if f.name = `nested.childCheck then 17
  else if f.name = `nested.indexDec then 18
  else 0

theorem layout : NestedLayout assign p := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [assign, p]

/-- The model environment: the root handle at the array variable, the child
index at the index variable, the replacement at the value variable, and the
call's path scalar. -/
def env0 : Ownership.Env :=
  fun x =>
    if x = 0 then some (.ref 0)
    else if x = 1 then some (.scalar 1)
    else if x = 2 then some (.scalar 7)
    else if x = 5 then some (.scalar 1)
    else none

/-- The child body: check the state it was handed and perform the designated
write into it at the call's path scalar with the value parameter. -/
def body : Ownership.Nested.NCode :=
  .base (.let 19 (.checkAlias 4) (.setArr 19 5 2 (.ret 19)))

/-- The model program, read off the recognizer's operands. -/
def term : Ownership.Nested.NCode := indexModelTerm assign p 1 body

/-! ## The machine and the agreement -/

/-- The fragment's starting machine: the heap, the array handle, the value
operand, the reified node index, the call's path scalar, the model's child
variable and the empty write trace. -/
def machine : NestedMachine :=
  { heap := H
    env := fun x =>
      if x = 0 then some (.ref 0)
      else if x = 2 then some (.scalar 7)
      else none
    nodes := fun _ => { index := .scalar 1 }
    callPath := 1
    childVar := 4
    pairs := fun _ => none
    writes := [] }

theorem agrees : NestedAgrees assign p machine env0 H 0 1 7 1 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [machine, env0, assign, p]

theorem hcell : H.cells 0 = some rootObj := by simp [H]

theorem hex : H.exclusive? 0 = true := by
  simp [H, rootObj, Ownership.Heap.exclusive?]

theorem hslot : rootObj.fields[1]? = some (.ref 1) := by decide

theorem hin : 1 < rootObj.fields.size := by decide

/-! ## The child-call contract -/

/-- The take-out heap: slot 1 of the root holds the placeholder. -/
def H1 : Ownership.Heap := takeOutHeap H 0 rootObj 1

/-- The heap the child body leaves: the child's slot 1 holds the replacement. -/
def H2 : Ownership.Heap := H1.set 1 { childObj with fields := childObj.fields.set! 1 (.scalar 7) }

/-- The final heap the model run reports. -/
def Hfin : Ownership.Heap :=
  H2.set 0 { takeOutObj rootObj 1 with
    fields := (takeOutObj rootObj 1).fields.set! 1 (.ref 1) }

/-- The model environment the call hands its callee. -/
def cenv : Ownership.Env :=
  callEnv (assign p.child) (.ref 1) (assign p.path) (.scalar 1) (assign p.value) (.scalar 7)

theorem H1_cells_zero : H1.cells 0 = some (takeOutObj rootObj 1) := by
  simp [H1, takeOutHeap, takeOutObj, H, Ownership.Heap.set]

theorem H1_cells_one : H1.cells 1 = some childObj := by
  simp [H1, takeOutHeap, H, Ownership.Heap.set, rootObj]

theorem H1_cells_other {q : Ownership.Ref} (h0 : q ≠ 0) (h1 : q ≠ 1) :
    H1.cells q = none := by
  simp [H1, takeOutHeap, H, Ownership.Heap.set, h0, h1]

/-- Every cell of the take-out heap has no reference fields. -/
theorem H1_fieldRefs {r : Ownership.Ref} {o : Ownership.Obj} (h : H1.cells r = some o) :
    Ownership.Entry.fieldRefs o = [] := by
  by_cases h0 : r = 0
  · subst h0
    rw [H1_cells_zero] at h
    have ho : o = takeOutObj rootObj 1 := (Option.some.inj h).symm
    subst ho
    simp [Ownership.Entry.fieldRefs, Ownership.Entry.refsOf, takeOutObj, rootObj]
  · by_cases h1 : r = 1
    · subst h1
      rw [H1_cells_one] at h
      have ho : o = childObj := (Option.some.inj h).symm
      subst ho
      simp [Ownership.Entry.fieldRefs, Ownership.Entry.refsOf, childObj]
    · rw [H1_cells_other h0 h1] at h
      simp at h

/-- The child's mutable footprint at the take-out heap is the child itself: its
cells have no reference fields. -/
theorem H1_footprint {q : Ownership.Ref} (h : Ownership.Entry.MutableFootprint H1 1 q) :
    q = 1 := by
  induction h with
  | root _ _ => rfl
  | step _ hcell _ hmem _ _ ih =>
      subst ih
      rw [H1_fieldRefs hcell] at hmem
      simp at hmem

/-- The child body's run: it checks the child, writes the replacement into slot
1, and returns the child reference. -/
theorem body_run : Ownership.Nested.runN body cenv H1 =
    .done H2 (cenv.set 19 (.ref 1)) (.ref 1) [(1, true)] := by
  simp [body, cenv, callEnv, Ownership.Nested.runN, H1, H2, takeOutHeap, H,
    Ownership.Heap.set, Ownership.Heap.exclusive?, Ownership.Res.addWrite,
    Ownership.run, rootObj, childObj, assign, p]

theorem H1_exclusive : H1.exclusive? 1 = true := by
  simp [H1, takeOutHeap, H, Ownership.Heap.set, Ownership.Heap.exclusive?, rootObj, childObj]

theorem childContract : ChildContract H1 cenv body 1 := by
  refine ⟨H1_exclusive, H2, cenv.set 19 (.ref 1), [(1, true)], body_run, by simp, ?_⟩
  intro q hq
  have hq1 : q ≠ 1 := by
    intro h
    subst h
    exact hq (Ownership.Entry.MutableFootprint.root H1_cells_one (by simp [childObj]))
  exact Ownership.Heap.set_other _ _ _ _ hq1

/-- The parent array is not in the child's mutable footprint. -/
theorem hsep : ¬ Ownership.Entry.MutableFootprint H1 1 0 := by
  intro h
  have h1 : 0 = 1 := H1_footprint h
  exact absurd h1 (by decide)

/-! ## The model run -/

/-- The model environment the run leaves: the extracted parent, the child, the
recursive result and the restored array. -/
def envfin : Ownership.Env :=
  (((env0.set 3 (.ref 0)).set 4 (.ref 1)).set 6 (.ref 1)).set 7 (.ref 0)

theorem model_run : Ownership.Nested.runN term env0 H = .done Hfin envfin (.ref 0) [(1, true)] := by
  simp [Ownership.Nested.runN, term, indexModelTerm, body, env0, envfin,
    H1, H2, Hfin, takeOutHeap, takeOutObj, H, Ownership.Heap.set,
    Ownership.Heap.exclusive?, Ownership.Env.set, Ownership.Nested.isolateEnv,
    Ownership.Res.addWrite, Ownership.Nested.addWrites, Ownership.run,
    rootObj, childObj, assign, p]

/-! ## The correspondence on the instance -/

/-- The correspondence instantiated: the executed recognized trace reports the
model's outcome, the model run is fault-free, and every recorded write is
exclusive. -/
theorem nestedIndex_simulates :
    NestedOutcome.ofExec assign p (execNested assign body p.fragment machine) =
        some (NestedOutcome.ofModel (Ownership.Nested.runN term env0 H)) ∧
      (∃ H' env' ws,
        Ownership.Nested.runN term env0 H = .done H' env' (.ref 0) ws ∧
          (∀ w ∈ ws, w.2 = true)) :=
  index_fragment_simulates_model assign p layout body machine env0 H 0 rootObj 1 7 1 1
    agrees hcell hex hslot hin hsep childContract

/-- The executed trace's own outcome: the final heap, the returned root handle,
no fault, and the child body's single exclusive write. -/
theorem nestedIndex_exec :
    NestedOutcome.ofExec assign p (execNested assign body p.fragment machine) =
      some { heap := Hfin, result := some (.ref 0), fault := none, writes := [(1, true)] } := by
  obtain ⟨hout, -⟩ := nestedIndex_simulates
  rw [hout, model_run]
  rfl

/-! ## The final heap's cells -/

theorem Hfin_zero : Hfin.cells 0 = some rootObj := by
  simp [Hfin, H2, H1, takeOutHeap, takeOutObj, Ownership.Heap.set, rootObj, childObj]

theorem Hfin_one : Hfin.cells 1 = some childWritten := by
  simp [Hfin, H2, H1, takeOutHeap, takeOutObj, Ownership.Heap.set, rootObj, childObj,
    childWritten]

theorem Hfin_cells_other {q : Ownership.Ref} (h0 : q ≠ 0) (h1 : q ≠ 1) :
    Hfin.cells q = H.cells q := by
  simp [Hfin, H2, H1, takeOutHeap, Ownership.Heap.set, H, h0, h1]

theorem H_cells_one : H.cells 1 = some childObj := by simp [H]

/-- The root's mutable footprint at the input heap is the root and its child. -/
theorem H_footprint {q : Ownership.Ref} (h : Ownership.Entry.MutableFootprint H 0 q) :
    q = 0 ∨ q = 1 := by
  induction h with
  | root _ _ => exact Or.inl rfl
  | step _ hcellr _ hmem _ _ ih =>
      rcases ih with h0 | h1
      · subst h0
        rw [hcell] at hcellr
        have ho : _ = rootObj := (Option.some.inj hcellr).symm
        rw [ho] at hmem
        simp [Ownership.Entry.fieldRefs, Ownership.Entry.refsOf, rootObj] at hmem
        exact Or.inr hmem
      · subst h1
        rw [H_cells_one] at hcellr
        have ho : _ = childObj := (Option.some.inj hcellr).symm
        rw [ho] at hmem
        simp [Ownership.Entry.fieldRefs, Ownership.Entry.refsOf, childObj] at hmem

/-- The final heap's mutable footprint from the root is the root and its child. -/
theorem Hfin_footprint {q : Ownership.Ref} (h : Ownership.Entry.MutableFootprint Hfin 0 q) :
    q = 0 ∨ q = 1 := by
  induction h with
  | root _ _ => exact Or.inl rfl
  | step _ hcellr _ hmem _ _ ih =>
      rcases ih with h0 | h1
      · subst h0
        rw [Hfin_zero] at hcellr
        have ho : _ = rootObj := (Option.some.inj hcellr).symm
        rw [ho] at hmem
        simp [Ownership.Entry.fieldRefs, Ownership.Entry.refsOf, rootObj] at hmem
        exact Or.inr hmem
      · subst h1
        rw [Hfin_one] at hcellr
        have ho : _ = childWritten := (Option.some.inj hcellr).symm
        rw [ho] at hmem
        simp [Ownership.Entry.fieldRefs, Ownership.Entry.refsOf, childWritten] at hmem

/-! ## The caller's checker state -/

/-- The caller's context: the root handle owned at variable `0`, the child index
and the value parameter as scalars, and the call's path scalar. -/
def ctx0 : Ownership.Ctx :=
  { us := fun x =>
      if x = 0 then .owned
      else if x = 1 then .scalar
      else if x = 2 then .scalar
      else if x = 5 then .scalar
      else .dead
    refOf := fun x => if x = 0 then some 0 else none
    mult := fun r => if r = 0 then 1 else if r = 1 then 1 else 0 }

def ctx1 : Ownership.Ctx := (ctx0.move 0 3).bindOwned 4 1

def ctx2 : Ownership.Ctx := ctx1.move 4 6

/-- The caller's context after the checker accepts the model program. -/
def ctxF : Ownership.Ctx := (ctx2.move 3 7).setUs 6 .dead

/-- The call's callee environment, as the state-indexed premise sees it, is the
contract's call environment. -/
theorem iso_env : Ownership.Nested.isolateEnv
    ((env0.set (assign p.parent) (.ref 0)).set (assign p.child) (.ref 1))
    (assign p.child) (assign p.path) (assign p.value) = cenv := by
  have h := isolateEnv_eq_callEnv
    (env := (env0.set (assign p.parent) (.ref 0)).set (assign p.child) (.ref 1))
    (state := assign p.child) (path := assign p.path) (x := assign p.value)
    (sv := .ref 1) (pv := .scalar 1) (xv := .scalar 7)
    (by simp [Ownership.Env.set])
    (by simp [Ownership.Env.set, env0, assign, p])
    (by simp [Ownership.Env.set, env0, assign, p])
  exact h

theorem checkN_term : Ownership.Nested.checkN ctx0 term = some ctxF := by
  simp [Ownership.Nested.checkN, Ownership.Nested.checkNF, term, indexModelTerm, body,
    ctx0, ctx1, ctx2, ctxF, Ownership.Ctx.multOf, Ownership.Nested.openRef,
    Ownership.Nested.CountFree, Ownership.Nested.countFreeCode, Ownership.Nested.retVar,
    Ownership.Nested.codeRetVar, Ownership.Nested.isolatedCtx, Ownership.check,
    Ownership.Ctx.setUs, Ownership.Ctx.bindOwned, Ownership.Ctx.move,
    assign, p]

theorem inv0 : Ownership.Inv H env0 ctx0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r
    by_cases h0 : r = 0
    · subst h0; simp [H, ctx0, Ownership.Heap.rc, rootObj]
    · by_cases h1 : r = 1
      · subst h1; simp [H, ctx0, Ownership.Heap.rc, h0, childObj]
      · simp [H, ctx0, Ownership.Heap.rc, h0, h1]
  · intro x r hx hr
    by_cases hx0 : x = 0
    · subst hx0
      have hr0 : r = 0 := by simpa [ctx0] using hr.symm
      subst hr0
      exact ⟨by simp [env0], by simp [ctx0]⟩
    · by_cases hx1 : x = 1
      · subst hx1; simp [ctx0, hx0] at hx
      · by_cases hx2 : x = 2
        · subst hx2; simp [ctx0, hx0, hx1] at hx
        · by_cases hx5 : x = 5
          · subst hx5; simp [ctx0, hx0, hx1, hx2] at hx
          · simp [ctx0, hx0, hx1, hx2, hx5] at hx
  · intro x r hx hr
    by_cases hx0 : x = 0
    · subst hx0; simp [ctx0] at hx
    · by_cases hx1 : x = 1
      · subst hx1; simp [ctx0, hx0] at hx
      · by_cases hx2 : x = 2
        · subst hx2; simp [ctx0, hx0, hx1] at hx
        · by_cases hx5 : x = 5
          · subst hx5; simp [ctx0, hx0, hx1, hx2] at hx
          · simp [ctx0, hx0, hx1, hx2, hx5] at hx
  · intro x hx
    by_cases hx0 : x = 0
    · subst hx0; simp [ctx0] at hx
    · by_cases hx1 : x = 1
      · subst hx1; exact ⟨1, by simp [env0]⟩
      · by_cases hx2 : x = 2
        · subst hx2; exact ⟨7, by simp [env0]⟩
        · by_cases hx5 : x = 5
          · subst hx5; exact ⟨1, by simp [env0]⟩
          · simp [ctx0, hx0, hx1, hx2, hx5] at hx
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

/-- The state-indexed heap premise at this heap: the root's slot holds the child,
the child is exclusive, the body's own obligation is trivial, and the outer
continuation restores the slot on whatever heap the body leaves. -/
theorem hok0 : Ownership.Nested.TakeOutsOK H env0 term := by
  refine ⟨0, rootObj, 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [env0, assign, p]
  · simp [env0, assign, p]
  · simp [H]
  · simp [rootObj]
  · decide
  · refine ⟨1, ?_, ?_, ?_, ?_⟩
    · simp [assign, p, Ownership.Env.set]
    · simpa [H1, takeOutHeap] using H1_exclusive
    · trivial
    · intro H' envb vb wsb hb
      rw [iso_env] at hb
      have hH1 : H.set 0 { rootObj with fields := rootObj.fields.setIfInBounds 1 (.scalar 0) } = H1 := by
        simp [H1, takeOutHeap]
      rw [hH1, body_run] at hb
      injection hb with hH henv hv hws
      rw [← hH]
      refine ⟨0, 1, takeOutObj rootObj 1, 1, ?_, ?_, ?_, ?_, trivial⟩
      · simp [Ownership.Env.set, assign, p]
      · simp [Ownership.Env.set, assign, p]
      · simp [Ownership.Env.set, env0, assign, p]
      · rw [H2, Ownership.Heap.set_other _ _ _ _ (by decide)]
        exact H1_cells_zero

/-! ## The boundary -/

/-- `ctxF`'s only owned variable is the returned array's. -/
theorem ctxF_owned {x : Ownership.Var} (hx : ctxF.us x = .owned) : x = 7 := by
  by_cases h7 : x = 7
  · exact h7
  · exfalso
    have h6 : x ≠ 6 := by
      intro h; subst h
      simp [ctxF, Ownership.Ctx.setUs] at hx
    have h4 : x ≠ 4 := by
      intro h; subst h
      simp [ctxF, ctx2, ctx1, Ownership.Ctx.setUs, Ownership.Ctx.move,
        Ownership.Ctx.bindOwned, h7, h6] at hx
    have h3 : x ≠ 3 := by
      intro h; subst h
      simp [ctxF, ctx2, ctx1, Ownership.Ctx.setUs, Ownership.Ctx.move,
        Ownership.Ctx.bindOwned, h7, h6, h4] at hx
    have h0 : x ≠ 0 := by
      intro h; subst h
      simp [ctxF, ctx2, ctx1, ctx0, Ownership.Ctx.setUs, Ownership.Ctx.move,
        Ownership.Ctx.bindOwned, h7, h6, h4, h3] at hx
    have hc0 : ctx0.us x ≠ .owned := by
      by_cases h1 : x = 1 <;> by_cases h2 : x = 2 <;> by_cases h5 : x = 5 <;>
        simp [ctx0, h0, h1, h2, h5]
    have hnot : ctxF.us x ≠ .owned := by
      simp only [ctxF, ctx2, ctx1, Ownership.Ctx.setUs, Ownership.Ctx.move,
        Ownership.Ctx.bindOwned, h7, h6, h4, h3, h0]
      exact hc0
    exact hnot hx

theorem ctxF_complete : Ownership.Entry.RootsComplete ctxF Hfin 0 := by
  intro x r hx hr
  have hx7 : x = 7 := ctxF_owned hx
  subst hx7
  have href : ctxF.refOf 7 = some 0 := by
    simp [ctxF, ctx2, ctx1, ctx0, Ownership.Ctx.setUs, Ownership.Ctx.move,
      Ownership.Ctx.bindOwned]
  rw [href] at hr
  have hr0 : r = 0 := (Option.some.inj hr).symm
  subst hr0
  exact Ownership.Entry.MutableFootprint.root Hfin_zero (by simp [rootObj])

/-- The kernel-checked boundary of the nested instance: the run is fault-free and
every write exclusive, the designated slot of the child holds the nonzero
replacement, the child's extracted slot is restored to the child while the scalar
sibling stays in place, cells outside the root's mutable footprint did not move,
the parent and child references are retained by their variables, and the entry
condition holds again for the caller's context. -/
theorem nestedIndex_boundary :
    ∃ H' env' ws,
      Ownership.Nested.runN term env0 H = .done H' env' (.ref 0) ws ∧
        (∀ w ∈ ws, w.2 = true) ∧
        -- the designated write landed in the child's selected slot
        H'.cells 1 = some childWritten ∧
        -- the extracted child's slot is restored, and the scalar sibling is intact
        H'.cells 0 = some rootObj ∧ rootObj.fields[0]? = some (.scalar 5) ∧
        rootObj.fields[1]? = some (.ref 1) ∧
        -- cells outside the root's mutable footprint did not move
        (∀ q, ¬ Ownership.Entry.MutableFootprint H 0 q → H'.cells q = H.cells q) ∧
        -- the parent and child references are retained by their variables
        env' 3 = some (.ref 0) ∧ env' 4 = some (.ref 1) ∧
        env' 6 = some (.ref 1) ∧ env' 7 = some (.ref 0) ∧
        -- the caller's entry condition is re-established
        Ownership.Entry.EntryInv H' env' ctxF 0 [] := by
  -- the correspondence: fault-freedom and exclusive writes at this instance
  obtain ⟨-, H', env', ws, hrun, hws⟩ := nestedIndex_simulates
  -- the model run is the concrete one
  have hrun' : H' = Hfin ∧ env' = envfin ∧ ws = [(1, true)] := by
    rw [model_run] at hrun
    injection hrun with hH henv hw hws'
    exact ⟨hH.symm, henv.symm, hws'.symm⟩
  obtain ⟨rfl, rfl, rfl⟩ := hrun'
  -- the caller's invariant
  obtain ⟨H'', env'', v'', ws'', hrun'', hws'', hinv''⟩ :=
    Ownership.Nested.checkN_sound checkN_term inv0 hok0
  rw [model_run] at hrun''
  injection hrun'' with hH2 henv2 hv hws2
  rw [hH2.symm, henv2.symm] at hinv''
  refine ⟨Hfin, envfin, [(1, true)], model_run, hws, Hfin_one, Hfin_zero, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · intro q hq
    have hq0 : q ≠ 0 := by
      intro h
      subst h
      exact hq (Ownership.Entry.MutableFootprint.root (root := 0) (o := rootObj)
        hcell (by simp [rootObj]))
    have hq1 : q ≠ 1 := by
      intro h
      subst h
      exact hq (Ownership.Entry.MutableFootprint.step (root := 0) (r := 0) (r' := 1)
        (o := rootObj) (o' := childObj)
        (Ownership.Entry.MutableFootprint.root (root := 0) (o := rootObj)
          hcell (by simp [rootObj]))
        hcell (by simp [rootObj])
        (by simp [Ownership.Entry.fieldRefs, Ownership.Entry.refsOf, rootObj])
        H_cells_one (by simp [childObj]))
    exact Hfin_cells_other hq0 hq1
  · simp [envfin, Ownership.Env.set]
  · simp [envfin, Ownership.Env.set]
  · simp [envfin, Ownership.Env.set]
  · simp [envfin, Ownership.Env.set]
  · refine ⟨hinv'', ?_, ?_, ?_⟩
    · intro r hr
      rcases Hfin_footprint hr with h | h
      · subst h; simp [Ownership.Heap.rc, Hfin_zero, rootObj]
      · subst h; simp [Ownership.Heap.rc, Hfin_one, childWritten]
    · intro r hr _
      exact Ownership.Entry.ClientReachable.isEmpty hr
    · exact ctxF_complete

#print axioms nestedIndex_simulates
#print axioms nestedIndex_exec
#print axioms nestedIndex_boundary

end OwnershipTest.NestedEmitted
