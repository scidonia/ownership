/-
The one-pair branch certificate fixtures.

`H0` is a unique pair (count one) whose left field holds the child `ref 1` and
whose right field holds the sibling `ref 2`. The exclusive/left run reuses the
pair cell: `unique_left_run` records the exclusive write at `ref 0`, and
`unique_left_post` binds the resulting cell's fields, count and persistence.
`unique_right_run` is the symmetric right run.

`Hb` is the shared branch entry: the same pair at count two, the retained
sibling counted three, and `Hb.next` fresh. `shared_left_copy` and
`shared_right_copy` bind the old pair's before/after fields and persistence, the
old count `k - 1`, the fresh pair's selected/retained fields and count one, the
retained sibling's count increment, and the caller's environment/context
reference and multiplicities. `copy_poststate` and `copy_inv` carry the
reconstruction and the invariant; the shared path is not a designated exclusive
write.

The child of the exclusive arm is the M4a nested checker's `callAt` run on the
selected component (`child_check`, `child_ok`, `child_run`), so the pair step
starts after an accepted child summary. The negative controls are
`shared_rejected` and `incShared_rejected`, each paired with the same checker's
positive control `unique_accepted`.
-/
import Ownership.Pair
import Ownership.Nested

open Ownership
open Ownership.Pair
open Ownership.Nested

namespace OwnershipTest.PairBranchProof

/-! ## Concrete heaps, environments and contexts -/

def childObj : Obj := ⟨#[.scalar 0], 1, false⟩

def sibObj : Obj := ⟨#[.scalar 0], 1, false⟩

/-- The shared entry's retained sibling: counted three. -/
def sharedSibObj : Obj := ⟨#[.scalar 0], 3, false⟩

/-- The unique pair: left `ref 1`, right `ref 2`, count one. -/
def pairObj : Obj := ⟨#[.ref 1, .ref 2], 1, false⟩

/-- The shared pair entry: the same fields at count two. -/
def sharedPairObj : Obj := ⟨#[.ref 1, .ref 2], 2, false⟩

/-- The unique pair's heap. -/
def H0 : Heap :=
  { cells := fun r =>
      if r = 0 then some pairObj
      else if r = 1 then some childObj
      else if r = 2 then some sibObj
      else none
    next := 3 }

/-- The shared branch-entry heap: pair count two, sibling count three. -/
def Hb : Heap :=
  { cells := fun r =>
      if r = 0 then some sharedPairObj
      else if r = 1 then some childObj
      else if r = 2 then some sharedSibObj
      else none
    next := 3 }

/-- Variable 0 owns the pair; variable 1 is the dead result slot. -/
def pairEnv : Env :=
  fun x => if x = 0 then some (.ref 0) else none

/-- The unique pair's context: the pair, child and sibling each at count one. -/
def ctx0 : Ctx :=
  { us := fun x => if x = 0 then .owned else .dead
    refOf := fun x => if x = 0 then some 0 else none
    mult := fun r => if r = 0 then 1 else if r = 1 then 1 else if r = 2 then 1 else 0 }

/-- The shared branch-entry context: pair two, child one, sibling three. -/
def ctxb : Ctx :=
  { us := fun x => if x = 0 then .owned else .dead
    refOf := fun x => if x = 0 then some 0 else none
    mult := fun r => if r = 0 then 2 else if r = 1 then 1 else if r = 2 then 3 else 0 }

theorem inv0 : Inv H0 pairEnv ctx0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r
    by_cases h0 : r = 0
    · subst h0; simp [H0, ctx0, Heap.rc, pairObj]
    · by_cases h1 : r = 1
      · subst h1; simp [H0, ctx0, Heap.rc, h0, childObj]
      · by_cases h2 : r = 2
        · subst h2; simp [H0, ctx0, Heap.rc, h0, h1, sibObj]
        · simp [H0, ctx0, Heap.rc, h0, h1, h2]
  · intro x r hx hr
    by_cases hx0 : x = 0
    · subst hx0
      have hr0 : r = 0 := by simpa [ctx0] using hr.symm
      subst hr0
      exact ⟨by simp [pairEnv], by simp [ctx0]⟩
    · simp [ctx0, hx0] at hx
  · intro x r hx hr
    by_cases hx0 : x = 0
    · subst hx0; simp [ctx0] at hx
    · simp [ctx0, hx0] at hx
  · intro x hx
    by_cases hx0 : x = 0
    · subst hx0; simp [ctx0] at hx
    · simp [ctx0, hx0] at hx
  · intro r o hcell
    by_cases h0 : r = 0
    · subst h0; simp [H0] at hcell; subst hcell; rfl
    · by_cases h1 : r = 1
      · subst h1; simp [H0, h0] at hcell; subst hcell; rfl
      · by_cases h2 : r = 2
        · subst h2; simp [H0, h0, h1] at hcell; subst hcell; rfl
        · simp [H0, h0, h1, h2] at hcell

theorem invb : Inv Hb pairEnv ctxb := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r
    by_cases h0 : r = 0
    · subst h0; simp [Hb, ctxb, Heap.rc, sharedPairObj]
    · by_cases h1 : r = 1
      · subst h1; simp [Hb, ctxb, Heap.rc, h0, childObj]
      · by_cases h2 : r = 2
        · subst h2; simp [Hb, ctxb, Heap.rc, h0, h1, sharedSibObj]
        · simp [Hb, ctxb, Heap.rc, h0, h1, h2]
  · intro x r hx hr
    by_cases hx0 : x = 0
    · subst hx0
      have hr0 : r = 0 := by simpa [ctxb] using hr.symm
      subst hr0
      exact ⟨by simp [pairEnv], by simp [ctxb]⟩
    · simp [ctxb, hx0] at hx
  · intro x r hx hr
    by_cases hx0 : x = 0
    · subst hx0; simp [ctxb] at hx
    · simp [ctxb, hx0] at hx
  · intro x hx
    by_cases hx0 : x = 0
    · subst hx0; simp [ctxb] at hx
    · simp [ctxb, hx0] at hx
  · intro r o hcell
    by_cases h0 : r = 0
    · subst h0; simp [Hb] at hcell; subst hcell; rfl
    · by_cases h1 : r = 1
      · subst h1; simp [Hb, h0] at hcell; subst hcell; rfl
      · by_cases h2 : r = 2
        · subst h2; simp [Hb, h0, h1] at hcell; subst hcell; rfl
        · simp [Hb, h0, h1, h2] at hcell

theorem shape0 : ∀ x r, ctx0.us x = .owned → ctx0.refOf x = some r →
    ∃ o pf, H0.cells r = some o ∧ pairOf? o = some pf := by
  intro x r hx hr
  have hx0 : x = 0 := by simpa [ctx0] using hx
  subst hx0
  have hr0 : r = 0 := by simpa [ctx0] using hr.symm
  subst hr0
  exact ⟨pairObj, ⟨1, 2⟩, by simp [H0], by simp [pairOf?, field?, pairObj]⟩

/-! ## The exclusive child, through the M4a nested checker -/

def childCode : NCode := .callAt 10 11 12 13 (.ret 13)

def childEnv : Env :=
  fun x =>
    if x = 10 then some (.ref 1)
    else if x = 11 then some (.scalar 0)
    else if x = 12 then some (.scalar 0)
    else none

def childCtx : Ctx :=
  { us := fun x =>
      if x = 10 then .owned else if x = 11 then .scalar else if x = 12 then .scalar else .dead
    refOf := fun x => if x = 10 then some 1 else none
    mult := fun r => if r = 1 then 1 else 0 }

theorem child_check : checkN childCtx childCode = some (childCtx.move 10 13) := by
  simp [checkN, checkNF, childCode, childCtx, Ctx.multOf, openRef]

theorem child_ok : TakeOutsOK H0 childEnv childCode := by
  refine ⟨1, ?_, ?_, trivial⟩
  · simp [childEnv]
  · decide

theorem child_run :
    runN childCode childEnv H0 = .done H0 (childEnv.set 13 (.ref 1)) (.ref 1) [(1, true)] := by
  change runN (.callAt 10 11 12 13 (.ret 13)) childEnv H0 =
    .done H0 (childEnv.set 13 (.ref 1)) (.ref 1) [(1, true)]
  simp [runN, childEnv, H0, childObj, sibObj, Heap.exclusive?, Res.addWrite]

/-! ## The unique branches -/

def pairCodeLeft : PCode := .pairWrite .left 0 1 1 (.ret 1)

def pairCodeRight : PCode := .pairWrite .right 0 2 1 (.ret 1)

theorem unique_accepted : ∃ c, checkP ctx0 pairCodeLeft = some c := by
  refine ⟨ctx0.pairReuse 0 1, ?_⟩
  simp [pairCodeLeft, checkP, ctx0, Ctx.multOf, Ctx.pairReuse, Ctx.move]

theorem unique_right_accepted : ∃ c, checkP ctx0 pairCodeRight = some c := by
  refine ⟨ctx0.pairReuse 0 1, ?_⟩
  simp [pairCodeRight, checkP, ctx0, Ctx.multOf, Ctx.pairReuse, Ctx.move]

theorem unique_left_run :
    runP pairCodeLeft pairEnv H0 =
      (Res.done (reuse H0 0 pairObj .left 1) (pairEnv.set 1 (.ref 0)) (.ref 0) []).addWrite
        (0, true) := by
  unfold pairCodeLeft
  rw [runP_reuse (r := 0) (o := pairObj) (pf := ⟨1, 2⟩) (henv := by simp [pairEnv])
    (hcell := by simp [H0]) (hpf := by simp [pairOf?, field?, pairObj]) (hex := by decide)]
  simp [runP, pairEnv, Env.set, Fields.retained]

/-- The accepted child run leaves the pair cell at `H0`, and the reuse step
starts from that same branch entry. -/
theorem exclusive_child_then_reuse :
    runN childCode childEnv H0 =
        .done H0 (childEnv.set 13 (.ref 1)) (.ref 1) [(1, true)] ∧
      runP pairCodeLeft pairEnv H0 =
        (Res.done (reuse H0 0 pairObj .left 1) (pairEnv.set 1 (.ref 0)) (.ref 0) []).addWrite
          (0, true) :=
  ⟨child_run, unique_left_run⟩

theorem unique_left_post :
    ((reuse H0 0 pairObj .left 1).cells 0).map (·.fields) = some #[.ref 1, .ref 2] ∧
      ((reuse H0 0 pairObj .left 1).cells 0).map (·.rc) = some 1 ∧
      ((reuse H0 0 pairObj .left 1).cells 0).map (·.persistent) = some false := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [reuse, pairObj, Heap.set]

theorem unique_right_run :
    runP pairCodeRight pairEnv H0 =
      (Res.done (reuse H0 0 pairObj .right 2) (pairEnv.set 1 (.ref 0)) (.ref 0) []).addWrite
        (0, true) := by
  unfold pairCodeRight
  rw [runP_reuse (r := 0) (o := pairObj) (pf := ⟨1, 2⟩) (henv := by simp [pairEnv])
    (hcell := by simp [H0]) (hpf := by simp [pairOf?, field?, pairObj]) (hex := by decide)]
  simp [runP, pairEnv, Env.set, Fields.retained]

theorem unique_right_post :
    ((reuse H0 0 pairObj .right 2).cells 0).map (·.fields) = some #[.ref 1, .ref 2] ∧
      ((reuse H0 0 pairObj .right 2).cells 0).map (·.rc) = some 1 ∧
      ((reuse H0 0 pairObj .right 2).cells 0).map (·.persistent) = some false := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [reuse, pairObj, Heap.set]

/-! ## The shared copies -/

theorem hb_fresh : Hb.cells Hb.next = none := by
  simp [Hb]

theorem shared_left_copy_inv :
    Inv (copy Hb 0 sharedPairObj .left 2 1) ((pairEnv.set 1 (.ref (copyRef Hb))).erase 0)
      (ctxb.pairCopy 0 1 0 2 (copyRef Hb)) := by
  apply copy_inv (o := sharedPairObj) (os := sharedSibObj) (sel := .left) (k := 2)
  · exact invb
  · simp [ctxb]
  · simp [ctxb]
  · simp [ctxb]
  · decide
  · simp [Hb]
  · simp [ctxb]
  · decide
  · simp [Hb]
  · decide
  · exact hb_fresh
  · decide
  · decide

theorem shared_left_copy :
    (copy Hb 0 sharedPairObj .left 2 1).cells 0 =
        some { sharedPairObj with rc := 1 } ∧
      ((copy Hb 0 sharedPairObj .left 2 1).cells 0).map (·.fields) =
        some #[.ref 1, .ref 2] ∧
      ((copy Hb 0 sharedPairObj .left 2 1).cells 0).map (·.persistent) = some false ∧
      (copy Hb 0 sharedPairObj .left 2 1).cells (copyRef Hb) =
        some ⟨#[.ref 1, .ref 2], 1, false⟩ ∧
      (copy Hb 0 sharedPairObj .left 2 1).rc 2 = Hb.rc 2 + 1 ∧
      (copy Hb 0 sharedPairObj .left 2 1).rc (copyRef Hb) = 1 ∧
      (copy Hb 0 sharedPairObj .left 2 1).next = Hb.next + 1 := by
  have h := copy_poststate (H := Hb) (r := 0) (o := sharedPairObj) (sel := .left)
    (s := 2) (rep := 1) (os := sharedSibObj) (by simp [Hb]) (by simp [Hb])
    (by decide) (by simp [Hb, copyRef]) (by decide)
  refine ⟨h.1, ?_, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2⟩
  simpa [Hb, sharedPairObj] using h.2.1

theorem shared_fresh_left : copyRef Hb = Hb.next ∧ copyRef Hb ≠ 0 ∧ copyRef Hb ≠ 2 := by
  simp [copyRef, Hb]

theorem shared_fresh_right : copyRef Hb = Hb.next ∧ copyRef Hb ≠ 0 ∧ copyRef Hb ≠ 1 := by
  simp [copyRef, Hb]

theorem shared_left_ctx :
    (ctxb.pairCopy 0 1 0 2 (copyRef Hb)).mult 0 = ctxb.mult 0 - 1 ∧
      (ctxb.pairCopy 0 1 0 2 (copyRef Hb)).mult 2 = ctxb.mult 2 + 1 ∧
      (ctxb.pairCopy 0 1 0 2 (copyRef Hb)).mult (copyRef Hb) = 1 ∧
      (ctxb.pairCopy 0 1 0 2 (copyRef Hb)).refOf 1 = some (copyRef Hb) ∧
      (ctxb.pairCopy 0 1 0 2 (copyRef Hb)).us 1 = .owned ∧
      (ctxb.pairCopy 0 1 0 2 (copyRef Hb)).us 0 = .dead := by
  simp [copyRef, Ctx.pairCopy, Ctx.move, Hb, ctxb]

theorem shared_right_copy :
    (copy Hb 0 sharedPairObj .right 1 2).cells 0 =
        some { sharedPairObj with rc := 1 } ∧
      ((copy Hb 0 sharedPairObj .right 1 2).cells 0).map (·.fields) =
        some #[.ref 1, .ref 2] ∧
      ((copy Hb 0 sharedPairObj .right 1 2).cells 0).map (·.persistent) = some false ∧
      (copy Hb 0 sharedPairObj .right 1 2).cells (copyRef Hb) =
        some ⟨#[.ref 1, .ref 2], 1, false⟩ ∧
      (copy Hb 0 sharedPairObj .right 1 2).rc 1 = Hb.rc 1 + 1 ∧
      (copy Hb 0 sharedPairObj .right 1 2).rc (copyRef Hb) = 1 ∧
      (copy Hb 0 sharedPairObj .right 1 2).next = Hb.next + 1 := by
  have h := copy_poststate (H := Hb) (r := 0) (o := sharedPairObj) (sel := .right)
    (s := 1) (rep := 2) (os := childObj) (by simp [Hb]) (by simp [Hb])
    (by decide) (by simp [Hb, copyRef]) (by decide)
  refine ⟨h.1, ?_, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2⟩
  simpa [Hb, sharedPairObj] using h.2.1

theorem shared_left_run :
    runP (.pairWrite .left 0 1 1 (.ret 1)) pairEnv Hb =
      (Res.done (copy Hb 0 sharedPairObj .left 2 1)
        (pairEnv.set 1 (.ref (copyRef Hb))) (.ref (copyRef Hb)) []).addWrite (0, false) := by
  rw [runP_copy (r := 0) (o := sharedPairObj) (pf := ⟨1, 2⟩) (henv := by simp [pairEnv])
    (hcell := by simp [Hb]) (hpf := by simp [pairOf?, field?, sharedPairObj]) (hex := by decide)]
  simp [runP, pairEnv, Env.set, Fields.retained]

theorem shared_right_run :
    runP (.pairWrite .right 0 2 1 (.ret 1)) pairEnv Hb =
      (Res.done (copy Hb 0 sharedPairObj .right 1 2)
        (pairEnv.set 1 (.ref (copyRef Hb))) (.ref (copyRef Hb)) []).addWrite (0, false) := by
  rw [runP_copy (r := 0) (o := sharedPairObj) (pf := ⟨1, 2⟩) (henv := by simp [pairEnv])
    (hcell := by simp [Hb]) (hpf := by simp [pairOf?, field?, sharedPairObj]) (hex := by decide)]
  simp [runP, pairEnv, Env.set, Fields.retained]

/-! ## Same-checker negative controls -/

/-- The pair at count two. -/
def sharedCtx : Ctx :=
  { ctx0 with mult := fun r => if r = 0 then 2 else if r = 1 then 1 else if r = 2 then 1 else 0 }

/-- The shared pair at count two is not a designated exclusive write. -/
theorem shared_rejected : checkP sharedCtx pairCodeLeft = none := by
  have hm : sharedCtx.multOf 0 = 2 := by simp [sharedCtx, ctx0, Ctx.multOf]
  exact checkP_refuses_shared (pairVar := 0) hm

/-- Duplicating the pair's handle raises the count past one. -/
theorem incShared_rejected : checkP (ctx0.inc 0 1) pairCodeLeft = none := by
  have hm : 1 < (ctx0.inc 0 1).multOf 0 := by simp [ctx0, Ctx.inc, Ctx.multOf]
  exact checkP_refuses_incShared (pairVar := 0) hm

-- Same-checker positive control and both refusals, executable.
#guard (checkP ctx0 pairCodeLeft).isSome
#guard (checkP sharedCtx pairCodeLeft).isNone
#guard (checkP (ctx0.inc 0 1) pairCodeLeft).isNone

-- The unique branch keeps the pair address and count, and the untouched sibling.
#guard ((reuse H0 0 pairObj .right 2).cells 0).map (·.fields) == some #[.ref 1, .ref 2]
#guard ((reuse H0 0 pairObj .right 2).cells 0).map (·.rc) == some 1

-- The shared copy's exact poststate.
#guard ((copy Hb 0 sharedPairObj .left 2 1).cells 0).map (·.rc) == some 1
#guard (copy Hb 0 sharedPairObj .left 2 1).rc 2 == Hb.rc 2 + 1
#guard (copy Hb 0 sharedPairObj .left 2 1).rc (copyRef Hb) == 1
#guard ((copy Hb 0 sharedPairObj .left 2 1).cells (copyRef Hb)).map (·.fields) ==
  some #[.ref 1, .ref 2]
#guard ((copy Hb 0 sharedPairObj .left 2 1).cells (copyRef Hb)).map (·.rc) == some 1
#guard ((copy Hb 0 sharedPairObj .left 2 1).cells (copyRef Hb)).map (·.persistent) ==
  some false

#print axioms Ownership.Pair.checkP_sound
#print axioms Ownership.Pair.copy_inv
#print axioms Ownership.Pair.copy_poststate
#print axioms unique_left_run
#print axioms unique_right_run
#print axioms shared_left_copy
#print axioms shared_right_copy

end OwnershipTest.PairBranchProof
