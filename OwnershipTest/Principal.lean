/-
The code-level instance of the nested principal guarantee.

`OwnershipLcnf.principal_supported_path` is parametric in the level list, the
level, the selected index, the call's scalars and the leaf body. This module
instantiates it at the recogniser's own layout on a reified transcription of the
captured `setAt._redArg` declaration, so the recognition premise is a
kernel-checked verdict on a concrete `Code` value.

The fixture is one level: the parent array at `ref 0` holds the child `ref 1` in
slot `0`, the leaf body checks the state it is handed and writes the value
parameter into it at the exposed path scalar, and the parent is at count one, so
the restoration takes the mutate branch. Every premise of the theorem is supplied
here — the layout, the operand identification, the initial machine/model
agreement, the level list's contract, the accounted entry, and the child call's
boundary at the counted protocol's heap — and the instance is closed: it has no
hypotheses.

The controls are ordered affirmative first: the positive child call and boundary
beside the retained-parent copy, where the restoration's disposition is
`.copy` and therefore the theorem's `.mutate` conjunct fails. These are heap and
checker calculations; they are not runtime or backend claims.
-/
import OwnershipLcnf.Principal

open Lean
open Lean.Compiler.LCNF
open Ownership

namespace OwnershipTest

/-! ## The reified captured declaration -/

/-- The private name the compiler gives a declaration's `_redArg` specialization. -/
def privateName (mod decl : Name) : Name := mkPrivateNameCore mod decl

/-- Expression placeholder for the fields the recognizer does not read. -/
def ty : Expr := .const ``Unit []

/-- A `stem.index` name, the form both the capture's printed names and the
compiler's `_uniq.N` names use. -/
def nm (stem : String) (idx : Nat) : Name := Name.mkNum (Name.str .anonymous stem) idx

/-- A binder identity: the compiler's `_uniq.N` name. -/
def u (idx : Nat) : FVarId := ⟨nm "_uniq" idx⟩

/-- A binder identity as a value argument. -/
def ua (idx : Nat) : Arg .impure := .fvar (u idx)

/-- A `let` binding: the `_uniq.N` identity, the capture's printed binder name,
and the bound value. -/
def uB (idx : Nat) (printed : Name) (v : LetValue .impure) : LetDecl .impure :=
  { fvarId := u idx, binderName := printed, type := ty, value := v }

/-- A join-point or function parameter: the `_uniq.N` identity and the
capture's printed binder name. -/
def uP (idx : Nat) (printed : Name) : Param .impure :=
  { fvarId := u idx, binderName := printed, type := ty, borrow := false }

/-- A constructor alternative's info: only the name is read. -/
def cinfo (n : Name) : CtorInfo := { name := n, cidx := 0, size := 0, usize := 0, ssize := 0 }

/-- The private name of the replayed `setAt._redArg`. -/
def setAtName : Name :=
  privateName `Scidonia.FracPerm.StateVar.Layout5 `Scidonia.FracPerm.StateVar.Layout5.setAt ++
    `_redArg

/-- The private name of the replayed `takeOut._redArg`. -/
def takeOutName : Name :=
  privateName `Scidonia.FracPerm.StateVar.Layout5 `Scidonia.FracPerm.StateVar.Layout5.takeOut ++
    `_redArg

/-- The captured `Path.here` alternative (binder identities `_uniq.1`–`_uniq.3`). -/
def hereAlt : Code .impure :=
  .dec (u 1) 1 false false (some 1) <|
  .dec (u 3) 1 true false none <|
  .inc (u 2) 1 true false <|
  .return (u 2)

/-- The captured `Path.left` alternative. -/
def leftAlt : Code .impure :=
  .let (uB 4 (nm "p" 4) (.oproj 2 (u 1))) <|
  .inc (u 4) 1 false false <|
  .dec (u 1) 1 false false (some 3) <|
  .let (uB 5 (nm "fst" 5) (.oproj 0 (u 3))) <|
  .let (uB 6 (nm "snd" 6) (.oproj 1 (u 3))) <|
  .jp (FunDecl.mk (u 13) (nm "resetjp" 7) #[uP 7 (nm "_x" 8), uP 8 (nm "isShared" 9)] ty <|
    .let (uB 9 (nm "_x" 10) (.fap setAtName #[ua 4, ua 2, ua 5])) <|
    .jp (FunDecl.mk (u 11) (nm "reusejp" 11) #[uP 10 (nm "_x" 12)] ty <|
      .return (u 10)) <|
    .cases (.mk `UInt8 ty (u 8) #[
      Alt.ctorAlt (cinfo `Bool.false) <|
        .oset (u 7) 0 (ua 9) <|
        .jmp (u 11) #[ua 7],
      Alt.ctorAlt (cinfo `Bool.true) <|
        .let (uB 12 (nm "reuseFailAlloc" 13) (.ctor (cinfo `Prod.mk) #[ua 9, ua 6])) <|
        .jmp (u 11) #[ua 12] ])) <|
  .let (uB 14 (nm "isSharedCheck" 14) (.isShared (u 3))) <|
  .cases (.mk `UInt8 ty (u 14) #[
    Alt.ctorAlt (cinfo `Bool.false) <| .jmp (u 13) #[ua 3, ua 14],
    Alt.ctorAlt (cinfo `Bool.true) <|
      .inc (u 6) 1 true false <|
      .inc (u 5) 1 true false <|
      .dec (u 3) 1 true false none <|
      .jmp (u 13) #[.erased, ua 14] ])

/-- The captured `Path.right` alternative. -/
def rightAlt : Code .impure :=
  .let (uB 15 (nm "p" 15) (.oproj 2 (u 1))) <|
  .inc (u 15) 1 false false <|
  .dec (u 1) 1 false false (some 3) <|
  .let (uB 16 (nm "fst" 16) (.oproj 0 (u 3))) <|
  .let (uB 17 (nm "snd" 17) (.oproj 1 (u 3))) <|
  .jp (FunDecl.mk (u 24) (nm "resetjp" 18) #[uP 18 (nm "_x" 19), uP 19 (nm "isShared" 20)] ty <|
    .let (uB 20 (nm "_x" 21) (.fap setAtName #[ua 15, ua 2, ua 17])) <|
    .jp (FunDecl.mk (u 22) (nm "reusejp" 22) #[uP 21 (nm "_x" 23)] ty <|
      .return (u 21)) <|
    .cases (.mk `UInt8 ty (u 19) #[
      Alt.ctorAlt (cinfo `Bool.false) <|
        .oset (u 18) 1 (ua 20) <|
        .jmp (u 22) #[ua 18],
      Alt.ctorAlt (cinfo `Bool.true) <|
        .let (uB 23 (nm "reuseFailAlloc" 24) (.ctor (cinfo `Prod.mk) #[ua 16, ua 20])) <|
        .jmp (u 22) #[ua 23] ])) <|
  .let (uB 25 (nm "isSharedCheck" 25) (.isShared (u 3))) <|
  .cases (.mk `UInt8 ty (u 25) #[
    Alt.ctorAlt (cinfo `Bool.false) <| .jmp (u 24) #[ua 3, ua 25],
    Alt.ctorAlt (cinfo `Bool.true) <|
      .inc (u 17) 1 true false <|
      .inc (u 16) 1 true false <|
      .dec (u 3) 1 true false none <|
      .jmp (u 24) #[.erased, ua 25] ])

/-- The captured `Path.index` alternative: the pre-bounds destructuring, the
bounds computation, the `Bool.false`/`Bool.true` alternatives in the captured
order, and the update tail through the put-back and the return. -/
def indexAlt : Code .impure :=
  .let (uB 26 (nm "a" 26) (.oproj 0 (u 1))) <|
  .inc (u 26) 1 false false <|
  .let (uB 27 (nm "i" 27) (.oproj 1 (u 1))) <|
  .inc (u 27) 1 true false <|
  .let (uB 28 (nm "p" 28) (.oproj 2 (u 1))) <|
  .inc (u 28) 1 false false <|
  .dec (u 1) 1 false false (some 3) <|
  .let (uB 29 (nm "_x" 29) (.fap `Array.size #[.erased, ua 3])) <|
  .let (uB 30 (nm "_x" 30) (.fap `Nat.decLt #[ua 27, ua 29])) <|
  .cases (.mk `UInt8 ty (u 30) #[
    Alt.ctorAlt (cinfo `Bool.false) <|
      .dec (u 28) 1 false false none <|
      .dec (u 27) 1 true false none <|
      .dec (u 26) 1 false false none <|
      .return (u 3),
    Alt.ctorAlt (cinfo `Bool.true) <|
      .let (uB 31 (nm "_x" 31) (.fap (setAtName ++ `_closed_0) #[])) <|
      .let (uB 32 (nm "_x" 32) (.fap
        `Scidonia.FracPerm.assertExclusiveArrayImpl._redArg #[ua 31, ua 3])) <|
      .let (uB 33 (nm "_x" 33) (.fap
        `Scidonia.FracPerm.StateVar.Layout5.stateDefault #[ua 26])) <|
      .let (uB 34 (nm "val" 34) (.fap takeOutName #[ua 32, ua 27, ua 33])) <|
      .let (uB 35 (nm "fst" 35) (.oproj 0 (u 34))) <|
      .inc (u 35) 1 true false <|
      .let (uB 36 (nm "snd" 36) (.oproj 1 (u 34))) <|
      .inc (u 36) 1 true false <|
      .dec (u 34) 1 false false none <|
      .let (uB 37 (nm "_x" 37) (.fap (setAtName ++ `_closed_1) #[])) <|
      .let (uB 38 (nm "_x" 38) (.fap
        `Scidonia.FracPerm.assertExclusiveImpl._redArg #[ua 37, ua 36])) <|
      .let (uB 39 (nm "_x" 39) (.fap setAtName #[ua 28, ua 2, ua 38])) <|
      .let (uB 40 (nm "xs'" 40) (.fap `Array.set #[.erased, ua 35, ua 27, ua 39, .erased])) <|
      .dec (u 27) 1 true false none <|
      .return (u 40) ])

/-- The reified captured declaration: the outer `cases` on the path. -/
def capturedDecl : Code .impure :=
  .cases (.mk `obj ty (u 1) #[
    Alt.ctorAlt (cinfo `Scidonia.FracPerm.StateVar.Layout5.Path.here) hereAlt,
    Alt.ctorAlt (cinfo `Scidonia.FracPerm.StateVar.Layout5.Path.left) leftAlt,
    Alt.ctorAlt (cinfo `Scidonia.FracPerm.StateVar.Layout5.Path.right) rightAlt,
    Alt.ctorAlt (cinfo `Scidonia.FracPerm.StateVar.Layout5.Path.index) indexAlt ])

/-- The prefix the recognizer reads from `capturedDecl`. -/
def capturedPrefix : OwnershipLcnf.NestedPrefix :=
  { node := u 1, array := u 3, value := u 2, childArray := u 26, index := u 27,
    path := u 28, sizeResult := u 29, bound := u 30, arraySite := u 31,
    arrayCheck := u 32, dflt := u 33, pair := u 34, parent := u 35,
    child := u 36, childSite := u 37, childCheck := u 38, recursive := u 39,
    restored := u 40, indexDec := u 27 }


/-- Two binder identities with the same name are the same binder: `FVarId`
carries only a name. -/
theorem fvarId_ext {a b : Lean.FVarId} (h : a.name = b.name) : a = b := by
  cases a with
  | mk na => cases b with | mk nb => simp_all

/-- A prefix's binder identities determine it. `NestedPrefix` has no
`DecidableEq`, so recognition is pinned field by field through the names. -/
theorem binderNames_injective {p q : OwnershipLcnf.NestedPrefix}
    (h : p.binderNames = q.binderNames) : p = q := by
  cases p with
  | mk pn pa pv pca pi pp ps pb pas pac pd pr par pch pcs pcc prec prest pid =>
    cases q with
    | mk qn qa qv qca qi qp qs qb qas qac qd qr qpar qch qcs qcc qrec qrest qid =>
      simp only [OwnershipLcnf.NestedPrefix.binderNames, List.cons.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
        h17, h18, h19, -⟩ := h
      rw [fvarId_ext h1, fvarId_ext h2, fvarId_ext h3, fvarId_ext h4,
        fvarId_ext h5, fvarId_ext h6, fvarId_ext h7, fvarId_ext h8,
        fvarId_ext h9, fvarId_ext h10, fvarId_ext h11, fvarId_ext h12,
        fvarId_ext h13, fvarId_ext h14, fvarId_ext h15, fvarId_ext h16,
        fvarId_ext h17, fvarId_ext h18, fvarId_ext h19]

/-- The recognizer accepts the reified captured declaration and reads exactly
`capturedPrefix`. This is the recognition premise of the instance. -/
theorem captured_hproj :
    OwnershipLcnf.projectNested setAtName takeOutName capturedDecl = some capturedPrefix := by
  have hbn : (OwnershipLcnf.projectNested setAtName takeOutName capturedDecl).map
      OwnershipLcnf.NestedPrefix.binderNames = some capturedPrefix.binderNames := by
    decide
  cases h : OwnershipLcnf.projectNested setAtName takeOutName capturedDecl with
  | none => rw [h] at hbn; simp at hbn
  | some p =>
      have hp : p.binderNames = capturedPrefix.binderNames := by
        rw [h] at hbn
        simpa using hbn
      simp [binderNames_injective hp]

/-- The recognition tie, as a kernel-checked proposition about the reified
declaration. -/
example : OwnershipLcnf.projectNested setAtName takeOutName capturedDecl =
    some capturedPrefix :=
  captured_hproj

/-! ## The layout and the operand identification -/

/-- The recognizer's slot assignment at the captured artifact's binders: the
model's variables take slots `0`–`7` and the auxiliary binders `8`–`17`.
`capturedPrefix.indexDec` is the index binder itself. -/
def assign (f : Lean.FVarId) : Ownership.Var :=
  if f.name = nm "_uniq" 3 then 0
  else if f.name = nm "_uniq" 27 then 1
  else if f.name = nm "_uniq" 2 then 2
  else if f.name = nm "_uniq" 35 then 3
  else if f.name = nm "_uniq" 36 then 4
  else if f.name = nm "_uniq" 28 then 5
  else if f.name = nm "_uniq" 39 then 6
  else if f.name = nm "_uniq" 40 then 7
  else if f.name = nm "_uniq" 1 then 8
  else if f.name = nm "_uniq" 26 then 9
  else if f.name = nm "_uniq" 29 then 10
  else if f.name = nm "_uniq" 30 then 11
  else if f.name = nm "_uniq" 31 then 12
  else if f.name = nm "_uniq" 32 then 13
  else if f.name = nm "_uniq" 33 then 14
  else if f.name = nm "_uniq" 34 then 15
  else if f.name = nm "_uniq" 37 then 16
  else if f.name = nm "_uniq" 38 then 17
  else 0

theorem layout : OwnershipLcnf.NestedLayout assign capturedPrefix := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    decide

/-! ## The heap -/

/-- The parent array: slot `0` holds the child at `ref 1`, the second slot is a
scalar; count one, non-persistent. -/
def parentObj : Ownership.Obj :=
  { fields := #[.ref 1, .scalar 0], rc := 1, persistent := false }

/-- The child state: two scalar slots; count one, non-persistent. -/
def childObj : Ownership.Obj :=
  { fields := #[.scalar 0, .scalar 0], rc := 1, persistent := false }

/-- The entry heap: the parent at `0`, the child at `1`, the fresh name `2`. -/
def H : Ownership.Heap :=
  { cells := fun r =>
      if r = 0 then some parentObj
      else if r = 1 then some childObj
      else none
    next := 2 }

/-- The child after the leaf body's write at the exposed path scalar. -/
def childAfter : Ownership.Obj :=
  { childObj with fields := childObj.fields.set! 1 (.scalar 7) }

/-- The counted protocol's boundary heap: the temporary pair is released and the
parent's selected slot holds the placeholder. -/
abbrev B : Ownership.Heap := (Ownership.CountedPair.protocol H 0 1 0).2

/-- The heap the child call leaves: the boundary with the child's slot written. -/
def Hout : Ownership.Heap := B.set 1 childAfter

-- the two shape guards: the boundary's parent cell and its cursor
example : Hout = B.set 1 childAfter := rfl
example : Hout.cells 0 = some (Ownership.PutBack.parentAfter parentObj 0) := rfl
example : Hout.next = 3 := rfl

theorem H_cells_zero : H.cells 0 = some parentObj := rfl

theorem H_cells_one : H.cells 1 = some childObj := rfl

theorem H_cells_other {r : Ownership.Ref} (h0 : r ≠ 0) (h1 : r ≠ 1) :
    H.cells r = none := by
  simp [H, h0, h1]

theorem H_rc_zero : H.rc 0 = 1 := by
  rw [Ownership.Heap.rc, H_cells_zero]
  rfl

theorem H_rc_one : H.rc 1 = 1 := by
  rw [Ownership.Heap.rc, H_cells_one]
  rfl

/-! ## The level, the call's scalars and the leaf body -/

/-- The level: the parent array at `ref 0`, its slot `0` holding the child at
`ref 1`, extracted through `3`/`4` and restored through `6`/`7`. -/
def l : Ownership.Path.Level :=
  { arr := 0, obj := parentObj, idx := 0, child := 1
    arrayVar := 0, indexVar := 1, parentVar := 3, childVar := 4
    resultVar := 6, restoredVar := 7 }

/-- The call's path scalar. -/
def pathVar : Ownership.Var := 5

/-- The call's value scalar. -/
def valueVar : Ownership.Var := 2

/-- The leaf body: check the state it was handed and write the value parameter
into it at the exposed path scalar. -/
def body : Ownership.Nested.NCode := .base (.setArr 4 5 2 (.ret 4))

theorem levelMatch :
    OwnershipLcnf.LevelMatch assign capturedPrefix l pathVar valueVar 0 parentObj 0 1 :=
  ⟨layout.array.symm, layout.index.symm, layout.parent.symm, layout.child.symm,
    layout.recursive.symm, layout.restored.symm, layout.path.symm, layout.value.symm,
    rfl, rfl, rfl, rfl⟩

/-! ## The counted boundary's cells and counts -/

/-- The protocol's first component: the boundary heap's fresh-name cursor. -/
abbrev Bfst : Ownership.Ref := (Ownership.CountedPair.protocol H 0 1 0).1

theorem protocol_boundary_facts :
    Bfst = H.next ∧
      B.cells 0 = some (Ownership.PutBack.parentAfter parentObj 0) ∧
      B.cells 1 = some childObj ∧
      B.cells Bfst = none ∧
      B.rc 0 = 1 ∧ B.rc 1 = 1 := by
  have hb := Ownership.CountedPair.protocol_boundary (H := H) (p := 0) (c := 1) (i := 0)
    (op := parentObj) (oc := childObj) (by rfl) (by rfl) (by decide) (by decide) (by decide)
  obtain ⟨hnext, hcell0, hcell1, hpair, hrc0, hrc1, -, -⟩ := hb
  exact ⟨hnext, hcell0, hcell1, hpair, hrc0, hrc1⟩

theorem B_cells_zero : B.cells 0 =
    some (Ownership.PutBack.parentAfter parentObj 0) := protocol_boundary_facts.2.1

theorem B_cells_one : B.cells 1 = some childObj := protocol_boundary_facts.2.2.1

theorem B_rc_zero : B.rc 0 = 1 := protocol_boundary_facts.2.2.2.2.1

theorem B_rc_one : B.rc 1 = 1 := protocol_boundary_facts.2.2.2.2.2

/-- Every other cell is empty: the pair cell is erased and every other cell is
the entry's. -/
theorem B_cells_other {r : Ownership.Ref} (h0 : r ≠ 0) (h1 : r ≠ 1) :
    B.cells r = none := by
  by_cases h2 : r = 2
  · subst h2
    have hpair := protocol_boundary_facts.2.2.2.1
    have hb : Bfst = 2 := by decide
    rw [hb] at hpair
    exact hpair
  · have htraffic : B =
        Ownership.CountedPair.pairFree
          (Ownership.CountedPair.pairInc (Ownership.CountedPair.takeOut H 0 1 0).2 0 1)
          0 1 2 := by
      show Ownership.CountedPair.pairTraffic (Ownership.CountedPair.takeOut H 0 1 0).2 2 = _
      exact Ownership.CountedPair.pairTraffic_takeOut (H := H) (p := 0) (c := 1) (i := 0)
        (by decide) (by decide)
    rw [htraffic, Ownership.CountedPair.pairFree_inc_cells_other h0 h1 h2]
    show (Ownership.CountedPair.setPlaceholder
      (Ownership.CountedPair.allocPair H 0 1) 0 0).cells r = none
    rw [Ownership.CountedPair.setPlaceholder_cells_other h0,
      Ownership.CountedPair.allocPair_cells_other h2, H_cells_other h0 h1]

/-- The protocol traffic is neutral for every reference: the boundary's stored
count is the entry's. -/
theorem B_rc_eq (r : Ownership.Ref) : B.rc r = H.rc r := by
  by_cases h0 : r = 0
  · subst h0; rw [B_rc_zero, H_rc_zero]
  · by_cases h1 : r = 1
    · subst h1; rw [B_rc_one, H_rc_one]
    · rw [Ownership.Heap.rc, B_cells_other h0 h1, Ownership.Heap.rc, H_cells_other h0 h1]

/-! ## The child's mutable footprint -/

/-- The child's mutable footprint is the child alone: its slots are scalars. -/
theorem child_footprint {Ht : Ownership.Heap} {q : Ownership.Ref}
    (h1 : Ht.cells 1 = some childObj)
    (h : Ownership.Entry.MutableFootprint Ht 1 q) : q = 1 := by
  induction h with
  | root _ _ => rfl
  | step hr hcell hpers hmem hcell' hpers' ih =>
      rw [ih] at hcell
      rw [h1] at hcell
      have ho : childObj = _ := Option.some.inj hcell
      subst ho
      simp [Ownership.Entry.fieldRefs, Ownership.Entry.refsOf, childObj] at hmem

theorem H_cells_child_blank :
    (Ownership.Path.blankLevel H l).cells 1 = some childObj := by
  simp [Ownership.Path.blankLevel, l, H, Ownership.Heap.set]

theorem child_separated : ¬ Ownership.Entry.MutableFootprint B 1 0 := by
  intro h
  have hq := child_footprint (Ht := B) B_cells_one h
  simp_all

theorem child_separated_entry : ¬ Ownership.Entry.MutableFootprint H 1 0 := by
  intro h
  have hq := child_footprint (Ht := H) H_cells_one h
  simp_all

theorem child_separated_blank : ¬ Ownership.Entry.MutableFootprint
    (Ownership.Path.blankLevel H l) 1 0 := by
  intro h
  have hq := child_footprint (Ht := Ownership.Path.blankLevel H l) H_cells_child_blank h
  simp_all

/-! ## The entry's accounting -/

/-- The caller's environment: the array handle at `0`, the selected index at
`1`, the replacement value at `2` and the call's path scalar at `5`. -/
def entryEnv : Ownership.Env :=
  fun x =>
    if x = 0 then some (.ref 0)
    else if x = 1 then some (.scalar 0)
    else if x = 2 then some (.scalar 7)
    else if x = 5 then some (.scalar 1)
    else none

/-- The caller's context: the array handle owned at count one, the scalars, and
everything else dead. -/
def entryCtx : Ownership.Ctx :=
  { us := fun x =>
      if x = 0 then .owned
      else if x = 1 then .scalar
      else if x = 2 then .scalar
      else if x = 5 then .scalar
      else .dead
    refOf := fun x => if x = 0 then some 0 else none
    mult := H.rc }

theorem entryCtx_us_owned {x : Ownership.Var} (hx : entryCtx.us x = .owned) : x = 0 := by
  by_cases h0 : x = 0
  · exact h0
  · by_cases h1 : x = 1
    · subst h1; simp [entryCtx] at hx
    · by_cases h2 : x = 2
      · subst h2; simp [entryCtx] at hx
      · by_cases h5 : x = 5
        · subst h5; simp [entryCtx] at hx
        · simp [entryCtx, h0, h1, h2, h5] at hx

theorem entryInv : Ownership.Inv H entryEnv entryCtx where
  rc_eq r := rfl
  owned := by
    intro x r hx hr
    have hx0 : x = 0 := entryCtx_us_owned hx
    subst hx0
    have hr0 : (0 : Ownership.Ref) = r := Option.some.inj (by simpa [entryCtx] using hr)
    subst hr0
    exact ⟨by simp [entryEnv], by show 1 ≤ H.rc 0; rw [H_rc_zero]; decide⟩
  borrow := by
    intro x r hx _
    by_cases h0 : x = 0
    · subst h0; simp [entryCtx] at hx
    · by_cases h1 : x = 1
      · subst h1; simp [entryCtx, h0] at hx
      · by_cases h2 : x = 2
        · subst h2; simp [entryCtx, h0, h1] at hx
        · by_cases h5 : x = 5
          · subst h5; simp [entryCtx, h0, h1, h2] at hx
          · simp [entryCtx, h0, h1, h2, h5] at hx
  scalar := by
    intro x hx
    by_cases h0 : x = 0
    · subst h0; simp [entryCtx] at hx
    · by_cases h1 : x = 1
      · subst h1; exact ⟨0, by simp [entryEnv]⟩
      · by_cases h2 : x = 2
        · subst h2; exact ⟨7, by simp [entryEnv]⟩
        · by_cases h5 : x = 5
          · subst h5; exact ⟨1, by simp [entryEnv]⟩
          · simp [entryCtx, h0, h1, h2, h5] at hx
  nonPersistent := by
    intro r o hc
    by_cases h0 : r = 0
    · subst h0; rw [H_cells_zero] at hc; injection hc with h; subst h; rfl
    · by_cases h1 : r = 1
      · subst h1; rw [H_cells_one] at hc; injection hc with h; subst h; rfl
      · rw [H_cells_other h0 h1] at hc; exact absurd hc (by simp)

theorem envOwner_zero : Ownership.EnvOwnerCount entryCtx [0] 0 = 1 := by
  simp [Ownership.EnvOwnerCount, entryCtx]

theorem envOwner_one : Ownership.EnvOwnerCount entryCtx [0] 1 = 0 := by
  simp [Ownership.EnvOwnerCount, entryCtx]

theorem envOwner_other {r : Ownership.Ref} (h0 : r ≠ 0) :
    Ownership.EnvOwnerCount entryCtx [0] r = 0 := by
  simp [Ownership.EnvOwnerCount, entryCtx]
  exact fun hh => h0 hh.symm

theorem incoming_H_zero : Ownership.IncomingCount H 0 = 0 := by
  rw [Ownership.IncomingCount_eq_edges]
  decide

theorem incoming_H_one : Ownership.IncomingCount H 1 = 1 := by
  rw [Ownership.IncomingCount_eq_edges]
  decide

theorem incoming_H_other {r : Ownership.Ref} (h1 : r ≠ 1) :
    Ownership.IncomingCount H r = 0 := by
  rw [Ownership.IncomingCount_eq_edges]
  have hparent : Ownership.RefCount parentObj.fields r = 0 := by
    unfold Ownership.RefCount
    rw [show parentObj.fields.toList = [.ref 1, .scalar 0] from rfl]
    simp [Ownership.Val.ref.injEq]
    exact fun hh => h1 hh.symm
  have hchild : Ownership.RefCount childObj.fields r = 0 := by
    unfold Ownership.RefCount
    rw [show childObj.fields.toList = [.scalar 0, .scalar 0] from rfl]
    simp
  simp [List.range_succ, Ownership.EdgeAt, H, hparent, hchild]

theorem entryAccounted : Ownership.Accounted [0] H entryEnv entryCtx := by
  refine
    { inv := entryInv
      support_nodup := List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩
      support_sound := ?_
      support_complete := ?_
      support_bound := ?_
      domain := ?_
      count := ?_ }
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    simp [entryCtx]
  · intro x hx
    simp only [List.mem_singleton]
    exact entryCtx_us_owned hx
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    exact ⟨0, by simp [entryCtx]⟩
  · intro r o hc
    by_cases h0 : r = 0
    · subst h0; decide
    · by_cases h1 : r = 1
      · subst h1; decide
      · rw [H_cells_other h0 h1] at hc; exact absurd hc (by simp)
  · intro r
    by_cases h0 : r = 0
    · subst h0
      rw [H_rc_zero, incoming_H_zero, envOwner_zero]
    · by_cases h1 : r = 1
      · subst h1
        rw [H_rc_one, incoming_H_one, envOwner_one]
      · have hz : H.rc r = 0 := by
          rw [Ownership.Heap.rc, H_cells_other h0 h1]
          rfl
        rw [hz, incoming_H_other h1, envOwner_other h0]

/-! ## The machine and its agreement -/

/-- The fragment's starting machine: the entry heap, the array handle, the value
operand, the reified node index, the call's path scalar, the model's child
variable and the empty write trace. -/
def machine : OwnershipLcnf.NestedMachine :=
  { heap := H
    env := fun x =>
      if x = 0 then some (.ref 0)
      else if x = 2 then some (.scalar 7)
      else none
    nodes := fun _ => { index := .scalar 0 }
    callPath := 1
    childVar := 4
    pairs := fun _ => none
    writes := [] }

theorem agrees :
    OwnershipLcnf.NestedAgrees assign capturedPrefix machine entryEnv H 0 0 7 1 :=
  ⟨rfl, by decide, by decide, by decide, by decide, by decide, by decide, rfl,
    by decide, rfl, rfl⟩

/-! ## The level list's contract -/

/-- The leaf body's checker context. -/
abbrev cb : Ownership.Ctx :=
  Ownership.PathConsolidation.bodyCtx pathVar valueVar entryCtx l

theorem slots : Ownership.Path.Slots H [l] := by
  intro m hm
  simp only [List.mem_singleton] at hm
  subst hm
  exact ⟨rfl, rfl, rfl⟩

theorem chained : Ownership.Path.Chained [l] := trivial

theorem distinct : Ownership.Path.DistinctArrays [l] :=
  ⟨by intro m hm; simp at hm, trivial⟩

theorem levelEnv : Ownership.Path.LevelEnv pathVar valueVar entryEnv l :=
  ⟨rfl, rfl, ⟨1, rfl⟩, ⟨7, rfl⟩, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩

theorem envok : Ownership.Path.EnvOK pathVar valueVar entryEnv [l] :=
  ⟨levelEnv, trivial⟩

theorem vars : Ownership.PathConsolidation.Vars pathVar valueVar l := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem levelCtx : Ownership.PathConsolidation.LevelCtx pathVar valueVar entryCtx l :=
  ⟨vars, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩

theorem acyclic : Ownership.PathConsolidation.Acyclic 1 H [l] :=
  ⟨child_separated_blank, child_separated_entry, trivial⟩

theorem live : Ownership.Path.Live H 1 := ⟨childObj, H_cells_one, rfl⟩

theorem checkBody :
    Ownership.Nested.checkNF cb [] body = some cb := by
  simp [body, cb, l, pathVar, valueVar, Ownership.Nested.checkNF, Ownership.check,
    Ownership.PathConsolidation.bodyCtx, Ownership.PathConsolidation.takeCtx,
    Ownership.Nested.isolatedCtx, Ownership.Ctx.multOf, entryCtx, H_rc_one]

theorem retOwned : cb.us 4 = .owned := by
  simp [cb, l, pathVar, valueVar, Ownership.PathConsolidation.bodyCtx,
    Ownership.PathConsolidation.takeCtx, Ownership.Nested.isolatedCtx]

theorem retRef : cb.refOf 4 = some 1 := by
  simp [cb, l, pathVar, valueVar, Ownership.PathConsolidation.bodyCtx,
    Ownership.PathConsolidation.takeCtx, Ownership.Nested.isolatedCtx]

theorem hpath :
    OwnershipLcnf.PathContract pathVar valueVar body 1 l [] H entryEnv entryCtx cb 4 :=
  { slots := slots
    chained := chained
    distinct := distinct
    envok := envok
    leaf := trivial
    levelCtx := levelCtx
    shapes := trivial
    counts := trivial
    acyclic := acyclic
    live := live
    annot := trivial
    checkBody := checkBody
    retBody := rfl
    retOwned := retOwned
    retRef := retRef
    endsAt := rfl
    countFree := rfl
    inv := entryInv }

/-! ## The boundary's accounting -/

/-- The caller's boundary environment: the extracted parent and child handles. -/
abbrev env1 : Ownership.Env := (entryEnv.set 3 (.ref 0)).set 4 (.ref 1)

/-- The caller's boundary context: the checker's take-out rule's context. -/
abbrev ctx1 : Ownership.Ctx := (entryCtx.move 0 3).bindOwned 4 1

theorem boundaryAccounted : Ownership.Accounted [4, 3] B env1 ctx1 := by
  have h := Ownership.counted_takeOut (h := entryAccounted) (a := 0) (fst := 3) (snd := 4)
    (e := 1) (r := 0) (o := parentObj) (idx := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rfl) (by rfl)
  simpa [env1, ctx1, Ownership.replaceVar] using h.1

theorem calledAccounted : Ownership.Accounted [4, 3] Hout env1 ctx1 := by
  have h := Ownership.Accounted.setFieldsScalar (h := boundaryAccounted)
    (r := 1) (o := childObj) (idx := 1) (old := 0) (w := 7)
    B_cells_one (by decide)
  simpa [Hout, childAfter, Ownership.Heap.set, Array.set!] using h

/-- The call's edge effect at the boundary: the leaf's write replaces a scalar
slot with a scalar, so no `.ref` occurrence at any name changes. -/
theorem B_edges : Ownership.EdgePreserved B Hout :=
  Ownership.EdgePreserved.set (H := B) (r := 1) (o := childObj) (o' := childAfter)
    B_cells_one
    (fun q => by
      simpa [childAfter] using
        (Ownership.RefCount_set_scalar_scalar (fields := childObj.fields) (i := 1)
          (old := 0) (w := 7) (q := q) (by decide)).symm)

/-! ## The child call -/

theorem bodyCountFree : Ownership.Nested.CountFree body = true := rfl

theorem bodyRetVar : Ownership.Nested.retVar body = some 4 := rfl

theorem callChecked : ∃ cb,
    Ownership.Nested.checkNF (Ownership.Nested.isolatedCtx ctx1 4 5 2 1) [] body = some cb ∧
      ∃ y, Ownership.Nested.retVar body = some y ∧ cb.us y = .owned ∧
        cb.refOf y = some 1 := by
  refine ⟨Ownership.Nested.isolatedCtx ctx1 4 5 2 1, ?_, 4, rfl, ?_, ?_⟩
  · simp [body, Ownership.Nested.checkNF, Ownership.check, ctx1,
      Ownership.Nested.isolatedCtx, Ownership.Ctx.multOf]
    show H.rc 1 = 1
    rw [H_rc_one]
  · simp [Ownership.Nested.isolatedCtx]
  · simp [Ownership.Nested.isolatedCtx]

theorem callInv :
    Ownership.Inv B (Ownership.Nested.isolateEnv env1 4 5 2)
      (Ownership.Nested.isolatedCtx ctx1 4 5 2 1) where
  rc_eq r := by
    show B.rc r = ctx1.mult r
    rw [B_rc_eq]
    rfl
  owned := by
    intro x r hx hr
    by_cases h4 : x = 4
    · subst h4
      have hr1 : r = 1 := Option.some.inj (by
        simpa [Ownership.Nested.isolatedCtx] using hr.symm)
      subst hr1
      refine ⟨by simp [Ownership.Nested.isolateEnv, env1], ?_⟩
      show 1 ≤ H.rc 1
      rw [H_rc_one]
      decide
    · by_cases h5 : x = 5
      · subst h5; simp [Ownership.Nested.isolatedCtx, h4] at hx
      · by_cases h2 : x = 2
        · subst h2; simp [Ownership.Nested.isolatedCtx, h4, h5] at hx
        · simp [Ownership.Nested.isolatedCtx, h4, h5, h2] at hx
  borrow := by
    intro x r hx _
    by_cases h4 : x = 4
    · subst h4; simp [Ownership.Nested.isolatedCtx] at hx
    · by_cases h5 : x = 5
      · subst h5; simp [Ownership.Nested.isolatedCtx, h4] at hx
      · by_cases h2 : x = 2
        · subst h2; simp [Ownership.Nested.isolatedCtx, h4, h5] at hx
        · simp [Ownership.Nested.isolatedCtx, h4, h5, h2] at hx
  scalar := by
    intro x hx
    by_cases h4 : x = 4
    · subst h4; simp [Ownership.Nested.isolatedCtx] at hx
    · by_cases h5 : x = 5
      · subst h5
        exact ⟨1, by simp [Ownership.Nested.isolateEnv, env1, entryEnv]⟩
      · by_cases h2 : x = 2
        · subst h2
          exact ⟨7, by simp [Ownership.Nested.isolateEnv, env1, entryEnv]⟩
        · simp [Ownership.Nested.isolatedCtx, h4, h5, h2] at hx
  nonPersistent := by
    intro r o hc
    by_cases h0 : r = 0
    · subst h0; rw [B_cells_zero] at hc; injection hc with h; subst h; rfl
    · by_cases h1 : r = 1
      · subst h1; rw [B_cells_one] at hc; injection hc with h; subst h; rfl
      · rw [B_cells_other h0 h1] at hc; exact absurd hc (by simp)

theorem callRuns :
    Ownership.Nested.runN body (Ownership.Nested.isolateEnv env1 4 5 2) B =
      .done Hout ((Ownership.Nested.isolateEnv env1 4 5 2).set 4 (.ref 1))
        (.ref 1) [(1, true)] := by
  have hcell : B.cells 1 = some childObj := B_cells_one
  have hex : B.exclusive? 1 = true :=
    (Ownership.Heap.exclusive?_eq_true).mpr ⟨childObj, hcell, rfl, rfl⟩
  have h4 : Ownership.Nested.isolateEnv env1 4 5 2 4 = some (.ref 1) := by
    simp [Ownership.Nested.isolateEnv, env1]
  have h5 : Ownership.Nested.isolateEnv env1 4 5 2 5 = some (.scalar 1) := by
    simp [Ownership.Nested.isolateEnv, env1, entryEnv]
  have h2 : Ownership.Nested.isolateEnv env1 4 5 2 2 = some (.scalar 7) := by
    simp [Ownership.Nested.isolateEnv, env1, entryEnv]
  simp only [body, Ownership.Nested.runN, Ownership.run, h4, h5, h2]
  rw [hcell]
  simp [hex, Hout, childAfter, Ownership.Res.addWrite, Array.set!]

theorem callChildRc : Hout.rc 1 = B.rc 1 := by
  rw [Hout, Ownership.Heap.rc, Ownership.Heap.set_self]
  rw [B_rc_one]
  rfl

theorem callChildPersistent : Hout.isPersistent 1 = B.isPersistent 1 := by
  rw [Hout, Ownership.Heap.isPersistent, Ownership.Heap.set_self,
    Ownership.Heap.isPersistent, B_cells_one]
  rfl

theorem childCall :
    Ownership.PutBack.ChildCall B Hout env1 ctx1 4 5 2 body 0 1 where
  admitted := bodyCountFree
  checked := callChecked
  inv := callInv
  annotations := trivial
  extraction := trivial
  separated := child_separated
  outcome := ⟨_, [(1, true)], callRuns⟩
  child_rc := callChildRc
  child_persistent := callChildPersistent

/-- The counted child-call contract: the boundary's call and the call's edge
effect. This is the instance's `hcall`. -/
theorem countedCall :
    Ownership.CountedChildCall B Hout env1 ctx1 4 5 2 body 0 1 [4, 3] where
  call := childCall
  edges := B_edges

/-- The caller's accounting at the body's return, derived from the boundary
accounting and the call's edge effect; its type is `calledAccounted`'s. -/
theorem countedCall_accounted : Ownership.Accounted [4, 3] Hout env1 ctx1 :=
  countedCall.accounted_of boundaryAccounted

/-! ## The controls -/

/-- A parent at count two is not exclusive, so the restoration copies and the
theorem's `.mutate` disposition fails at that heap. The affirmative control is
`countedCall` and the boundary facts above. -/
theorem retained_parent_copies :
    Ownership.PutBack.disposition? (H.inc 0 1) 0 0 = some .copy ∧
      (Ownership.PutBack.copy (H.inc 0 1) 0 { parentObj with rc := 2 } 0 1).1 = 2 ∧
      (Ownership.PutBack.copy (H.inc 0 1) 0 { parentObj with rc := 2 } 0 1).2.cells 1 =
        some childObj := by
  have hcell : (H.inc 0 1).cells 0 = some { parentObj with rc := 2 } :=
    Ownership.CountedPair.inc_cells_self (H := H) (r := 0) (n := 1) (o := parentObj)
      H_cells_zero
  have hnext : (H.inc 0 1).next = 2 := by
    rw [Ownership.PutBack.inc_next]
    rfl
  obtain ⟨hdisp, -, hfresh, -, -⟩ :=
    Ownership.PutBack.shared_parent_copies (H := H.inc 0 1) (p := 0) (c := 1) (i := 0)
      (o := { parentObj with rc := 2 }) hcell (by decide) rfl (by rw [hnext]; decide)
  refine ⟨hdisp, ?_, ?_⟩
  · rw [hfresh, hnext]
  · obtain ⟨-, -, -, hother, -, -⟩ :=
      Ownership.PutBack.copy_result (H := H.inc 0 1) (p := 0) (c := 1) (i := 0)
        (o := { parentObj with rc := 2 }) hcell (by rw [hnext]; decide)
    rw [hother 1 (by decide) (by rw [hnext]; decide)]
    exact H_cells_one

/-- The retained parent at count two does not take the theorem's mutate branch. -/
theorem retained_parent_not_mutate :
    Ownership.PutBack.disposition? (H.inc 0 1) 0 0 ≠ some .mutate := by
  rw [retained_parent_copies.1]
  decide

/-! ## The instance -/

/-- The closed instance: every premise of `principal_supported_path` is supplied
at the recogniser's layout, so the conclusion has no hypotheses. -/
theorem principal_instance :
    ∃ Hm envm ws Hf,
      OwnershipLcnf.NestedOutcome.ofExec assign capturedPrefix
          (OwnershipLcnf.execNestedAST setAtName takeOutName assign body
            capturedPrefix capturedDecl machine) =
        some (OwnershipLcnf.NestedOutcome.ofModel
          (Ownership.Nested.runN (Ownership.Path.build pathVar valueVar body [l])
            entryEnv H)) ∧
      Ownership.Nested.runN (Ownership.Path.build pathVar valueVar body [l]) entryEnv H =
        .done Hm envm (.ref 0) ws ∧
      (∀ w ∈ ws, w.2 = true) ∧
      Ownership.Accounted [4, 3] B env1 ctx1 ∧
      Ownership.HeapCompat B (Ownership.Path.blankLevel H l) ∧
      B.cells H.next = none ∧
      B.next = H.next + 1 ∧
      Ownership.Heap.Exclusive B 0 ∧
      Ownership.Heap.Exclusive B 1 ∧
      Ownership.PutBack.disposition? Hout 0 0 = some .mutate ∧
      Ownership.PutBack.putBack Hout 0 0 1 = some (0, Hf) ∧
      Hf = Ownership.PutBack.mutate Hout 0 (Ownership.PutBack.parentAfter parentObj 0) 0 1 ∧
      ((Ownership.PutBack.parentAfter parentObj 0).fields.setIfInBounds 0 (.ref 1))[0]? =
        some (.ref 1) ∧
      Ownership.Accounted
        ((Ownership.replaceVar
            (Ownership.replaceVar (4 :: Ownership.replaceVar [0] 0 3) 4 6) 3 7).erase 6)
        Hf
        ((((entryEnv.set 3 (.ref 0)).set 4 (.ref 1)).set 6 (.ref 1)).set 7 (.ref 0))
        (((((entryCtx.move 0 3).bindOwned 4 1).move 4 6).move 3 7).setUs 6 .dead) ∧
      Ownership.HeapCompat Hf Hm ∧
      (OwnershipLcnf.execCounted assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.heap =
        (Ownership.CountedPair.protocol machine.heap 0 1 0).2 ∧
      Ownership.HeapCompat
        (OwnershipLcnf.execCounted assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.heap
        (machine.heap.set 0 { parentObj with
          fields := parentObj.fields.setIfInBounds 0 (.scalar 0) }) ∧
      (OwnershipLcnf.execCounted assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.env =
        (OwnershipLcnf.execNested assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.env ∧
      (OwnershipLcnf.execCounted assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.nodes =
        (OwnershipLcnf.execNested assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.nodes ∧
      (OwnershipLcnf.execCounted assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.pairs =
        (OwnershipLcnf.execNested assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.pairs ∧
      (OwnershipLcnf.execCounted assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.callPath =
        (OwnershipLcnf.execNested assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.callPath ∧
      (OwnershipLcnf.execCounted assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.childVar =
        (OwnershipLcnf.execNested assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.childVar ∧
      (OwnershipLcnf.execCounted assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.writes =
        (OwnershipLcnf.execNested assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.writes ∧
      (∀ q, ¬ Ownership.Entry.MutableFootprint B 1 q →
        Hout.cells q = B.cells q) ∧
      (∀ q, q ≠ 0 → Hf.cells q = Hout.cells q) :=
  OwnershipLcnf.principal_supported_path setAtName takeOutName captured_hproj layout
    pathVar valueVar body [] l machine entryEnv H 0 parentObj 0 7 1 1 levelMatch agrees
    entryCtx 1 cb 4 hpath entryAccounted countedCall

/-! ## The conjuncts, type-ascribed -/

/-- Each conjunct of the instance's conclusion, at its exact type. A conjunct
weakened in the theorem would no longer be an inhabitant of the ascribed type. -/
theorem instance_conjuncts :
    ∃ Hm envm ws Hf,
      OwnershipLcnf.NestedOutcome.ofExec assign capturedPrefix
          (OwnershipLcnf.execNestedAST setAtName takeOutName assign body
            capturedPrefix capturedDecl machine) =
        some (OwnershipLcnf.NestedOutcome.ofModel
          (Ownership.Nested.runN (Ownership.Path.build pathVar valueVar body [l])
            entryEnv H)) ∧
      Ownership.Nested.runN (Ownership.Path.build pathVar valueVar body [l]) entryEnv H =
        .done Hm envm (.ref 0) ws ∧
      (∀ w ∈ ws, w.2 = true) ∧
      Ownership.Accounted [4, 3] B env1 ctx1 ∧
      Ownership.HeapCompat B (Ownership.Path.blankLevel H l) ∧
      B.cells H.next = none ∧
      B.next = H.next + 1 ∧
      Ownership.Heap.Exclusive B 0 ∧
      Ownership.Heap.Exclusive B 1 ∧
      Ownership.PutBack.disposition? Hout 0 0 = some .mutate ∧
      Ownership.PutBack.putBack Hout 0 0 1 = some (0, Hf) ∧
      Hf = Ownership.PutBack.mutate Hout 0 (Ownership.PutBack.parentAfter parentObj 0) 0 1 ∧
      ((Ownership.PutBack.parentAfter parentObj 0).fields.setIfInBounds 0 (.ref 1))[0]? =
        some (.ref 1) ∧
      Ownership.Accounted
        ((Ownership.replaceVar
            (Ownership.replaceVar (4 :: Ownership.replaceVar [0] 0 3) 4 6) 3 7).erase 6)
        Hf
        ((((entryEnv.set 3 (.ref 0)).set 4 (.ref 1)).set 6 (.ref 1)).set 7 (.ref 0))
        (((((entryCtx.move 0 3).bindOwned 4 1).move 4 6).move 3 7).setUs 6 .dead) ∧
      Ownership.HeapCompat Hf Hm ∧
      (OwnershipLcnf.execCounted assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.heap =
        (Ownership.CountedPair.protocol machine.heap 0 1 0).2 ∧
      Ownership.HeapCompat
        (OwnershipLcnf.execCounted assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.heap
        (machine.heap.set 0 { parentObj with
          fields := parentObj.fields.setIfInBounds 0 (.scalar 0) }) ∧
      (OwnershipLcnf.execCounted assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.env =
        (OwnershipLcnf.execNested assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.env ∧
      (OwnershipLcnf.execCounted assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.nodes =
        (OwnershipLcnf.execNested assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.nodes ∧
      (OwnershipLcnf.execCounted assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.pairs =
        (OwnershipLcnf.execNested assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.pairs ∧
      (OwnershipLcnf.execCounted assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.callPath =
        (OwnershipLcnf.execNested assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.callPath ∧
      (OwnershipLcnf.execCounted assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.childVar =
        (OwnershipLcnf.execNested assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.childVar ∧
      (OwnershipLcnf.execCounted assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.writes =
        (OwnershipLcnf.execNested assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.writes ∧
      (∀ q, ¬ Ownership.Entry.MutableFootprint B 1 q →
        Hout.cells q = B.cells q) ∧
      (∀ q, q ≠ 0 → Hf.cells q = Hout.cells q) :=
  principal_instance

/-- The same proposition as the instance's own type, destructured conjunct by
conjunct: `obtain` names every conjunct and the assembly re-checks each against
the ascription above, so a conjunct weakened in the theorem fails here. -/
example : (∃ Hm envm ws Hf,
      OwnershipLcnf.NestedOutcome.ofExec assign capturedPrefix
          (OwnershipLcnf.execNestedAST setAtName takeOutName assign body
            capturedPrefix capturedDecl machine) =
        some (OwnershipLcnf.NestedOutcome.ofModel
          (Ownership.Nested.runN (Ownership.Path.build pathVar valueVar body [l])
            entryEnv H)) ∧
      Ownership.Nested.runN (Ownership.Path.build pathVar valueVar body [l]) entryEnv H =
        .done Hm envm (.ref 0) ws ∧
      (∀ w ∈ ws, w.2 = true) ∧
      Ownership.Accounted [4, 3] B env1 ctx1 ∧
      Ownership.HeapCompat B (Ownership.Path.blankLevel H l) ∧
      B.cells H.next = none ∧
      B.next = H.next + 1 ∧
      Ownership.Heap.Exclusive B 0 ∧
      Ownership.Heap.Exclusive B 1 ∧
      Ownership.PutBack.disposition? Hout 0 0 = some .mutate ∧
      Ownership.PutBack.putBack Hout 0 0 1 = some (0, Hf) ∧
      Hf = Ownership.PutBack.mutate Hout 0 (Ownership.PutBack.parentAfter parentObj 0) 0 1 ∧
      ((Ownership.PutBack.parentAfter parentObj 0).fields.setIfInBounds 0 (.ref 1))[0]? =
        some (.ref 1) ∧
      Ownership.Accounted
        ((Ownership.replaceVar
            (Ownership.replaceVar (4 :: Ownership.replaceVar [0] 0 3) 4 6) 3 7).erase 6)
        Hf
        ((((entryEnv.set 3 (.ref 0)).set 4 (.ref 1)).set 6 (.ref 1)).set 7 (.ref 0))
        (((((entryCtx.move 0 3).bindOwned 4 1).move 4 6).move 3 7).setUs 6 .dead) ∧
      Ownership.HeapCompat Hf Hm ∧
      (OwnershipLcnf.execCounted assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.heap =
        (Ownership.CountedPair.protocol machine.heap 0 1 0).2 ∧
      Ownership.HeapCompat
        (OwnershipLcnf.execCounted assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.heap
        (machine.heap.set 0 { parentObj with
          fields := parentObj.fields.setIfInBounds 0 (.scalar 0) }) ∧
      (OwnershipLcnf.execCounted assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.env =
        (OwnershipLcnf.execNested assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.env ∧
      (OwnershipLcnf.execCounted assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.nodes =
        (OwnershipLcnf.execNested assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.nodes ∧
      (OwnershipLcnf.execCounted assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.pairs =
        (OwnershipLcnf.execNested assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.pairs ∧
      (OwnershipLcnf.execCounted assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.callPath =
        (OwnershipLcnf.execNested assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.callPath ∧
      (OwnershipLcnf.execCounted assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.childVar =
        (OwnershipLcnf.execNested assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.childVar ∧
      (OwnershipLcnf.execCounted assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.writes =
        (OwnershipLcnf.execNested assign body
          (OwnershipLcnf.countedPrefix capturedPrefix.fragment) machine).1.writes ∧
      (∀ q, ¬ Ownership.Entry.MutableFootprint B 1 q →
        Hout.cells q = B.cells q) ∧
      (∀ q, q ≠ 0 → Hf.cells q = Hout.cells q)) := by
  obtain ⟨Hm, envm, ws, Hf, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25⟩ := principal_instance
  exact ⟨Hm, envm, ws, Hf, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25⟩

#print axioms principal_instance
#print axioms instance_conjuncts
#print axioms countedCall
#print axioms countedCall_accounted
#print axioms retained_parent_copies

end OwnershipTest
