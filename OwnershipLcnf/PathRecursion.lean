/-
The nested `setAt` child-call contract of a finite path, derived level by level.

`OwnershipLcnf/NestedSemantics.lean` relates one recognized `Path.index` prefix
to the model term `indexModelTerm`, conditional on `ChildContract` — an assumed
contract about the admitted model body the recursive call runs. This module
removes that hypothesis for a finite level list: the body a level's call runs is
`Ownership.Path.build` of the remaining levels (`callBody_build`), and the
contract for it is *derived* by induction on the list's length, so the
correspondence no longer takes an arbitrary `ChildContract` for the emitted
callee.

## The induction

`ChildContracts` states `ChildContract` at every level of a level list: at each
level, the level's take-out heap, the environment the call exposes, and the
remaining levels' build. `childContracts_of_path` proves it by induction on the
list, with `PathContract` carrying the per-state facts one level supplies:

* the base case is the leaf: the innermost call's body is the leaf program, and
  its contract is discharged from the leaf's own agreement, checker acceptance,
  exit variable, count-freedom and annotation (`callAt_frame_confined`). The
  leaf contract is the only function-level contract supplied; it is not derived
  from the level list, because the emitted callee's body is not captured;
* the step derives the level's contract from `callAt_frame_confined` on the
  remaining levels' build, whose checker acceptance is `checkNF_build` and whose
  agreement is `agrees_of_path`. The tail's agreement needs the tail's
  `ChildConfined`, which `confined_of_childContracts` derives *from the induction
  hypothesis*: the head contract's preservation clause is exactly the level's
  preservation row of `ChildConfined`, and the separation row is the heap-shape
  fact `Acyclic`.

So the contract at a level is not assumed: it follows from the level's data and
the leaf, and the induction hypothesis is the tail's own contract. The
recursive call's target identity is what makes the tail the same declaration:
`OwnershipLcnf/NestedProjection.lean` requires the call to be the recognized
declaration itself (`unless recFn == declName do none`), so the body at the next
level is again a recognized `Path.index` shape, which is why the model's
syntactic descent (`callBody_build`) is the right induction.

## The correspondence

`index_path_fragment_simulates_model` feeds the derived contract to
`index_fragment_simulates_model`, and `indexModelTerm` of the tail's build is
`build` of the whole list, so the executed recognized prefix reports the model
run of the finite path. `index_path_simulates_model` is the same result for a code
value the recognizer accepts (`execNestedAST_recognized`).

`OwnershipTest/PathRecursion.lean` is the depth-two instance: it supplies the
level list's data and a concrete leaf, derives the contract at both levels
(`ChildContracts.head` and `ChildContracts.second`), runs the correspondence, and
computes the model run it reports.

## What remains, and what is not claimed

* **The leaf body's contract.** Agreement, checker acceptance, exit variable,
  count-freedom and annotation are supplied for the innermost body. They are the
  emitted callee's contract, not facts the level list determines; the depth-three
  family `Ownership.PathSafety`'s `leafAgrees` uses (`agrees_extract_restore`) is
  one instantiation. The leaf's *write account* (`WritesIn`) is not a premise
  here: it is consumed by the separate post-state non-growth row
  (`writesIn_build` and `footprint_contained`), not by the correspondence.
* **N10, the emitted call's meaning.** `execNested`'s `.recurse` rule *is* the
  contract N10 states: the call runs the admitted model body on the environment
  that exposes only the call's own state, path and value, on the caller's heap.
  The emitted recursive callee's body is still not captured, so nothing here says
  the linked declaration's body is the model build; the derivation says the model
  build is what the *call* is assumed to run, level by level.
* **The deeper level's index: the model's nest does not reach it.** A level after
  the first reads its environment from the call's isolated one, so the model's
  level discipline (`LevelShape`, `LevelEnv`) requires that level's index to be
  one of the two scalars the call exposes — the path or the value — and its index
  value to be that scalar's value. The emitted recognizer does something else: it
  reads the selected index by re-projecting the path the invocation holds
  (`oproj[1]` of the node, `NestedPrefix.index`) and hands the *continuation*
  (`oproj[2]`, `NestedPrefix.path`) to the recursive call, so each invocation
  derives its own index from its own path. This theorem therefore covers level
  lists whose deeper levels take their index from the exposed scalar, and excludes
  deeper levels whose index is obtained by re-projecting that continuation. The
  exclusion is a limitation of the model's finite nest — its flat environment and
  its state/path/value abstraction of a call — and not a restriction on the
  emitted program, which does re-project at every invocation. Carrying that
  comparison further would need the callee's own frame, whose fresh binder for
  `oproj[1]` the flat environment cannot name; that gap belongs with the N10
  obligation above, not with this result.
* **Finite syntactic depth.** The induction is over the level list's length, which
  is the program's own syntax (`calls_build`, `extractions_build`). Depth that
  depends on data, mutual recursion, and the linked executable's stack behaviour
  are outside this result; it is not an executor certificate and it does not
  claim arbitrary runtime recursion.

The path's own data (`PathContract`) is data about the level list, the heap and
the leaf, not a contract about the recursive callee: `Slots`, `Chained`,
`DistinctArrays`, `EnvOK`, `LevelCtx`/`Shapes`/`Counts`, `Acyclic`, `Live`,
`AnnotationsIn`, `EndsAt`, and the caller's `Inv`.
-/
import OwnershipLcnf.NestedSemantics
import Ownership.PathConsolidation

open Ownership
open Ownership.Nested
open Ownership.Entry
open Ownership.Path
open Ownership.PathConsolidation
open Ownership.PathSafety

namespace OwnershipLcnf

/-! ## The level a recognized prefix's model term describes -/

/-- The model level the recognized prefix's model term describes. Every model
variable of the level is the prefix's own binder, the call's two scalars are the
model's path and value scalars, and the level's array, object, selected index and
extracted child are the instance's. This is the identification that makes
`indexModelTerm` of a tail's build the `build` of the whole list. -/
structure LevelMatch (assign : Lean.FVarId → Ownership.Var) (p : NestedPrefix) (l : Level)
    (path value : Ownership.Var) (rA : Ownership.Ref) (o : Ownership.Obj) (i : Nat)
    (childRef : Ownership.Ref) : Prop where
  arrayVar : l.arrayVar = assign p.array
  indexVar : l.indexVar = assign p.index
  parentVar : l.parentVar = assign p.parent
  childVar : l.childVar = assign p.child
  resultVar : l.resultVar = assign p.recursive
  restoredVar : l.restoredVar = assign p.restored
  pathVar : path = assign p.path
  valueVar : value = assign p.value
  arr : l.arr = rA
  obj : l.obj = o
  idx : l.idx = i
  child : l.child = childRef

/-- `indexModelTerm` at the level the prefix describes, with the remaining levels
as the callee's body, is the `build` of the whole list. -/
theorem indexModelTerm_build {assign : Lean.FVarId → Ownership.Var} {p : NestedPrefix}
    {l : Level} {path value : Ownership.Var} {rA : Ownership.Ref} {o : Ownership.Obj}
    {i : Nat} {childRef : Ownership.Ref} {body : Ownership.Nested.NCode}
    {rest : List Level} (hm : LevelMatch assign p l path value rA o i childRef) :
    indexModelTerm assign p childRef (build path value body rest) =
      build path value body (l :: rest) := by
  simp [indexModelTerm, build, hm.arrayVar, hm.indexVar, hm.parentVar, hm.childVar,
    hm.resultVar, hm.restoredVar, hm.pathVar, hm.valueVar, hm.child]

/-! ## The child-call contract at every level -/

/-- The child-call contract at each level of a finite path. A level's recursive
call runs the remaining levels, so the contract is `ChildContract` at the heap the
level's take-out leaves, the environment the call exposes and the tail's build;
the tail's own levels are the second component. -/
def ChildContracts (path value : Ownership.Var) (body : Ownership.Nested.NCode)
    (H : Ownership.Heap) (env : Ownership.Env) : List Level → Prop
  | [] => True
  | l :: rest =>
      ChildContract (blankLevel H l) (isolateEnv (bindLevel env l) l.childVar path value)
          (build path value body rest) l.child ∧
        ChildContracts path value body (blankLevel H l)
          (isolateEnv (bindLevel env l) l.childVar path value) rest

/-- The contract at the first level of a non-empty path. -/
theorem ChildContracts.head {path value : Ownership.Var} {body : Ownership.Nested.NCode}
    {H : Ownership.Heap} {env : Ownership.Env} {l : Level} {rest : List Level}
    (h : ChildContracts path value body H env (l :: rest)) :
    ChildContract (blankLevel H l) (isolateEnv (bindLevel env l) l.childVar path value)
      (build path value body rest) l.child :=
  h.1

/-- The contracts of the levels after the first, at the state the first level's
call hands them. -/
theorem ChildContracts.tail {path value : Ownership.Var} {body : Ownership.Nested.NCode}
    {H : Ownership.Heap} {env : Ownership.Env} {l : Level} {rest : List Level}
    (h : ChildContracts path value body H env (l :: rest)) :
    ChildContracts path value body (blankLevel H l)
      (isolateEnv (bindLevel env l) l.childVar path value) rest :=
  h.2

/-- The contract at the level after the first: the list's own step, stated at the
state the first level's call hands the second. Applied repeatedly it reaches every
level, and its base case is the leaf. -/
theorem ChildContracts.second {path value : Ownership.Var}
    {body : Ownership.Nested.NCode} {H : Ownership.Heap} {env : Ownership.Env}
    {l m : Level} {rest : List Level}
    (h : ChildContracts path value body H env (l :: m :: rest)) :
    ChildContract (blankLevel (blankLevel H l) m)
      (isolateEnv (bindLevel (isolateEnv (bindLevel env l) l.childVar path value) m)
        m.childVar path value)
      (build path value body rest) m.child :=
  h.tail.head

/-! ## The facts a level list supplies -/

/-- The data a finite level list supplies for the child-call contract at its first
level: the path's slot, chain, distinctness, environment and leaf facts, the
checker discipline of the levels, the heap-shape facts, and the caller's
invariant. Every field is a fact about the level list, the heap or the leaf body:
the level discipline is `levelCtx`, `shapes` and `counts`, and the leaf's own
contract is `leaf` (its agreement at the innermost state), `checkBody` (its
acceptance at the innermost isolated context), `retBody`, `retOwned`, `retRef`
(its exit), `countFree` and `annot`. No field is a contract about the recursive
callee. The leaf's write account (`WritesIn`) is deliberately absent: the
correspondence does not use it, and `writesIn_build` derives the path's account
from the leaf's for the separate post-state non-growth row. -/
structure PathContract (path value : Ownership.Var) (body : Ownership.Nested.NCode)
    (tip : Ownership.Ref) (l : Level) (rest : List Level) (H : Ownership.Heap)
    (env : Ownership.Env) (c : Ownership.Ctx) (cb : Ownership.Ctx)
    (y : Ownership.Var) : Prop where
  /-- Each level's array is a live non-persistent cell whose selected slot holds
  the next reference. -/
  slots : Slots H (l :: rest)
  /-- The path is chained: each extracted child is the next level's array. -/
  chained : Chained (l :: rest)
  /-- The path's arrays are pairwise distinct. -/
  distinct : DistinctArrays (l :: rest)
  /-- Each level reads the array handle, the selected index and the call's two
  scalars from the environment its take-out starts from. -/
  envok : EnvOK path value env (l :: rest)
  /-- The leaf body's agreement at the state the innermost call hands it. -/
  leaf : leafAgrees path value body (blankLevel H l)
      (isolateEnv (bindLevel env l) l.childVar path value) rest
  /-- The first level's context discipline. -/
  levelCtx : LevelCtx path value c l
  /-- The levels after the first start in the context the recursive call leaves. -/
  shapes : Shapes path value rest
  /-- Every array and extracted child along the path is counted once. -/
  counts : Counts c.mult rest
  /-- The child's mutable footprint does not contain the suspended parent, and
  the tip cannot reach back up to a level the path emptied. -/
  acyclic : Acyclic tip H (l :: rest)
  /-- The tip is live. -/
  live : Live H tip
  /-- The leaf body's extraction annotations lie in the tip's footprint. -/
  annot : AnnotationsIn H tip body
  /-- The leaf body's checker acceptance at the innermost isolated context. -/
  checkBody : checkNF (tailCtx path value c (l :: rest)) [] body = some cb
  /-- The leaf body's exit variable. -/
  retBody : retVar body = some y
  /-- The exit is an owned handle. -/
  retOwned : cb.us y = .owned
  /-- The exit denotes the tip. -/
  retRef : cb.refOf y = some tip
  /-- The last level extracts the tip. -/
  endsAt : EndsAt tip (l :: rest)
  /-- The leaf body neither duplicates nor consumes a handle. -/
  countFree : CountFree body = true
  /-- The caller's invariant at the entry state. -/
  inv : Inv H env c

/-- The next level's facts, at the state the current level's call hands it. -/
theorem PathContract.tail {path value : Ownership.Var} {body : Ownership.Nested.NCode}
    {tip : Ownership.Ref} {l m : Level} {rest' : List Level} {H : Ownership.Heap}
    {env : Ownership.Env} {c : Ownership.Ctx} {cb : Ownership.Ctx} {y : Ownership.Var}
    (h : PathContract path value body tip l (m :: rest') H env c cb y) :
    PathContract path value body tip m rest' (blankLevel H l)
      (isolateEnv (bindLevel env l) l.childVar path value) (bodyCtx path value c l) cb y := by
  have hnoBack : ¬ MutableFootprint H tip l.arr := h.acyclic.2.1
  obtain ⟨harr, hvar, _⟩ := h.chained
  have hi_take : Inv (blankLevel H l) (bindLevel env l) (takeCtx c l) :=
    inv_after_takeOut h.inv h.levelCtx.us_arr h.levelCtx.ref_arr h.levelCtx.mult_child
      (h.slots l (by simp)).1
  have hi_iso : Inv (blankLevel H l)
      (isolateEnv (bindLevel env l) l.childVar path value) (bodyCtx path value c l) :=
    inv_isolated hi_take (takeCtx_us_child c l) (takeCtx_refOf_child c l)
      (takeCtx_us_path h.levelCtx) (takeCtx_us_value h.levelCtx)
  refine
    { slots := Slots.blank (fun k hk => h.slots k (List.mem_cons_of_mem _ hk)) h.distinct.1
      chained := h.chained.2.2
      distinct := h.distinct.2
      envok := h.envok.2
      leaf := by simpa only [leafAgrees] using h.leaf
      levelCtx :=
        levelCtx_isolate h.levelCtx h.shapes.1 ⟨h.counts.1, h.counts.2.1⟩ harr hvar
      shapes := h.shapes.2
      counts := Counts.congr (fun _ => rfl) rest' h.counts.2.2
      acyclic := h.acyclic.2.2
      live := Live.blank hnoBack h.live
      annot := AnnotationsIn.blank hnoBack h.annot
      checkBody := by simpa [tailCtx] using h.checkBody
      retBody := h.retBody
      retOwned := h.retOwned
      retRef := h.retRef
      endsAt := by simpa [EndsAt] using h.endsAt
      countFree := h.countFree
      inv := hi_iso }

/-! ## `ChildConfined` from the derived contracts -/

/-- `ChildConfined` at every level, from the derived contracts: the head
contract's preservation clause is the level's preservation row, and the heap-shape
fact `Acyclic` supplies the separation row. The induction is over the level list;
the tail's rows are the induction hypothesis. -/
theorem confined_of_childContracts {path value : Ownership.Var}
    {body : Ownership.Nested.NCode} :
    ∀ (ls : List Level) {H : Ownership.Heap} {env : Ownership.Env} {tip : Ownership.Ref},
      Acyclic tip H ls → ChildContracts path value body H env ls →
        ChildConfined path value body H env ls := by
  intro ls
  induction ls with
  | nil => intro H env tip _ _; trivial
  | cons l rest ih =>
      intro H env tip hacyc hc
      obtain ⟨hsep, -, hacyc'⟩ := hacyc
      obtain ⟨hhead, htail⟩ := hc
      obtain ⟨Hh, envh, wsh, hrun, -, hpres⟩ := hhead.outcome
      refine ⟨hsep, ?_, ih hacyc' htail⟩
      intro H' envb vb wsb hrun' q hq
      rw [hrun] at hrun'
      injection hrun' with hH _ _ _
      subst hH
      exact hpres q hq

/-! ## The contract at every level, derived -/

/-- The child-call contract at every level of a finite path, derived by induction
on the level list. The base case is the leaf body's own contract at the innermost
call; the step derives the level's contract from `callAt_frame_confined` on the
remaining levels' build, whose checker acceptance is `checkNF_build` and whose
agreement is `agrees_of_path`. No `ChildContract` is assumed. -/
theorem childContracts_of_path {path value : Ownership.Var}
    {body : Ownership.Nested.NCode} :
    ∀ (rest : List Level) (l : Level) {H : Ownership.Heap} {env : Ownership.Env}
      {c : Ownership.Ctx} {tip : Ownership.Ref} {cb : Ownership.Ctx}
      {y : Ownership.Var},
      PathContract path value body tip l rest H env c cb y →
        ChildContracts path value body H env (l :: rest) := by
  intro rest
  induction rest with
  | nil =>
      intro l H env c tip cb y h
      have hchild : l.child = tip := h.endsAt
      have hi_take : Inv (blankLevel H l) (bindLevel env l) (takeCtx c l) :=
        inv_after_takeOut h.inv h.levelCtx.us_arr h.levelCtx.ref_arr h.levelCtx.mult_child
          (h.slots l (by simp)).1
      have hi_iso : Inv (blankLevel H l)
          (isolateEnv (bindLevel env l) l.childVar path value) (bodyCtx path value c l) :=
        inv_isolated hi_take (takeCtx_us_child c l) (takeCtx_refOf_child c l)
          (takeCtx_us_path h.levelCtx) (takeCtx_us_value h.levelCtx)
      have hann : AnnotationsIn (blankLevel H l) l.child body := by
        have hb := AnnotationsIn.blank (l := l) (tip := tip) h.acyclic.2.1 h.annot
        rwa [← hchild] at hb
      have hcheck : checkNF (bodyCtx path value c l) [] body = some cb := by
        simpa [tailCtx, bodyCtx] using h.checkBody
      have hret : ∃ z, retVar body = some z ∧ cb.us z = .owned ∧
          cb.refOf z = some l.child :=
        ⟨y, h.retBody, h.retOwned, by rw [hchild]; exact h.retRef⟩
      have hok : TakeOutsOK (blankLevel H l)
          (isolateEnv (bindLevel env l) l.childVar path value) body :=
        takeOutsOK_of_inv hi_iso (by simpa [leafAgrees] using h.leaf) hcheck
      obtain ⟨H', envb, vb, ws, hrun, hws, hv, hpres⟩ :=
        callAt_frame_confined hann hcheck hret hi_iso hok
      rw [hv] at hrun
      have hexcl : (blankLevel H l).exclusive? l.child = true :=
        Heap.exclusive?_eq_true.mpr
          (Inv.exclusive hi_take (by rw [takeCtx_mult]; exact h.levelCtx.mult_child))
      exact ⟨⟨hexcl, ⟨H', envb, ws, hrun, hws, hpres⟩⟩, trivial⟩
  | cons m rest' ih =>
      intro l H env c tip cb y h
      obtain ⟨hsep, hnoBack, -⟩ := h.acyclic
      obtain ⟨harr, hvar, _⟩ := h.chained
      have htail : PathContract path value body tip m rest' (blankLevel H l)
          (isolateEnv (bindLevel env l) l.childVar path value) (bodyCtx path value c l) cb y :=
        h.tail
      have htailC : ChildContracts path value body (blankLevel H l)
          (isolateEnv (bindLevel env l) l.childVar path value) (m :: rest') :=
        ih m htail
      have htailConf : ChildConfined path value body (blankLevel H l)
          (isolateEnv (bindLevel env l) l.childVar path value) (m :: rest') :=
        confined_of_childContracts (m :: rest') htail.acyclic htailC
      have hi_take : Inv (blankLevel H l) (bindLevel env l) (takeCtx c l) :=
        inv_after_takeOut h.inv h.levelCtx.us_arr h.levelCtx.ref_arr h.levelCtx.mult_child
          (h.slots l (by simp)).1
      have hi_iso : Inv (blankLevel H l)
          (isolateEnv (bindLevel env l) l.childVar path value) (bodyCtx path value c l) :=
        inv_isolated hi_take (takeCtx_us_child c l) (takeCtx_refOf_child c l)
          (takeCtx_us_path h.levelCtx) (takeCtx_us_value h.levelCtx)
      have hagree : Agrees (blankLevel H l)
          (isolateEnv (bindLevel env l) l.childVar path value)
          (build path value body (m :: rest')) :=
        agrees_of_path rest' m htail.slots htail.chained htail.distinct htail.envok
          htail.leaf htailConf
      have hcheck : checkNF (bodyCtx path value c l) []
          (build path value body (m :: rest')) =
          some (levelFinal (bodyCtx path value c l) m) :=
        checkNF_build rest' m htail.levelCtx htail.shapes htail.counts htail.chained
          htail.checkBody htail.retBody htail.retOwned htail.retRef htail.endsAt
          htail.countFree
      have hann : AnnotationsIn (blankLevel H l) l.child
          (build path value body (m :: rest')) :=
        annotationsIn_of_path rest' m l.child tip htail.slots htail.chained harr.symm
          htail.endsAt (Live.blank hnoBack h.live) (AnnotationsIn.blank hnoBack h.annot)
      have hret : ∃ z, retVar (build path value body (m :: rest')) = some z ∧
          (levelFinal (bodyCtx path value c l) m).us z = .owned ∧
          (levelFinal (bodyCtx path value c l) m).refOf z = some l.child :=
        ⟨m.restoredVar, retVar_build rest' m, levelFinal_us_restored htail.levelCtx,
          by rw [levelFinal_refOf_restored htail.levelCtx, harr]⟩
      have hok : TakeOutsOK (blankLevel H l)
          (isolateEnv (bindLevel env l) l.childVar path value)
          (build path value body (m :: rest')) :=
        takeOutsOK_of_inv hi_iso hagree hcheck
      obtain ⟨H', envb, vb, ws, hrun, hws, hv, hpres⟩ :=
        callAt_frame_confined hann hcheck hret hi_iso hok
      rw [hv] at hrun
      have hexcl : (blankLevel H l).exclusive? l.child = true :=
        Heap.exclusive?_eq_true.mpr
          (Inv.exclusive hi_take (by rw [takeCtx_mult]; exact h.levelCtx.mult_child))
      exact ⟨⟨hexcl, ⟨H', envb, ws, hrun, hws, hpres⟩⟩, htailC⟩

/-- The child-call contract at the first level of a finite path, derived: the
level's recursive call runs the remaining levels' build, and nothing about that
build is assumed. -/
theorem childContract_of_path {path value : Ownership.Var}
    {body : Ownership.Nested.NCode} (rest : List Level) (l : Level)
    {H : Ownership.Heap} {env : Ownership.Env} {c : Ownership.Ctx} {tip : Ownership.Ref}
    {cb : Ownership.Ctx} {y : Ownership.Var}
    (h : PathContract path value body tip l rest H env c cb y) :
    ChildContract (blankLevel H l) (isolateEnv (bindLevel env l) l.childVar path value)
      (build path value body rest) l.child :=
  (childContracts_of_path rest l h).head

/-! ## The correspondence without a supplied child contract -/

/-- The recognized nested prefix at the first level of a finite path reports the
model's run of the whole path. The child-call contract `ChildContract` is *not* a
premise: it is the head of `ChildContracts`, derived from the level list's data
and the leaf body's contract. The model term the prefix is related to is
`build path value body (l :: rest)` — the finite path — and the callee's body is
its tail.

What the theorem still rests on is the leaf body's contract (in `hpath`) and the
N10 meaning of the emitted call: `execNested`'s `.recurse` rule runs the admitted
model body on the environment that exposes only the call's own state, path and
value. The emitted callee's own body is not captured, so this is a statement
about the model the call is assumed to run, at the syntactic depth of the list. -/
theorem index_path_fragment_simulates_model
    (assign : Lean.FVarId → Ownership.Var) (p : NestedPrefix) (hl : NestedLayout assign p)
    (path value : Ownership.Var) (body : Ownership.Nested.NCode)
    (rest : List Level) (l : Level) (s : NestedMachine) (mEnv : Ownership.Env)
    (H : Ownership.Heap) (rA : Ownership.Ref) (o : Ownership.Obj) (i v pv : Nat)
    (childRef : Ownership.Ref)
    (hm : LevelMatch assign p l path value rA o i childRef)
    (hag : NestedAgrees assign p s mEnv H rA i v pv)
    (c : Ownership.Ctx) (tip : Ownership.Ref) (cb : Ownership.Ctx) (y : Ownership.Var)
    (hpath : PathContract path value body tip l rest H mEnv c cb y) :
    NestedOutcome.ofExec assign p
        (execNested assign (build path value body rest) p.fragment s) =
        some (NestedOutcome.ofModel
          (Ownership.Nested.runN (build path value body (l :: rest)) mEnv H)) ∧
      (∃ H' env' ws,
        Ownership.Nested.runN (build path value body (l :: rest)) mEnv H =
          .done H' env' (.ref rA) ws ∧ (∀ w ∈ ws, w.2 = true)) := by
  have hvars : Vars path value l := hpath.levelCtx.toVars
  -- the take-out's heap is the level's blank heap
  have hheap : takeOutHeap H rA o i = blankLevel H l := by
    simp [takeOutHeap, blankLevel, hm.arr, hm.obj, hm.idx]
  -- the contract at the first level, derived rather than assumed
  have hcc : ChildContract (blankLevel H l)
      (isolateEnv (bindLevel mEnv l) l.childVar path value)
      (build path value body rest) l.child :=
    childContract_of_path rest l hpath
  -- the call's environment is the model environment, restricted
  have henv : isolateEnv (bindLevel mEnv l) l.childVar path value =
      callEnv (assign p.child) (.ref childRef) (assign p.path) (.scalar pv)
        (assign p.value) (.scalar v) := by
    have hpathVal : (bindLevel mEnv l) path = some (.scalar pv) := by
      rw [bindLevel, Ownership.Env.set_other _ _ _ _ (Ne.symm hvars.child_ne_path),
        Ownership.Env.set_other _ _ _ _ (Ne.symm hvars.parent_ne_path), hm.pathVar]
      exact hag.path_model
    have hvalueVal : (bindLevel mEnv l) value = some (.scalar v) := by
      rw [bindLevel, Ownership.Env.set_other _ _ _ _ (Ne.symm hvars.child_ne_value),
        Ownership.Env.set_other _ _ _ _ (Ne.symm hvars.parent_ne_value), hm.valueVar]
      exact hag.value_model
    have h := isolateEnv_eq_callEnv (env := bindLevel mEnv l) (state := l.childVar)
      (path := path) (x := value) (sv := .ref l.child) (pv := .scalar pv) (xv := .scalar v)
      (bindLevel_child mEnv l) hpathVal hvalueVal
    rw [h, hm.childVar, hm.pathVar, hm.valueVar, hm.child]
  -- the parent is outside the extracted child's mutable footprint
  have hsep : ¬ MutableFootprint (takeOutHeap H rA o i) childRef rA := by
    rw [hheap, ← hm.child, ← hm.arr]
    exact hpath.acyclic.1
  -- the contract, at the heap and environment the correspondence takes
  have hcc' : ChildContract (takeOutHeap H rA o i)
      (callEnv (assign p.child) (.ref childRef) (assign p.path) (.scalar pv)
        (assign p.value) (.scalar v)) (build path value body rest) childRef := by
    rw [hheap, ← henv, ← hm.child]
    exact hcc
  -- the level's own slot and cell facts, read off the path
  have hcell : H.cells rA = some o := by
    obtain ⟨hcell, -⟩ := hpath.slots l (by simp)
    rw [← hm.arr, ← hm.obj]
    exact hcell
  have hslot : o.fields[i]? = some (.ref childRef) := by
    obtain ⟨-, hslot, -⟩ := hpath.slots l (by simp)
    rw [← hm.obj, ← hm.idx, ← hm.child]
    exact hslot
  have hin : i < o.fields.size := by
    have h := hslot
    rw [Array.getElem?_eq_some_iff] at h
    exact h.1
  have hex : H.exclusive? rA = true := by
    refine Heap.exclusive?_eq_true.mpr (Inv.exclusive hpath.inv ?_)
    rw [← hm.arr]
    exact hpath.levelCtx.mult_arr
  have hsim := index_fragment_simulates_model assign p hl
    (build path value body rest) s mEnv H rA o i v pv childRef hag hcell hex hslot hin
    hsep hcc'
  rw [indexModelTerm_build hm] at hsim
  exact hsim

/-- The correspondence over a code value the recognizer accepts: the recognition
hypothesis is consumed by `execNestedAST_recognized`, so nothing is assumed about
`code` beyond the recognizer's verdict, and the child contract is still derived
from the level list rather than supplied. -/
theorem index_path_simulates_model (declName takeOut : Lean.Name)
    (assign : Lean.FVarId → Ownership.Var) (p : NestedPrefix) (code : Lean.Compiler.LCNF.Code .impure)
    (hproj : projectNested declName takeOut code = some p)
    (hl : NestedLayout assign p) (path value : Ownership.Var)
    (body : Ownership.Nested.NCode) (rest : List Level) (l : Level)
    (s : NestedMachine) (mEnv : Ownership.Env) (H : Ownership.Heap)
    (rA : Ownership.Ref) (o : Ownership.Obj) (i v pv : Nat) (childRef : Ownership.Ref)
    (hm : LevelMatch assign p l path value rA o i childRef)
    (hag : NestedAgrees assign p s mEnv H rA i v pv)
    (c : Ownership.Ctx) (tip : Ownership.Ref) (cb : Ownership.Ctx) (y : Ownership.Var)
    (hpath : PathContract path value body tip l rest H mEnv c cb y) :
    NestedOutcome.ofExec assign p
        (execNestedAST declName takeOut assign (build path value body rest) p code s) =
        some (NestedOutcome.ofModel
          (Ownership.Nested.runN (build path value body (l :: rest)) mEnv H)) ∧
      (∃ H' env' ws,
        Ownership.Nested.runN (build path value body (l :: rest)) mEnv H =
          .done H' env' (.ref rA) ws ∧ (∀ w ∈ ws, w.2 = true)) := by
  rw [execNestedAST_recognized declName takeOut assign (build path value body rest) p code s
    hproj]
  exact index_path_fragment_simulates_model assign p hl path value body rest l s mEnv H rA o i
    v pv childRef hm hag c tip cb y hpath

#print axioms ChildContracts.head
#print axioms ChildContracts.second
#print axioms confined_of_childContracts
#print axioms childContracts_of_path
#print axioms childContract_of_path
#print axioms index_path_fragment_simulates_model
#print axioms index_path_simulates_model

end OwnershipLcnf
