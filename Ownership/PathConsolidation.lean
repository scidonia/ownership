/-
Consolidating the compositional premises of the path theory.

`Ownership.Path` builds a nested program off a level chain and derives its
agreement and annotation reachability; `Ownership.PathSafety` turns that into
depth-independent safety, confinement and client retention. Both take several
premises the path's own shape should determine: the checker's acceptance of the
built program, the child-call contract `ChildConfined`, the leaf body's
agreement, and the three heap facts `footprint_within` needs. This module
derives them for supported paths, and names what remains.

* Checker acceptance. `checkNF_build` derives acceptance of `build path value
  body ls` from the context discipline at each level and the checker's
  acceptance of the leaf body, and states the result as the *final context*:
  the level's own take-out, call and put-back context, `pathFinal`. The
  discipline is `LevelCtx` for the first level and `LevelShape` for the levels
  after it, whose contexts the recursive call re-exposes. The multiplicity facts
  `Counts` are not free: `counts_of_path` derives them from the entry
  condition's unique tree and the path's own footprint membership.

* The child-call contract. `childConfined_of_path` derives `ChildConfined` at
  every level from the remaining levels' contract: the preservation half is
  `callAt_frame_confined`, with the annotation premise lifted through the
  take-out by `AnnotationsIn.blank`, the checker acceptance by `checkNF_build`,
  and the state-indexed heap premise by `takeOutsOK_of_inv`. The separation half
  and the annotation lift's non-reachability premise are the heap-shape fact
  `Acyclic`: the extracted child's mutable footprint does not contain the parent
  array, and the tip cannot reach back up to an emptied level.

* Leaf agreement. `agrees_extract_restore` derives the agreement of a
  constructed leaf body — extract the selected slot, restore it, run a scalar
  block — from the extraction's slot facts. What remains supplied for a general
  leaf is its agreement (`leafAgrees`, which `agrees_extract_restore` discharges
  for that family), its checker acceptance, its exit variable, its count-freedom,
  and its write annotation; those are the emitted callee's contract, not facts
  about the path.

* Footprint containment. `slotRefs_runN` tracks what a run leaves in a footprint
  cell's fields: the model's only reference-valued write is a put-back's element,
  and `WritesIn` records exactly those. `writesIn_build` derives it for the path,
  leaving only the leaf body's own writes. `footprint_contained` then derives
  the footprint's non-growth from the run's confinement plus that account, in
  place of the three heap facts `footprint_within` takes.

* Observations. `observation_retention` replaces the fixed client-root list with
  the interface's observation: the client's roots together with the values the
  interface produced. The premise that the produced values are separated from the
  footprint is the interface's own obligation — `obsSeparated_of_separated`
  composes the client's separation with the produced value's, and
  `CallbackTrafficOutside` states what a callback-valued interface adds.

* Node and continuation traffic. `protocol_cells` relates the counted extraction
  protocol of `Ownership.CountedPair` to the model's take-out: on every session
  cell the two heaps agree, and the temporary pair is the only extra object.
  `pair_outside_footprint` places that pair outside the state's mutable
  footprint, so its traffic cannot be a footprint cell's traffic;
  `path_mult_preserved` shows the path's own contexts report the entry
  multiplicities. A path node and a continuation are not `Ref`s of the model heap
  at all, so no theorem here can speak about their counts: the emitted separation
  stays a named runtime contract (A2).

* The finite level list. `calls_build` and `extractions_build` fix the model's
  call structure to the level list — one call site and one extraction per level —
  and `callBody_build` shows each call's embedded body is the *remaining list*, so
  the model's "recursion" is a syntactic descent rather than a declaration. That
  is a conservative syntactic bound, not an executor certificate: the emitted
  `setAt` callee's body is not captured and the executor's call rule is not
  established. The finite-list/emitted-recursion row is therefore a named,
  narrowed boundary, and the section on it states exactly what a connection would
  need.

Boundary. Everything below is about the model: finite level lists, the model's
`NCode`/`Ctx`/`Heap`, and the counted pair of `Ownership.CountedPair`. Nothing
identifies a `Ref` with a runtime address, and nothing claims the linked
executable performs these steps.
-/
import Ownership.PathSafety
import Ownership.CountedPair

namespace Ownership
namespace PathConsolidation

open Ownership.Nested
open Ownership.Entry
open Ownership.Path
open Ownership.PathSafety

/-! ## The contexts the built path is checked from -/

/-- The context a level's take-out leaves: the array handle has moved to the
parent variable and the extracted child is an owned handle in the child
variable. -/
def takeCtx (c : Ctx) (l : Level) : Ctx :=
  (c.move l.arrayVar l.parentVar).bindOwned l.childVar l.child

/-- The context the level's continuation is checked from after the recursive call
returns: the extracted handle has moved to the call's result variable. -/
def callCtx (c : Ctx) (l : Level) : Ctx := (takeCtx c l).move l.childVar l.resultVar

/-- The context after the level's put-back binds the restored handle. -/
def restoreCtx (c : Ctx) (l : Level) : Ctx := (callCtx c l).move l.parentVar l.restoredVar

/-- The context the level's put-back exits with: the extraction's frame is
restored, so the call's result variable is dead again and the restored handle is
the level's exit. -/
def levelFinal (c : Ctx) (l : Level) : Ctx := (restoreCtx c l).setUs l.resultVar .dead

/-- The context a level's recursive body is checked from: only the extracted
handle and the call's two scalars are exposed. -/
def bodyCtx (path value : Var) (c : Ctx) (l : Level) : Ctx :=
  isolatedCtx (takeCtx c l) l.childVar path value l.child

/-- Multiplicities are read off the counted heap, so every context the level's
operations build reports the same multiplicities. -/
theorem takeCtx_mult (c : Ctx) (l : Level) : (takeCtx c l).mult = c.mult := rfl

theorem callCtx_mult (c : Ctx) (l : Level) : (callCtx c l).mult = c.mult := rfl

theorem bodyCtx_mult (path value : Var) (c : Ctx) (l : Level) :
    (bodyCtx path value c l).mult = c.mult := rfl

/-- The contexts the innermost body is checked from, level by level. -/
def tailCtx (path value : Var) (c : Ctx) : List Level → Ctx
  | [] => c
  | l :: rest => tailCtx path value (bodyCtx path value c l) rest

/-- The context `build` leaves: the first level's own final context. The
continuation after a level's call is that level's put-back, so the remaining
levels do not appear. -/
def pathFinal (c : Ctx) : List Level → Ctx
  | [] => c
  | l :: _ => levelFinal c l

/-! ## The variable discipline a level needs -/

/-- The variables a level's take-out, call and put-back write must be distinct
from the ones they read, and from the call's two scalars. These are the moves'
non-interference conditions, not properties of the heap. -/
structure Vars (path value : Var) (l : Level) : Prop where
  child_ne_arr : l.child ≠ l.arr
  parent_ne_child : l.parentVar ≠ l.childVar
  result_ne_parent : l.resultVar ≠ l.parentVar
  result_ne_child : l.resultVar ≠ l.childVar
  result_ne_handle : l.resultVar ≠ l.arrayVar
  result_ne_restored : l.resultVar ≠ l.restoredVar
  parent_ne_restored : l.parentVar ≠ l.restoredVar
  child_ne_restored : l.childVar ≠ l.restoredVar
  parent_ne_handle : l.parentVar ≠ l.arrayVar
  child_ne_handle : l.childVar ≠ l.arrayVar
  restored_ne_handle : l.restoredVar ≠ l.arrayVar
  idx_ne_handle : l.indexVar ≠ l.arrayVar
  idx_ne_parent : l.indexVar ≠ l.parentVar
  idx_ne_child : l.indexVar ≠ l.childVar
  idx_ne_result : l.indexVar ≠ l.resultVar
  handle_ne_path : l.arrayVar ≠ path
  handle_ne_value : l.arrayVar ≠ value
  parent_ne_path : l.parentVar ≠ path
  parent_ne_value : l.parentVar ≠ value
  child_ne_path : l.childVar ≠ path
  child_ne_value : l.childVar ≠ value
  result_ne_path : l.resultVar ≠ path
  result_ne_value : l.resultVar ≠ value
  restored_ne_path : l.restoredVar ≠ path
  restored_ne_value : l.restoredVar ≠ value

attribute [simp] Vars.child_ne_arr Vars.parent_ne_child Vars.result_ne_parent
  Vars.result_ne_child Vars.result_ne_handle Vars.result_ne_restored
  Vars.parent_ne_restored Vars.child_ne_restored Vars.parent_ne_handle
  Vars.child_ne_handle Vars.restored_ne_handle Vars.idx_ne_handle
  Vars.idx_ne_parent Vars.idx_ne_child Vars.idx_ne_result Vars.handle_ne_path
  Vars.handle_ne_value Vars.parent_ne_path Vars.parent_ne_value
  Vars.child_ne_path Vars.child_ne_value Vars.result_ne_path Vars.result_ne_value
  Vars.restored_ne_path Vars.restored_ne_value

/-- The shape of a level *after* the first: the recursive call re-exposes only the
extracted handle and the call's two scalars, so the level's index must be one of
those scalars and every variable it writes must avoid all three. -/
structure LevelShape (path value : Var) (l : Level) : Prop
    extends Vars path value l where
  idx_source : l.indexVar = path ∨ l.indexVar = value

/-- The shapes of the levels after the first. -/
def Shapes (path value : Var) : List Level → Prop
  | [] => True
  | l :: rest => LevelShape path value l ∧ Shapes path value rest

/-- The context discipline the first level needs: its array handle is owned and
denotes the level's array, its index and the call's two arguments are scalars,
and the variables the level writes are dead. -/
structure LevelCtx (path value : Var) (c : Ctx) (l : Level) : Prop
    extends Vars path value l where
  us_arr : c.us l.arrayVar = .owned
  ref_arr : c.refOf l.arrayVar = some l.arr
  mult_arr : c.mult l.arr = 1
  mult_child : c.mult l.child = 1
  us_idx : c.us l.indexVar = .scalar
  us_parent : c.us l.parentVar = .dead
  us_child : c.us l.childVar = .dead
  us_result : c.us l.resultVar = .dead
  us_restored : c.us l.restoredVar = .dead
  us_path : c.us path = .scalar
  us_value : c.us value = .scalar

/-- Every array and extracted child along a path is counted once. The
multiplicities are a fact about the counted heap, so they do not change as the
path's contexts do; the predicate is stated on the multiplicity function itself. -/
def Counts (mult : Ref → Nat) : List Level → Prop
  | [] => True
  | l :: rest => mult l.arr = 1 ∧ mult l.child = 1 ∧ Counts mult rest

/-! ## The leaf's and the path's own checker facts -/

/-- A count-free nested program stays count-free when the path's take-out, call
and put-back wrap it. -/
theorem countFree_build {path value : Var} {body : NCode} :
    ∀ ls : List Level, CountFree (build path value body ls) = CountFree body := by
  intro ls
  induction ls with
  | nil => rfl
  | cons l rest ih => simp [build, CountFree, ih]

/-! ## The context facts a level's take-out, call and put-back need -/

/-- The take-out binds its extracted child as an owned handle. -/
theorem takeCtx_us_child (c : Ctx) (l : Level) :
    (takeCtx c l).us l.childVar = .owned := by
  rw [takeCtx, Ctx.bindOwned_us_self]

/-- The take-out leaves the array handle owned in the parent variable. -/
theorem takeCtx_us_parent {path value : Var} {c : Ctx} {l : Level}
    (hl : LevelCtx path value c l) :
    (takeCtx c l).us l.parentVar = .owned := by
  have hv : Vars path value l := hl.toVars
  rw [takeCtx, Ctx.bindOwned_us_other _ _ _ _ hv.parent_ne_child, Ctx.move_us_y,
    hl.us_arr]

/-- The take-out leaves the call's path scalar untouched. -/
theorem takeCtx_us_path {path value : Var} {c : Ctx} {l : Level}
    (hl : LevelCtx path value c l) :
    (takeCtx c l).us path = .scalar := by
  have hv : Vars path value l := hl.toVars
  rw [takeCtx, Ctx.bindOwned_us_other _ _ _ _ (Ne.symm hv.child_ne_path),
    Ctx.move_us_other _ _ _ _ (Ne.symm hv.parent_ne_path) (Ne.symm hv.handle_ne_path)]
  exact hl.us_path

/-- The take-out leaves the call's value scalar untouched. -/
theorem takeCtx_us_value {path value : Var} {c : Ctx} {l : Level}
    (hl : LevelCtx path value c l) :
    (takeCtx c l).us value = .scalar := by
  have hv : Vars path value l := hl.toVars
  rw [takeCtx, Ctx.bindOwned_us_other _ _ _ _ (Ne.symm hv.child_ne_value),
    Ctx.move_us_other _ _ _ _ (Ne.symm hv.parent_ne_value) (Ne.symm hv.handle_ne_value)]
  exact hl.us_value

/-- The take-out leaves the call's result variable dead. -/
theorem takeCtx_us_result {path value : Var} {c : Ctx} {l : Level}
    (hl : LevelCtx path value c l) :
    (takeCtx c l).us l.resultVar = .dead := by
  have hv : Vars path value l := hl.toVars
  rw [takeCtx, Ctx.bindOwned_us_other _ _ _ _ hv.result_ne_child,
    Ctx.move_us_other _ _ _ _ hv.result_ne_parent hv.result_ne_handle]
  exact hl.us_result

/-- The take-out leaves the put-back's result variable dead. -/
theorem takeCtx_us_restored {path value : Var} {c : Ctx} {l : Level}
    (hl : LevelCtx path value c l) :
    (takeCtx c l).us l.restoredVar = .dead := by
  have hv : Vars path value l := hl.toVars
  rw [takeCtx, Ctx.bindOwned_us_other _ _ _ _ (Ne.symm hv.child_ne_restored),
    Ctx.move_us_other _ _ _ _ (Ne.symm hv.parent_ne_restored) hv.restored_ne_handle]
  exact hl.us_restored

/-- The take-out binds the extracted handle to the child variable. -/
theorem takeCtx_refOf_child (c : Ctx) (l : Level) :
    (takeCtx c l).refOf l.childVar = some l.child := by
  rw [takeCtx, Ctx.bindOwned_refOf_self]

/-- The continuation's context still owns the extracted array in the parent
variable. -/
theorem callCtx_us_parent {path value : Var} {c : Ctx} {l : Level}
    (hl : LevelCtx path value c l) :
    (callCtx c l).us l.parentVar = .owned := by
  have hv : Vars path value l := hl.toVars
  rw [callCtx, Ctx.move_us_other _ _ _ _ (Ne.symm hv.result_ne_parent) hv.parent_ne_child]
  exact takeCtx_us_parent hl

/-- The continuation's context owns the extracted handle in the result variable. -/
theorem callCtx_us_result (c : Ctx) (l : Level) :
    (callCtx c l).us l.resultVar = .owned := by
  rw [callCtx, Ctx.move_us_y]
  exact takeCtx_us_child c l

/-- The continuation's context leaves the put-back's result variable dead. -/
theorem callCtx_us_restored {path value : Var} {c : Ctx} {l : Level}
    (hl : LevelCtx path value c l) :
    (callCtx c l).us l.restoredVar = .dead := by
  have hv : Vars path value l := hl.toVars
  rw [callCtx, Ctx.move_us_other _ _ _ _ (Ne.symm hv.result_ne_restored)
    (Ne.symm hv.child_ne_restored)]
  exact takeCtx_us_restored hl

/-- The continuation's context still reads the selected index. -/
theorem callCtx_us_idx {path value : Var} {c : Ctx} {l : Level}
    (hl : LevelCtx path value c l) :
    (callCtx c l).us l.indexVar = .scalar := by
  have hv : Vars path value l := hl.toVars
  rw [callCtx, Ctx.move_us_other _ _ _ _ hv.idx_ne_result hv.idx_ne_child,
    takeCtx, Ctx.bindOwned_us_other _ _ _ _ hv.idx_ne_child,
    Ctx.move_us_other _ _ _ _ hv.idx_ne_parent hv.idx_ne_handle]
  exact hl.us_idx

/-- The continuation's context still names the level's array from the parent
variable. -/
theorem callCtx_refOf_parent {path value : Var} {c : Ctx} {l : Level}
    (hl : LevelCtx path value c l) :
    (callCtx c l).refOf l.parentVar = some l.arr := by
  have hv : Vars path value l := hl.toVars
  rw [callCtx, Ctx.move_refOf_other _ _ _ _ (Ne.symm hv.result_ne_parent),
    takeCtx, Ctx.bindOwned_refOf_other _ _ _ _ hv.parent_ne_child, Ctx.move_refOf_y]
  exact hl.ref_arr

/-- The continuation's context binds the extracted handle to the call's result. -/
theorem callCtx_refOf_result (c : Ctx) (l : Level) :
    (callCtx c l).refOf l.resultVar = some l.child := by
  rw [callCtx, Ctx.move_refOf_y]
  exact takeCtx_refOf_child c l

/-- The put-back's exit owns the restored handle. -/
theorem levelFinal_us_restored {path value : Var} {c : Ctx} {l : Level}
    (hl : LevelCtx path value c l) :
    (levelFinal c l).us l.restoredVar = .owned := by
  have hv : Vars path value l := hl.toVars
  rw [levelFinal, Ctx.setUs_other _ _ _ _ (Ne.symm hv.result_ne_restored),
    restoreCtx, Ctx.move_us_y]
  exact callCtx_us_parent hl

/-- The put-back's exit still names the level's array from the restored handle. -/
theorem levelFinal_refOf_restored {path value : Var} {c : Ctx} {l : Level}
    (hl : LevelCtx path value c l) :
    (levelFinal c l).refOf l.restoredVar = some l.arr := by
  rw [levelFinal, Ctx.setUs_refOf, restoreCtx, Ctx.move_refOf_y]
  exact callCtx_refOf_parent hl

/-! ## The level's checker guards -/

/-- The take-out's checker guard at a level's start context. -/
theorem takeGuard {path value : Var} {c : Ctx} {l : Level}
    (hl : LevelCtx path value c l) :
    c.us l.arrayVar = .owned ∧ c.multOf l.arrayVar = 1 ∧
      c.us l.indexVar = .scalar ∧ c.mult l.child = 1 ∧
      c.us l.parentVar = .dead ∧ c.us l.childVar = .dead ∧
      l.parentVar ≠ l.childVar := by
  have hv : Vars path value l := hl.toVars
  refine ⟨hl.us_arr, ?_, hl.us_idx, hl.mult_child, hl.us_parent, hl.us_child,
    hv.parent_ne_child⟩
  simp [Ctx.multOf, hl.ref_arr, hl.mult_arr]

/-- The recursive call's checker guard at the take-out's context. -/
theorem callGuard {path value : Var} {c : Ctx} {l : Level} {body : NCode}
    (hl : LevelCtx path value c l) (hcf : CountFree body = true) :
    (takeCtx c l).us l.childVar = .owned ∧ (takeCtx c l).multOf l.childVar = 1 ∧
      (takeCtx c l).us path = .scalar ∧ (takeCtx c l).us value = .scalar ∧
      (takeCtx c l).us l.resultVar = .dead ∧ CountFree body = true := by
  refine ⟨takeCtx_us_child c l, ?_, takeCtx_us_path hl, takeCtx_us_value hl,
    takeCtx_us_result hl, hcf⟩
  simp [Ctx.multOf, takeCtx_refOf_child, takeCtx_mult, hl.mult_child]

/-- The put-back's checker guard at the continuation's context. -/
theorem putBackGuard {path value : Var} {c : Ctx} {l : Level}
    (hl : LevelCtx path value c l) :
    (callCtx c l).us l.parentVar = .owned ∧
      (callCtx c l).multOf l.parentVar = 1 ∧
      (callCtx c l).us l.resultVar = .owned ∧
      (callCtx c l).multOf l.resultVar = 1 ∧
      (callCtx c l).us l.indexVar = .scalar ∧
      (callCtx c l).us l.restoredVar = .dead ∧
      l.resultVar ≠ l.parentVar ∧ l.resultVar ≠ l.restoredVar := by
  have hv : Vars path value l := hl.toVars
  refine ⟨callCtx_us_parent hl, ?_, callCtx_us_result c l, ?_, callCtx_us_idx hl,
    callCtx_us_restored hl, hv.result_ne_parent, hv.result_ne_restored⟩
  · simp [Ctx.multOf, callCtx_refOf_parent hl, callCtx_mult, hl.mult_arr]
  · simp [Ctx.multOf, callCtx_refOf_result c l, callCtx_mult, hl.mult_child]

/-! ## The tail levels' context discipline -/

/-- Every level after the first starts in the context the recursive call leaves:
the extracted handle is owned and denotes the level's array, the level's own
variables are dead, and its index is one of the call's scalars. -/
theorem levelCtx_isolate {path value : Var} {c : Ctx} {l m : Level}
    (hl : LevelCtx path value c l) (hm : LevelShape path value m)
    (hmul : c.mult m.arr = 1 ∧ c.mult m.child = 1)
    (harr : l.child = m.arr) (hvar : l.childVar = m.arrayVar) :
    LevelCtx path value (bodyCtx path value c l) m := by
  obtain ⟨hca, hpc, hrp, hrc, hrh, hrs, hps, hcs, hph, hch, hsh, hih, hip, hic,
    hir, hap, hav, hpp, hpv, hcp, hcv, hrp2, hrv, hsp, hsv⟩ := hm.toVars
  have hvo : Vars path value l := hl.toVars
  have hpt : path ≠ l.childVar := fun h => hvo.child_ne_path h.symm
  have hvl : value ≠ l.childVar := fun h => hvo.child_ne_value h.symm
  have hpm : path ≠ m.arrayVar := fun h => hap h.symm
  have hvm : value ≠ m.arrayVar := fun h => hav h.symm
  refine ⟨hm.toVars, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp_all [bodyCtx, isolatedCtx]
  · simp_all [bodyCtx, isolatedCtx]
  · exact hmul.1
  · exact hmul.2
  · rcases hm.idx_source with h | h
    · rw [h]; simp_all [bodyCtx, isolatedCtx]
    · rw [h]; simp_all [bodyCtx, isolatedCtx]
  · simp_all [bodyCtx, isolatedCtx]
  · simp_all [bodyCtx, isolatedCtx]
  · simp_all [bodyCtx, isolatedCtx]
  · simp_all [bodyCtx, isolatedCtx]
  · simp_all [bodyCtx, isolatedCtx]
  · simp_all [bodyCtx, isolatedCtx]

/-- Multiplicities are read off the counted heap, so the same counting facts hold
in every context the path reaches. -/
theorem Counts.congr {m m' : Ref → Nat} (h : ∀ r, m r = m' r) :
    ∀ ls : List Level, Counts m ls → Counts m' ls := by
  intro ls
  induction ls with
  | nil => intro _; trivial
  | cons l rest ih =>
      intro hc
      exact ⟨by rw [← h l.arr]; exact hc.1, by rw [← h l.child]; exact hc.2.1,
        ih hc.2.2⟩

/-- The built program exits through its first level's restored handle. -/
theorem retVar_build {path value : Var} {body : NCode} :
    ∀ (rest : List Level) (l : Level),
      retVar (build path value body (l :: rest)) = some l.restoredVar := by
  intro rest l
  rfl

/-- The recursive call's checker rule, as an equation: the guard holds, the state
variable names the extracted handle, the body is admitted from the isolated
context with an owned exit at that handle, and the continuation is admitted from
the context that moves the handle to the call's result. -/
theorem checkNF_callAt_eq {c : Ctx} {fs : List Frame} {state path x result : Var}
    {r : Ref} {body k : NCode} {cb ctx' : Ctx} {y : Var}
    (hx : c.us state = .owned ∧ c.multOf state = 1 ∧ c.us path = .scalar ∧
      c.us x = .scalar ∧ c.us result = .dead ∧ CountFree body = true)
    (hr : c.refOf state = some r) (hopen : openRef fs r = false)
    (hbody : checkNF (isolatedCtx c state path x r) [] body = some cb)
    (hret : retVar body = some y) (hus : cb.us y = .owned)
    (href : cb.refOf y = some r)
    (hk : checkNF (c.move state result) fs k = some ctx') :
    checkNF c fs (.callAt state path x result body k) = some ctx' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hx
  have hg : c.us state = .owned ∧ c.multOf state = 1 ∧ c.us path = .scalar ∧
      c.us x = .scalar ∧ c.us result = .dead ∧ CountFree body = true :=
    ⟨h1, h2, h3, h4, h5, h6⟩
  simp [checkNF, hg, hr, hopen, hbody, hret, hus, href]
  exact hk

/-! ## Checker acceptance of the built path -/

/-- The level's put-back and exit, admitted from the continuation's context. The
frame the take-out pushed is exactly the level's frame, so the put-back pops it
and the exit returns the restored handle. -/
theorem checkNF_levelTail {path value : Var} {c : Ctx} {l : Level}
    (hl : LevelCtx path value c l) :
    checkNF (callCtx c l) [{ arr := l.arr, idx := l.indexVar, elem := l.child }]
        (.putBack l.parentVar l.resultVar l.indexVar l.restoredVar
          (.ret l.restoredVar)) = some (levelFinal c l) := by
  refine (checkNF_putBack (callCtx c l)
    [{ arr := l.arr, idx := l.indexVar, elem := l.child }]
    { arr := l.arr, idx := l.indexVar, elem := l.child } []
    l.parentVar l.resultVar l.indexVar l.restoredVar (.ret l.restoredVar) l.arr l.child
    (putBackGuard hl) (callCtx_refOf_parent hl) (callCtx_refOf_result c l)
    ⟨rfl, rfl, rfl⟩).trans ?_
  have h : (((callCtx c l).move l.parentVar l.restoredVar).setUs l.resultVar .dead).us
      l.restoredVar = .owned := levelFinal_us_restored hl
  simp [checkNF, h, levelFinal, restoreCtx]

/-- Checker acceptance of the built path, derived from the level discipline and
the leaf's own admission. The final context is the first level's `levelFinal`:
the built program's exit is that level's restored handle. -/
theorem checkNF_build {path value : Var} {body : NCode} :
    ∀ (rest : List Level) (l : Level) {c cb : Ctx} {y : Var} {tip : Ref},
      LevelCtx path value c l → Shapes path value rest →
      Counts c.mult rest → Chained (l :: rest) →
      checkNF (tailCtx path value c (l :: rest)) [] body = some cb →
      retVar body = some y → cb.us y = .owned → cb.refOf y = some tip →
      EndsAt tip (l :: rest) → CountFree body = true →
      checkNF c [] (build path value body (l :: rest)) = some (levelFinal c l) := by
  intro rest
  induction rest with
  | nil =>
      intro l c cb y tip hl _ _ _ hleaf hret hus href hends hcf
      have htake : checkNF c [] (.takeOut l.arrayVar l.indexVar l.parentVar l.childVar
          l.child (.callAt l.childVar path value l.resultVar body
            (.putBack l.parentVar l.resultVar l.indexVar l.restoredVar
              (.ret l.restoredVar)))) =
          checkNF (takeCtx c l) [{ arr := l.arr, idx := l.indexVar, elem := l.child }]
            (.callAt l.childVar path value l.resultVar body
              (.putBack l.parentVar l.resultVar l.indexVar l.restoredVar
                (.ret l.restoredVar))) :=
        checkNF_takeOut c [] l.arrayVar l.indexVar l.parentVar l.childVar l.child
          _ l.arr (takeGuard hl) hl.ref_arr hl.child_ne_arr (by simp [openRef])
      have hbody : checkNF (bodyCtx path value c l) [] body = some cb := by
        simpa [tailCtx, bodyCtx] using hleaf
      have href' : cb.refOf y = some l.child := by
        have h : l.child = tip := hends
        rw [h]
        exact href
      have hopen : openRef [{ arr := l.arr, idx := l.indexVar, elem := l.child }]
          l.child = false := by
        simp [openRef, Ne.symm hl.child_ne_arr]
      have hk := checkNF_levelTail (path := path) (value := value) (c := c) (l := l) hl
      have hcall := checkNF_callAt_eq (c := takeCtx c l)
        (fs := [{ arr := l.arr, idx := l.indexVar, elem := l.child }])
        (state := l.childVar) (path := path) (x := value) (result := l.resultVar)
        (r := l.child) (body := body)
        (k := .putBack l.parentVar l.resultVar l.indexVar l.restoredVar
          (.ret l.restoredVar)) (cb := cb) (y := y) (ctx' := levelFinal c l)
        (callGuard hl hcf) (takeCtx_refOf_child c l) hopen hbody hret hus href' hk
      simpa [build] using (htake.trans hcall)
  | cons m rest' ih =>
      intro l c cb y tip hl hshapes hcounts hchain hleaf hret hus href hends hcf
      have hchain' : Chained (m :: rest') := hchain.2.2
      have harr : l.child = m.arr := hchain.1
      have hvar : l.childVar = m.arrayVar := hchain.2.1
      have hmul : c.mult m.arr = 1 ∧ c.mult m.child = 1 :=
        ⟨hcounts.1, hcounts.2.1⟩
      have hl' : LevelCtx path value (bodyCtx path value c l) m :=
        levelCtx_isolate hl hshapes.1 hmul harr hvar
      have hcounts' : Counts (bodyCtx path value c l).mult rest' :=
        Counts.congr (fun _ => rfl) rest' hcounts.2.2
      have hbody : checkNF (bodyCtx path value c l) []
          (build path value body (m :: rest')) = some (levelFinal (bodyCtx path value c l) m) :=
        ih m hl' hshapes.2 hcounts' hchain' (by simpa [tailCtx] using hleaf)
          hret hus href (by simpa [EndsAt] using hends) hcf
      have htake : checkNF c [] (.takeOut l.arrayVar l.indexVar l.parentVar l.childVar
          l.child (.callAt l.childVar path value l.resultVar (build path value body (m :: rest'))
            (.putBack l.parentVar l.resultVar l.indexVar l.restoredVar
              (.ret l.restoredVar)))) =
          checkNF (takeCtx c l) [{ arr := l.arr, idx := l.indexVar, elem := l.child }]
            (.callAt l.childVar path value l.resultVar (build path value body (m :: rest'))
              (.putBack l.parentVar l.resultVar l.indexVar l.restoredVar
                (.ret l.restoredVar))) :=
        checkNF_takeOut c [] l.arrayVar l.indexVar l.parentVar l.childVar l.child
          _ l.arr (takeGuard hl) hl.ref_arr hl.child_ne_arr (by simp [openRef])
      have hret' : retVar (build path value body (m :: rest')) = some m.restoredVar :=
        retVar_build rest' m
      have hus' : (levelFinal (bodyCtx path value c l) m).us m.restoredVar = .owned :=
        levelFinal_us_restored hl'
      have href' : (levelFinal (bodyCtx path value c l) m).refOf m.restoredVar =
          some l.child := by
        rw [levelFinal_refOf_restored hl', harr]
      have hopen : openRef [{ arr := l.arr, idx := l.indexVar, elem := l.child }]
          l.child = false := by
        simp [openRef, Ne.symm hl.child_ne_arr]
      have hk := checkNF_levelTail (path := path) (value := value) (c := c) (l := l) hl
      have hcall := checkNF_callAt_eq (c := takeCtx c l)
        (fs := [{ arr := l.arr, idx := l.indexVar, elem := l.child }])
        (state := l.childVar) (path := path) (x := value) (result := l.resultVar)
        (r := l.child) (body := build path value body (m :: rest'))
        (k := .putBack l.parentVar l.resultVar l.indexVar l.restoredVar
          (.ret l.restoredVar)) (cb := levelFinal (bodyCtx path value c l) m)
        (y := m.restoredVar) (ctx' := levelFinal c l)
        (callGuard hl (by rw [countFree_build]; exact hcf))
        (takeCtx_refOf_child c l) hopen hbody hret' hus' href' hk
      simpa [build] using (htake.trans hcall)

/-! ## The take-out does not disturb the tip's footprint -/

/-- A footprint at the tip survives a take-out that empties a cell the tip cannot
reach: every cell the derivation reads is still where it was. -/
theorem MutableFootprint.blank_mono {H : Heap} {l : Level} {tip : Ref}
    (hne : ¬ MutableFootprint H tip l.arr) :
    ∀ {q : Ref}, MutableFootprint H tip q → MutableFootprint (blankLevel H l) tip q := by
  intro q h
  induction h with
  | root hcell hpers =>
      have htip : tip ≠ l.arr := by
        intro he
        exact hne (he ▸ MutableFootprint.root hcell hpers)
      exact MutableFootprint.root (by rw [blankLevel_cells_ne htip]; exact hcell) hpers
  | step hr hcell hpers hmem hcell' hpers' ih =>
      have hstep : MutableFootprint H tip _ :=
        MutableFootprint.step hr hcell hpers hmem hcell' hpers'
      have hrne : ∀ {r : Ref}, MutableFootprint H tip r → r ≠ l.arr := by
        intro r hr' he
        exact hne (he ▸ hr')
      have hr'ne : (fun r => r) _ ≠ l.arr := fun he => hne (he ▸ hstep)
      exact MutableFootprint.step ih
        (by rw [blankLevel_cells_ne (hrne hr)]; exact hcell) hpers hmem
        (by rw [blankLevel_cells_ne hr'ne]; exact hcell') hpers'

/-- A program whose extraction annotations lie in the tip's footprint keeps them
there through a take-out that does not disturb that footprint. -/
theorem AnnotationsIn.blank {H : Heap} {l : Level} {tip : Ref} :
    ∀ {code : NCode}, ¬ MutableFootprint H tip l.arr → AnnotationsIn H tip code →
      AnnotationsIn (blankLevel H l) tip code := by
  intro code
  induction code with
  | base c => intro _ _; trivial
  | ret x => intro _ _; trivial
  | takeOut a i fst snd e k ih =>
      intro hne h
      exact ⟨MutableFootprint.blank_mono hne h.1, ih hne h.2⟩
  | putBack a e i result k ih => intro hne h; exact ih hne h
  | callAt state path x result body k ihbody ihk =>
      intro hne h
      exact ⟨ihbody hne h.1, ihk hne h.2⟩

/-! ## The heap shape the path still needs -/

/-- The remaining heap-shape facts, level by level: the extracted child's mutable
footprint does not contain the parent array, so the suspended parent is outside
the call's reach; and the tip cannot reach back up to a level the path emptied, so
the leaf's annotations survive that take-out. Both are properties of the object
graph rather than of the path's syntax. -/
def Acyclic (tip : Ref) : Heap → List Level → Prop
  | _, [] => True
  | H, l :: rest =>
      ¬ MutableFootprint (blankLevel H l) l.child l.arr ∧
      ¬ MutableFootprint H tip l.arr ∧
      Acyclic tip (blankLevel H l) rest

/-- Every step of the path keeps the tip live when it starts live. -/
theorem Live.blank {H : Heap} {l : Level} {tip : Ref}
    (hne : ¬ MutableFootprint H tip l.arr) (hlive : Live H tip) :
    Live (blankLevel H l) tip := by
  obtain ⟨o, hcell, hpers⟩ := hlive
  have htip : tip ≠ l.arr := by
    intro he
    exact hne (he ▸ MutableFootprint.root hcell hpers)
  exact ⟨o, by rw [blankLevel_cells_ne htip]; exact hcell, hpers⟩

/-! ## Leaf agreement of a constructed leaf body -/

/-- The agreement of the leaf body that extracts the selected slot, restores it,
and runs a scalar block: derived from the extraction's own slot facts. The only
premises are where the environment binds the handle and the index, which object
the slot holds, what the slot holds, and that the take-out's two binders and the
index are distinct. -/
theorem agrees_extract_restore {H : Heap} {env : Env} {code : Code}
    {r : Ref} {o : Obj} {idx : Nat} {e : Ref} {a i fst snd result : Var}
    (ha : env a = some (.ref r)) (hi : env i = some (.scalar idx))
    (hcell : H.cells r = some o) (hslot : o.fields[idx]? = some (.ref e))
    (hfs : fst ≠ snd) (hif : i ≠ fst) (his : i ≠ snd) :
    Agrees H env (.takeOut a i fst snd e (.putBack fst snd i result (.base code))) := by
  refine ⟨r, o, idx, ha, hi, hcell, hslot, ?_⟩
  refine ⟨r, e, { o with fields := o.fields.setIfInBounds idx (.scalar 0) }, idx,
    ?_, ?_, ?_, Heap.set_self _ _ _, trivial⟩
  · rw [Env.set_other _ _ _ _ hfs, Env.set_self]
  · rw [Env.set_self]
  · rw [Env.set_other _ _ _ _ his, Env.set_other _ _ _ _ hif]
    exact hi

/-! ## The child-call contract at every level -/

/-- `ChildConfined` at every level of a supported path, derived from the remaining
levels' contract. The preservation half is `callAt_frame_confined`: the state's
head is the extracted child, its annotations are in that child's footprint
(`annotationsIn_of_path`, lifted through the take-out by `AnnotationsIn.blank`),
its body is admitted (`checkNF_build`), its obligation is derived
(`takeOutsOK_of_inv`), and its invariant is the take-out's own (`inv_isolated`).
The separation and non-reachability halves are the heap-shape fact `Acyclic`.

The leaf body itself is not derived: its checker acceptance, its count-freedom,
its exit variable and its annotation are the premises `checkNF`, `retVar`,
`cb.us`/`cb.refOf` and `AnnotationsIn` below. They are the emitted callee's
contract, not facts the path's level list determines. -/
theorem childConfined_of_path {path value : Var} {body : NCode} :
    ∀ (rest : List Level) (l : Level) {H : Heap} {env : Env} {c : Ctx} {tip : Ref}
      {cb : Ctx} {y : Var},
      Slots H (l :: rest) → Chained (l :: rest) → DistinctArrays (l :: rest) →
      EnvOK path value env (l :: rest) →
      leafAgrees path value body (blankLevel H l)
        (isolateEnv (bindLevel env l) l.childVar path value) rest →
      LevelCtx path value c l → Shapes path value rest → Counts c.mult rest →
      Acyclic tip H (l :: rest) → Live H tip → AnnotationsIn H tip body →
      checkNF (tailCtx path value c (l :: rest)) [] body = some cb →
      retVar body = some y → cb.us y = .owned → cb.refOf y = some tip →
      EndsAt tip (l :: rest) → CountFree body = true → Inv H env c →
      ChildConfined path value body H env (l :: rest) := by
  intro rest
  induction rest with
  | nil =>
      intro l H env c tip cb y hslots hchain hdist henv hleaf hl hshapes hcounts
        hacyc hlive hann hcheck hret hus href hends hcf hi
      obtain ⟨hsep, hnoBack, -⟩ := hacyc
      have hchild : l.child = tip := hends
      have hi_take : Inv (blankLevel H l) (bindLevel env l) (takeCtx c l) :=
        inv_after_takeOut hi hl.us_arr hl.ref_arr hl.mult_child
          (hslots l (by simp)).1
      have hi_iso : Inv (blankLevel H l)
          (isolateEnv (bindLevel env l) l.childVar path value)
          (bodyCtx path value c l) :=
        inv_isolated hi_take (takeCtx_us_child c l) (takeCtx_refOf_child c l)
          (takeCtx_us_path hl) (takeCtx_us_value hl)
      have hann' : AnnotationsIn (blankLevel H l) l.child body := by
        have h := AnnotationsIn.blank (l := l) (tip := tip) hnoBack hann
        rwa [← hchild] at h
      have hcheck' : checkNF (bodyCtx path value c l) [] body = some cb := by
        simpa [tailCtx, bodyCtx] using hcheck
      have hret' : ∃ z, retVar body = some z ∧ cb.us z = .owned ∧
          cb.refOf z = some l.child := by
        refine ⟨y, hret, hus, ?_⟩
        rw [hchild]
        exact href
      have hok : TakeOutsOK (blankLevel H l)
          (isolateEnv (bindLevel env l) l.childVar path value) body :=
        takeOutsOK_of_inv hi_iso (by simpa [leafAgrees] using hleaf) hcheck'
      refine ⟨hsep, ?_, trivial⟩
      intro H' envb vb wsb hrun q hq
      obtain ⟨Hc, envc, vc, wsc, hcrun, -, -, hconf⟩ :=
        callAt_frame_confined (c := c) (state := l.childVar) (path := path)
          (x := value) (r := l.child) (body := body) (H := blankLevel H l)
          (env := isolateEnv (bindLevel env l) l.childVar path value) (cb := cb)
          hann' hcheck' hret' hi_iso hok
      have hrun' : runN body (isolateEnv (bindLevel env l) l.childVar path value)
          (blankLevel H l) = .done H' envb vb wsb := by simpa [build] using hrun
      rw [hcrun] at hrun'
      injection hrun' with hH _ _ _
      subst hH
      exact hconf q hq
  | cons m rest' ih =>
      intro l H env c tip cb y hslots hchain hdist henv hleaf hl hshapes hcounts
        hacyc hlive hann hcheck hret hus href hends hcf hi
      obtain ⟨hsep, hnoBack, hacyc'⟩ := hacyc
      obtain ⟨harr, hvar, hchain'⟩ := hchain
      obtain ⟨hdistL, hdist'⟩ := hdist
      obtain ⟨henv0, henv'⟩ := henv
      have hslots' : Slots (blankLevel H l) (m :: rest') :=
        Slots.blank (fun k hk => hslots k (List.mem_cons_of_mem _ hk)) hdistL
      have hlive' : Live (blankLevel H l) tip := Live.blank hnoBack hlive
      have hann' : AnnotationsIn (blankLevel H l) tip body :=
        AnnotationsIn.blank (l := l) hnoBack hann
      have hi_take : Inv (blankLevel H l) (bindLevel env l) (takeCtx c l) :=
        inv_after_takeOut hi hl.us_arr hl.ref_arr hl.mult_child
          (hslots l (by simp)).1
      have hi_iso : Inv (blankLevel H l)
          (isolateEnv (bindLevel env l) l.childVar path value)
          (bodyCtx path value c l) :=
        inv_isolated hi_take (takeCtx_us_child c l) (takeCtx_refOf_child c l)
          (takeCtx_us_path hl) (takeCtx_us_value hl)
      have hmul : c.mult m.arr = 1 ∧ c.mult m.child = 1 := ⟨hcounts.1, hcounts.2.1⟩
      have hl' : LevelCtx path value (bodyCtx path value c l) m :=
        levelCtx_isolate hl hshapes.1 hmul harr hvar
      have hcounts' : Counts (bodyCtx path value c l).mult rest' :=
        Counts.congr (fun _ => rfl) rest' hcounts.2.2
      have hends' : EndsAt tip (m :: rest') := hends
      have hconf' : ChildConfined path value body (blankLevel H l)
          (isolateEnv (bindLevel env l) l.childVar path value) (m :: rest') :=
        ih m hslots' hchain' hdist' henv' (by simpa [leafAgrees] using hleaf) hl' hshapes.2
          hcounts' hacyc' hlive' hann' (by simpa [tailCtx] using hcheck) hret hus href
          hends' hcf (by simpa using hi_iso)
      have hagree : Agrees (blankLevel H l)
          (isolateEnv (bindLevel env l) l.childVar path value)
          (build path value body (m :: rest')) :=
        agrees_of_path rest' m hslots' hchain' hdist' henv' (by simpa [leafAgrees] using hleaf)
          hconf'
      have hcheck' : checkNF (bodyCtx path value c l) [] (build path value body (m :: rest')) =
          some (levelFinal (bodyCtx path value c l) m) :=
        checkNF_build rest' m hl' hshapes.2 hcounts' hchain' (by simpa [tailCtx] using hcheck)
          hret hus href hends' hcf
      have hok : TakeOutsOK (blankLevel H l)
          (isolateEnv (bindLevel env l) l.childVar path value)
          (build path value body (m :: rest')) :=
        takeOutsOK_of_inv hi_iso hagree hcheck'
      have hannCall : AnnotationsIn (blankLevel H l) l.child
          (build path value body (m :: rest')) :=
        annotationsIn_of_path rest' m l.child tip hslots' hchain' harr.symm hends'
          hlive' hann'
      have hret' : ∃ z, retVar (build path value body (m :: rest')) = some z ∧
          (levelFinal (bodyCtx path value c l) m).us z = .owned ∧
          (levelFinal (bodyCtx path value c l) m).refOf z = some l.child := by
        refine ⟨m.restoredVar, retVar_build rest' m, levelFinal_us_restored hl', ?_⟩
        rw [levelFinal_refOf_restored hl', harr]
      refine ⟨hsep, ?_, hconf'⟩
      intro H' envb vb wsb hrun q hq
      obtain ⟨Hc, envc, vc, wsc, hcrun, -, -, hconf⟩ :=
        callAt_frame_confined (c := c) (state := l.childVar) (path := path)
          (x := value) (r := l.child) (body := build path value body (m :: rest'))
          (H := blankLevel H l)
          (env := isolateEnv (bindLevel env l) l.childVar path value)
          (cb := levelFinal (bodyCtx path value c l) m)
          hannCall hcheck' hret' hi_iso hok
      rw [hcrun] at hrun
      injection hrun with hH _ _ _
      subst hH
      exact hconf q hq

/-! ## The references a run leaves in a footprint cell -/

/-- Replacing an array entry leaves the other entries alone. -/
theorem mem_setIfInBounds {xs : Array Val} {i : Nat} {v x : Val} :
    x ∈ xs.setIfInBounds i v → x = v ∨ x ∈ xs := by
  intro h
  rw [Array.mem_iff_getElem?] at h ⊢
  obtain ⟨j, hj⟩ := h
  rw [Array.getElem?_setIfInBounds] at hj
  split at hj
  · split at hj
    · exact Or.inl (Option.some.inj hj).symm
    · exact absurd hj (by simp)
  · exact Or.inr ⟨j, hj⟩

/-- The references of a written field array are the old references plus the
written value's. -/
theorem fieldRefs_setIfInBounds {o : Obj} {i : Nat} {v : Val} {z : Ref}
    (h : z ∈ fieldRefs { o with fields := o.fields.setIfInBounds i v }) :
    z ∈ fieldRefs o ∨ z ∈ refsOf v := by
  obtain ⟨x, hx, hzx⟩ := List.mem_flatMap.mp h
  rcases mem_setIfInBounds (xs := o.fields) (i := i) (v := v) (x := x)
    (by rwa [← Array.mem_toList_iff]) with rfl | hx'
  · exact Or.inr hzx
  · exact Or.inl (List.mem_flatMap.mpr ⟨x, by rwa [Array.mem_toList_iff], hzx⟩)

/-- A scalar store adds no reference to a cell's fields. -/
theorem fieldRefs_set_scalar {o : Obj} {i : Nat} {n : Nat} {z : Ref}
    (h : z ∈ fieldRefs { o with fields := o.fields.setIfInBounds i (.scalar n) }) :
    z ∈ fieldRefs o := by
  rcases fieldRefs_setIfInBounds h with h' | h'
  · exact h'
  · simp [refsOf] at h'

/-- Every reference the current heap leaves in a footprint cell's fields is a
footprint member. -/
def SlotRefs (H Hc : Heap) (root : Ref) : Prop :=
  ∀ q o', MutableFootprint H root q → Hc.cells q = some o' → ∀ z ∈ fieldRefs o',
    MutableFootprint H root z

/-- The references a written field array holds, as a `set!`-shaped object. -/
theorem fieldRefs_set_ref {o : Obj} {i : Nat} {e z : Ref}
    (h : z ∈ fieldRefs { o with fields := o.fields.setIfInBounds i (.ref e) }) :
    z ∈ fieldRefs o ∨ z = e := by
  rcases fieldRefs_setIfInBounds h with h' | h'
  · exact Or.inl h'
  · exact Or.inr (by simpa [refsOf] using h')

/-- Writing one cell keeps the field-reference account when every reference the
new cell holds is either one the old cell held or a footprint member. -/
theorem SlotRefs.set_obj {H Hc : Heap} {root r : Ref} {o o' : Obj}
    (h : SlotRefs H Hc root) (hcell : Hc.cells r = some o)
    (hsub : ∀ z, z ∈ fieldRefs o' → z ∈ fieldRefs o ∨ MutableFootprint H root z) :
    SlotRefs H (Hc.set r o') root := by
  intro q oq hq hq' z hz
  by_cases hqr : q = r
  · subst hqr
    rw [Heap.set_self] at hq'
    injection hq' with hoo
    subst hoo
    rcases hsub z hz with h' | h'
    · exact h q o hq hcell z h'
    · exact h'
  · rw [Heap.set_other _ _ _ _ hqr] at hq'
    exact h q oq hq hq' z hz

/-- Counting a cell up or down does not change its fields. -/
theorem inc_fields {H : Heap} {r q : Ref} {n : Nat} {o' : Obj}
    (h : (H.inc r n).cells q = some o') :
    ∃ o, H.cells q = some o ∧ o'.fields = o.fields := by
  unfold Heap.inc at h
  cases ho : H.cells r with
  | none =>
      rw [ho] at h
      exact ⟨o', h, rfl⟩
  | some o =>
      rw [ho] at h
      by_cases hqr : q = r
      · subst hqr
        rw [Heap.set_self] at h
        injection h with hh
        exact ⟨o, ho, by rw [← hh]⟩
      · exact ⟨o', by rwa [Heap.set_other _ _ _ _ hqr] at h, rfl⟩

theorem dec_fields {H : Heap} {r q : Ref} {n : Nat} {o' : Obj}
    (h : (H.dec r n).cells q = some o') :
    ∃ o, H.cells q = some o ∧ o'.fields = o.fields := by
  unfold Heap.dec at h
  cases ho : H.cells r with
  | none =>
      rw [ho] at h
      exact ⟨o', h, rfl⟩
  | some o =>
      rw [ho] at h
      by_cases hqr : q = r
      · subst hqr
        rw [Heap.set_self] at h
        injection h with hh
        exact ⟨o, ho, by rw [← hh]⟩
      · exact ⟨o', by rwa [Heap.set_other _ _ _ _ hqr] at h, rfl⟩

theorem SlotRefs.inc {H Hc : Heap} {root : Ref} {r : Ref} {n : Nat}
    (h : SlotRefs H Hc root) : SlotRefs H (Hc.inc r n) root := by
  intro q o' hq hq' z hz
  obtain ⟨o, ho, hf⟩ := inc_fields hq'
  simp only [fieldRefs] at hz ⊢
  rw [hf] at hz
  exact h q o hq ho z hz

theorem SlotRefs.dec {H Hc : Heap} {root : Ref} {r : Ref} {n : Nat}
    (h : SlotRefs H Hc root) : SlotRefs H (Hc.dec r n) root := by
  intro q o' hq hq' z hz
  obtain ⟨o, ho, hf⟩ := dec_fields hq'
  simp only [fieldRefs] at hz ⊢
  rw [hf] at hz
  exact h q o hq ho z hz

/-- The write an `addWrite` extended a trace with is in the trace. -/
theorem addWrite_mem {r : Res} {w : Write} {H' : Heap} {env' : Env} {v : Val}
    {ws : List Write} (h : r.addWrite w = .done H' env' v ws) : w ∈ ws := by
  cases r with
  | done H0 env0 v0 ws0 =>
      simp only [Res.addWrite] at h
      injection h with _ _ _ hws
      rw [← hws]
      exact List.mem_cons_self
  | fault _ _ _ _ => simp [Res.addWrite] at h

/-- A completed `addWrite` is the run it extended plus the write that extended it. -/
theorem addWrite_split {r : Res} {w : Write} {H' : Heap} {env' : Env} {v : Val}
    {ws : List Write} (h : r.addWrite w = .done H' env' v ws) :
    ∃ ws0, r = .done H' env' v ws0 ∧ ws = w :: ws0 := by
  cases r with
  | done H0 env0 v0 ws0 =>
      simp only [Res.addWrite] at h
      injection h with h1 h2 h3 hws
      subst h1; subst h2; subst h3
      exact ⟨ws0, rfl, hws.symm⟩
  | fault _ _ _ _ => simp [Res.addWrite] at h

/-- Every reference a program writes into a slot is a footprint member. A
straight-line block stores scalars, a take-out writes the placeholder scalar, and
a put-back writes the element the environment binds. The predicate is stated on
the environment each step reads, so it tracks the bindings the run performs. -/
def WritesIn (H : Heap) (root : Ref) : Env → NCode → Prop
  | _, .base _ => True
  | _, .ret _ => True
  | env, .takeOut a _ fst snd e k =>
      ∃ r, env a = some (.ref r) ∧
        WritesIn H root ((env.set fst (.ref r)).set snd (.ref e)) k
  | env, .putBack a e _ result k =>
      (∀ re, env e = some (.ref re) → MutableFootprint H root re) ∧
      (∀ r, env a = some (.ref r) → WritesIn H root (env.set result (.ref r)) k)
  | env, .callAt state path x result body k =>
      (∀ r, env state = some (.ref r) →
        WritesIn H root (isolateEnv env state path x) body ∧
        WritesIn H root (env.set result (.ref r)) k)

/-! ## Straight-line blocks -/

/-- A straight-line block preserves the field-reference account when every write
it performs selects the exclusive branch: its only store is a scalar, and a count
change does not touch fields. -/
theorem slotRefs_run {code : Code} :
    ∀ {env Hc Hc' env' v ws H root},
      SlotRefs H Hc root → run code env Hc = .done Hc' env' v ws →
      (∀ w ∈ ws, w.2 = true) → SlotRefs H Hc' root := by
  induction code with
  | «let» x w k ih =>
      intro env Hc Hc' env' v ws H root hsl hrun hall
      cases w with
      | lit n => exact ih hsl (by simpa [run] using hrun) hall
      | size a =>
          unfold run at hrun
          split at hrun
          · split at hrun
            · exact ih hsl hrun hall
            · simp at hrun
          · simp at hrun
      | isShared z =>
          unfold run at hrun
          split at hrun
          · exact ih hsl hrun hall
          · simp at hrun
      | checkAlias z =>
          unfold run at hrun
          split at hrun
          · split at hrun
            · exact ih hsl hrun hall
            · simp at hrun
          · simp at hrun
  | inc x n k ih =>
      intro env Hc Hc' env' v ws H root hsl hrun hall
      unfold run at hrun
      split at hrun
      · exact ih (SlotRefs.inc hsl) hrun hall
      · simp at hrun
  | dec x n k ih =>
      intro env Hc Hc' env' v ws H root hsl hrun hall
      unfold run at hrun
      split at hrun
      · exact ih (SlotRefs.dec hsl) hrun hall
      · simp at hrun
  | check x k ih =>
      intro env Hc Hc' env' v ws H root hsl hrun hall
      unfold run at hrun
      split at hrun
      · split at hrun
        · exact ih hsl hrun hall
        · simp at hrun
      · simp at hrun
  | setArr x _ v' k ih =>
      intro env Hc Hc' env' v ws H root hsl hrun hall
      unfold run at hrun
      split at hrun
      · split at hrun
        · simp at hrun
        · split at hrun
          · -- exclusive: the store is a scalar
            obtain ⟨ws0, hrun', hws⟩ := addWrite_split hrun
            refine ih (SlotRefs.set_obj hsl (by assumption) (fun z hz => Or.inl
              (fieldRefs_set_scalar hz))) hrun' ?_
            intro w hw
            exact hall w (by rw [hws]; exact List.mem_cons_of_mem _ hw)
          · -- copy: the trace records the shared write, which the run cannot have
            exfalso
            exact absurd (hall _ (addWrite_mem hrun)) (by simp)
      · simp at hrun
  | ret x =>
      intro env Hc Hc' env' v ws H root hsl hrun hall
      simp only [run] at hrun
      injection hrun with h1 _ _ _
      subst h1
      exact hsl

/-- A completed `addWrites` is the run it extended followed by the writes it
appended. -/
theorem addWrites_split {r : Res} {ws : List Write} {H' : Heap} {env' : Env}
    {v : Val} {ws' : List Write} (h : addWrites r ws = .done H' env' v ws') :
    ∃ ws0, r = .done H' env' v ws0 ∧ ws' = ws ++ ws0 := by
  cases r with
  | done H0 env0 v0 ws0 =>
      unfold addWrites at h
      injection h with h1 h2 h3 hws
      subst h1; subst h2; subst h3
      exact ⟨ws0, rfl, hws.symm⟩
  | fault _ _ _ _ => simp [addWrites] at h

/-- A nested program preserves the field-reference account when every write it
performs selects the exclusive branch and every reference it writes is a
footprint member. -/
theorem slotRefs_runN {code : NCode} :
    ∀ {env Hc Hc' env' v ws H root},
      SlotRefs H Hc root → WritesIn H root env code →
      runN code env Hc = .done Hc' env' v ws →
      (∀ w ∈ ws, w.2 = true) → SlotRefs H Hc' root := by
  induction code with
  | base code =>
      intro env Hc Hc' env' v ws H root hsl _ hrun hall
      exact slotRefs_run hsl hrun hall
  | takeOut a i fst snd e k ih =>
      intro env Hc Hc' env' v ws H root hsl hw hrun hall
      obtain ⟨r0, hw0, hw'⟩ := hw
      cases hi : env i with
      | none => simp [runN, hw0, hi] at hrun
      | some vi =>
          cases vi with
          | ref rr => simp [runN, hw0, hi] at hrun
          | erased => simp [runN, hw0, hi] at hrun
          | scalar idx =>
              cases hc : Hc.cells r0 with
              | none => simp [runN, hw0, hi, hc] at hrun
              | some o =>
                  cases hslot : o.fields[idx]? with
                  | none => simp [runN, hw0, hi, hc, hslot] at hrun
                  | some vf =>
                      cases vf with
                      | scalar n => simp [runN, hw0, hi, hc, hslot] at hrun
                      | erased => simp [runN, hw0, hi, hc, hslot] at hrun
                      | ref e' =>
                          by_cases he : e' = e
                          · simp only [runN, hw0, hi, hc, hslot, he] at hrun
                            have hsl' : SlotRefs H
                                (Hc.set r0 { o with
                                  fields := o.fields.setIfInBounds idx (.scalar 0) }) root :=
                              SlotRefs.set_obj hsl hc
                                (fun z hz => Or.inl (fieldRefs_set_scalar hz))
                            exact ih hsl' hw' hrun hall
                          · simp [runN, hw0, hi, hc, hslot, he] at hrun
  | putBack a e i result k ih =>
      intro env Hc Hc' env' v ws H root hsl hw hrun hall
      obtain ⟨hwe, hwa⟩ := hw
      cases ha : env a with
      | none => simp [runN, ha] at hrun
      | some va =>
          cases va with
          | scalar n => simp [runN, ha] at hrun
          | erased => simp [runN, ha] at hrun
          | ref r =>
              cases he : env e with
              | none => simp [runN, ha, he] at hrun
              | some ve =>
                  cases ve with
                  | scalar n => simp [runN, ha, he] at hrun
                  | erased => simp [runN, ha, he] at hrun
                  | ref re =>
                      cases hi : env i with
                      | none => simp [runN, ha, he, hi] at hrun
                      | some vi =>
                          cases vi with
                          | ref rr => simp [runN, ha, he, hi] at hrun
                          | erased => simp [runN, ha, he, hi] at hrun
                          | scalar idx =>
                              cases hc : Hc.cells r with
                              | none => simp [runN, ha, he, hi, hc] at hrun
                              | some o =>
                                  simp only [runN, ha, he, hi, hc] at hrun
                                  have hsl' : SlotRefs H
                                      (Hc.set r { o with
                                        fields := o.fields.setIfInBounds idx (.ref re) }) root :=
                                    SlotRefs.set_obj hsl hc (fun z hz => by
                                      rcases fieldRefs_set_ref hz with h | h
                                      · exact Or.inl h
                                      · exact Or.inr (h ▸ hwe re he))
                                  exact ih hsl' (hwa r ha) hrun hall
  | callAt state path x result body k ihbody ihk =>
      intro env Hc Hc' env' v ws H root hsl hw hrun hall
      cases hs : env state with
      | none => simp [runN, hs] at hrun
      | some vs =>
          cases vs with
          | scalar n => simp [runN, hs] at hrun
          | erased => simp [runN, hs] at hrun
          | ref r =>
              cases hp : env path with
              | none => simp [runN, hs, hp] at hrun
              | some vp =>
                  cases vp with
                  | ref rr => simp [runN, hs, hp] at hrun
                  | erased => simp [runN, hs, hp] at hrun
                  | scalar np =>
                      cases hx : env x with
                      | none => simp [runN, hs, hp, hx] at hrun
                      | some vx =>
                          cases vx with
                          | ref rr => simp [runN, hs, hp, hx] at hrun
                          | erased => simp [runN, hs, hp, hx] at hrun
                          | scalar nx =>
                              cases hex : Hc.exclusive? r with
                              | false => simp [runN, hs, hp, hx, hex] at hrun
                              | true =>
                                  cases hb : runN body (isolateEnv env state path x) Hc with
                                  | fault Hf envf ff wsf =>
                                      simp [runN, hs, hp, hx, hex, hb] at hrun
                                  | done Hb envb vb wsb =>
                                      simp only [runN, hs, hp, hx, hex, hb] at hrun
                                      obtain ⟨hwb1, hwb2⟩ := hw r hs
                                      obtain ⟨ws0, hcont, hws⟩ := addWrites_split hrun
                                      have hslb : SlotRefs H Hb root :=
                                        ihbody hsl hwb1 hb (fun w hw' => hall w (by
                                          rw [hws]
                                          exact List.mem_append_left _ hw'))
                                      exact ihk hslb hwb2 hcont (fun w hw' => hall w (by
                                        rw [hws]
                                        exact List.mem_append_right _ hw'))
  | ret x =>
      intro env Hc Hc' env' v ws H root hsl _ hrun hall
      simp only [runN] at hrun
      injection hrun with h1 _ _ _
      subst h1
      exact hsl

/-! ## The leaf's write account, lifted along the path -/

/-- The environments the innermost body runs in: each level's take-out binds the
extracted handles, and the recursive call re-exposes only its own three
variables. -/
def tailEnv (path value : Var) (env : Env) : List Level → Env
  | [] => env
  | l :: rest =>
      tailEnv path value (isolateEnv (bindLevel env l) l.childVar path value) rest

/-- The built path's own writes are accounted by the path: each take-out writes
the placeholder scalar, each put-back writes the extracted child — a footprint
member — and each call's body is the remaining levels. Only the leaf body's own
writes are supplied. -/
theorem writesIn_build {path value : Var} {body : NCode} :
    ∀ (rest : List Level) (l : Level) {H : Heap} {env : Env} {root : Ref},
      (∀ m ∈ (l :: rest), MutableFootprint H root m.child) →
      EnvOK path value env (l :: rest) →
      WritesIn H root (tailEnv path value env (l :: rest)) body →
      WritesIn H root env (build path value body (l :: rest)) := by
  intro rest
  induction rest with
  | nil =>
      intro l H env root hfp henv hleaf
      obtain ⟨henv0, -⟩ := henv
      obtain ⟨harr, -, -, -, -, -, -, -, -, -, -, -⟩ := henv0
      -- the take-out: binds the level's array and extracted child
      refine ⟨l.arr, harr, ?_⟩
      -- the call: state is the child variable, result the result variable
      intro r hr
      have hchild : ((env.set l.parentVar (.ref l.arr)).set l.childVar (.ref l.child))
          l.childVar = some (.ref l.child) := Env.set_self _ _ _
      rw [hchild] at hr
      have hrc : l.child = r := Val.ref.inj (Option.some.inj hr)
      subst hrc
      refine ⟨?_, ?_⟩
      · simpa [tailEnv, build, bindLevel] using hleaf
      · -- the put-back writes the extracted child, which is a footprint member
        refine ⟨?_, ?_⟩
        · intro re hre
          have hres : (((env.set l.parentVar (.ref l.arr)).set l.childVar (.ref l.child)).set
              l.resultVar (.ref l.child)) l.resultVar = some (.ref l.child) :=
            Env.set_self _ _ _
          rw [hres] at hre
          have hre' : l.child = re := Val.ref.inj (Option.some.inj hre)
          rw [← hre']
          exact hfp l (by simp)
        · intro r' _
          trivial
  | cons m rest' ih =>
      intro l H env root hfp henv hleaf
      obtain ⟨henv0, henv'⟩ := henv
      obtain ⟨harr, -, -, -, -, -, -, -, -, -, -, -⟩ := henv0
      refine ⟨l.arr, harr, ?_⟩
      intro r hr
      have hchild : ((env.set l.parentVar (.ref l.arr)).set l.childVar (.ref l.child))
          l.childVar = some (.ref l.child) := Env.set_self _ _ _
      rw [hchild] at hr
      have hrc : l.child = r := Val.ref.inj (Option.some.inj hr)
      subst hrc
      refine ⟨?_, ?_⟩
      · refine ih m (fun k hk => hfp k (List.mem_cons_of_mem _ hk)) henv' ?_
        simpa [tailEnv, bindLevel] using hleaf
      · refine ⟨?_, ?_⟩
        · intro re hre
          have hres : (((env.set l.parentVar (.ref l.arr)).set l.childVar (.ref l.child)).set
              l.resultVar (.ref l.child)) l.resultVar = some (.ref l.child) :=
            Env.set_self _ _ _
          rw [hres] at hre
          have hre' : l.child = re := Val.ref.inj (Option.some.inj hre)
          rw [← hre']
          exact hfp l (by simp)
        · intro r' _
          trivial

/-! ## Footprint containment -/

/-- The entry heap's field references are closed under the mutable footprint:
every reference a footprint cell's fields hold is itself a footprint member.
This is the heap-shape condition on the entry state; a dangling reference or a
persistent referrer would break it. -/
def Closed (H : Heap) (root : Ref) : Prop :=
  ∀ q o z, MutableFootprint H root q → H.cells q = some o → z ∈ fieldRefs o →
    MutableFootprint H root z

/-- A closed entry heap satisfies the field-reference account against itself. -/
theorem slotRefs_self {H : Heap} {root : Ref} (h : Closed H root) :
    SlotRefs H H root :=
  fun q o _ hcell z hz => h q o z ‹_› hcell hz

/-- If a run leaves every cell outside the root's mutable footprint as it found
it and leaves only footprint references in the footprint cells' fields, then the
mutable footprint did not grow. -/
theorem footprint_contained {H H' : Heap} {root : Ref}
    (hout : Outside H' H root) (hsl : SlotRefs H H' root) :
    ∀ q, MutableFootprint H' root q → MutableFootprint H root q := by
  intro q hq
  induction hq with
  | root hcell hpers =>
      by_cases hmem : MutableFootprint H root root
      · exact hmem
      · rw [hout root hmem] at hcell
        exact MutableFootprint.root hcell hpers
  | step hr hcell _ hmem hcell' _ ih =>
      exact hsl _ _ ih hcell _ hmem

/-! ## Counts along the path -/

/-- Every array and extracted child along a supported path is counted once in the
entry context: the entry invariant's unique tree fixes each footprint cell's
count, and its heap agreement fixes the context's multiplicity. -/
theorem counts_of_path {H : Heap} {root : Ref} {c : Ctx} :
    ∀ (rest : List Level) (l : Level),
      UniqueTree H root → (∀ r, H.rc r = c.mult r) →
      (∀ m ∈ (l :: rest), MutableFootprint H root m.arr) →
      (∀ m ∈ (l :: rest), MutableFootprint H root m.child) →
      Counts c.mult (l :: rest) := by
  intro rest
  induction rest with
  | nil =>
      intro l huniq hrc harr hchild
      refine ⟨?_, ?_, trivial⟩
      · rw [← hrc, huniq _ (harr l (by simp))]
      · rw [← hrc, huniq _ (hchild l (by simp))]
  | cons m rest' ih =>
      intro l huniq hrc harr hchild
      refine ⟨?_, ?_, ?_⟩
      · rw [← hrc, huniq _ (harr l (by simp))]
      · rw [← hrc, huniq _ (hchild l (by simp))]
      · exact ih m huniq hrc (fun k hk => harr k (List.mem_cons_of_mem _ hk))
          (fun k hk => hchild k (List.mem_cons_of_mem _ hk))

/-! ## The client's observations and callbacks -/

/-- What an interface hands a client: the handles the client already holds, and
the references of the values the interface produced for it. -/
structure Observation where
  roots : List Ref
  produced : List Ref
  deriving Repr

/-- The observation is separated: nothing reachable from the handles it names is
in the state's mutable footprint. The `produced` half is the interface's own
obligation — a value the interface hands out must not name a footprint cell,
directly or through a chain the run built. -/
def ObsSeparated (H : Heap) (root : Ref) (obs : Observation) : Prop :=
  ClientSeparated H root (obs.roots ++ obs.produced)

/-- The references a value names. -/
def producedRefs (v : Val) : List Ref := refsOf v

/-- An observation whose roots are the entry condition's client and whose
produced values are the interface's return. -/
def obsOf (roots : List Ref) (v : Val) : Observation :=
  ⟨roots, producedRefs v⟩

/-- The interface premise: the values it produces for a client name no footprint
reference, directly. Transitive separation of the produced value is what the
retention theorem consumes; this is its direct half. -/
def ProducesOutside (H : Heap) (root : Ref) (v : Val) : Prop :=
  ∀ r ∈ producedRefs v, ¬ MutableFootprint H root r

/-- A separated produced value satisfies the direct premise. The retention
theorem needs the transitive form; this records that the direct one is weaker. -/
theorem producesOutside_of_separated {H : Heap} {root : Ref} {v : Val}
    (hv : ClientSeparated H root (producedRefs v)) : ProducesOutside H root v :=
  fun r hr => hv r (ClientReachable.direct hr)

/-- Reachability from a concatenated handle list is reachability from one of its
parts: a derivation starts at a single handle. -/
theorem clientReachable_append {H : Heap} {l₁ l₂ : List Ref} {r : Ref}
    (h : ClientReachable H (l₁ ++ l₂) r) :
    ClientReachable H l₁ r ∨ ClientReachable H l₂ r := by
  induction h with
  | direct h => 
      rcases List.mem_append.mp h with h | h
      · exact Or.inl (ClientReachable.direct h)
      · exact Or.inr (ClientReachable.direct h)
  | step hr hcell hmem ih =>
      rcases ih with ih | ih
      · exact Or.inl (ClientReachable.step ih hcell hmem)
      · exact Or.inr (ClientReachable.step ih hcell hmem)

/-- The observation is separated when its two parts are separately so. -/
theorem obsSeparated_of_separated {H : Heap} {root : Ref} {roots : List Ref}
    {v : Val} (hroots : ClientSeparated H root roots)
    (hv : ClientSeparated H root (producedRefs v)) :
    ObsSeparated H root (obsOf roots v) := by
  intro r hr
  rcases clientReachable_append hr with h | h
  · exact hroots r h
  · exact hv r h

/-- Retention over the interface's observations rather than a fixed client-root
list: no reference the client can reach after a confined run is in the entry
footprint, so nothing the interface handed it is a handle into the state. The
observation's handles are the client's own and the produced references; the
interface premise `ObsSeparated` is what makes the produced half non-escaping. -/
theorem observation_retention {H H' : Heap} {root : Ref} {obs : Observation}
    (hsep : ObsSeparated H root obs) (hout : Outside H' H root) :
    ∀ r, ClientReachable H' (obs.roots ++ obs.produced) r → ¬ MutableFootprint H root r :=
  client_retention hsep hout

/-- The observation is separated again at the post heap when the footprint did
not grow. -/
theorem observation_preserved {H H' : Heap} {root : Ref} {obs : Observation}
    (hsep : ObsSeparated H root obs) (hout : Outside H' H root)
    (hwithin : ∀ r, MutableFootprint H' root r → MutableFootprint H root r) :
    ObsSeparated H' root obs :=
  clientSeparated_preserved hsep hout hwithin

/-- What a callback-valued interface must additionally establish: every value the
interface passes to a callback, and every value a callback returns, is separated
from the state — its references, and everything reachable from them, are outside
the footprint. Two further conditions are not expressible here and are not
claimed: the callback's own code must be checked from the client's context rather
than the session's, and a callback that returns a fresh handle forces the
observation to be re-established at the next boundary. The recognized fragment
has no callback, so the checker refuses such a program rather than certifying
it. -/
def CallbackTrafficOutside (H : Heap) (root : Ref) (traffic : List Ref) : Prop :=
  ClientSeparated H root traffic

/-- Callback traffic that is separated at the entry heap keeps the client's
observation non-escaping across a confined run: the retention theorem applies to
the union of the client's handles and the traffic. -/
theorem callback_retention {H H' : Heap} {root : Ref} {roots traffic : List Ref}
    (hsep : ClientSeparated H root (roots ++ traffic)) (hout : Outside H' H root)
    (hwithin : ∀ r, MutableFootprint H' root r → MutableFootprint H root r) :
    ClientSeparated H' root (roots ++ traffic) :=
  clientSeparated_preserved hsep hout hwithin

/-! ## The temporary pair through the representation relation -/

/-- The fresh name is a name no session cell lives at and no session cell's field
mentions: allocation makes it new, so nothing the state reaches can name it. -/
def FreshName (H : Heap) : Prop :=
  H.cells H.next = none ∧ ∀ q o, H.cells q = some o → H.next ∉ fieldRefs o

/-- The counted extraction's parent cell is the model's take-out cell. -/
theorem protocol_parent_cell {H : Heap} {l : Level} {oc : Obj}
    (hcell : H.cells l.arr = some l.obj) (hchild : H.cells l.child = some oc)
    (hpc : l.arr ≠ l.child) (hpn : l.arr ≠ H.next) (hcn : l.child ≠ H.next) :
    (CountedPair.protocol H l.arr l.child l.idx).2.cells l.arr =
      (blankLevel H l).cells l.arr := by
  obtain ⟨-, hp, -, -, -, -, -, -⟩ :=
    CountedPair.protocol_boundary (i := l.idx) hcell hchild hpc hpn hcn
  rw [hp, blankLevel_cells]

/-- The counted extraction leaves the extracted child's cell exactly where the
model's take-out leaves it. -/
theorem protocol_child_cell {H : Heap} {l : Level} {oc : Obj}
    (hcell : H.cells l.arr = some l.obj) (hchild : H.cells l.child = some oc)
    (hpc : l.arr ≠ l.child) (hpn : l.arr ≠ H.next) (hcn : l.child ≠ H.next) :
    (CountedPair.protocol H l.arr l.child l.idx).2.cells l.child =
      (blankLevel H l).cells l.child := by
  obtain ⟨-, -, hc, -, -, -, -, -⟩ :=
    CountedPair.protocol_boundary (i := l.idx) hcell hchild hpc hpn hcn
  rw [hc, blankLevel_cells_ne (Ne.symm hpc), hchild]

/-- Every session cell — every cell but the temporary pair's — sees what the
model's take-out leaves. -/
theorem protocol_cells {H : Heap} {l : Level} {oc : Obj}
    (hcell : H.cells l.arr = some l.obj) (hchild : H.cells l.child = some oc)
    (hpc : l.arr ≠ l.child) (hpn : l.arr ≠ H.next) (hcn : l.child ≠ H.next) :
    ∀ q, q ≠ H.next →
      (CountedPair.protocol H l.arr l.child l.idx).2.cells q = (blankLevel H l).cells q := by
  intro q hq
  by_cases hqa : q = l.arr
  · subst hqa
    exact protocol_parent_cell hcell hchild hpc hpn hcn
  · by_cases hqc : q = l.child
    · subst hqc
      exact protocol_child_cell hcell hchild hpc hpn hcn
    · have h1 : (CountedPair.protocol H l.arr l.child l.idx).2.cells q = H.cells q := by
        simp only [CountedPair.protocol]
        rw [CountedPair.pairTraffic_takeOut hpn hcn,
          CountedPair.pairFree_inc_cells_other hqa hqc hq]
        show (CountedPair.setPlaceholder (CountedPair.allocPair H l.arr l.child)
          l.arr l.idx).cells q = _
        rw [CountedPair.setPlaceholder_cells_other hqa,
          CountedPair.allocPair_cells_other hq]
      rw [h1, blankLevel_cells_ne hqa]

/-- The temporary pair's cell holds no name the state could have: its fields are
the level's array and extracted child. -/
theorem protocol_pair_no_name {H : Heap} {l : Level}
    (hpn : l.arr ≠ H.next) (hcn : l.child ≠ H.next) :
    H.next ∉ fieldRefs (⟨CountedPair.pairFields l.arr l.child, 1, false⟩ : Obj) := by
  simp [fieldRefs, CountedPair.pairFields, refsOf, Ne.symm hpn, Ne.symm hcn]

/-- The temporary pair sits outside the state's mutable footprint: no cell the
state reaches names it, and the pair's own fields name only the level's array and
extracted child. Its reference-count traffic therefore cannot be the traffic of a
footprint cell. -/
theorem pair_outside_footprint {H : Heap} {l : Level} {root : Ref} {oc : Obj}
    (hfresh : FreshName H) (hcell : H.cells l.arr = some l.obj)
    (hchild : H.cells l.child = some oc)
    (hpc : l.arr ≠ l.child) (hpn : l.arr ≠ H.next) (hcn : l.child ≠ H.next)
    (hroot : root ≠ H.next) :
    ¬ MutableFootprint (CountedPair.protocol H l.arr l.child l.idx).2 root H.next := by
  have hpairnone : (CountedPair.protocol H l.arr l.child l.idx).2.cells H.next = none := by
    obtain ⟨-, -, -, hp, -, -, -, -⟩ :=
      CountedPair.protocol_boundary (i := l.idx) hcell hchild hpc hpn hcn
    have : (CountedPair.protocol H l.arr l.child l.idx).1 = H.next := rfl
    rw [← this]
    exact hp
  have hnoname : ∀ q o, (CountedPair.protocol H l.arr l.child l.idx).2.cells q = some o →
      H.next ∉ fieldRefs o := by
    intro q o hqo
    by_cases hq : q = H.next
    · subst hq
      rw [hpairnone] at hqo
      exact absurd hqo (by simp)
    · rw [protocol_cells hcell hchild hpc hpn hcn q hq] at hqo
      by_cases hqa : q = l.arr
      · subst hqa
        rw [blankLevel_cells] at hqo
        have ho : o = { l.obj with
            fields := l.obj.fields.setIfInBounds l.idx (.scalar 0) } :=
          (Option.some.inj hqo).symm
        rw [ho]
        intro hmem
        rcases fieldRefs_setIfInBounds (o := l.obj) (i := l.idx) (v := .scalar 0)
          hmem with h | h
        · exact hfresh.2 l.arr l.obj hcell h
        · simp [refsOf] at h
      · rw [blankLevel_cells_ne hqa] at hqo
        exact hfresh.2 q o hqo
  have hno : ∀ q, MutableFootprint (CountedPair.protocol H l.arr l.child l.idx).2 root q →
      q ≠ H.next := by
    intro q hfp
    induction hfp with
    | root _ _ => exact hroot
    | step hr hcell' hpers hmem hcell₀ hpers₀ ih =>
        intro he
        exact hnoname _ _ hcell' (he ▸ hmem)
  intro hfp
  exact hno H.next hfp rfl

/-! ## The remaining runtime contract -/

/- The runtime separation of node and continuation traffic is a contract about
the emitted program, not a theorem about this model. What the model establishes
is its own part of the argument:

* `pair_outside_footprint`: the objects the model does see — the extraction's
  temporary pair — are outside the state's mutable footprint, and
  `Ownership.CountedPair.pair_traffic_neutral` accounts their whole traffic;
* `protocol_cells`: on every session cell the counted extraction agrees with the
  model's take-out, so the counted protocol and the model describe the same
  cells;
* `path_mult_preserved`: the path's own take-out, call and restore report the
  entry multiplicity function unchanged.

What is missing is a subject, not a proof step: the emitted recursive call
allocates a path node and a continuation closure, and neither is a `Ref` of
`Ownership.Heap`. No predicate of this model can quantify over them, so no
theorem here can say their counts are disjoint from the session's. Contract A2
therefore stays a runtime obligation with three parts — the node and continuation
are distinct objects from the state's cells, no session cell names them, and
their counted traffic is not the counted traffic of any session cell — and the
emitted callee's body remains uncaptured (`OwnershipLcnf`'s `ChildContract` is
the same boundary). The run's own count traffic is what the checker's
`CountFree` restricts; a run-level count-confinement theorem is not proved here.
-/

/-- The path's own extraction, call and restore do not change the checker's
multiplicities: every context the built program is checked from reports the
entry multiplicity function. -/
theorem path_mult_preserved {path value : Var} :
    ∀ (ls : List Level) (c : Ctx), (tailCtx path value c ls).mult = c.mult := by
  intro ls
  induction ls with
  | nil => intro c; rfl
  | cons l rest ih =>
      intro c
      show (tailCtx path value (bodyCtx path value c l) rest).mult = c.mult
      rw [ih (bodyCtx path value c l), bodyCtx_mult]

/-! ## The consolidated path result -/

/-- A supported path, consolidated. Given the path's level facts and one entry
condition, the theorem derives what `Ownership.PathSafety.path_run_separated`
takes separately: the built program's checker acceptance (`checkNF_build`), the
child-call contract at every level (`childConfined_of_path`), the annotation
reachability (`annotationsIn_of_path`), and the post-state footprint containment
(`slotRefs_runN` plus `footprint_contained`). The conclusions are the fault-free,
exclusively-writing run, the checker's invariant at the final context, the
untouched cells outside the entry footprint, the client non-escape facts, and the
footprint's non-growth.

What is still supplied is the leaf body's contract — its agreement
(`leafAgrees`, for the extract/restore family discharged by
`agrees_extract_restore`), its checker acceptance and exit variable, its
count-freedom, its write annotation (`WritesIn`), and the extraction annotations
at the tip — together with two heap-shape facts the path's syntax cannot imply:
`Acyclic` (the extracted child does not reach its parent, and the tip does not
reach back up to an emptied level) and `Closed` (the entry heap's footprint is
closed under field references). -/
theorem path_consolidated {path value : Var} {body : NCode} :
    ∀ (rest : List Level) (l : Level) {H : Heap} {env : Env} {c : Ctx}
      {root : Ref} {client : List Ref} {tip : Ref} {cb : Ctx} {y : Var},
      Slots H (l :: rest) → Chained (l :: rest) → DistinctArrays (l :: rest) →
      EnvOK path value env (l :: rest) →
      Shapes path value rest → LevelCtx path value c l →
      Acyclic tip H (l :: rest) →
      leafAgrees path value body (blankLevel H l)
        (isolateEnv (bindLevel env l) l.childVar path value) rest →
      WritesIn H root (tailEnv path value env (l :: rest)) body →
      checkNF (tailCtx path value c (l :: rest)) [] body = some cb →
      retVar body = some y → cb.us y = .owned → cb.refOf y = some tip →
      EndsAt tip (l :: rest) → Live H tip → AnnotationsIn H tip body →
      CountFree body = true → EntryInv H env c root client → l.arr = root →
      (∀ z r, c.us z = .borrow → c.refOf z = some r → False) →
      Closed H root →
      ∃ H' env' v ws,
        runN (build path value body (l :: rest)) env H = .done H' env' v ws ∧
          (∀ w ∈ ws, w.2 = true) ∧
          Inv H' env' (pathFinal c (l :: rest)) ∧
          Outside H' H root ∧
          (∀ r, ClientReachable H' client r → ¬ MutableFootprint H root r) ∧
          (∀ r, MutableFootprint H' root r → MutableFootprint H root r) ∧
          ClientSeparated H' root client := by
  intro rest l H env c root client tip cb y hslots hchain hdist henv hshapes hl
    hacyc hleaf hwrites hcheck hret hus href hends hlive hann hcf hEntry hroot
    hnoBorrow hclosed
  have harrs : ∀ m ∈ (l :: rest), MutableFootprint H root m.arr := by
    intro m hm
    have h := arrs_mem rest l hslots hchain hends m hm
    rwa [hroot] at h
  have hchilds : ∀ m ∈ (l :: rest), MutableFootprint H root m.child := by
    intro m hm
    have h := children_mem hlive rest l hslots hchain hends m hm
    rwa [hroot] at h
  have hcounts : Counts c.mult (l :: rest) :=
    counts_of_path rest l hEntry.uniqueTree hEntry.rc_eq harrs hchilds
  have hcn : checkN c (build path value body (l :: rest)) =
      some (pathFinal c (l :: rest)) :=
    checkNF_build rest l hl hshapes hcounts.2.2 hchain hcheck hret hus href hends hcf
  have hconf : ChildConfined path value body H env (l :: rest) :=
    childConfined_of_path rest l hslots hchain hdist henv hleaf hl hshapes hcounts.2.2
      hacyc hlive hann hcheck hret hus href hends hcf hEntry.toInv
  obtain ⟨H', env', v, ws, hrun, hws, hinv, hout, hsep⟩ :=
    path_run_separated rest l hslots hchain hdist henv hleaf hconf hEntry hroot
      hends hlive hann hnoBorrow hcn
  have hsl' : SlotRefs H H' root :=
    slotRefs_runN (slotRefs_self hclosed)
      (writesIn_build rest l hchilds henv hwrites) hrun hws
  have hwithin : ∀ r, MutableFootprint H' root r → MutableFootprint H root r :=
    footprint_contained hout hsl'
  exact ⟨H', env', v, ws, hrun, hws, hinv, hout, hsep, hwithin,
    clientSeparated_preserved hEntry.separated hout hwithin⟩

/-! ## The finite level list and the emitted recursion -/

/-! This section states the model's coverage of the finite-list row rather than
bridging it. The model is a finite syntactic nest: `build` writes one take-out,
one recursive call and one put-back per level, so the program's call structure is
a list, and the "recursive" step is the list's tail. Nothing here is a recursive
declaration — `NCode` has no self-reference — and nothing here relates that nest
to the emitted `setAt` declaration's own recursion. -/

/-- The extract-and-restore steps a nested program performs. -/
def extractions : NCode → Nat
  | .base _ => 0
  | .takeOut _ _ _ _ _ k => extractions k + 1
  | .putBack _ _ _ _ k => extractions k
  | .callAt _ _ _ _ body k => extractions body + extractions k
  | .ret _ => 0

/-- The recursive call sites a nested program contains. -/
def calls : NCode → Nat
  | .base _ => 0
  | .takeOut _ _ _ _ _ k => calls k
  | .putBack _ _ _ _ k => calls k
  | .callAt _ _ _ _ body k => calls body + 1 + calls k
  | .ret _ => 0

/-- The body the outermost recursive call runs, if the program has one. -/
def callBody? : NCode → Option NCode
  | .base _ => none
  | .takeOut _ _ _ _ _ k => callBody? k
  | .putBack _ _ _ _ k => callBody? k
  | .callAt _ _ _ _ body _ => some body
  | .ret _ => none

/-- The built program's call sites are the leaf body's plus one per level. -/
theorem calls_build {path value : Var} {body : NCode} :
    ∀ ls : List Level, calls (build path value body ls) = calls body + ls.length := by
  intro ls
  induction ls with
  | nil => simp [build, Nat.add_zero]
  | cons l rest ih =>
      have h : calls (build path value body (l :: rest)) =
          calls (build path value body rest) + 1 + 0 := rfl
      rw [h, ih]
      simp [Nat.add_assoc]

/-- The built program extracts once per level, on top of the leaf's own
extractions. -/
theorem extractions_build {path value : Var} {body : NCode} :
    ∀ ls : List Level,
      extractions (build path value body ls) = extractions body + ls.length := by
  intro ls
  induction ls with
  | nil => simp [build, Nat.add_zero]
  | cons l rest ih =>
      have h : extractions (build path value body (l :: rest)) =
          extractions (build path value body rest) + 1 := rfl
      rw [h, ih]
      simp [Nat.add_assoc]

/-- The built program's outermost call runs the remaining levels: the recursive
target is a strictly smaller term of the same list, not a declaration. -/
theorem callBody_build {path value : Var} {body : NCode} :
    ∀ (rest : List Level) (l : Level),
      callBody? (build path value body (l :: rest)) = some (build path value body rest) := by
  intro rest l
  rfl

/-- The call's body is strictly smaller than the list it was built from, so the
nest's depth is bounded by the program's own syntax. -/
theorem callBody_measure (rest : List Level) (l : Level) :
    rest.length < (l :: rest).length :=
  Nat.lt_succ_self _

/- The boundary. What the finite model establishes is the syntactic bound: per
level exactly one extraction, one call site and one restoration, and each call's
embedded body is the remaining list. Relating that to the emitted program needs
three things this development does not have.

* The emitted `setAt` recursive callee's body, captured as LCNF. It is not:
  `scripts/check_nested_projection.lean` recognizes the prefix around the call
  and `OwnershipLcnf/NestedSemantics.lean` relates that prefix to the model
  conditionally on a callee contract, but the callee's own body is not captured
  (the N10 boundary).
* That callee's contract: checker acceptance from the isolated context, an exit
  variable denoting the state it was handed, count-freedom, preservation outside
  that state's mutable footprint, and the emitted call's operand identities —
  the `ChildContract` hypothesis `OwnershipLcnf/NestedSemantics.lean` leaves
  open. `childConfined_of_path` derives the model-level counterpart; it does not
  supply the emitted one.
* The executor's call rule: that at the emitted call site the program runs the
  declaration's body on the handed state and continues with its result, which is
  what `runN`'s `.callAt` models. Establishing that rule is an
  emitted-semantics obligation, not a lemma about the level list.

So the finite model is a conservative syntactic bound on the program's call
structure, not an executor certificate. Depth that depends on data, mutual
recursion, and the linked executable's stack behaviour are outside it, and no
theorem here says the emitted program descends the list in this shape.
-/

end PathConsolidation
end Ownership
