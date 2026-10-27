/-
Path-depth safety and client retention.

`Ownership.Path` derives the heap/program agreement and annotation reachability
of a built path from the path's own level facts. This module turns those
derivations into the two results a nested update needs at every supported depth,
and it fixes their boundary.

* Safety over every finite path. `path_run_safe` ranges over a level list
  `l :: rest` of any length: a path whose built program is accepted by `checkN`
  from the entry context and whose level, leaf and child-call premises hold runs
  fault-free, writes only exclusively and preserves the checker's invariant.
  `path_run_confined` adds that the run leaves every cell outside the entry
  root's mutable footprint as it found it, and `path_run_separated` adds that a
  client separated from that footprint cannot reach into it afterwards.

* The call rule. `level_call_confined` states, for a level of such a path, the
  contract the recursive call's body satisfies — fault-freedom, exclusive
  writes, return of the extracted child, and preservation outside that child's
  footprint — and derives its premises from the remaining levels. It does not
  re-prove the contract: the conclusion *is* `callAt_frame_confined`'s, whose
  agreement and heap premises come from `agrees_of_path` and
  `takeOutsOK_of_inv`. `path_run_safe` likewise cites `checkN_sound` (through
  `checkN_sound_of_entryInv`) for the whole run rather than redoing its
  induction.

* Client retention. `ClientReachable.of_outside` and `client_retention` show
  that a reference a permitted client can reach after a confined run is not in
  the entry heap's mutable footprint: the client's own chain exists unchanged
  outside the footprint, so the run cannot have handed it a handle into the
  state. `clientSeparated_preserved` states the model's `ClientSeparated` at the
  post heap; it needs `footprint_within`, which says the footprint did not grow,
  and that is a heap fact rather than a consequence of confinement alone (a run
  that wrote a fresh reference into a footprint cell would grow it).
  `footprint_within` names the three heap facts that suffice — the run adds no
  cell, the entry cells are non-persistent, and every written field reference is
  already a footprint member. This module does not derive them for an arbitrary
  supported path: that needs an induction over the run tracking which references
  the program can name, and the depth-three certificate discharges them for its
  own run instead.

Boundary. A path is a finite list of levels: `build` writes the take-out, the
call and the put-back of every level, and the call body is the *remaining list*.
The recursion this covers is the syntactic depth of the path, i.e. the finite
fragment the recognizer admits — not arbitrary runtime recursion. The emitted
recursive callee's body is not captured, so the leaf body's agreement
(`leafAgrees`/`Agrees`) and the callee's checker acceptance are premises about
an admitted model body, not facts about the compiled declaration; the prefix
correspondence for the recognized nested alternative lives in
`OwnershipLcnf/NestedSemantics.lean` and is conditional on the same callee
contract. Callbacks and joins are outside the recognized fragment — the
recognizer rejects unsupported control flow rather than flattening it — so no
callback is certified here. The emitted continuation's retention (the reviewer's
A2: treating node/continuation reference-count traffic as disjoint from the state
is conditional on real separation, not on those objects being absent from the
model heap) is a named runtime obligation, not something these theorems derive.
No physical reference count, allocation policy or linked executable is claimed.
-/
import Ownership.Path
import Ownership.Entry
import Ownership.Nested

namespace Ownership
namespace PathSafety

open Ownership.Nested
open Ownership.Entry
open Ownership.Path

/-! ## The entry condition supplies the footprint-live handles -/

/-- A context with no borrowed handle exposes only footprint cells: an owned
variable denotes a footprint member by root completeness, and a borrow is
excluded by the caller. -/
theorem liveIn_of_entryInv {H : Heap} {env : Env} {c : Ctx} {root : Ref}
    {client : List Ref} (hEntry : EntryInv H env c root client)
    (hnoBorrow : ∀ z r, c.us z = .borrow → c.refOf z = some r → False) :
    LiveIn c H root := by
  intro z q hz hq
  rcases hz with hz | hz
  · exact hEntry.complete z q hz hq
  · exact absurd hq (hnoBorrow z q hz)

/-! ## The state after a take-out -/

/-- Emptying a level's slot and binding the extracted array and element to the
take-out's two fresh variables preserves the handle/count invariant. This is the
invariant the call's body is checked from, level by level. -/
theorem inv_after_takeOut {H : Heap} {env : Env} {c : Ctx} {l : Level}
    (hi : Inv H env c) (ha : c.us l.arrayVar = .owned)
    (hr : c.refOf l.arrayVar = some l.arr) (he : c.mult l.child = 1)
    (hcell : H.cells l.arr = some l.obj) :
    Inv (blankLevel H l) (bindLevel env l)
      ((c.move l.arrayVar l.parentVar).bindOwned l.childVar l.child) :=
  Inv.setFields (Inv.bindOwned (Inv.move hi ha hr) he) hcell

/-! ## Safety at every depth -/

/-- Safety of a supported path at every finite depth. `rest` is the remainder of
the path and `l` its first level, so the statement ranges over paths of every
length. The premises are the path's slot, chain, distinctness, environment, leaf
agreement and child-call facts; the conclusions are fault-freedom, exclusivity
of every write, and the checker's invariant at the output context.

The `.callAt` steps are discharged by `checkN_sound`'s call case, cited here
through `checkN_sound_of_entryInv`; nothing is re-proved. The agreement premise
is derived by `agrees_of_path`.

The call's body is the remaining level list, so every recursive step is a finite
expansion of the path's syntactic depth. This says nothing about a runtime call
stack, the emitted recursive callee's body, or a callback. -/
theorem path_run_safe {path value : Var} {body : NCode} :
    ∀ (rest : List Level) (l : Level) {H : Heap} {env : Env} {c : Ctx}
      {root : Ref} {client : List Ref} {ctx' : Ctx},
      Slots H (l :: rest) → Chained (l :: rest) → DistinctArrays (l :: rest) →
      EnvOK path value env (l :: rest) →
      leafAgrees path value body (blankLevel H l)
        (isolateEnv (bindLevel env l) l.childVar path value) rest →
      ChildConfined path value body H env (l :: rest) →
      EntryInv H env c root client →
      checkN c (build path value body (l :: rest)) = some ctx' →
      ∃ H' env' v ws,
        runN (build path value body (l :: rest)) env H = .done H' env' v ws ∧
          (∀ w ∈ ws, w.2 = true) ∧ Inv H' env' ctx' := by
  intro rest l H env c root client ctx' hslots hchain hdist henv hleaf hconf hEntry hc
  exact checkN_sound_of_entryInv hEntry
    (agrees_of_path rest l hslots hchain hdist henv hleaf hconf) hc

/-- Confinement at every depth: the same run leaves every cell outside the entry
root's mutable footprint as it found it. The annotation premise is derived by
`annotationsIn_of_path` and the state-indexed heap premise by
`takeOutsOK_of_entryInv`; the confinement is `runN_confined`, whose call case
runs the callee's own confinement induction. `level_call_confined` states that
same boundary as the recursive call's contract, through
`callAt_frame_confined`. -/
theorem path_run_confined {path value : Var} {body : NCode} :
    ∀ (rest : List Level) (l : Level) {H : Heap} {env : Env} {c : Ctx}
      {root : Ref} {client : List Ref} {ctx' : Ctx} {tip : Ref},
      Slots H (l :: rest) → Chained (l :: rest) → DistinctArrays (l :: rest) →
      EnvOK path value env (l :: rest) →
      leafAgrees path value body (blankLevel H l)
        (isolateEnv (bindLevel env l) l.childVar path value) rest →
      ChildConfined path value body H env (l :: rest) →
      EntryInv H env c root client → l.arr = root →
      EndsAt tip (l :: rest) → Live H tip → AnnotationsIn H tip body →
      (∀ z r, c.us z = .borrow → c.refOf z = some r → False) →
      checkN c (build path value body (l :: rest)) = some ctx' →
      ∃ H' env' v ws,
        runN (build path value body (l :: rest)) env H = .done H' env' v ws ∧
          (∀ w ∈ ws, w.2 = true) ∧ Inv H' env' ctx' ∧ Outside H' H root := by
  intro rest l H env c root client ctx' tip hslots hchain hdist henv hleaf hconf
    hEntry hroot hends hlive hannBody hnoBorrow hc
  have hagree : Agrees H env (build path value body (l :: rest)) :=
    agrees_of_path rest l hslots hchain hdist henv hleaf hconf
  have hok : TakeOutsOK H env (build path value body (l :: rest)) :=
    takeOutsOK_of_entryInv hEntry hagree hc
  have hann : AnnotationsIn H root (build path value body (l :: rest)) :=
    annotationsIn_of_path rest l root tip hslots hchain hroot hends hlive hannBody
  have hliveIn : LiveIn c H root := liveIn_of_entryInv hEntry hnoBorrow
  obtain ⟨H', env', v, ws, hrun, hws, hinv⟩ :=
    checkN_sound_of_entryInv hEntry hagree hc
  have hout : Outside H' H root :=
    runN_confined hEntry.toInv hliveIn (fun q _ => rfl) hann hc hok hws hrun
  exact ⟨H', env', v, ws, hrun, hws, hinv, hout⟩

/-! ## The call rule at a level of the path -/

/-- The recursive call a level of a supported path emits, at every depth. The
level extracts its child and hands it to the call; the remaining levels are the
call's body, running from the take-out's isolated environment on the take-out
heap. The conclusions — fault-freedom, exclusive writes, return of the extracted
child, and preservation of every cell outside that child's footprint — are
`callAt_frame_confined`'s. This theorem supplies its premises from the path: the
annotation premise by `annotationsIn_of_path`, the state-indexed heap premise by
`takeOutsOK_of_inv`, and the isolated invariant by `inv_isolated` from the
caller's invariant at the take-out state. The callee's checker acceptance and
return variable are the call site's own facts.

The body is the finite remainder of the path; the emitted recursive callee's
body is not captured, so the contract is about the admitted model program the
remaining levels build. -/
theorem level_call_confined {path value : Var} {body : NCode}
    (rest' : List Level) (m : Level) {l : Level} {tip : Ref}
    {H : Heap} {env : Env} {c : Ctx} {cb : Ctx}
    (hslots : Slots (blankLevel H l) (m :: rest'))
    (hchain : Chained (m :: rest'))
    (hlink : m.arr = l.child)
    (hdist : DistinctArrays (m :: rest'))
    (henv : EnvOK path value
      (isolateEnv (bindLevel env l) l.childVar path value) (m :: rest'))
    (hleaf : leafAgrees path value body (blankLevel H l)
      (isolateEnv (bindLevel env l) l.childVar path value) (m :: rest'))
    (hconf : ChildConfined path value body (blankLevel H l)
      (isolateEnv (bindLevel env l) l.childVar path value) (m :: rest'))
    (hi : Inv (blankLevel H l) (bindLevel env l) c)
    (hstate : c.us l.childVar = .owned) (href : c.refOf l.childVar = some l.child)
    (hpath : c.us path = .scalar) (harg : c.us value = .scalar)
    (hcheck : checkNF (isolatedCtx c l.childVar path value l.child) []
      (build path value body (m :: rest')) = some cb)
    (hret : ∃ y, retVar (build path value body (m :: rest')) = some y ∧
      cb.us y = .owned ∧ cb.refOf y = some l.child)
    (hends : EndsAt tip (m :: rest')) (hlive : Live (blankLevel H l) tip)
    (hannBody : AnnotationsIn (blankLevel H l) tip body) :
    ∃ H' env' v ws,
      runN (build path value body (m :: rest'))
        (isolateEnv (bindLevel env l) l.childVar path value) (blankLevel H l) =
        .done H' env' v ws ∧
      (∀ w ∈ ws, w.2 = true) ∧ v = .ref l.child ∧
      (∀ q, ¬ MutableFootprint (blankLevel H l) l.child q →
        H'.cells q = (blankLevel H l).cells q) := by
  have hi_iso : Inv (blankLevel H l)
      (isolateEnv (bindLevel env l) l.childVar path value)
      (isolatedCtx c l.childVar path value l.child) :=
    inv_isolated hi hstate href hpath harg
  have hann : AnnotationsIn (blankLevel H l) l.child
      (build path value body (m :: rest')) :=
    annotationsIn_of_path rest' m l.child tip hslots hchain hlink hends hlive hannBody
  have hagree : Agrees (blankLevel H l)
      (isolateEnv (bindLevel env l) l.childVar path value)
      (build path value body (m :: rest')) :=
    agrees_of_path rest' m hslots hchain hdist henv hleaf hconf
  have hok : TakeOutsOK (blankLevel H l)
      (isolateEnv (bindLevel env l) l.childVar path value)
      (build path value body (m :: rest')) :=
    takeOutsOK_of_inv hi_iso hagree hcheck
  exact callAt_frame_confined hann hcheck hret hi_iso hok

/-! ## Client retention -/

/-- Client reachability survives a confined run, and every reference the client
can reach afterwards is outside the entry heap's mutable footprint.

Induction along the client's chain. A handle the client holds is outside the
footprint by `hsep`, so `Outside` gives its cell in the entry heap; a step's
target is then reachable in the entry heap, and `hsep` places it outside the
footprint in turn. At the end of the chain the reached reference is therefore
both entry-reachable and outside the footprint, so the run could not have handed
the client a handle into the state. -/
theorem ClientReachable.of_outside {H H' : Heap} {root : Ref} {client : List Ref}
    {r : Ref} (hsep : ClientSeparated H root client) (hout : Outside H' H root)
    (hr : ClientReachable H' client r) :
    ClientReachable H client r ∧ ¬ MutableFootprint H root r := by
  induction hr with
  | direct h =>
      exact ⟨ClientReachable.direct h, hsep _ (ClientReachable.direct h)⟩
  | step hr hcell hmem ih =>
      rename_i r o r'
      obtain ⟨ihr, ihsep⟩ := ih
      have hcell0 : H.cells r = some o := by
        rw [← hout r ihsep]
        exact hcell
      have hreach : ClientReachable H client r' := ClientReachable.step ihr hcell0 hmem
      exact ⟨hreach, hsep r' hreach⟩

/-- A permitted client cannot acquire a reference into the state's mutable
footprint across a confined call/return. -/
theorem client_retention {H H' : Heap} {root : Ref} {client : List Ref}
    (hsep : ClientSeparated H root client) (hout : Outside H' H root) :
    ∀ r, ClientReachable H' client r → ¬ MutableFootprint H root r :=
  fun _ hr => (ClientReachable.of_outside hsep hout hr).2

/-- The mutable footprint does not grow. Three heap facts suffice: the post heap
has no cell the entry heap lacked (so every footprint cell is live in both), the
entry heap's cells are all non-persistent, and every field reference of a
post-heap footprint cell was already a footprint member at the entry heap.

The third fact is what confinement alone does not give: a run that wrote a fresh
reference into a footprint cell would add a footprint member without touching
anything outside. For a run of a supported path every reference-valued write is
an extracted child, which the annotation premise already places in the
footprint. -/
theorem footprint_within {H H' : Heap} {root : Ref}
    (hmono : ∀ q, H.cells q = none → H'.cells q = none)
    (hnp : ∀ q o, H.cells q = some o → o.persistent = false)
    (hrefs : ∀ q, MutableFootprint H root q → ∀ z,
      (∃ o o', H.cells q = some o ∧ H'.cells q = some o' ∧ z ∈ fieldRefs o') →
        MutableFootprint H root z) :
    ∀ q, MutableFootprint H' root q → MutableFootprint H root q := by
  have hsome : ∀ q o, H'.cells q = some o → ∃ o', H.cells q = some o' := by
    intro q o h
    cases h0 : H.cells q with
    | none =>
        rw [hmono q h0] at h
        exact absurd h (by simp)
    | some o' => exact ⟨o', rfl⟩
  intro q hq
  induction hq with
  | root hcell _ =>
      obtain ⟨o', ho'⟩ := hsome _ _ hcell
      exact MutableFootprint.root ho' (hnp _ _ ho')
  | step hr hcell _ hmem _ _ ih =>
      obtain ⟨o', ho'⟩ := hsome _ _ hcell
      exact hrefs _ ih _ ⟨_, _, ho', hcell, hmem⟩

/-- The entry condition's client separation carries to the post heap, given that
the footprint did not grow. -/
theorem clientSeparated_preserved {H H' : Heap} {root : Ref} {client : List Ref}
    (hsep : ClientSeparated H root client) (hout : Outside H' H root)
    (hwithin : ∀ r, MutableFootprint H' root r → MutableFootprint H root r) :
    ClientSeparated H' root client := by
  intro r hr hfp
  exact (ClientReachable.of_outside hsep hout hr).2 (hwithin r hfp)

/-- Safety, confinement and client retention of a supported path's run, at every
depth. This composes `path_run_confined` with `client_retention`; the client list
is the entry condition's own. -/
theorem path_run_separated {path value : Var} {body : NCode} :
    ∀ (rest : List Level) (l : Level) {H : Heap} {env : Env} {c : Ctx}
      {root : Ref} {client : List Ref} {ctx' : Ctx} {tip : Ref},
      Slots H (l :: rest) → Chained (l :: rest) → DistinctArrays (l :: rest) →
      EnvOK path value env (l :: rest) →
      leafAgrees path value body (blankLevel H l)
        (isolateEnv (bindLevel env l) l.childVar path value) rest →
      ChildConfined path value body H env (l :: rest) →
      EntryInv H env c root client → l.arr = root →
      EndsAt tip (l :: rest) → Live H tip → AnnotationsIn H tip body →
      (∀ z r, c.us z = .borrow → c.refOf z = some r → False) →
      checkN c (build path value body (l :: rest)) = some ctx' →
      ∃ H' env' v ws,
        runN (build path value body (l :: rest)) env H = .done H' env' v ws ∧
          (∀ w ∈ ws, w.2 = true) ∧ Inv H' env' ctx' ∧ Outside H' H root ∧
          (∀ r, ClientReachable H' client r → ¬ MutableFootprint H root r) := by
  intro rest l H env c root client ctx' tip hslots hchain hdist henv hleaf hconf
    hEntry hroot hends hlive hannBody hnoBorrow hc
  obtain ⟨H', env', v, ws, hrun, hws, hinv, hout⟩ :=
    path_run_confined rest l hslots hchain hdist henv hleaf hconf hEntry hroot
      hends hlive hannBody hnoBorrow hc
  exact ⟨H', env', v, ws, hrun, hws, hinv, hout,
    client_retention hEntry.separated hout⟩

end PathSafety
end Ownership
