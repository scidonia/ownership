/-
The put-back's two dispositions on the counted heap.

`Ownership/CountedPair.lean` takes the nested index arm up to the extraction
boundary: the parent and child are live at their entry counts, the temporary
pair is gone, and the child is exclusive. The arm's next and final ownership
step is the restore, captured in `docs/notes/artifacts/setAt-nested.lcnf.txt` as

    let xs' := Array.set ◾ fst.35 i.27 _x.39 ◾;
    dec i.27;
    return xs'

with `fst.35` the extracted parent, `i.27` the selected index and `_x.39` the
recursive call's result. The call has arity 5, matching the core declaration
`Array.set (xs : Array α) (i : @& Nat) (v : α) (h : i < xs.size) : Array α` as
a specialized call: the erased element type, the array, the index, the value and
the erased bounds proof. Three consequences of that shape drive this module.

* `Array.set` owns its array argument, so the call consumes the parent handle.
  In the in-place branch it returns that same array, so the handle continues; in
  the copy branch it returns a fresh array and consumes the parent's reference,
  which this module records as one decrement.
* The value argument `_x.39` is consumed into the slot: the captured code never
  increments the recursive result before the store, so the child handle is
  *transferred* into the slot, not duplicated.
* The core declaration documents that the array "is modified in-place if there
  are no other references to it". The exclusivity test this module uses is the
  array cell's count one together with a false persistence flag, which is the
  test the checker's `exclusive?` applies; that the runtime applies the same
  test is the correspondence recorded as a contract below. The bounds proof is
  the captured call's last operand, so the modelled path is always in bounds.

`Ownership.run`'s `.setArr` case already gives the copy branch its shape:
allocate the updated cell, then decrement the old reference. This module uses
the same shape for the put-back, so the two dispositions model one runtime
operation rather than two unrelated ones.

## The dispositions

| disposition | condition | result | parent cell | parent count | child count |
| --- | --- | --- | --- | --- | --- |
| mutate | live, count one, non-persistent, in bounds | the parent reference | the parent's own cell, selected slot holds the child | one, unchanged | one, unchanged (handle moved) |
| copy | live, in bounds, count other than one or persistent | the fresh name `H.next` | not written; keeps its fields, loses one reference for the consumed handle | `rc - 1` (saturating) | one, unchanged (handle moved) |

In the copy branch the fresh cell carries the parent's fields with the child in
the selected slot, at count one and non-persistent, exactly as `Heap.alloc`
builds it. The other reference fields are copied without adding counted edges:
the array's slots are not separately owned element handles, the emitted
`Array.set` copies the slot array, and the only handle this path moves is the
recursive result. Freeing the copy through `CountedPair.releaseFields` is
therefore outside this path and is not claimed.

## The child-call boundary

The put-back runs after the recursive call, so the branch condition has to hold
on the heap the call leaves. `ChildCall` names the call's boundary and *derives*
the parent's fate from it rather than assuming it:

* the body is admitted (`Nested.CountFree`) and the checker accepts it from
  `Nested.isolatedCtx`, whose context exposes only the call's own state, path and
  index and leaves every other variable dead;
* it runs from `Nested.isolateEnv`, the environment the caller actually hands
  it, so a suspended parent variable is not nameable at run time either;
* the caller's invariant `Inv` holds on that isolated environment and context,
  the extraction annotations name footprint cells (`Entry.AnnotationsIn`), and
  the extraction obligations are discharged (`Nested.TakeOutsOK`);
* the parent is outside the child's mutable footprint (`Entry.MutableFootprint`).

`ChildCall.parent` then derives `Hout.cells p = Hin.cells p`, and the parent's
count and liveness with it, from `Entry.callAt_frame_confined` — not from an
assumption about the parent's cell. The consequence is the retention control: a
body that stored the parent reference into the child's cell, with no increment
at all, would have to reach the parent. If it could, the parent would be inside
the child's mutable footprint and the separation premise fails
(`retention_separation_fails`); and under the isolated environment the variable
that names the parent is dead, so such a body faults instead of returning
(`OwnershipTest/PutBack.lean`); its caller-side run succeeds, so the boundary —
not the body's syntax — is what excludes it. The increment-only control therefore does not
carry the argument alone: `CountFree` alone admits `.putBack`, which is why the
cell equality is derived rather than assumed.

Two things remain premises rather than consequences: the returned child handle's
accounting (`child_rc`, `child_persistent` — the body neither duplicates nor
consumes the handle it returns and leaves its persistence flag alone), and the
whole structure, because the emitted recursive declaration is not captured. That
is the same boundary as N10: `ChildCall` is a hypothesis about an admitted model
body, and `OwnershipLcnf.ChildContract` states the corresponding model-level
form.

## Restoration

`restorationBoundary_of_entry` carries the counted entry through
`CountedPair.protocol`: the boundary parent cell is the take-out's
placeholder-filled cell at count one, the child cell is live at count one, and
the index is in bounds. `putBack_exclusive` then derives, from that boundary and
the child-call contract, that the put-back takes the mutate branch, returns the
parent's own reference, writes the child into the selected slot, and leaves both
counts at one. It is stated as two independently reviewable theorems,
`restoration_functional` (the result reference and the slot write) and
`restoration_counts` (the parent's and child's counts and liveness), with
`putBack_exclusive` combining them.

`mutate_eq_model` identifies the mutate outcome with the model's own restoration:
`Ownership.Nested.NCode.putBack` writes the same slot with the same reference
and returns the parent reference. The model's put-back is unconditional, so the
derivation supplies the condition N11 previously assumed.

## Negative controls

`OwnershipTest/PutBack.lean` carries the concrete instances: the exclusive
restoration, then a count-two parent whose copy leaves the alias at count one
and the fresh result at count one with the same contents, a persistent parent
whose only branch is copy, and both retention routes — a body that increments a
handle to the parent (outside the supported interface; were it admitted, the
parent would be at count two and the put-back would copy) and a body that stores
the parent reference into the child's slot with no increment. The second runs to
completion on a caller environment that binds the parent (`putBack_retaining_positive`:
the child's slot holds the parent and no count moves), which is what `CountFree`
alone admits; the boundary excludes it because the isolated environment leaves
only the parent's variable dead (`putBack_retaining_operands` — array and index
operands present), and because a heap where the parent is reachable from the
child violates the separation premise.

## Boundary assumptions

* **The emitted call boundary.** That `Array.set`'s in-place test is the
  exclusivity of the array value, and that its copy branch consumes the
  argument handle, are contracts about the emitted code and the runtime, not
  theorems here. The disposition is derived for the model's `exclusive?` and the
  runtime correspondence is named in
  `docs/notes/OWNERSHIP_RUNTIME_EVIDENCE.md` as measurement, not refinement.
  The captured `dec i.27` that follows the call, and the index and site handles
  around it, are scalar/path bookkeeping, as in N1 and N2, and are not modelled.
* **The child-call boundary.** The parent's cell preservation is *derived*
  (`ChildCall.parent`, from `Entry.callAt_frame_confined`), and a body that
  could reach the parent is excluded by the separation premise
  (`retention_separation_fails`). The boundary itself is still a hypothesis: the
  checker acceptance from the isolated context, the invariant, the annotations,
  the extraction obligations and the separation premise are supplied to it, and
  the emitted recursive declaration is not captured (N10). The returned handle's
  accounting (`child_rc`, `child_persistent`) is a premise too: this module
  proves no concrete count-preservation result over `runN`; the abstract
  counterpart is the checker's `countFree_check_mult`.
* **Persistence.** A persistent parent is never in-place here. The model's
  decrement never frees a cell, so a persistent parent keeps its cell with a
  lowered count; the runtime handling of persistent objects' references is not
  modelled.
* **Free/cascade.** The only free in reach is `CountedPair`'s restricted
  one-cell form; no cascading free is modelled, and none is reached.
* **Allocated-address identity.** A `Ref` is a name. The copy's fresh name is
  `H.next`, and nothing here identifies it with a runtime address, an allocation
  site, or a reused address.
* **Off-path inputs.** `putBack` reports no outcome for a missing parent cell or
  an index outside the array. The captured call's bounds proof rules the latter
  out and the take-out's success rules out the former, so the model returns
  `none` rather than a fabricated heap outside the path.
-/
import Ownership.CountedPair
import Ownership.Entry

namespace Ownership
namespace PutBack

/-! ## Heap support -/

theorem set_next (H : Heap) (r : Ref) (o : Obj) : (H.set r o).next = H.next := rfl

theorem dec_next (H : Heap) (r : Ref) (n : Nat) : (H.dec r n).next = H.next := by
  unfold Heap.dec
  split <;> rfl

theorem inc_next (H : Heap) (r : Ref) (n : Nat) : (H.inc r n).next = H.next := by
  unfold Heap.inc
  split <;> rfl

theorem alloc_next (H : Heap) (fields : Array Val) : (H.alloc fields).2.next = H.next + 1 := rfl

/-! ## The branch condition -/

/-- The condition the emitted `Array.set` tests for its in-place branch: the
parent cell is live, its count is one, its persistence flag is false, and the
index is inside the array. The count and the flag are the exclusivity test; the
bounds fact is the proof argument the captured call carries. -/
def InPlace (H : Heap) (p : Ref) (i : Nat) : Prop :=
  ∃ o, H.cells p = some o ∧ o.rc = 1 ∧ o.persistent = false ∧ i < o.fields.size

/-- The executable form of the branch test, read off the parent cell. -/
def inPlace? (H : Heap) (p : Ref) (i : Nat) : Bool :=
  match H.cells p with
  | none => false
  | some o => o.rc == 1 && !o.persistent && decide (i < o.fields.size)

theorem inPlace?_eq_true {H : Heap} {p : Ref} {i : Nat} :
    inPlace? H p i = true ↔ InPlace H p i := by
  unfold inPlace? InPlace
  cases h : H.cells p with
  | none => simp
  | some o =>
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq,
        Option.some.injEq, exists_eq_left']
      exact ⟨fun ⟨⟨hrc, hp⟩, hlt⟩ => ⟨hrc, hp, hlt⟩,
        fun ⟨hrc, hp, hlt⟩ => ⟨⟨hrc, hp⟩, hlt⟩⟩

/-- The in-place condition entails the heap's exclusivity test on the array
value, which is the test the runtime correspondence identifies. -/
theorem InPlace.exclusive {H : Heap} {p : Ref} {i : Nat} (h : InPlace H p i) :
    H.exclusive? p = true := by
  obtain ⟨o, hcell, hrc, hpers, -⟩ := h
  exact (Heap.exclusive?_eq_true).mpr ⟨o, hcell, hrc, hpers⟩

/-- Exclusivity plus an in-bounds index is the in-place condition. -/
theorem inPlace_of_exclusive {H : Heap} {p : Ref} {i : Nat} {o : Obj}
    (hcell : H.cells p = some o) (hrc : o.rc = 1) (hpers : o.persistent = false)
    (hlt : i < o.fields.size) : InPlace H p i :=
  ⟨o, hcell, hrc, hpers, hlt⟩

/-- A count other than one rules out the in-place branch. -/
theorem not_inPlace_of_rc_ne_one {H : Heap} {p : Ref} {i : Nat} {o : Obj}
    (hcell : H.cells p = some o) (hrc : o.rc ≠ 1) : ¬ InPlace H p i := by
  rintro ⟨o', ho', hrc', -, -⟩
  rw [hcell] at ho'
  simp only [Option.some.injEq] at ho'
  subst ho'
  exact hrc hrc'

/-- A persistent parent rules out the in-place branch. -/
theorem not_inPlace_of_persistent {H : Heap} {p : Ref} {i : Nat} {o : Obj}
    (hcell : H.cells p = some o) (hpers : o.persistent = true) : ¬ InPlace H p i := by
  rintro ⟨o', ho', -, hpers', -⟩
  rw [hcell] at ho'
  simp only [Option.some.injEq] at ho'
  subst ho'
  rw [hpers] at hpers'
  exact Bool.noConfusion hpers'

/-! ## The dispositions -/

/-- Which branch the put-back takes. `copy` is the runtime's shared branch. -/
inductive Disposition where
  | mutate
  | copy
  deriving DecidableEq, Repr

/-- The disposition on the modelled path. `none` is a missing parent cell or an
index outside the parent array; the captured call's bounds proof excludes the
latter and the take-out's success excludes the former, so the model reports no
outcome off that path. -/
def disposition? (H : Heap) (p : Ref) (i : Nat) : Option Disposition :=
  match H.cells p with
  | none => none
  | some o =>
      if i < o.fields.size then
        some (if inPlace? H p i then .mutate else .copy)
      else none

/-- The parent cell the take-out leaves: the entry's fields with the model's
placeholder in the selected slot. -/
def parentAfter (op : Obj) (i : Nat) : Obj :=
  { op with fields := op.fields.setIfInBounds i (.scalar 0) }

/-- The mutate branch's effect: the parent's own cell receives the child in the
selected slot. The parent keeps its name and its count, and the child handle
moves into the slot, so no count changes. -/
def mutate (H : Heap) (p : Ref) (o : Obj) (i : Nat) (c : Ref) : Heap :=
  H.set p { o with fields := o.fields.setIfInBounds i (.ref c) }

/-- The copy branch's effect: allocate one fresh cell carrying the parent's
fields with the child in the selected slot, then decrement the parent for the
handle the call consumed. The old cell is not written. -/
def copy (H : Heap) (p : Ref) (o : Obj) (i : Nat) (c : Ref) : Ref × Heap :=
  let fields := o.fields.setIfInBounds i (.ref c)
  (H.next, Heap.dec (H.alloc fields).2 p 1)

/-- The concrete put-back: read the parent cell, choose the disposition, and
return the result reference with the heap. -/
def putBack (H : Heap) (p : Ref) (i : Nat) (c : Ref) : Option (Ref × Heap) :=
  match H.cells p with
  | none => none
  | some o =>
      match disposition? H p i with
      | some .mutate => some (p, mutate H p o i c)
      | some .copy => some (copy H p o i c)
      | none => none

/-- The in-place condition selects the mutate branch. -/
theorem disposition_mutate_of_inPlace {H : Heap} {p : Ref} {i : Nat}
    (hin : InPlace H p i) : disposition? H p i = some .mutate := by
  obtain ⟨o, hcell, hrc, hpers, hlt⟩ := hin
  have hin? : inPlace? H p i = true := (inPlace?_eq_true).mpr ⟨o, hcell, hrc, hpers, hlt⟩
  unfold disposition?
  rw [hcell]
  simp [hlt, hin?]

/-- A live, in-bounds, exclusive parent selects the mutate branch. -/
theorem putBack_eq_mutate {H : Heap} {p : Ref} {i : Nat} {c : Ref} {o : Obj}
    (hcell : H.cells p = some o) (hrc : o.rc = 1) (hpers : o.persistent = false)
    (hlt : i < o.fields.size) :
    putBack H p i c = some (p, mutate H p o i c) := by
  have hdisp := disposition_mutate_of_inPlace (inPlace_of_exclusive hcell hrc hpers hlt)
  unfold putBack
  rw [hcell]
  simp [hdisp]

/-- A live, in-bounds parent that is not exclusive selects the copy branch. -/
theorem disposition_copy_of_not_inPlace {H : Heap} {p : Ref} {i : Nat} {o : Obj}
    (hcell : H.cells p = some o) (hlt : i < o.fields.size)
    (hnot : ¬ InPlace H p i) :
    disposition? H p i = some .copy := by
  have hb : (o.rc == 1 && !o.persistent) = false := by
    by_cases h1 : o.rc = 1
    · by_cases hp : o.persistent = false
      · exact absurd (inPlace_of_exclusive hcell h1 hp hlt) hnot
      · have hp' : o.persistent = true := by
          cases hpo : o.persistent with
          | false => exact absurd hpo hp
          | true => rfl
        simp [h1, hp']
    · have h1' : (o.rc == 1) = false := by simpa using h1
      simp [h1']
  have hin : inPlace? H p i = false := by
    unfold inPlace?
    rw [hcell]
    simp [hlt, hb]
  unfold disposition?
  rw [hcell]
  simp [hlt, hin]

/-- A live, in-bounds parent that is not exclusive selects the copy branch. -/
theorem putBack_eq_copy {H : Heap} {p c : Ref} {i : Nat} {o : Obj}
    (hcell : H.cells p = some o) (hlt : i < o.fields.size)
    (hnot : ¬ InPlace H p i) :
    putBack H p i c = some (copy H p o i c) := by
  have hdisp := disposition_copy_of_not_inPlace hcell hlt hnot
  unfold putBack
  rw [hcell]
  simp [hdisp]

/-! ## The child-call contract -/

/-- The child-call boundary: the facts the checker and the entry invariant supply
for the recursive call, from which the put-back's inputs are *derived*.

The body is admitted (`Nested.CountFree`), checked from the isolated context (so
it cannot name the suspended parent's variable), and run from the isolated
environment on the caller's heap. `Entry.callAt_frame_confined` consumes the
invariant, the annotations and the extraction obligations below and yields the
confinement fact: the body writes no cell outside the child's mutable footprint.
The parent's cell is deliberately **not** a field, so a body that could reach and
write the parent cannot satisfy this boundary.

`ChildCall.writes_exclusive` exposes the other fact the same result derives: every
write in the run the boundary admits selects the exclusive branch.

The returned-handle accounting is a premise: `child_rc` and `child_persistent`
say the body neither duplicates nor consumes the handle it returns and leaves the
child's persistence flag alone. The emitted recursive declaration is not
captured, so the whole structure is a hypothesis about an admitted model body
(N10), as `OwnershipLcnf.ChildContract` is. -/
structure ChildCall (Hin Hout : Heap) (env : Env) (ctx : Ctx) (state path x : Var)
    (body : Nested.NCode) (p c : Ref) : Prop where
  /-- The body is in the supported interface: the checker requires a call body to
  neither duplicate nor consume a handle, which is `Nested.CountFree`. -/
  admitted : Nested.CountFree body = true
  /-- The checker accepts the body from the isolated context, and its exit
  variable still denotes the reference the call was given. -/
  checked : ∃ cb,
    Nested.checkNF (Nested.isolatedCtx ctx state path x c) [] body = some cb ∧
    ∃ y, Nested.retVar body = some y ∧ cb.us y = .owned ∧ cb.refOf y = some c
  /-- The caller's invariant holds on the isolated environment and context. -/
  inv : Inv Hin (Nested.isolateEnv env state path x)
    (Nested.isolatedCtx ctx state path x c)
  /-- The extraction annotations name footprint cells. -/
  annotations : Entry.AnnotationsIn Hin c body
  /-- The extraction obligations of the body. -/
  extraction : Nested.TakeOutsOK Hin (Nested.isolateEnv env state path x) body
  /-- The parent is outside the child's mutable footprint. -/
  separated : ¬ Entry.MutableFootprint Hin c p
  /-- The body runs from the isolated environment on the caller's heap and
  returns the child handle, the reference the call was given. -/
  outcome : ∃ envb ws, Nested.runN body (Nested.isolateEnv env state path x) Hin =
    .done Hout envb (.ref c) ws
  /-- The returned child handle is the call's own: its count is unchanged, so the
  body neither duplicated nor consumed it. -/
  child_rc : Hout.rc c = Hin.rc c
  /-- The child's persistence flag is unchanged. -/
  child_persistent : Hout.isPersistent c = Hin.isPersistent c

/-- The child call's confinement, derived from the call boundary: the body
leaves every cell outside the child's mutable footprint exactly as it found it.
`Entry.callAt_frame_confined` supplies the fact for the run it produces; the call
boundary's own outcome is the same run, so the heaps coincide. -/
theorem ChildCall.confined {Hin Hout : Heap} {env : Env} {ctx : Ctx}
    {state path x : Var} {body : Nested.NCode} {p c : Ref}
    (h : ChildCall Hin Hout env ctx state path x body p c) :
    ∀ q, ¬ Entry.MutableFootprint Hin c q → Hout.cells q = Hin.cells q := by
  obtain ⟨cb, hc, hret⟩ := h.checked
  obtain ⟨H', env', v, ws, hrun, -, -, hconf⟩ :=
    Entry.callAt_frame_confined (state := state) (path := path) (x := x) (r := c)
      (H := Hin) (env := Nested.isolateEnv env state path x)
      h.annotations hc hret h.inv h.extraction
  obtain ⟨envb, wsb, hrunb⟩ := h.outcome
  rw [hrun] at hrunb
  injection hrunb with hH _ _ _
  intro q hq
  rw [← hH]
  exact hconf q hq

/-- Every write in the call's trace selects the exclusive branch. This is not a
field: `Entry.callAt_frame_confined` derives it for the run the boundary admits,
and the boundary's own outcome is that same run. -/
theorem ChildCall.writes_exclusive {Hin Hout : Heap} {env : Env} {ctx : Ctx}
    {state path x : Var} {body : Nested.NCode} {p c : Ref}
    (h : ChildCall Hin Hout env ctx state path x body p c) {envb : Env}
    {ws : List Write}
    (hrun : Nested.runN body (Nested.isolateEnv env state path x) Hin =
      .done Hout envb (.ref c) ws) :
    ∀ w ∈ ws, w.2 = true := by
  obtain ⟨cb, hc, hret⟩ := h.checked
  obtain ⟨H', env', v, ws', hrun', hws', -, -⟩ :=
    Entry.callAt_frame_confined (state := state) (path := path) (x := x) (r := c)
      (H := Hin) (env := Nested.isolateEnv env state path x)
      h.annotations hc hret h.inv h.extraction
  rw [hrun'] at hrun
  injection hrun with _ _ _ hws
  rw [← hws]
  exact hws'

/-- The suspended parent's cell is what the take-out left: its contents, its
count and its liveness are unchanged by the child call. This is derived — the
separation premise puts the parent outside the child's mutable footprint — rather
than assumed. -/
theorem ChildCall.parent {Hin Hout : Heap} {env : Env} {ctx : Ctx}
    {state path x : Var} {body : Nested.NCode} {p c : Ref}
    (h : ChildCall Hin Hout env ctx state path x body p c) :
    Hout.cells p = Hin.cells p :=
  h.confined p h.separated

/-- The parent's count after the call is the boundary count: the derived cell
equality read as the count fact the branch selection uses. -/
theorem ChildCall.parent_rc {Hin Hout : Heap} {env : Env} {ctx : Ctx}
    {state path x : Var} {body : Nested.NCode} {p c : Ref}
    (h : ChildCall Hin Hout env ctx state path x body p c) :
    Hout.rc p = Hin.rc p := by
  cases hcell : Hin.cells p with
  | none =>
      have hout : Hout.cells p = none := by rw [h.parent, hcell]
      simp [Heap.rc, hcell, hout]
  | some o =>
      have hout : Hout.cells p = some o := by rw [h.parent, hcell]
      rw [CountedPair.rc_of_cells hout, CountedPair.rc_of_cells hcell]

/-- The parent stays live across the call, from the derived cell equality. -/
theorem ChildCall.parent_live {Hin Hout : Heap} {env : Env} {ctx : Ctx}
    {state path x : Var} {body : Nested.NCode} {p c : Ref}
    (h : ChildCall Hin Hout env ctx state path x body p c)
    (hlive : Hin.cells p ≠ none) : Hout.cells p ≠ none := by
  rw [h.parent]
  exact hlive

/-- The child call completes and returns the child handle. -/
theorem ChildCall.runs {Hin Hout : Heap} {env : Env} {ctx : Ctx}
    {state path x : Var} {body : Nested.NCode} {p c : Ref}
    (h : ChildCall Hin Hout env ctx state path x body p c) :
    ∃ envb ws, Nested.runN body (Nested.isolateEnv env state path x) Hin =
      .done Hout envb (.ref c) ws :=
  h.outcome

/-- A body that retains a counted handle is not a child call: the contract's
admission premise is `CountFree`, which excludes the increment. -/
theorem not_childCall_of_not_countFree {Hin Hout : Heap} {env : Env} {ctx : Ctx}
    {state path x : Var} {body : Nested.NCode} {p c : Ref}
    (hcf : Nested.CountFree body = false) :
    ¬ ChildCall Hin Hout env ctx state path x body p c := by
  intro h
  rw [h.admitted] at hcf
  exact Bool.noConfusion hcf

/-- A reference-write retention is excluded by the boundary's separation premise:
if the parent lies in the child's mutable footprint, some body could reach it
through a field, so no admitted call has that heap. This is the control that
`CountFree` alone does not supply, because `Nested.CountFree` admits `.putBack`,
which stores a reference without changing any count. -/
theorem retention_separation_fails {Hin Hout : Heap} {env : Env} {ctx : Ctx}
    {state path x : Var} {body : Nested.NCode} {p c : Ref}
    (hmem : Entry.MutableFootprint Hin c p) :
    ¬ ChildCall Hin Hout env ctx state path x body p c := by
  intro h
  exact h.separated hmem

/-- A live cell at a positive count. The model's decrement never removes a cell,
so a positive count always has a cell behind it. -/
theorem cells_ne_none_of_rc_pos {H : Heap} {r : Ref} {n : Nat}
    (h : H.rc r = n) (hn : n ≠ 0) : H.cells r ≠ none := by
  intro hnone
  simp [Heap.rc, hnone] at h
  exact hn h.symm

/-- The persistence flag read through the heap is the cell's own flag. -/
theorem isPersistent_of_cells {H : Heap} {r : Ref} {o : Obj}
    (h : H.cells r = some o) : H.isPersistent r = o.persistent := by
  simp [Heap.isPersistent, h]

/-! ## The restoration boundary -/

/-- The restoration boundary: the heap the child call starts from is the
protocol boundary, its parent cell is the take-out's placeholder-filled cell at
count one, the child cell is live at count one, and the index is in bounds. -/
structure Boundary (H : Heap) (p c : Ref) (i : Nat) (op oc : Obj) : Prop where
  /-- The parent cell the take-out left. -/
  parent : H.cells p = some (parentAfter op i)
  /-- The entry's parent count, one. -/
  parent_rc : op.rc = 1
  /-- The entry's parent persistence flag, false. -/
  parent_persistent : op.persistent = false
  /-- The selected index is inside the parent array. -/
  index : i < op.fields.size
  /-- The child cell is live. -/
  child : H.cells c = some oc
  /-- The entry's child count, one. -/
  child_rc : oc.rc = 1
  /-- The entry's child persistence flag, false. -/
  child_persistent : oc.persistent = false
  /-- The parent and the child are different cells. -/
  distinct : p ≠ c

/-- The counted entry reaches the restoration boundary through `protocol`: the
take-out's placeholder write leaves the parent at its entry count, and the pair
traffic is neutral for both components. -/
theorem restorationBoundary_of_entry {H : Heap} {p c : Ref} {i : Nat} {op oc : Obj}
    (hPcell : H.cells p = some op) (hCcell : H.cells c = some oc)
    (hPrc : op.rc = 1) (hCrc : oc.rc = 1)
    (hPpers : op.persistent = false) (hCpers : oc.persistent = false)
    (hslot : op.fields[i]? = some (.ref c))
    (hpc : p ≠ c) (hpn : p ≠ H.next) (hcn : c ≠ H.next) :
    Boundary (CountedPair.protocol H p c i).2 p c i op oc := by
  have hb := CountedPair.protocol_boundary (i := i) hPcell hCcell hpc hpn hcn
  dsimp only at hb
  obtain ⟨-, hparent, hchild, -, -, -, -, -⟩ := hb
  have hlt : i < op.fields.size := (Array.getElem?_eq_some_iff.mp hslot).1
  exact ⟨hparent, hPrc, hPpers, hlt, hchild, hCrc, hCpers, hpc⟩

/-- The well-formed counted entry itself reaches the boundary. -/
theorem restorationBoundary_of_wellFormed {H : Heap} {p c : Ref} {i : Nat}
    (hw : CountedPair.WellFormedEntry H p c i) :
    ∃ op oc, Boundary (CountedPair.protocol H p c i).2 p c i op oc := by
  obtain ⟨op, oc, hPcell, hCcell, hPrc, hCrc, hPpers, hCpers, hslot, hpc, -,
    hpn, hcn⟩ := hw
  exact ⟨op, oc,
    restorationBoundary_of_entry hPcell hCcell hPrc hCrc hPpers hCpers hslot hpc hpn hcn⟩

/-- The child call starts from the boundary and leaves the parent cell there. -/
theorem Boundary.parent_after_call {H : Heap} {p c : Ref} {i : Nat} {op oc : Obj}
    {Hc : Heap} {env : Env} {ctx : Ctx} {state path x : Var} {body : Nested.NCode}
    (hb : Boundary H p c i op oc) (hcall : ChildCall H Hc env ctx state path x body p c) :
    Hc.cells p = some (parentAfter op i) := by
  rw [hcall.parent]
  exact hb.parent

/-! ## Restoration -/

/-- The put-back on the heap the child call leaves takes the mutate branch. -/
theorem putBack_mutate_of_boundary {H : Heap} {p c : Ref} {i : Nat} {op oc : Obj}
    {Hc : Heap} {env : Env} {ctx : Ctx} {state path x : Var} {body : Nested.NCode}
    (hb : Boundary H p c i op oc) (hcall : ChildCall H Hc env ctx state path x body p c) :
    putBack Hc p i c = some (p, mutate Hc p (parentAfter op i) i c) := by
  have hparent := hb.parent_after_call hcall
  have hlt : i < (parentAfter op i).fields.size := by
    simpa [parentAfter] using hb.index
  have hrc : (parentAfter op i).rc = 1 := by simpa [parentAfter] using hb.parent_rc
  have hpers : (parentAfter op i).persistent = false := by
    simpa [parentAfter] using hb.parent_persistent
  exact putBack_eq_mutate hparent hrc hpers hlt

/-- The branch the put-back selects on the boundary is `mutate`. -/
theorem disposition_mutate_of_boundary {H : Heap} {p c : Ref} {i : Nat} {op oc : Obj}
    {Hc : Heap} {env : Env} {ctx : Ctx} {state path x : Var} {body : Nested.NCode}
    (hb : Boundary H p c i op oc) (hcall : ChildCall H Hc env ctx state path x body p c) :
    disposition? Hc p i = some .mutate := by
  have hparent := hb.parent_after_call hcall
  have hlt : i < (parentAfter op i).fields.size := by
    simpa [parentAfter] using hb.index
  exact disposition_mutate_of_inPlace
    (inPlace_of_exclusive hparent (by simpa [parentAfter] using hb.parent_rc)
      (by simpa [parentAfter] using hb.parent_persistent) hlt)

/-- Functional restoration: the put-back returns the parent's own reference and
writes the child into the selected slot of the parent's cell. The other slots,
the other cells, the child's cell and the fresh-name counter are unchanged:
nothing is allocated, so the address is the parent's own name. -/
theorem restoration_functional {H : Heap} {p c : Ref} {i : Nat} {op oc : Obj}
    {Hc : Heap} {env : Env} {ctx : Ctx} {state path x : Var} {body : Nested.NCode}
    (hb : Boundary H p c i op oc) (hcall : ChildCall H Hc env ctx state path x body p c) :
    let H' := mutate Hc p (parentAfter op i) i c
    putBack Hc p i c = some (p, H') ∧
      H'.cells p = some { parentAfter op i with
        fields := (parentAfter op i).fields.setIfInBounds i (.ref c) } ∧
      ((parentAfter op i).fields.setIfInBounds i (.ref c))[i]? = some (.ref c) ∧
      (∀ j, j ≠ i →
        ((parentAfter op i).fields.setIfInBounds i (.ref c))[j]? =
          (parentAfter op i).fields[j]?) ∧
      (∀ q, q ≠ p → H'.cells q = Hc.cells q) ∧
      H'.cells c = Hc.cells c ∧
      H'.next = Hc.next := by
  have hm := putBack_mutate_of_boundary hb hcall
  have hlt : i < (parentAfter op i).fields.size := by
    simpa [parentAfter] using hb.index
  refine ⟨hm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (Hc.set p { parentAfter op i with fields :=
      (parentAfter op i).fields.setIfInBounds i (.ref c) }).cells p = _
    rw [Heap.set_self]
  · exact Array.getElem?_setIfInBounds_self_of_lt hlt
  · intro j hj
    exact Array.getElem?_setIfInBounds_ne (Ne.symm hj)
  · intro q hq
    exact Heap.set_other _ _ _ _ hq
  · exact Heap.set_other _ _ _ _ (Ne.symm hb.distinct)
  · rfl

/-- Reference-count preservation: after the restoration both components are live
at count one. The parent's count is its own; the child's count is unchanged, so
the edge in the slot is the handle the call returned, not a second one. -/
theorem restoration_counts {H : Heap} {p c : Ref} {i : Nat} {op oc : Obj}
    {Hc : Heap} {env : Env} {ctx : Ctx} {state path x : Var} {body : Nested.NCode}
    (hb : Boundary H p c i op oc) (hcall : ChildCall H Hc env ctx state path x body p c) :
    let H' := mutate Hc p (parentAfter op i) i c
    Hc.rc p = 1 ∧ Hc.rc c = 1 ∧
      H'.rc p = 1 ∧ H'.rc c = 1 ∧
      H'.cells p ≠ none ∧ H'.cells c ≠ none ∧
      Heap.Exclusive H' p ∧ Heap.Exclusive H' c := by
  have hparent := hb.parent_after_call hcall
  have hrc_p : (parentAfter op i).rc = 1 := by simpa [parentAfter] using hb.parent_rc
  have hpers_p : (parentAfter op i).persistent = false := by
    simpa [parentAfter] using hb.parent_persistent
  -- the boundary counts
  have hrcHp : H.rc p = 1 := by
    rw [CountedPair.rc_of_cells hb.parent]
    exact hrc_p
  have hrcHc : H.rc c = 1 := by
    rw [CountedPair.rc_of_cells hb.child]
    exact hb.child_rc
  have hrcHcp : Hc.rc p = 1 := by
    rw [hcall.parent_rc]
    exact hrcHp
  have hrcHcc : Hc.rc c = 1 := by rw [hcall.child_rc]; exact hrcHc
  have hliveHc : Hc.cells c ≠ none :=
    cells_ne_none_of_rc_pos hrcHcc (by decide)
  -- the child cell the body left
  obtain ⟨oc', hoc'⟩ : ∃ o, Hc.cells c = some o := by
    cases h : Hc.cells c with
    | none => exact absurd h hliveHc
    | some o => exact ⟨o, rfl⟩
  have hrc_c' : oc'.rc = 1 := by
    rw [← CountedPair.rc_of_cells hoc']
    exact hrcHcc
  have hpers_c' : oc'.persistent = false := by
    have hH : H.isPersistent c = false := by
      rw [isPersistent_of_cells hb.child, hb.child_persistent]
    have hc : Hc.isPersistent c = false := by rw [hcall.child_persistent, hH]
    rw [← isPersistent_of_cells hoc']
    exact hc
  -- the mutate outcome
  have hcell' : (mutate Hc p (parentAfter op i) i c).cells p =
      some { parentAfter op i with
        fields := (parentAfter op i).fields.setIfInBounds i (.ref c) } := by
    show (Hc.set p _).cells p = _
    rw [Heap.set_self]
  have hcellc' : (mutate Hc p (parentAfter op i) i c).cells c = some oc' := by
    show (Hc.set p _).cells c = some oc'
    rw [Heap.set_other _ _ _ _ (Ne.symm hb.distinct)]
    exact hoc'
  refine ⟨hrcHcp, hrcHcc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [CountedPair.rc_of_cells hcell', hrc_p]
  · rw [CountedPair.rc_of_cells hcellc', hrc_c']
  · rw [hcell']; simp
  · rw [hcellc']; simp
  · exact ⟨_, hcell', hrc_p, hpers_p⟩
  · exact ⟨_, hcellc', hrc_c', hpers_c'⟩

/-- Exclusive restoration: from the counted boundary and the child-call contract,
the put-back takes the mutate branch, returns the parent's own reference, writes
the child into the selected slot, and leaves both counts at one. -/
theorem putBack_exclusive {H : Heap} {p c : Ref} {i : Nat} {op oc : Obj}
    {Hc : Heap} {env : Env} {ctx : Ctx} {state path x : Var} {body : Nested.NCode}
    (hb : Boundary H p c i op oc) (hcall : ChildCall H Hc env ctx state path x body p c) :
    let H' := mutate Hc p (parentAfter op i) i c
    disposition? Hc p i = some .mutate ∧
      putBack Hc p i c = some (p, H') ∧
      ((parentAfter op i).fields.setIfInBounds i (.ref c))[i]? = some (.ref c) ∧
      H'.rc p = 1 ∧ H'.rc c = 1 ∧
      H'.cells p ≠ none ∧ H'.cells c ≠ none ∧
      Heap.Exclusive H' p ∧ Heap.Exclusive H' c := by
  have hbranch := disposition_mutate_of_boundary hb hcall
  have hfun := restoration_functional hb hcall
  have hcounts := restoration_counts hb hcall
  dsimp only at hfun hcounts
  obtain ⟨hpb, -, hslot, -, -, -, -⟩ := hfun
  obtain ⟨-, -, hrcp, hrcc, hlivep, hlivec, hexp, hexc⟩ := hcounts
  exact ⟨hbranch, hpb, hslot, hrcp, hrcc, hlivep, hlivec, hexp, hexc⟩

/-- Exclusive restoration from the well-formed counted entry itself: the
`CountedPair` boundary facts reach the restoration point, and the put-back that
runs there takes the mutate branch and leaves both counts at one. -/
theorem putBack_exclusive_of_wellFormed {H : Heap} {p c : Ref} {i : Nat}
    (hw : CountedPair.WellFormedEntry H p c i)
    {Hc : Heap} {env : Env} {ctx : Ctx} {state path x : Var} {body : Nested.NCode}
    (hcall : ChildCall (CountedPair.protocol H p c i).2 Hc env ctx state path x body p c) :
    ∃ op, putBack Hc p i c = some (p, mutate Hc p (parentAfter op i) i c) ∧
      (mutate Hc p (parentAfter op i) i c).rc p = 1 ∧
      (mutate Hc p (parentAfter op i) i c).rc c = 1 ∧
      Heap.Exclusive (mutate Hc p (parentAfter op i) i c) p ∧
      Heap.Exclusive (mutate Hc p (parentAfter op i) i c) c := by
  obtain ⟨op, oc, hb⟩ := restorationBoundary_of_wellFormed hw
  have h := putBack_exclusive hb hcall
  dsimp only at h
  obtain ⟨-, hpb, -, hrcp, hrcc, -, -, hexp, hexc⟩ := h
  exact ⟨op, hpb, hrcp, hrcc, hexp, hexc⟩

/-! ## The copy branch and its controls -/

/-- The copy branch's effects: the result is the fresh name, the fresh cell
carries the updated fields at count one, and the old parent keeps its contents
and loses one reference for the handle the call consumed. -/
theorem copy_result {H : Heap} {p c : Ref} {i : Nat} {o : Obj}
    (hcell : H.cells p = some o) (hpn : p ≠ H.next) :
    (copy H p o i c).1 = H.next ∧
      (copy H p o i c).2.cells H.next =
        some ⟨o.fields.setIfInBounds i (.ref c), 1, false⟩ ∧
      (copy H p o i c).2.cells p = some { o with rc := o.rc - 1 } ∧
      (∀ q, q ≠ p → q ≠ H.next → (copy H p o i c).2.cells q = H.cells q) ∧
      (copy H p o i c).2.rc p = o.rc - 1 ∧
      (copy H p o i c).2.next = H.next + 1 := by
  have hdecl : copy H p o i c =
      (H.next, Heap.dec (H.alloc (o.fields.setIfInBounds i (.ref c))).2 p 1) := rfl
  have hfresh : (H.alloc (o.fields.setIfInBounds i (.ref c))).2.cells p = some o := by
    rw [Heap.alloc_cells_other hpn]
    exact hcell
  have hnew : (H.alloc (o.fields.setIfInBounds i (.ref c))).2.cells H.next =
      some ⟨o.fields.setIfInBounds i (.ref c), 1, false⟩ :=
    Heap.alloc_cells_self H _
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hdecl, Heap.dec_other (Ne.symm hpn)]
    exact hnew
  · rw [hdecl]
    exact CountedPair.dec_cells_self hfresh
  · intro q hqp hqn
    rw [hdecl, Heap.dec_other hqp]
    exact Heap.alloc_cells_other hqn
  · rw [hdecl, CountedPair.rc_of_cells (CountedPair.dec_cells_self hfresh)]
  · rw [hdecl, dec_next, alloc_next]

/-- A shared parent at count two is not exclusive, so the put-back copies: the
alias stays live at one fewer reference with the same contents, and the fresh
cell is the result. (`putBack_eq_copy` and `copy_result` are the general form for
any live in-bounds parent that is not in place.) -/
theorem shared_parent_copies {H : Heap} {p c : Ref} {i : Nat} {o : Obj}
    (hcell : H.cells p = some o) (hlt : i < o.fields.size) (hrc : o.rc = 2)
    (hpn : p ≠ H.next) :
    disposition? H p i = some .copy ∧
      putBack H p i c = some (copy H p o i c) ∧
      (copy H p o i c).1 = H.next ∧
      (copy H p o i c).2.cells H.next =
        some ⟨o.fields.setIfInBounds i (.ref c), 1, false⟩ ∧
      (copy H p o i c).2.cells p = some { o with rc := 1 } := by
  have hnot : ¬ InPlace H p i := not_inPlace_of_rc_ne_one hcell (by rw [hrc]; decide)
  have hdisp := disposition_copy_of_not_inPlace hcell hlt hnot
  have hpb := putBack_eq_copy (c := c) hcell hlt hnot
  obtain ⟨hfresh, hnew, hold, -, -, -⟩ := copy_result hcell hpn
  refine ⟨hdisp, hpb, hfresh, hnew, ?_⟩
  rw [hold]
  simp [hrc]

/-- A persistent parent is never exclusive, so the put-back copies it. -/
theorem persistent_parent_copies {H : Heap} {p c : Ref} {i : Nat} {o : Obj}
    (hcell : H.cells p = some o) (hlt : i < o.fields.size) (hpers : o.persistent = true)
    (hpn : p ≠ H.next) :
    disposition? H p i = some .copy ∧
      putBack H p i c = some (copy H p o i c) ∧
      (copy H p o i c).1 = H.next ∧
      (copy H p o i c).2.cells p = some { o with rc := o.rc - 1 } := by
  have hnot : ¬ InPlace H p i := not_inPlace_of_persistent hcell hpers
  have hdisp := disposition_copy_of_not_inPlace hcell hlt hnot
  have hpb := putBack_eq_copy (c := c) hcell hlt hnot
  obtain ⟨hfresh, -, hold, -, -, -⟩ := copy_result hcell hpn
  exact ⟨hdisp, hpb, hfresh, hold⟩

/-- A child call that retained the parent would leave the count two, which is the
shared disposition: the copy branch, the alias back at count one and the new
result at count one, instead of a write. The supported interface excludes it
(`CountFree` forbids the increment that retains a handle), so this is the
control the contract rules out. -/
theorem retained_parent_copies {H : Heap} {p c : Ref} {i : Nat} {o : Obj}
    (hcell : H.cells p = some o) (hlt : i < o.fields.size) (hrc : o.rc = 1)
    (hpn : p ≠ H.next) :
    let Hr := H.inc p 1
    let o' := { o with rc := o.rc + 1 }
    Hr.cells p = some o' ∧
      disposition? Hr p i = some .copy ∧
      putBack Hr p i c = some (copy Hr p o' i c) ∧
      (copy Hr p o' i c).1 = Hr.next ∧
      (copy Hr p o' i c).2.cells p = some { o' with rc := o'.rc - 1 } ∧
      (copy Hr p o' i c).2.rc p = 1 := by
  intro Hr o'
  have hcellr : Hr.cells p = some o' := CountedPair.inc_cells_self hcell
  have hnext : Hr.next = H.next := inc_next H p 1
  have hpnr : p ≠ Hr.next := by rw [hnext]; exact hpn
  have hrc' : o'.rc = o.rc + 1 := rfl
  have hlt' : i < o'.fields.size := by simpa using hlt
  have hnot : ¬ InPlace Hr p i :=
    not_inPlace_of_rc_ne_one hcellr (by rw [hrc', hrc]; decide)
  have hdisp := disposition_copy_of_not_inPlace hcellr hlt' hnot
  have hpb := putBack_eq_copy (c := c) hcellr hlt' hnot
  obtain ⟨hfresh, -, hold, -, hrcp, -⟩ := copy_result hcellr hpnr
  refine ⟨hcellr, hdisp, hpb, hfresh, hold, ?_⟩
  rw [hrcp, hrc', hrc]

/-! ## Correspondence with the model's restoration -/

/-- The mutate branch is the model's own put-back: running
`Ownership.Nested.NCode.putBack` writes the same slot with the same reference and
returns the parent reference. The model writes with `set!`, which is
`setIfInBounds`, so the heaps are the same operation. -/
theorem mutate_eq_model {H : Heap} {p c : Ref} {i : Nat} {o : Obj}
    (hcell : H.cells p = some o)
    {a e iv result : Var} {env : Env}
    (ha : env a = some (.ref p)) (he : env e = some (.ref c))
    (hi : env iv = some (.scalar i)) :
    Nested.runN (.putBack a e iv result (.ret result)) env H =
      .done (mutate H p o i c) (env.set result (.ref p)) (.ref p) [] := by
  simp only [Nested.runN, ha, he, hi, hcell, mutate, Array.set!]
  simp [Env.set_self]

end PutBack
end Ownership
