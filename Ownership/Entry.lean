/-
The entry invariant: a transitive mutable footprint, transitive client
reachability, and a completeness condition tying every owned variable to the one
root, with the nested-state countermodels.

`EntryInv` extends the handle/count invariant with
* `UniqueTree` — every cell in the mutable footprint has count one;
* `ClientSeparated` — no client-reachable reference is in the footprint;
* `RootsComplete` — every owned variable of the checker's context denotes a cell
  in the footprint.

The footprint is transitive reachability through non-persistent cells, not one
level of direct field references: a cell joins the footprint only when it is
live, non-persistent and named by a footprint cell's field, so a grandchild is
in the footprint and a persistent (immutable-observation) descendant is not.
The client side is transitive for the same reason: a client holding a wrapper
object whose own field names a footprint cell reaches that cell indirectly.

The unique tree is a sufficient condition, not the only admissible one; the
point here is that the initializer must establish it (or a protocol that proves
the actual write target exclusive). The fresh-array initializer does; a state
whose two slots name the same child does not, whatever their depth, and a client
handle into the footprint — directly or through an intermediate object —
violates separation.
-/
import Ownership.Runner
import Ownership.Nested

namespace Ownership
namespace Entry

open Ownership.Runner

/-- The references a value names. -/
def refsOf : Val → List Ref
  | .ref r => [r]
  | _ => []

/-- The references in an object's fields. -/
def fieldRefs (o : Obj) : List Ref := o.fields.toList.flatMap refsOf

/-- Transitive mutable reachability from a root cell. The root joins the
footprint when it is live and non-persistent; a field reference of a footprint
cell joins it when the referred cell is live and non-persistent. A persistent
cell is therefore neither in the footprint nor a step through which the
footprint continues, so an immutable observation may be shared freely. -/
inductive MutableFootprint (H : Heap) (root : Ref) : Ref → Prop where
  | root {o : Obj} (hcell : H.cells root = some o) (hpers : o.persistent = false) :
      MutableFootprint H root root
  | step {r : Ref} {o : Obj} (hr : MutableFootprint H root r)
      (hcell : H.cells r = some o) (hpers : o.persistent = false)
      {r' : Ref} (hmem : r' ∈ fieldRefs o) {o' : Obj}
      (hcell' : H.cells r' = some o') (hpers' : o'.persistent = false) :
      MutableFootprint H root r'

namespace MutableFootprint

/-- Every cell in the mutable footprint is live and non-persistent. -/
theorem cell_nonPersistent {H : Heap} {root : Ref} {r : Ref}
    (h : MutableFootprint H root r) :
    ∃ o, H.cells r = some o ∧ o.persistent = false := by
  induction h with
  | root hcell hpers => exact ⟨_, hcell, hpers⟩
  | step _ _ _ _ hcell' hpers' _ => exact ⟨_, hcell', hpers'⟩

/-- Every footprint cell is the root or a field reference of a footprint cell:
the relation has no other way to admit a cell. -/
theorem eq_root_or_field {H : Heap} {root : Ref} {r : Ref}
    (h : MutableFootprint H root r) :
    r = root ∨ ∃ q o, MutableFootprint H root q ∧ H.cells q = some o ∧
      r ∈ fieldRefs o := by
  induction h with
  | root _ _ => exact Or.inl rfl
  | step hr hcell hpers hmem _ _ _ =>
      exact Or.inr ⟨_, _, hr, hcell, hmem⟩

end MutableFootprint

/-- A reference that is not the root and whose every in-heap referrer is a
persistent (immutable) cell is not in the mutable footprint: traversal stops at
immutable observations. -/
theorem not_mutable_of_persistent_parents {H : Heap} {root r : Ref}
    (hne : r ≠ root)
    (hpar : ∀ q o, H.cells q = some o → r ∈ fieldRefs o → o.persistent = true) :
    ¬ MutableFootprint H root r := by
  intro h
  rcases MutableFootprint.eq_root_or_field h with hroot | ⟨q, o, hq, hcell, hmem⟩
  · exact hne hroot
  · have hp : o.persistent = true := hpar q o hcell hmem
    obtain ⟨o', hc', hp'⟩ := MutableFootprint.cell_nonPersistent hq
    rw [hc'] at hcell
    have : o' = o := Option.some.inj hcell
    rw [this, hp] at hp'
    exact Bool.false_ne_true hp'.symm

/-- Every cell in the mutable footprint is exclusively owned. -/
def UniqueTree (H : Heap) (root : Ref) : Prop :=
  ∀ r, MutableFootprint H root r → H.rc r = 1

/-- Transitive reachability from a client's handles: the handles themselves, and
the field references of any object they reach. -/
inductive ClientReachable (H : Heap) (client : List Ref) : Ref → Prop where
  | direct {r : Ref} (h : r ∈ client) : ClientReachable H client r
  | step {r : Ref} {o : Obj} (hr : ClientReachable H client r)
      (hcell : H.cells r = some o) {r' : Ref} (hmem : r' ∈ fieldRefs o) :
      ClientReachable H client r'

/-- No client-reachable reference is in the footprint: the intersection of
transitive client reachability with the transitive mutable footprint is empty. -/
def ClientSeparated (H : Heap) (root : Ref) (client : List Ref) : Prop :=
  ∀ r, ClientReachable H client r → ¬ MutableFootprint H root r

/-- Every owned variable the checker's context carries denotes a cell in the one
root's mutable footprint. This is the completeness condition on roots: a context
cannot carry an owned handle to a disjoint tree while `EntryInv` still holds. -/
def RootsComplete (c : Ctx) (H : Heap) (root : Ref) : Prop :=
  ∀ x r, c.us x = .owned → c.refOf x = some r → MutableFootprint H root r

/-- The concrete entry condition: the handle/count invariant plus the footprint,
client-separation and root-completeness facts. -/
structure EntryInv (H : Heap) (env : Env) (c : Ctx) (root : Ref) (client : List Ref) : Prop
    extends Inv H env c where
  uniqueTree : UniqueTree H root
  separated : ClientSeparated H root client
  complete : RootsComplete c H root

/-! ## Object identity from a cell equation -/

/-- Two objects are equal when they are the cell at the same reference. -/
theorem obj_eq_of_cells {H : Heap} {r : Ref} {o o' : Obj}
    (h : H.cells r = some o) (h' : H.cells r = some o') : o = o' := by
  rw [h] at h'
  exact Option.some.inj h'

/-! ## One-level countermodels, restated over the transitive relations -/

/-- A state whose two slots both name the child: the outer array is exclusive,
the child's count is two. -/
def repeatedChildHeap : Heap :=
  { cells := fun r =>
      if r = 0 then some ⟨#[.scalar 0], 2, false⟩
      else if r = 1 then some ⟨#[.ref 0, .ref 0], 1, false⟩
      else none
    next := 2 }

/-- The outer array's two slots both name `ref 0`, so `ref 0` is in its mutable
footprint. -/
theorem repeatedChild_mem : MutableFootprint repeatedChildHeap 1 0 := by
  have hroot : MutableFootprint repeatedChildHeap 1 1 :=
    MutableFootprint.root (o := ⟨#[.ref 0, .ref 0], 1, false⟩)
      (by simp [repeatedChildHeap]) (by simp)
  exact MutableFootprint.step (o := ⟨#[.ref 0, .ref 0], 1, false⟩) (r' := 0)
    (o' := ⟨#[.scalar 0], 2, false⟩) hroot
    (by simp [repeatedChildHeap]) (by simp) (by simp [fieldRefs, refsOf])
    (by simp [repeatedChildHeap]) (by simp)

/-- The repeated child is **not** a unique mutable tree. -/
theorem repeatedChild_not_unique : ¬ UniqueTree repeatedChildHeap 1 := by
  intro h
  have hrc := h 0 repeatedChild_mem
  simp [repeatedChildHeap, Heap.rc] at hrc

/-- A client handle on the child violates separation. -/
theorem clientRetained_not_separated :
    ¬ ClientSeparated repeatedChildHeap 1 [0] := by
  intro h
  exact h 0 (ClientReachable.direct (by simp)) repeatedChild_mem

/-! ## Three-level heaps: the shared grandchild and its unique control -/

def grRootObj : Obj := ⟨#[.ref 1, .ref 2], 1, false⟩

/-- The left child's slot names its own grandchild `ref 3`. -/
def grLeftObj : Obj := ⟨#[.ref 3], 1, false⟩

/-- The right child's slot names its own grandchild `ref 4`. -/
def grRightObj : Obj := ⟨#[.ref 4], 1, false⟩

def grLeafObj : Obj := ⟨#[.scalar 0], 1, false⟩

/-- Root → two distinct children → each child's own distinct grandchild, every
live cell counted once. -/
def uniqueGrandH : Heap :=
  { cells := fun r =>
      if r = 0 then some grRootObj
      else if r = 1 then some grLeftObj
      else if r = 2 then some grRightObj
      else if r = 3 then some grLeafObj
      else if r = 4 then some grLeafObj
      else none
    next := 5 }

theorem uniqueGrand_cells {r : Ref} {o : Obj} (h : uniqueGrandH.cells r = some o) :
    o = grRootObj ∨ o = grLeftObj ∨ o = grRightObj ∨ o = grLeafObj := by
  by_cases h0 : r = 0
  · subst h0
    exact Or.inl (obj_eq_of_cells h (by simp [uniqueGrandH]))
  · by_cases h1 : r = 1
    · subst h1
      exact Or.inr (Or.inl (obj_eq_of_cells h (by simp [uniqueGrandH])))
    · by_cases h2 : r = 2
      · subst h2
        exact Or.inr (Or.inr (Or.inl (obj_eq_of_cells h (by simp [uniqueGrandH]))))
      · by_cases h3 : r = 3
        · subst h3
          exact Or.inr (Or.inr (Or.inr (obj_eq_of_cells h (by simp [uniqueGrandH]))))
        · by_cases h4 : r = 4
          · subst h4
            exact Or.inr (Or.inr (Or.inr (obj_eq_of_cells h (by simp [uniqueGrandH]))))
          · have hc : uniqueGrandH.cells r = none := by
              simp [uniqueGrandH, h0, h1, h2, h3, h4]
            rw [hc] at h
            simp at h

/-- Any live cell of the control heap is counted once. -/
theorem uniqueGrand_rc {r : Ref} {o : Obj} (h : uniqueGrandH.cells r = some o) :
    uniqueGrandH.rc r = 1 := by
  have hc := h
  obtain ho | ho | ho | ho := uniqueGrand_cells h
  · subst ho; simp [Heap.rc, hc, grRootObj]
  · subst ho; simp [Heap.rc, hc, grLeftObj]
  · subst ho; simp [Heap.rc, hc, grRightObj]
  · subst ho; simp [Heap.rc, hc, grLeafObj]

/-- The unique three-level control: a genuine root → child → grandchild tree, two
levels deep, satisfies the transitive `UniqueTree`. The one-level relation could
not state this, let alone prove it. -/
theorem uniqueGrandchild_unique : UniqueTree uniqueGrandH 0 := by
  intro r hr
  cases hr with
  | root hcell _ => exact uniqueGrand_rc hcell
  | step _ _ _ _ hcell' _ => exact uniqueGrand_rc hcell'

/-- The shared-grandchild heap: both children's slots name the same grandchild
`ref 3`, so its count is two. -/
def sharedGrandH : Heap :=
  { cells := fun r =>
      if r = 0 then some ⟨#[.ref 1, .ref 2], 1, false⟩
      else if r = 1 then some ⟨#[.ref 3], 1, false⟩
      else if r = 2 then some ⟨#[.ref 3], 1, false⟩
      else if r = 3 then some ⟨#[.scalar 0], 2, false⟩
      else none
    next := 4 }

theorem sharedGrand_root : MutableFootprint sharedGrandH 0 0 :=
  MutableFootprint.root (o := ⟨#[.ref 1, .ref 2], 1, false⟩)
    (by simp [sharedGrandH]) (by simp)

theorem sharedGrand_footprint_child : MutableFootprint sharedGrandH 0 1 :=
  MutableFootprint.step (o := ⟨#[.ref 1, .ref 2], 1, false⟩) (r' := 1)
    (o' := ⟨#[.ref 3], 1, false⟩) sharedGrand_root
    (by simp [sharedGrandH]) (by simp) (by simp [fieldRefs, refsOf])
    (by simp [sharedGrandH]) (by simp)

/-- The grandchild is two hops from the root: root → child → grandchild. -/
theorem sharedGrand_mem : MutableFootprint sharedGrandH 0 3 :=
  MutableFootprint.step (o := ⟨#[.ref 3], 1, false⟩) (r' := 3)
    (o' := ⟨#[.scalar 0], 2, false⟩) sharedGrand_footprint_child
    (by simp [sharedGrandH]) (by simp) (by simp [fieldRefs, refsOf])
    (by simp [sharedGrandH]) (by simp)

/-- The grandchild is reachable from the root at depth two, but it is named
twice, so the mutable footprint is not unique. Under the one-level footprint this
heap looked exactly like its unique control. -/
theorem sharedGrandchild_not_unique : ¬ UniqueTree sharedGrandH 0 := by
  intro h
  have hrc := h 3 sharedGrand_mem
  simp [sharedGrandH, Heap.rc] at hrc

/-- The shared grandchild is reachable through either child, so a client handle
on it violates separation as well. -/
theorem sharedGrand_client_not_separated :
    ¬ ClientSeparated sharedGrandH 0 [3] := by
  intro h
  exact h 3 (ClientReachable.direct (by simp)) sharedGrand_mem

/-! ## Indirect external-client reachability -/

/-- The client holds a wrapper (`ref 5`) that is *not* in the footprint; the
wrapper's own field names a footprint cell (`ref 1`, the root's child). -/
def indirectClientH : Heap :=
  { cells := fun r =>
      if r = 0 then some ⟨#[.ref 1], 1, false⟩
      else if r = 1 then some ⟨#[.scalar 0], 1, false⟩
      else if r = 5 then some ⟨#[.ref 1], 1, false⟩
      else none
    next := 6 }

/-- The root's own cell is in the footprint. -/
theorem indirectClient_root : MutableFootprint indirectClientH 0 0 :=
  MutableFootprint.root (o := ⟨#[.ref 1], 1, false⟩)
    (by simp [indirectClientH]) (by simp)

/-- The root's child `ref 1` is in the footprint. -/
theorem indirectClient_child : MutableFootprint indirectClientH 0 1 :=
  MutableFootprint.step (o := ⟨#[.ref 1], 1, false⟩) (r' := 1)
    (o' := ⟨#[.scalar 0], 1, false⟩) indirectClient_root
    (by simp [indirectClientH]) (by simp) (by simp [fieldRefs, refsOf])
    (by simp [indirectClientH]) (by simp)

/-- The client's own handle, the wrapper `ref 5`, is live. -/
theorem indirectClient_wrapper_cell :
    indirectClientH.cells 5 = some ⟨#[.ref 1], 1, false⟩ := by
  simp [indirectClientH]

/-- The client reaches the root's child indirectly: through the wrapper `ref 5`
the client holds, not by naming the child itself. -/
theorem indirectClient_reachable : ClientReachable indirectClientH [5] 1 :=
  ClientReachable.step (r' := 1) (ClientReachable.direct (by simp))
    indirectClient_wrapper_cell (by simp [fieldRefs, refsOf])

/-- An indirect client reference violates separation even though the client's own
handle is not in the footprint. -/
theorem indirectClient_not_separated : ¬ ClientSeparated indirectClientH 0 [5] := by
  intro h
  exact h 1 indirectClient_reachable indirectClient_child

/-- The client's own handle is not a footprint cell: the violation is indirect,
not a direct membership. -/
theorem indirectClient_wrapper_outside : ¬ MutableFootprint indirectClientH 0 5 := by
  refine not_mutable_of_persistent_parents (by decide) ?_
  intro q o hcell hmem
  by_cases h0 : q = 0
  · have ho : o = ⟨#[.ref 1], 1, false⟩ :=
      obj_eq_of_cells hcell (by simp [indirectClientH, h0])
    subst ho
    simp [fieldRefs, refsOf] at hmem
  · by_cases h1 : q = 1
    · have ho : o = ⟨#[.scalar 0], 1, false⟩ :=
        obj_eq_of_cells hcell (by simp [indirectClientH, h0, h1])
      subst ho
      simp [fieldRefs, refsOf] at hmem
    · by_cases h5 : q = 5
      · have ho : o = ⟨#[.ref 1], 1, false⟩ :=
          obj_eq_of_cells hcell (by simp [indirectClientH, h0, h1, h5])
        subst ho
        simp [fieldRefs, refsOf] at hmem
      · have hc : indirectClientH.cells q = none := by
          simp [indirectClientH, h0, h1, h5]
        rw [hc] at hcell
        simp at hcell

/-! ## Immutable observations are excluded from the mutable footprint -/

/-- The root's slot names a persistent child, whose own field names a
grandchild. -/
def immutableChildH : Heap :=
  { cells := fun r =>
      if r = 0 then some ⟨#[.ref 1], 1, false⟩
      else if r = 1 then some ⟨#[.ref 2], 1, true⟩
      else if r = 2 then some ⟨#[.scalar 0], 1, false⟩
      else none
    next := 3 }

theorem immutableChild_root : MutableFootprint immutableChildH 0 0 :=
  MutableFootprint.root (o := ⟨#[.ref 1], 1, false⟩)
    (by simp [immutableChildH]) (by simp)

/-- A persistent child may be shared, so it is not in the mutable footprint. -/
theorem persistentChild_not_mutable : ¬ MutableFootprint immutableChildH 0 1 := by
  intro h
  obtain ⟨o, hcell, hpers⟩ := MutableFootprint.cell_nonPersistent h
  have ho : o = ⟨#[.ref 2], 1, true⟩ :=
    obj_eq_of_cells hcell (by simp [immutableChildH])
  subst ho
  simp at hpers

/-- Traversal does not continue through the persistent child, so the grandchild
behind it is not in the mutable footprint either. -/
theorem persistentGrandchild_not_mutable : ¬ MutableFootprint immutableChildH 0 2 := by
  refine not_mutable_of_persistent_parents (by decide) ?_
  intro q o hcell hmem
  by_cases h0 : q = 0
  · have ho : o = ⟨#[.ref 1], 1, false⟩ :=
      obj_eq_of_cells hcell (by simp [immutableChildH, h0])
    subst ho
    simp [fieldRefs, refsOf] at hmem
  · by_cases h1 : q = 1
    · have ho : o = ⟨#[.ref 2], 1, true⟩ :=
        obj_eq_of_cells hcell (by simp [immutableChildH, h0, h1])
      subst ho
      rfl
    · by_cases h2 : q = 2
      · have ho : o = ⟨#[.scalar 0], 1, false⟩ :=
          obj_eq_of_cells hcell (by simp [immutableChildH, h0, h1, h2])
        subst ho
        simp [fieldRefs, refsOf] at hmem
      · have hc : immutableChildH.cells q = none := by
          simp [immutableChildH, h0, h1, h2]
        rw [hc] at hcell
        simp at hcell

/-! ## The fresh-array initializer -/

/-- The fresh array's footprint is just the root: the array's fields are
scalars, so the relation has no step to take. -/
theorem freshArray_unique (n : Nat) : UniqueTree (initHeap n).2 (initHeap n).1 := by
  intro r hr
  obtain ⟨o, hcell, _⟩ := MutableFootprint.cell_nonPersistent hr
  have ho : o = ⟨Array.replicate n (Val.scalar 0), 1, false⟩ := by
    by_cases h0 : r = 0
    · subst h0
      have := hcell.symm; simp [initHeap] at this; exact this
    · simp [initHeap, h0] at hcell
  subst ho
  rw [Heap.rc, hcell]
  rfl

/-- No reference is client-reachable from an empty client handle set: without a
handle to start from, the relation has no derivation. -/
theorem ClientReachable.isEmpty {H : Heap} {r : Ref}
    (h : ClientReachable H [] r) : False := by
  induction h with
  | direct h => simp at h
  | step _ _ _ ih => exact ih

/-- A fresh array has no client-reachable references, so separation is
immediate. -/
theorem freshArray_separated (n : Nat) :
    ClientSeparated (initHeap n).2 (initHeap n).1 [] := by
  intro r hr _
  exact ClientReachable.isEmpty hr

/-- The initializer's only owned variable denotes the root itself, which is a
footprint cell, so the initializer's context is complete. -/
theorem freshArray_complete (n : Nat) :
    RootsComplete (initCtx (initHeap n).1) (initHeap n).2 (initHeap n).1 := by
  intro x r hx hr
  have hx0 : x = 0 := by
    by_cases h0 : x = 0
    · exact h0
    · by_cases h1 : x = 1
      · subst h1; simp [initCtx, h0] at hx
      · by_cases h2 : x = 2
        · subst h2; simp [initCtx, h0, h1] at hx
        · simp [initCtx, h0, h1, h2] at hx
  subst hx0
  have hr0 : r = (initHeap n).1 := by
    simpa [initCtx] using hr.symm
  subst hr0
  exact MutableFootprint.root (o := ⟨Array.replicate n (Val.scalar 0), 1, false⟩)
    (by simp [initHeap]) (by simp)

/-- The initializer establishes the concrete entry condition. -/
theorem initEntryInv (n : Nat) :
    EntryInv (initHeap n).2 (initEnv (initHeap n).1) (initCtx (initHeap n).1)
      (initHeap n).1 [] :=
  { toInv := initInv n
    uniqueTree := freshArray_unique n
    separated := freshArray_separated n
    complete := freshArray_complete n }

/-- A1 under the entry condition: the measured write prefix is fault-free and
every write is exclusive. -/
theorem artifact_entry (n : Nat) :
    ∃ H' env' v ws,
      run (execSet 0 3 1 2) (initEnv (initHeap n).1) (initHeap n).2 =
        .done H' env' v ws ∧
      (∀ w ∈ ws, w.2 = true) :=
  accepted_no_fault_and_exclusive_writes
    (execSet_check (initHeap n).1) (initEntryInv n).toInv

/-! ## Deriving the nested checker's heap premise -/

open Ownership.Nested

/-- The state-indexed heap premise of the nested checker, derived from the
handle/count invariant, the checker's acceptance and the heap/program agreement.

The invariant supplies every existence and multiplicity fact the obligation
needs — the owned array's cell is live because its multiplicity is one and the
counts agree, the index and the environment bindings are where the invariant
puts them — and the agreement supplies the one thing the invariant cannot: which
object each take-out's annotation names. A recursive call's continuation
obligation is derived on whatever heap the body leaves, using the body's own
soundness for the caller's invariant at that heap. -/
theorem takeOutsOK_of_inv {code : NCode} :
    ∀ {H : Heap} {env : Env} {c : Ctx} {fs : List Frame} {ctx' : Ctx},
      Inv H env c → Agrees H env code → checkNF c fs code = some ctx' →
        TakeOutsOK H env code := by
  induction code with
  | base code => intro H env c fs ctx' hi hagree hc; trivial
  | ret x => intro H env c fs ctx' hi hagree hc; trivial
  | takeOut a i fst snd e k ih =>
      intro H env c fs ctx' hi hagree hc
      obtain ⟨r0, o, idx, ha', hi', hcell, hfield, hagree'⟩ := hagree
      by_cases hx : c.us a = .owned ∧ c.multOf a = 1 ∧ c.us i = .scalar ∧
          c.mult e = 1 ∧ c.us fst = .dead ∧ c.us snd = .dead ∧ fst ≠ snd
      · have hxc := hx
        obtain ⟨ha, hm, hi_us, he, hfst, hsnd, hfs⟩ := hx
        cases hr : c.refOf a with
        | none => simp [checkNF, hxc, hr] at hc
        | some r =>
            have henv_a : env a = some (.ref r) := (hi.owned a r ha hr).1
            have hrq : r = r0 := by
              rw [henv_a] at ha'
              exact Val.ref.inj (Option.some.inj ha')
            subst r0
            by_cases hne : e = r
            · simp [checkNF, hxc, hr, hne] at hc
            · by_cases hopen : openRef fs r = true
              · simp [checkNF, hxc, hr, hne, hopen] at hc
              · have hopenf : openRef fs r = false := by
                  cases h : openRef fs r with
                  | false => rfl
                  | true => exact absurd h hopen
                have hc' : checkNF ((c.move a fst).bindOwned snd e)
                    ({ arr := r, idx := i, elem := e } :: fs) k = some ctx' := by
                  rw [checkNF_takeOut c fs a i fst snd e k r
                        ⟨ha, hm, hi_us, he, hfst, hsnd, hfs⟩ hr hne hopenf] at hc
                  exact hc
                have hi_move : Inv H (env.set fst (.ref r)) (c.move a fst) :=
                  Inv.move hi ha hr
                have hi_bind : Inv H ((env.set fst (.ref r)).set snd (.ref e))
                    ((c.move a fst).bindOwned snd e) :=
                  Inv.bindOwned hi_move he
                have hi_new : Inv (H.set r { o with fields := o.fields.setIfInBounds idx (.scalar 0) })
                    ((env.set fst (.ref r)).set snd (.ref e))
                    ((c.move a fst).bindOwned snd e) :=
                  Inv.setFields hi_bind hcell
                exact ⟨r, o, idx, henv_a, hi', hcell, hfield, hne,
                  ih hi_new hagree' hc'⟩
      · simp [checkNF, hx] at hc
  | putBack a e i result k ih =>
      intro H env c fs ctx' hi hagree hc
      obtain ⟨r0, re0, o, idx, ha', he', hi', hcell, hagree'⟩ := hagree
      by_cases hx : c.us a = .owned ∧ c.multOf a = 1 ∧ c.us e = .owned ∧
          c.multOf e = 1 ∧ c.us i = .scalar ∧ c.us result = .dead ∧
          e ≠ a ∧ e ≠ result
      · have hxc := hx
        obtain ⟨ha, hm, he_us, he_m, hi_us, hres, hne_a, hne_res⟩ := hx
        cases hr : c.refOf a with
        | none => simp [checkNF, hxc, hr] at hc
        | some r =>
            cases hre : c.refOf e with
            | none => simp [checkNF, hxc, hr, hre] at hc
            | some re =>
                cases fs with
                | nil => simp [checkNF, hxc, hr, hre] at hc
                | cons f rest =>
                    have henv_a : env a = some (.ref r) := (hi.owned a r ha hr).1
                    have henv_e : env e = some (.ref re) := (hi.owned e re he_us hre).1
                    have hrq : r = r0 := by
                      rw [henv_a] at ha'
                      exact Val.ref.inj (Option.some.inj ha')
                    have hreq : re = re0 := by
                      rw [henv_e] at he'
                      exact Val.ref.inj (Option.some.inj he')
                    subst r0
                    subst re0
                    by_cases hf : f.arr = r ∧ f.idx = i ∧ f.elem = re
                    · obtain ⟨hf1, hf2, hf3⟩ := hf
                      have hc' : checkNF ((c.move a result).setUs e .dead) rest k = some ctx' := by
                        rw [checkNF_putBack c (f :: rest) f rest a e i result k r re
                              ⟨ha, hm, he_us, he_m, hi_us, hres, hne_a, hne_res⟩ hr hre
                              ⟨hf1, hf2, hf3⟩] at hc
                        exact hc
                      have hi_move : Inv (H.set r { o with fields := o.fields.set! idx (.ref re) })
                          (env.set result (.ref r)) (c.move a result) :=
                        Inv.setFields (Inv.move hi ha hr) hcell
                      have hi_dead : Inv (H.set r { o with fields := o.fields.set! idx (.ref re) })
                          (env.set result (.ref r)) ((c.move a result).setUs e .dead) :=
                        Inv.setDead hi_move
                      exact ⟨r, re, o, idx, henv_a, henv_e, hi', hcell,
                        ih hi_dead hagree' hc'⟩
                    · simp [checkNF, hxc, hr, hre, hf] at hc
      · simp [checkNF, hx] at hc
  | callAt state path x result body k ihbody ihk =>
      intro H env c fs ctx' hi hagree hc
      obtain ⟨r0, henv_s, hagreeb, hagreek⟩ := hagree
      by_cases hx : c.us state = .owned ∧ c.multOf state = 1 ∧
          c.us path = .scalar ∧ c.us x = .scalar ∧ c.us result = .dead ∧
          CountFree body = true
      · have hxc := hx
        obtain ⟨hs, hm, hp, hxus, hres, hcf⟩ := hx
        cases hr : c.refOf state with
        | none => simp [checkNF, hxc, hr] at hc
        | some r =>
            have henv_s' : env state = some (.ref r) := (hi.owned state r hs hr).1
            have hrq : r = r0 := by
              rw [henv_s'] at henv_s
              exact Val.ref.inj (Option.some.inj henv_s)
            subst r0
            by_cases hopen : openRef fs r = true
            · simp [checkNF, hxc, hr, hopen] at hc
            · have hopenf : openRef fs r = false := by
                cases h : openRef fs r with
                | false => rfl
                | true => exact absurd h hopen
              obtain ⟨cb, y, hcbody, hret, hcbus, hcbref, hc'⟩ :=
                checkNF_callAt_some (c := c) (fs := fs) (r := r) (k := k) (body := body)
                  ⟨hs, hm, hp, hxus, hres, hcf⟩ hr hopenf hc
              have hmul : c.mult r = 1 := by
                simpa [Ctx.multOf, hr] using hm
              have hex : H.exclusive? r = true :=
                (Heap.exclusive?_eq_true).mpr (hi.exclusive hmul)
              have hi_iso : Inv H (isolateEnv env state path x)
                  (isolatedCtx c state path x r) :=
                inv_isolated hi hs hr hp hxus
              have hokb : TakeOutsOK H (isolateEnv env state path x) body :=
                ihbody hi_iso hagreeb hcbody
              refine ⟨r, henv_s', hex, hokb, ?_⟩
              intro H' envb vb wsb hrunb
              obtain ⟨H'', env'', v'', ws'', hrun'', hws'', hinv''⟩ :=
                checkN_sound hcbody hi_iso hokb
              rw [hrunb] at hrun''
              injection hrun'' with hH henv hv hws'
              subst hH
              have hcbm : ∀ q, cb.mult q = c.mult q :=
                countFree_check_mult (ctx := isolatedCtx c state path x r) hcf hcbody
              have hi_ctx : Inv H' env c :=
                inv_of_rc_cells hi (fun q => by rw [hinv''.rc_eq q, hcbm q])
                  (fun q hq => runN_cells_none hrunb q hq) hinv''.nonPersistent
              have hi_cont : Inv H' (env.set result (.ref r)) (c.move state result) :=
                Inv.move hi_ctx hs hr
              exact ihk hi_cont (hagreek H' envb vb wsb hrunb) hc'
      · simp [checkNF, hx] at hc

/-- `TakeOutsOK` from the entry invariant, the heap/program agreement premise and
checker acceptance: no caller has to discharge the heap obligation separately.
The agreement premise is load-bearing and cannot be dropped: the `.takeOut`
obligation contains the slot-content equality, which no `EntryInv` field and no
checker rule can imply. -/
theorem takeOutsOK_of_entryInv {H : Heap} {env : Env} {c : Ctx} {root : Ref}
    {client : List Ref} {code : NCode} {ctx' : Ctx}
    (hEntry : EntryInv H env c root client) (hagree : Agrees H env code)
    (hc : checkN c code = some ctx') :
    TakeOutsOK H env code :=
  takeOutsOK_of_inv hEntry.toInv hagree hc (fs := [])

/-- The nested checker's soundness from the entry invariant alone (plus the
heap/program agreement premise): the `TakeOutsOK` hypothesis is derived, not
supplied. -/
theorem checkN_sound_of_entryInv {H : Heap} {env : Env} {c : Ctx} {root : Ref}
    {client : List Ref} {code : NCode} {ctx' : Ctx}
    (hEntry : EntryInv H env c root client) (hagree : Agrees H env code)
    (hc : checkN c code = some ctx') :
    ∃ H' env' v ws, runN code env H = .done H' env' v ws ∧
      (∀ w ∈ ws, w.2 = true) ∧ Inv H' env' ctx' :=
  checkN_sound hc hEntry.toInv (takeOutsOK_of_entryInv hEntry hagree hc)

/-! ## The recursive body touches nothing outside its own subtree -/

/-- The program's extraction annotations name cells in the footprint: each
take-out's annotated element, and every annotation of a recursive body and of its
continuation. This is the reachability premise the checker cannot state — a
handle's multiplicity being one does not place it in the root's footprint, and
the checker never sees a slot's contents. -/
def AnnotationsIn (H : Heap) (r : Ref) : NCode → Prop
  | .base _ | .ret _ => True
  | .takeOut _ _ _ _ e k => MutableFootprint H r e ∧ AnnotationsIn H r k
  | .putBack _ _ _ _ k => AnnotationsIn H r k
  | .callAt _ _ _ _ body k => AnnotationsIn H r body ∧ AnnotationsIn H r k

/-- Every handle the checker's context exposes (owned or borrowed) denotes a cell
in the root's footprint. -/
def LiveIn (c : Ctx) (H : Heap) (r : Ref) : Prop :=
  ∀ z q, (c.us z = .owned ∨ c.us z = .borrow) → c.refOf z = some q →
    MutableFootprint H r q

/-- The heap agrees with the entry heap outside the root's mutable footprint. -/
def Outside (H : Heap) (H0 : Heap) (r : Ref) : Prop :=
  ∀ q, ¬ MutableFootprint H0 r q → H.cells q = H0.cells q

theorem LiveIn.setUs {c : Ctx} {H : Heap} {r : Ref} {z : Var} {u : U}
    (h : LiveIn c H r) (ho : u ≠ .owned) (hb : u ≠ .borrow) :
    LiveIn (c.setUs z u) H r := by
  intro z' q hz hq
  by_cases hzz : z' = z
  · subst z'
    have hcs : (c.setUs z u).us z = u := Ctx.setUs_self c z u
    rw [hcs] at hz
    rcases hz with hz | hz
    · exact absurd hz ho
    · exact absurd hz hb
  · have h2 : c.refOf z' = some q := by simpa using hq
    exact h z' q (by simpa [Ctx.setUs, hzz] using hz) h2

theorem LiveIn.move {c : Ctx} {H : Heap} {r : Ref} {x y : Var}
    (h : LiveIn c H r) : LiveIn (c.move x y) H r := by
  intro z q hz hq
  by_cases hzy : z = y
  · subst z
    have h1 : (c.move x y).us y = c.us x := Ctx.move_us_y c x y
    have h2 : (c.move x y).refOf y = c.refOf x := Ctx.move_refOf_y c x y
    exact h x q (by rw [← h1]; exact hz) (by rw [← h2]; exact hq)
  · by_cases hzx : z = x
    · subst z
      have hd : (c.move x y).us x = .dead := by simp [Ctx.move, hzy]
      rw [hd] at hz
      rcases hz with hz | hz <;> simp at hz
    · have h2 : c.refOf z = some q := by simpa [Ctx.move, hzy] using hq
      exact h z q (by simpa [Ctx.move, hzy, hzx] using hz) h2

theorem LiveIn.bindOwned {c : Ctx} {H : Heap} {r : Ref} {x : Var} {e : Ref}
    (h : LiveIn c H r) (he : MutableFootprint H r e) : LiveIn (c.bindOwned x e) H r := by
  intro z q hz hq
  by_cases hzx : z = x
  · subst z
    have h2 : (c.bindOwned x e).refOf x = some e := by simp [Ctx.bindOwned]
    rw [h2] at hq
    have hq' : e = q := Option.some.inj hq
    subst hq'
    exact he
  · have h2 : c.refOf z = some q := by simpa [Ctx.bindOwned, hzx] using hq
    exact h z q (by simpa [Ctx.bindOwned, hzx] using hz) h2

theorem LiveIn.inc {c : Ctx} {H : Heap} {r : Ref} {q : Ref} {n : Nat}
    (h : LiveIn c H r) : LiveIn (c.inc q n) H r := by
  intro z q hz hq
  exact h z q (by simpa [Ctx.inc] using hz) (by simpa [Ctx.inc] using hq)

theorem LiveIn.dec {c : Ctx} {H : Heap} {r : Ref} {q : Ref} {z : Var} {n : Nat}
    (h : LiveIn c H r) : LiveIn ((c.dec q n).setUs z .dead) H r := by
  refine LiveIn.setUs (h := ?_) (by simp) (by simp)
  intro z' q' hz hq
  exact h z' q' (by simpa [Ctx.dec] using hz) (by simpa [Ctx.dec] using hq)

/-- Writing a footprint cell leaves every cell outside the footprint alone. -/
theorem Outside.set_footprint {H H0 : Heap} {r q : Ref} {o : Obj}
    (h : Outside H H0 r) (hq : MutableFootprint H0 r q) :
    Outside (H.set q o) H0 r := by
  intro q' hq'
  by_cases hqq : q' = q
  · subst q'; exact absurd hq hq'
  · rw [Heap.set_other _ _ _ _ hqq]; exact h q' hq'

/-- A straight-line block whose every write is exclusive and whose context only
exposes footprint handles leaves the heap outside the footprint untouched. -/
theorem run_confined {code : Code} :
    ∀ {c : Ctx} {H0 : Heap} {r : Ref} {ctx' : Ctx} {env : Env} {H H' : Heap}
      {env' : Env} {v : Val} {ws : List Write},
      Inv H env c → LiveIn c H0 r → Outside H H0 r →
      check c code = some ctx' → (∀ w ∈ ws, w.2 = true) →
      run code env H = .done H' env' v ws → Outside H' H0 r := by
  induction code with
  | «let» x w k ih =>
      intro c H0 r ctx' env H H' env' v ws hi hlive hout hc hall hrun
      cases w with
      | lit n =>
          exact ih (hi.setScalar (n := n)) (LiveIn.setUs hlive (by simp) (by simp)) hout
            (by simpa [check] using hc) hall (by simpa [run] using hrun)
      | size a =>
          cases hr : c.refOf a with
          | none => simp [check, hr] at hc
          | some r0 =>
              by_cases hu : c.us a = .owned ∨ c.us a = .borrow
              · simp only [check, hr, hu, if_true] at hc
                obtain ⟨o, ho⟩ := hi.cell_of_ref hu hr
                exact ih (hi.setScalar (n := _)) (LiveIn.setUs hlive (by simp) (by simp)) hout hc hall
                  (by simpa [run, hi.isRef hu hr, ho] using hrun)
              · simp [check, hr, hu] at hc
      | isShared z =>
          cases hr : c.refOf z with
          | none => simp [check, hr] at hc
          | some r0 =>
              by_cases hu : c.us z = .owned ∨ c.us z = .borrow
              · simp only [check, hr, hu, if_true] at hc
                obtain ⟨o, ho⟩ := hi.cell_of_ref hu hr
                exact ih (hi.setScalar (n := _)) (LiveIn.setUs hlive (by simp) (by simp)) hout hc hall
                  (by simpa [run, hi.isRef hu hr, ho] using hrun)
              · simp [check, hr, hu] at hc
      | checkAlias z =>
          by_cases hx : c.us z = .owned ∧ c.multOf z = 1
          · simp only [check, hx, if_true] at hc
            obtain ⟨hx1, hx2⟩ := hx
            obtain ⟨r0, hr0, hmul⟩ := Ctx.multOf_eq_one hx2
            have htrue : H.exclusive? r0 = true :=
              (Heap.exclusive?_eq_true).mpr (hi.exclusive hmul)
            exact ih (hi.move hx1 hr0) (LiveIn.move hlive) hout hc hall (by
              have hr' := hrun
              unfold run at hr'
              simp only [hi.isRef (Or.inl hx1) hr0] at hr'
              rw [if_pos htrue] at hr'
              exact hr')
          · simp [check, hx] at hc
  | inc x n k ih =>
      intro c H0 r ctx' env H H' env' v ws hi hlive hout hc hall hrun
      cases hr : c.refOf x with
      | none => simp [check, hr] at hc
      | some r0 =>
          by_cases hx : c.us x = .owned
          · simp only [check, hr, hx, if_true] at hc
            have hfp : MutableFootprint H0 r r0 := hlive x r0 (Or.inl hx) hr
            obtain ⟨o, ho⟩ := hi.cell_of_ref (Or.inl hx) hr
            have hout' : Outside (H.inc r0 n) H0 r := by
              have hinc : H.inc r0 n = H.set r0 { o with rc := o.rc + n } := by
                simp [Heap.inc, ho]
              rw [hinc]
              exact Outside.set_footprint hout hfp
            exact ih (hi.inc hx hr) (LiveIn.inc hlive) hout' hc hall
              (by simpa [run, hi.isRef (Or.inl hx) hr] using hrun)
          · simp [check, hr, hx] at hc
  | dec x n k ih =>
      intro c H0 r ctx' env H H' env' v ws hi hlive hout hc hall hrun
      cases hr : c.refOf x with
      | none => simp [check, hr] at hc
      | some r0 =>
          by_cases hx : c.us x = .owned ∧ n < c.mult r0
          · simp only [check, hr, hx, if_true] at hc
            obtain ⟨hx1, hn⟩ := hx
            have hfp : MutableFootprint H0 r r0 := hlive x r0 (Or.inl hx1) hr
            obtain ⟨o, ho⟩ := hi.cell_of_ref (Or.inl hx1) hr
            have hout' : Outside (H.dec r0 n) H0 r := by
              have hdec : H.dec r0 n = H.set r0 { o with rc := o.rc - n } := by
                simp [Heap.dec, ho]
              rw [hdec]
              exact Outside.set_footprint hout hfp
            exact ih (hi.dec hx1 hr hn) (LiveIn.dec hlive) hout' hc hall
              (by simpa [run, hi.isRef (Or.inl hx1) hr] using hrun)
          · simp [check, hr, hx] at hc
  | check x k ih =>
      intro c H0 r ctx' env H H' env' v ws hi hlive hout hc hall hrun
      by_cases hx : c.us x = .owned ∧ c.multOf x = 1
      · simp only [check, hx, if_true] at hc
        obtain ⟨hx1, hm⟩ := hx
        obtain ⟨r0, hr0, hmul⟩ := Ctx.multOf_eq_one hm
        have htrue : H.exclusive? r0 = true :=
          (Heap.exclusive?_eq_true).mpr (hi.exclusive hmul)
        exact ih hi hlive hout hc hall (by
          have hr' := hrun
          unfold run at hr'
          simp only [hi.isRef (Or.inl hx1) hr0] at hr'
          rw [if_pos htrue] at hr'
          exact hr')
      · simp [check, hx] at hc
  | setArr x i v' k ih =>
      intro c H0 r ctx' env H H' env' v ws hi hlive hout hc hall hrun
      by_cases hx : c.us x = .owned ∧ c.multOf x = 1 ∧ c.us i = .scalar ∧
          c.us v' = .scalar
      · simp only [check, hx, if_true] at hc
        obtain ⟨hx1, hm, hi_us, hv'⟩ := hx
        obtain ⟨r0, hr0, hmul⟩ := Ctx.multOf_eq_one hm
        have hfp : MutableFootprint H0 r r0 := hlive x r0 (Or.inl hx1) hr0
        have htrue : H.exclusive? r0 = true :=
          (Heap.exclusive?_eq_true).mpr (hi.exclusive hmul)
        obtain ⟨o, ho⟩ := hi.cell_of_ref (Or.inl hx1) hr0
        obtain ⟨idx, hidx⟩ := hi.scalar i hi_us
        obtain ⟨val, hval⟩ := hi.scalar v' hv'
        have hrun0 : (run k (env.set x (.ref r0))
            (H.set r0 { o with fields := o.fields.set! idx (.scalar val) })).addWrite
            (r0, true) = .done H' env' v ws := by
          simpa [run, hi.isRef (Or.inl hx1) hr0, hidx, hval, ho, htrue] using hrun
        obtain ⟨ws0, hk⟩ := addWrite_done hrun0
        have hws : ws = (r0, true) :: ws0 := by
          rw [hk] at hrun0
          simp only [Res.addWrite] at hrun0
          injection hrun0 with _ _ _ hws'
          exact hws'.symm
        refine ih (Inv.setArr hi hx1 hr0 ho) hlive (Outside.set_footprint hout hfp)
          hc ?_ hk
        intro w hw
        exact hall w (by rw [hws]; exact List.mem_cons_of_mem _ hw)
      · simp [check, hx] at hc
  | ret x =>
      intro c H0 r ctx' env H H' env' v ws hi hlive hout hc hall hrun
      simp only [run] at hrun
      injection hrun with h1 _ _ _
      subst h1
      exact hout

/-- A nested program whose every write is exclusive, whose context only exposes
footprint handles, and whose extraction annotations name footprint cells leaves
the heap outside the footprint untouched. The recursive call's body is checked
and run from the isolated context and environment, so its own `LiveIn` is just
the root membership. -/
theorem runN_confined {code : NCode} :
    ∀ {c : Ctx} {H0 : Heap} {r : Ref} {fs : List Frame} {ctx' : Ctx} {env : Env}
      {H H' : Heap} {env' : Env} {v : Val} {ws : List Write},
      Inv H env c → LiveIn c H0 r → Outside H H0 r →
      AnnotationsIn H0 r code → checkNF c fs code = some ctx' →
      TakeOutsOK H env code → (∀ w ∈ ws, w.2 = true) →
      runN code env H = .done H' env' v ws → Outside H' H0 r := by
  induction code with
  | base code =>
      intro c H0 r fs ctx' env H H' env' v ws hi hlive hout hann hc hok hall hrun
      by_cases hfs : fs = []
      · subst hfs
        exact run_confined hi hlive hout (by simpa [checkNF] using hc) hall hrun
      · simp [checkNF, hfs] at hc
  | takeOut a i fst snd e k ih =>
      intro c H0 r fs ctx' env H H' env' v ws hi hlive hout hann hc hok hall hrun
      obtain ⟨he_mem, hann'⟩ := hann
      obtain ⟨r0, o, idx, ha', hi', hcell, hfield, hne, hok'⟩ := hok
      by_cases hx : c.us a = .owned ∧ c.multOf a = 1 ∧ c.us i = .scalar ∧
          c.mult e = 1 ∧ c.us fst = .dead ∧ c.us snd = .dead ∧ fst ≠ snd
      · have hxc := hx
        obtain ⟨ha, hm, hi_us, he, hfst, hsnd, hfs⟩ := hx
        cases hr : c.refOf a with
        | none => simp [checkNF, hxc, hr] at hc
        | some rarr =>
            have henv_a : env a = some (.ref rarr) := (hi.owned a rarr ha hr).1
            have hrq : rarr = r0 := by
              rw [henv_a] at ha'
              exact Val.ref.inj (Option.some.inj ha')
            subst r0
            by_cases hne' : e = rarr
            · simp [checkNF, hxc, hr, hne'] at hc
            · by_cases hopen : openRef fs rarr = true
              · simp [checkNF, hxc, hr, hne', hopen] at hc
              · have hopenf : openRef fs rarr = false := by
                  cases h : openRef fs rarr with
                  | false => rfl
                  | true => exact absurd h hopen
                have hc' : checkNF ((c.move a fst).bindOwned snd e)
                    ({ arr := rarr, idx := i, elem := e } :: fs) k = some ctx' := by
                  rw [checkNF_takeOut c fs a i fst snd e k rarr
                        ⟨ha, hm, hi_us, he, hfst, hsnd, hfs⟩ hr hne' hopenf] at hc
                  exact hc
                have hfp : MutableFootprint H0 r rarr := hlive a rarr (Or.inl ha) hr
                have hlive' : LiveIn ((c.move a fst).bindOwned snd e) H0 r :=
                  LiveIn.bindOwned (LiveIn.move hlive) he_mem
                have hrun' : runN k ((env.set fst (.ref rarr)).set snd (.ref e))
                    (H.set rarr { o with fields := o.fields.setIfInBounds idx (.scalar 0) }) =
                    .done H' env' v ws := by
                  have hred := hrun
                  unfold runN at hred
                  simp only [henv_a, hi', hcell, hfield] at hred
                  exact hred
                exact ih (Inv.setFields (Inv.bindOwned (Inv.move hi ha hr) he) hcell)
                  hlive' (Outside.set_footprint hout hfp) hann' hc' hok' hall hrun'
      · simp [checkNF, hx] at hc
  | putBack a e i result k ih =>
      intro c H0 r fs ctx' env H H' env' v ws hi hlive hout hann hc hok hall hrun
      obtain ⟨r0, re0, o, idx, ha', he', hi', hcell, hok'⟩ := hok
      by_cases hx : c.us a = .owned ∧ c.multOf a = 1 ∧ c.us e = .owned ∧
          c.multOf e = 1 ∧ c.us i = .scalar ∧ c.us result = .dead ∧
          e ≠ a ∧ e ≠ result
      · have hxc := hx
        obtain ⟨ha, hm, he_us, he_m, hi_us, hres, hne_a, hne_res⟩ := hx
        cases hr : c.refOf a with
        | none => simp [checkNF, hxc, hr] at hc
        | some rarr =>
            cases hre : c.refOf e with
            | none => simp [checkNF, hxc, hr, hre] at hc
            | some re =>
                cases fs with
                | nil => simp [checkNF, hxc, hr, hre] at hc
                | cons f rest =>
                    have henv_a : env a = some (.ref rarr) := (hi.owned a rarr ha hr).1
                    have henv_e : env e = some (.ref re) := (hi.owned e re he_us hre).1
                    have hrq : rarr = r0 := by
                      rw [henv_a] at ha'
                      exact Val.ref.inj (Option.some.inj ha')
                    have hreq : re = re0 := by
                      rw [henv_e] at he'
                      exact Val.ref.inj (Option.some.inj he')
                    subst r0
                    subst re0
                    by_cases hf : f.arr = rarr ∧ f.idx = i ∧ f.elem = re
                    · obtain ⟨hf1, hf2, hf3⟩ := hf
                      have hc' : checkNF ((c.move a result).setUs e .dead) rest k = some ctx' := by
                        rw [checkNF_putBack c (f :: rest) f rest a e i result k rarr re
                              ⟨ha, hm, he_us, he_m, hi_us, hres, hne_a, hne_res⟩ hr hre
                              ⟨hf1, hf2, hf3⟩] at hc
                        exact hc
                      have hfp : MutableFootprint H0 r rarr := hlive a rarr (Or.inl ha) hr
                      have hlive' : LiveIn ((c.move a result).setUs e .dead) H0 r :=
                        LiveIn.setUs (LiveIn.move hlive) (by simp) (by simp)
                      have hrun' : runN k (env.set result (.ref rarr))
                          (H.set rarr { o with fields := o.fields.set! idx (.ref re) }) =
                          .done H' env' v ws := by
                        have hred := hrun
                        unfold runN at hred
                        simp only [henv_a, henv_e, hi', hcell] at hred
                        exact hred
                      exact ih (Inv.setDead (Inv.setFields (Inv.move hi ha hr) hcell)) hlive'
                        (Outside.set_footprint hout hfp) hann hc' hok' hall hrun'
                    · simp [checkNF, hxc, hr, hre, hf] at hc
      · simp [checkNF, hx] at hc
  | callAt state path x result body k ihbody ihk =>
      intro c H0 r fs ctx' env H H' env' v ws hi hlive hout hann hc hok hall hrun
      obtain ⟨hannb, hannk⟩ := hann
      obtain ⟨r0, henv_s, hex, hokb, hokk⟩ := hok
      by_cases hx : c.us state = .owned ∧ c.multOf state = 1 ∧
          c.us path = .scalar ∧ c.us x = .scalar ∧ c.us result = .dead ∧
          CountFree body = true
      · have hxc := hx
        obtain ⟨hs, hm, hp, hxus, hres, hcf⟩ := hx
        cases hr : c.refOf state with
        | none => simp [checkNF, hxc, hr] at hc
        | some rarr =>
            have henv_s' : env state = some (.ref rarr) := (hi.owned state rarr hs hr).1
            have hrq : rarr = r0 := by
              rw [henv_s'] at henv_s
              exact Val.ref.inj (Option.some.inj henv_s)
            subst r0
            by_cases hopen : openRef fs rarr = true
            · simp [checkNF, hxc, hr, hopen] at hc
            · have hopenf : openRef fs rarr = false := by
                cases h : openRef fs rarr with
                | false => rfl
                | true => exact absurd h hopen
              obtain ⟨cb, y, hcbody, hret, hcbus, hcbref, hc'⟩ :=
                checkNF_callAt_some (c := c) (fs := fs) (r := rarr) (k := k) (body := body)
                  ⟨hs, hm, hp, hxus, hres, hcf⟩ hr hopenf hc
              have hi_iso : Inv H (isolateEnv env state path x)
                  (isolatedCtx c state path x rarr) :=
                inv_isolated hi hs hr hp hxus
              have hstate : MutableFootprint H0 r rarr := hlive state rarr (Or.inl hs) hr
              have hlive_iso : LiveIn (isolatedCtx c state path x rarr) H0 r := by
                intro z q hz hq
                rcases hz with hz | hz
                · have hzs : z = state := isolatedCtx_us_owned.mp hz
                  subst z
                  have hzr : (isolatedCtx c state path x rarr).refOf state = some rarr := by
                    simp [isolatedCtx]
                  rw [hzr] at hq
                  have hqr : q = rarr := (Option.some.inj hq).symm
                  rw [hqr]
                  exact hstate
                · exact absurd hz isolatedCtx_us_ne_borrow
              obtain ⟨Hb, envb, vb, wsb, hrunb, hwsb, hinvb⟩ :=
                checkN_sound hcbody hi_iso hokb
              have houtb : Outside Hb H0 r :=
                ihbody hi_iso hlive_iso hout hannb hcbody hokb hwsb hrunb
              obtain ⟨pn, hp'⟩ := hi.scalar path hp
              obtain ⟨xn, hx'⟩ := hi.scalar x hxus
              have hrun_all : addWrites (runN k (env.set result (.ref rarr)) Hb) wsb =
                  .done H' env' v ws := by
                have hred := hrun
                unfold runN at hred
                simp only [henv_s', hp', hx', hex, hrunb] at hred
                exact hred
              obtain ⟨ws0, hk⟩ := addWrites_done hrun_all
              have hws : ws = wsb ++ ws0 := by
                rw [hk] at hrun_all
                simp only [addWrites] at hrun_all
                injection hrun_all with _ _ _ hws'
                exact hws'.symm
              have hall' : ∀ w ∈ ws0, w.2 = true := by
                intro w hw
                exact hall w (by rw [hws]; exact List.mem_append_right _ hw)
              have hcbm : ∀ q, cb.mult q = c.mult q :=
                countFree_check_mult (ctx := isolatedCtx c state path x rarr) hcf hcbody
              have hi_ctx : Inv Hb env c :=
                inv_of_rc_cells hi (fun q => by rw [hinvb.rc_eq q, hcbm q])
                  (fun q hq => runN_cells_none hrunb q hq) hinvb.nonPersistent
              have hi_cont : Inv Hb (env.set result (.ref rarr)) (c.move state result) :=
                Inv.move hi_ctx hs hr
              exact ihk hi_cont (LiveIn.move hlive) houtb hannk hc'
                (hokk Hb envb vb wsb hrunb) hall' hk
      · simp [checkNF, hx] at hc
  | ret x =>
      intro c H0 r fs ctx' env H H' env' v ws hi hlive hout hann hc hok hall hrun
      simp only [runN] at hrun
      injection hrun with h1 _ _ _
      subst h1
      exact hout

/-- The recursive call's contract, both halves: a body the checker admits from
the isolated context runs fault-free, every write in its trace selects the
exclusive branch, it exits through a variable that still denotes the reference
the call was given, and — given that every extraction annotation names a
footprint cell — it touches no cell outside that reference's mutable footprint.
The body has its own environment, so a suspended parent frame's variables are
untouched, and it leaves the caller's continuation a heap that agrees with the
entry heap everywhere outside its own subtree. -/
theorem callAt_frame_confined {c : Ctx} {state path x : Var} {r : Ref} {body : NCode}
    {H : Heap} {env : Env} {cb : Ctx}
    (hann : AnnotationsIn H r body)
    (hc : checkNF (isolatedCtx c state path x r) [] body = some cb)
    (hret : ∃ y, retVar body = some y ∧ cb.us y = .owned ∧ cb.refOf y = some r)
    (hi : Inv H env (isolatedCtx c state path x r))
    (hok : TakeOutsOK H env body) :
    ∃ H' env' v ws, runN body env H = .done H' env' v ws ∧
      (∀ w ∈ ws, w.2 = true) ∧ v = .ref r ∧
      (∀ q, ¬ MutableFootprint H r q → H'.cells q = H.cells q) := by
  obtain ⟨H', env', v, ws, hrun, hws, hv⟩ :=
    callAt_frame_sound hc hret hi hok
  refine ⟨H', env', v, ws, hrun, hws, hv, ?_⟩
  have hroot : MutableFootprint H r r := by
    have hown := hi.owned state r (by simp [isolatedCtx]) (by simp [isolatedCtx])
    have hne : H.cells r ≠ none := hi.rc_ne_zero hown.2
    cases ho : H.cells r with
    | none => exact absurd ho hne
    | some o => exact MutableFootprint.root ho (hi.nonPersistent r o ho)
  have hlive : LiveIn (isolatedCtx c state path x r) H r := by
    intro z q hz hq
    rcases hz with hz | hz
    · have hzs : z = state := isolatedCtx_us_owned.mp hz
      subst z
      have hzr : (isolatedCtx c state path x r).refOf state = some r := by simp [isolatedCtx]
      rw [hzr] at hq
      have hqr : q = r := (Option.some.inj hq).symm
      rw [hqr]
      exact hroot
    · exact absurd hz isolatedCtx_us_ne_borrow
  exact runN_confined hi hlive (fun q _ => rfl) hann hc hok hws hrun

end Entry
end Ownership
