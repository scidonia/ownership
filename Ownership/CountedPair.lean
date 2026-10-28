/-
A concrete counted model of the extract/call/restore temporary pair.

`Ownership.Heap`'s `dec` is a saturating count decrement that never removes a
cell, because the write theorem only needs counts on live cells. The emitted
index arm does more: it allocates a `Prod.mk` pair around the array and the
extracted element, increments the pair's two projections to create owned
handles, and decrements the unique pair. That decrement, at count one, destroys
the pair and releases its two component edges. This module adds exactly that
restricted free and derives the counts at the protocol boundary.

The emitted steps, and their count effects on the parent array `p`, the child
`c` and the pair `q`, are:

| step | emitted operation | parent | child | pair |
| --- | --- | --- | --- | --- |
| take-out | `takeOut` returns `Prod.mk xs' e` | transfer | transfer | allocate `rc = 1` |
| parent projection | `oproj[0]`, then `inc` | `+1` | | |
| child projection | `oproj[1]`, then `inc` | | `+1` | |
| pair decrement | `dec` at `rc = 1` | `-1` | `-1` | free |

The take-out helper is captured in `docs/notes/artifacts/setAt-nested.lcnf.txt`:
`Array.getInternal s i` reads the selected element, `Array.set s i d` returns the
array with the default placeholder in that slot, and `ctor_0[Prod.mk] xs' e`
builds the pair. Because `getInternal` borrows and the constructor consumes its
arguments, the pair receives the caller's array and element handles: allocation
does not add a second counted reference to either component. The index arm then
projects both fields, increments each projection once, and decrements the pair;
the pair was the unique owner of its two fields, so its destruction removes both
edges.

The free below is deliberately restricted: it acts on one cell, removes it, and
releases each reference field directly. It does not recursively free a component
whose count reaches zero. The extraction protocol never reaches that case: the
pair's edges are released while the two projection handles still hold the
components, so both counts stay at least one. The restriction is stated rather
than assumed away, and the negative controls in `OwnershipTest/CountedPair.lean`
show what the omitted free or a retained alias would leave behind.

## Boundary assumptions

* **Persistence.** The entry's parent and child are non-persistent, and the
  boundary's exclusivity is exactly count one together with that flag. A
  persistent component is outside this protocol and is not claimed to become
  exclusive.
* **Free/cascade.** The free releases one cell's reference fields without a
  recursive cascade. The protocol's own counts never reach a cascading case, so
  the restriction is sufficient here; the runtime's general cascade is not
  modelled.
* **Allocated-address identity.** A `Ref` is a name, and the pair's fresh name
  is `H.next`. Nothing identifies that name with a runtime address, a specific
  allocation site, or a reused address; the account is about counts, not about
  the backend's allocation.

Nothing here is a Compiler/LCNF or C-backend claim, and nothing here says Lean's
runtime performs these steps. It is a small counted semantics for the captured
helper and arm, together with the correspondence to `Ownership.Heap`'s `rc` and
`Exclusive` predicates.
-/
import Ownership.Heap

namespace Ownership
namespace CountedPair

/-! ## Small heap facts -/

/-- The cell's count, read from its live cell. -/
theorem rc_of_cells {H : Heap} {r : Ref} {o : Obj} (h : H.cells r = some o) :
    H.rc r = o.rc := by
  simp [Heap.rc, h]

/-- Counting up keeps the cell and records the new count. -/
theorem inc_cells_self {H : Heap} {r : Ref} {n : Nat} {o : Obj}
    (h : H.cells r = some o) :
    (H.inc r n).cells r = some { o with rc := o.rc + n } := by
  unfold Heap.inc
  rw [h]
  simp [Heap.set]

/-- Counting down keeps the cell and records the new count. -/
theorem dec_cells_self {H : Heap} {r : Ref} {n : Nat} {o : Obj}
    (h : H.cells r = some o) :
    (H.dec r n).cells r = some { o with rc := o.rc - n } := by
  unfold Heap.dec
  rw [h]
  simp [Heap.set]

/-- A live non-persistent cell is exclusive exactly at count one. -/
theorem exclusive_iff {H : Heap} {r : Ref} {o : Obj} (h : H.cells r = some o) :
    Heap.Exclusive H r ↔ o.rc = 1 ∧ o.persistent = false := by
  constructor
  · rintro ⟨o', ho', hrc, hp⟩
    rw [h] at ho'
    injection ho' with heq
    subst heq
    exact ⟨hrc, hp⟩
  · rintro ⟨hrc, hp⟩
    exact ⟨o, h, hrc, hp⟩

/-- A count other than one rules out exclusivity. -/
theorem not_exclusive_of_rc_ne_one {H : Heap} {r : Ref} (h : H.rc r ≠ 1) :
    ¬ Heap.Exclusive H r := by
  intro he
  exact h (Heap.exclusive_rc he)

/-- The object an increment and a decrement leave behind is the original. -/
theorem obj_inc_dec (o : Obj) :
    { { o with rc := o.rc + 1 } with rc := (o.rc + 1) - 1 } = o := by
  cases o with
  | mk fields rc persistent =>
      simp

/-! ## The temporary pair and its free -/

/-- The two component edges of the temporary pair, in projection order. -/
def pairFields (p c : Ref) : Array Val := #[.ref p, .ref c]

/-- Release a cell's reference fields, one decrement per `.ref` field. The
restricted free used by the extraction protocol; other fields are ignored. -/
def releaseFields (H : Heap) (fields : Array Val) : Heap :=
  fields.foldl (fun H' v =>
    match v with
    | .ref q => H'.dec q 1
    | _ => H') H

/-- The pair's fields hold one edge to each component. -/
@[simp] theorem releaseFields_pairFields (H : Heap) (p c : Ref) :
    releaseFields H (pairFields p c) = (H.dec p 1).dec c 1 := by
  simp [releaseFields, pairFields]

/-- The restricted free: a decrement that removes the cell when its count
reaches zero and releases that cell's reference fields. It does not cascade into
a component whose own count reaches zero. -/
def decRef (H : Heap) (r : Ref) : Heap :=
  match H.cells r with
  | none => H
  | some o =>
      if o.rc ≤ 1 then
        (releaseFields H o.fields).erase r
      else
        H.set r { o with rc := o.rc - 1 }

/-- Freeing a unique two-component pair removes the pair cell and releases its
two edges. This is the restricted free's pair instance. -/
def pairFree (H : Heap) (p c : Ref) (pair : Ref) : Heap :=
  ((H.dec p 1).dec c 1).erase pair

/-- The pair cell's own object is the two-field object the allocation built. -/
theorem decRef_pair {H : Heap} {pair p c : Ref} {o : Obj}
    (hcell : H.cells pair = some o) (hfields : o.fields = pairFields p c)
    (hrc : o.rc = 1) :
    decRef H pair = pairFree H p c pair := by
  unfold decRef pairFree
  rw [hcell]
  simp [hfields, hrc, releaseFields_pairFields]

/-! ## The pair-inc/inc/release chain -/

/-- Increment both pair components once, in projection order. -/
def pairInc (H : Heap) (p c : Ref) : Heap := (H.inc p 1).inc c 1

/-- Decrement both pair components once, in projection order. -/
def pairRelease (H : Heap) (p c : Ref) : Heap := (H.dec p 1).dec c 1

@[simp] theorem pairInc_cells_parent {H : Heap} {p c : Ref} {o : Obj}
    (hp : H.cells p = some o) (hpc : p ≠ c) :
    (pairInc H p c).cells p = some { o with rc := o.rc + 1 } := by
  unfold pairInc
  rw [Heap.inc_other (H := H.inc p 1) (r := c) (r' := p) (n := 1) hpc]
  exact inc_cells_self hp

@[simp] theorem pairInc_cells_child {H : Heap} {p c : Ref} {o : Obj}
    (hc : H.cells c = some o) (hpc : p ≠ c) :
    (pairInc H p c).cells c = some { o with rc := o.rc + 1 } := by
  unfold pairInc
  have hc' : (H.inc p 1).cells c = some o := by
    rw [Heap.inc_other (H := H) (r := p) (r' := c) (n := 1) (Ne.symm hpc)]
    exact hc
  exact inc_cells_self hc'

theorem pairInc_cells_other {H : Heap} {p c q : Ref} (hqp : q ≠ p) (hqc : q ≠ c) :
    (pairInc H p c).cells q = H.cells q := by
  unfold pairInc
  rw [Heap.inc_other (H := H.inc p 1) (r := c) (r' := q) (n := 1) hqc]
  exact Heap.inc_other (H := H) (r := p) (r' := q) (n := 1) hqp

@[simp] theorem pairRelease_cells_parent {H : Heap} {p c : Ref} {o : Obj}
    (hp : H.cells p = some o) (hpc : p ≠ c) :
    (pairRelease H p c).cells p = some { o with rc := o.rc - 1 } := by
  unfold pairRelease
  rw [Heap.dec_other (H := H.dec p 1) (r := c) (r' := p) (n := 1) hpc]
  exact dec_cells_self hp

@[simp] theorem pairRelease_cells_child {H : Heap} {p c : Ref} {o : Obj}
    (hc : H.cells c = some o) (hpc : p ≠ c) :
    (pairRelease H p c).cells c = some { o with rc := o.rc - 1 } := by
  unfold pairRelease
  have hc' : (H.dec p 1).cells c = some o := by
    rw [Heap.dec_other (H := H) (r := p) (r' := c) (n := 1) (Ne.symm hpc)]
    exact hc
  exact dec_cells_self hc'

theorem pairRelease_cells_other {H : Heap} {p c q : Ref}
    (hqp : q ≠ p) (hqc : q ≠ c) :
    (pairRelease H p c).cells q = H.cells q := by
  unfold pairRelease
  rw [Heap.dec_other (H := H.dec p 1) (r := c) (r' := q) (n := 1) hqc]
  exact Heap.dec_other (H := H) (r := p) (r' := q) (n := 1) hqp

/-- The full pair traffic, including the two component increments and the
release, leaves the parent cell's count where it found it. -/
theorem pairFree_inc_cells_parent {H : Heap} {p c pair : Ref} {o : Obj}
    (hp : H.cells p = some o) (hpc : p ≠ c) (hpp : p ≠ pair) :
    (pairFree (pairInc H p c) p c pair).cells p = some o := by
  unfold pairFree
  rw [Heap.erase_other (((pairInc H p c).dec p 1).dec c 1) pair p hpp]
  change (pairRelease (pairInc H p c) p c).cells p = some o
  rw [pairRelease_cells_parent (pairInc_cells_parent hp hpc) hpc]
  rw [obj_inc_dec]

/-- The full pair traffic leaves the child cell exactly as it found it. -/
theorem pairFree_inc_cells_child {H : Heap} {p c pair : Ref} {o : Obj}
    (hc : H.cells c = some o) (hpc : p ≠ c) (hcp : c ≠ pair) :
    (pairFree (pairInc H p c) p c pair).cells c = some o := by
  unfold pairFree
  rw [Heap.erase_other (((pairInc H p c).dec p 1).dec c 1) pair c hcp]
  change (pairRelease (pairInc H p c) p c).cells c = some o
  rw [pairRelease_cells_child (pairInc_cells_child hc hpc) hpc]
  rw [obj_inc_dec]

/-- The pair free removes the unique pair cell. -/
theorem pairFree_cells_pair (H : Heap) (p c pair : Ref) :
    (pairFree H p c pair).cells pair = none := by
  unfold pairFree
  exact Heap.erase_self _ _

/-- The full pair traffic leaves unrelated cells alone. -/
theorem pairFree_inc_cells_other {H : Heap} {p c pair q : Ref}
    (hqp : q ≠ p) (hqc : q ≠ c) (hqq : q ≠ pair) :
    (pairFree (pairInc H p c) p c pair).cells q = H.cells q := by
  unfold pairFree
  rw [Heap.erase_other (((pairInc H p c).dec p 1).dec c 1) pair q hqq]
  change (pairRelease (pairInc H p c) p c).cells q = H.cells q
  rw [pairRelease_cells_other hqp hqc, pairInc_cells_other hqp hqc]

/-! ## The take-out step -/

/-- Allocate the temporary pair at the fresh name and put the two component
edges in its fields. The allocation transfers the caller's existing handles; it
does not increment either component. -/
def allocPair (H : Heap) (p c : Ref) : Heap := (H.alloc (pairFields p c)).2

@[simp] theorem allocPair_cells_self (H : Heap) (p c : Ref) :
    (allocPair H p c).cells H.next = some ⟨pairFields p c, 1, false⟩ := by
  unfold allocPair
  exact Heap.alloc_cells_self H (pairFields p c)

theorem allocPair_cells_other {H : Heap} {p c r : Ref} (h : r ≠ H.next) :
    (allocPair H p c).cells r = H.cells r := by
  unfold allocPair
  exact Heap.alloc_cells_other h

/-- Put the model's placeholder into the parent's selected slot. -/
def setPlaceholder (H : Heap) (p : Ref) (i : Nat) : Heap :=
  match H.cells p with
  | some o => H.set p { o with fields := o.fields.setIfInBounds i (.scalar 0) }
  | none => H

@[simp] theorem setPlaceholder_cells_self {H : Heap} {p : Ref} {i : Nat} {o : Obj}
    (h : H.cells p = some o) :
    (setPlaceholder H p i).cells p =
      some { o with fields := o.fields.setIfInBounds i (.scalar 0) } := by
  simp [setPlaceholder, h]

theorem setPlaceholder_cells_other {H : Heap} {p : Ref} {i : Nat} {r : Ref}
    (h : r ≠ p) : (setPlaceholder H p i).cells r = H.cells r := by
  unfold setPlaceholder
  split
  · exact Heap.set_other _ _ _ _ h
  · rfl

/-- The emitted take-out: allocate the fresh pair holding the parent and child
handles, and empty the parent's selected slot. The pair name is the heap's
fresh name, and the returned heap is the pair allocation followed by the
placeholder write. -/
def takeOut (H : Heap) (p c : Ref) (i : Nat) : Ref × Heap :=
  (H.next, setPlaceholder (allocPair H p c) p i)

/-- The take-out's pair cell is live at count one with the two component
edges. -/
theorem takeOut_cells_pair {H : Heap} {p c : Ref} {i : Nat} (hpn : p ≠ H.next) :
    (takeOut H p c i).2.cells H.next = some ⟨pairFields p c, 1, false⟩ := by
  show (setPlaceholder (allocPair H p c) p i).cells H.next = _
  rw [setPlaceholder_cells_other (Ne.symm hpn)]
  exact allocPair_cells_self H p c

/-- The take-out leaves the parent live, with the placeholder in the selected
slot. -/
theorem takeOut_cells_parent {H : Heap} {p c : Ref} {i : Nat} {o : Obj}
    (hp : H.cells p = some o) (hpn : p ≠ H.next) :
    (takeOut H p c i).2.cells p =
      some { o with fields := o.fields.setIfInBounds i (.scalar 0) } := by
  have h1 : (allocPair H p c).cells p = some o := by
    rw [allocPair_cells_other hpn]
    exact hp
  show (setPlaceholder (allocPair H p c) p i).cells p = _
  rw [setPlaceholder_cells_self h1]

/-- The take-out leaves the child's cell exactly where it was. -/
theorem takeOut_cells_child {H : Heap} {p c : Ref} {i : Nat} {o : Obj}
    (hc : H.cells c = some o) (hcn : c ≠ H.next) (hcp : c ≠ p) :
    (takeOut H p c i).2.cells c = some o := by
  have h1 : (allocPair H p c).cells c = some o := by
    rw [allocPair_cells_other hcn]
    exact hc
  show (setPlaceholder (allocPair H p c) p i).cells c = some o
  rw [setPlaceholder_cells_other hcp]
  exact h1

/-- The captured take-out's ownership convention, at the count level: the
helper transfers the two existing handles into the fresh pair at count one and
does not increment either component. This is the concrete counterpart of the
N8 take-out shape in `OwnershipLcnf/NestedSemantics.lean`; it is derived from
`takeOut`, not assumed. -/
theorem takeOut_transfers {H : Heap} {p c : Ref} {i : Nat} {op oc : Obj}
    (hPcell : H.cells p = some op) (hCcell : H.cells c = some oc)
    (hpc : p ≠ c) (hpn : p ≠ H.next) (hcn : c ≠ H.next) :
    let t := takeOut H p c i
    t.2.cells t.1 = some ⟨pairFields p c, 1, false⟩ ∧
      t.2.rc p = H.rc p ∧ t.2.rc c = H.rc c := by
  have hpair : (takeOut H p c i).2.cells H.next = some ⟨pairFields p c, 1, false⟩ :=
    takeOut_cells_pair hpn
  refine ⟨?_, ?_, ?_⟩
  · show (takeOut H p c i).2.cells H.next = _
    exact hpair
  · rw [rc_of_cells (takeOut_cells_parent hPcell hpn), rc_of_cells hPcell]
  · rw [rc_of_cells (takeOut_cells_child hCcell hcn (Ne.symm hpc)), rc_of_cells hCcell]

/-! ## Projections and the pair traffic -/

/-- A pair projection, as a heap read: the field at the selected index. -/
def project (H : Heap) (pair : Ref) (i : Nat) : Option Val :=
  match H.cells pair with
  | some o => o.fields[i]?
  | none => none

/-- A projection followed by the explicit increment that makes the borrowed
component an owned handle. -/
def incProjection (H : Heap) (pair : Ref) (i : Nat) : Heap :=
  match project H pair i with
  | some (.ref q) => H.inc q 1
  | _ => H

/-- The emitted pair sequence: project index 0 and increment, project index 1
and increment. The pair cell is untouched by these increments. -/
def incPairComponents (H : Heap) (pair : Ref) : Heap :=
  incProjection (incProjection H pair 0) pair 1

/-- The pair's increments followed by its unique decrement: the pair is freed
and both component edges are released. -/
def pairTraffic (H : Heap) (pair : Ref) : Heap :=
  decRef (incPairComponents H pair) pair

theorem incProjection_pair_zero {H : Heap} {pair p : Ref} {o : Obj}
    (hcell : H.cells pair = some o) (h0 : o.fields[0]? = some (.ref p)) :
    incProjection H pair 0 = H.inc p 1 := by
  simp [incProjection, project, hcell, h0]

theorem incProjection_pair_one {H : Heap} {pair p c : Ref} {o : Obj}
    (hcell : H.cells pair = some o)
    (h1 : o.fields[1]? = some (.ref c)) (hpPair : pair ≠ p) :
    incProjection (H.inc p 1) pair 1 = (H.inc p 1).inc c 1 := by
  have hcell' : (H.inc p 1).cells pair = some o := by
    rw [Heap.inc_other (H := H) (r := p) (r' := pair) (n := 1) hpPair]
    exact hcell
  simp [incProjection, project, hcell', h1]

theorem incPairComponents_eq {H : Heap} {pair p c : Ref} {o : Obj}
    (hcell : H.cells pair = some o)
    (h0 : o.fields[0]? = some (.ref p)) (h1 : o.fields[1]? = some (.ref c))
    (hpPair : pair ≠ p) :
    incPairComponents H pair = pairInc H p c := by
  unfold incPairComponents pairInc
  rw [incProjection_pair_zero hcell h0]
  exact incProjection_pair_one hcell h1 hpPair

/-- The pair traffic is exactly the component increments followed by the pair
free. -/
theorem pairTraffic_eq_pairFree {H : Heap} {pair p c : Ref} {o : Obj}
    (hcell : H.cells pair = some o) (hfields : o.fields = pairFields p c)
    (hrc : o.rc = 1) (hpPair : pair ≠ p) (hcPair : pair ≠ c) :
    pairTraffic H pair = pairFree (pairInc H p c) p c pair := by
  have h0 : o.fields[0]? = some (.ref p) := by simp [hfields, pairFields]
  have h1 : o.fields[1]? = some (.ref c) := by simp [hfields, pairFields]
  unfold pairTraffic
  rw [incPairComponents_eq hcell h0 h1 hpPair]
  have hcell1 : (H.inc p 1).cells pair = some o := by
    rw [Heap.inc_other (H := H) (r := p) (r' := pair) (n := 1) hpPair]
    exact hcell
  have hcell2 : (pairInc H p c).cells pair = some o := by
    unfold pairInc
    rw [Heap.inc_other (H := H.inc p 1) (r := c) (r' := pair) (n := 1) hcPair]
    exact hcell1
  exact decRef_pair hcell2 hfields hrc

/-- The pair traffic through a freshly allocated take-out pair. -/
theorem pairTraffic_takeOut {H : Heap} {p c : Ref} {i : Nat}
    (hpn : p ≠ H.next) (hcn : c ≠ H.next) :
    pairTraffic (takeOut H p c i).2 H.next =
      pairFree (pairInc (takeOut H p c i).2 p c) p c H.next := by
  apply pairTraffic_eq_pairFree (o := ⟨pairFields p c, 1, false⟩)
  · exact takeOut_cells_pair hpn
  · rfl
  · rfl
  · exact Ne.symm hpn
  · exact Ne.symm hcn

/-! ## The protocol boundary -/

/-- Take out, project and increment both components, then decrement the unique
pair. The returned pair name is the heap's fresh name. -/
def protocol (H : Heap) (p c : Ref) (i : Nat) : Ref × Heap :=
  (H.next, pairTraffic (takeOut H p c i).2 H.next)

/-- The same sequence without the pair decrement: both projections are
incremented and the pair is left alive. This is the omitted-free control. -/
def protocolNoFree (H : Heap) (p c : Ref) (i : Nat) : Ref × Heap :=
  (H.next, incPairComponents (takeOut H p c i).2 H.next)

/-- A concrete entry for the extraction protocol. The parent and child are live
non-persistent cells, the parent's selected slot holds the child, the two are
distinct, and the heap's fresh name has no cell, so the pair is new. -/
def CountedEntry (H : Heap) (p c : Ref) (i : Nat) (kp kc : Nat) : Prop :=
  ∃ op oc, H.cells p = some op ∧ H.cells c = some oc ∧
    op.rc = kp ∧ oc.rc = kc ∧
    op.persistent = false ∧ oc.persistent = false ∧
    op.fields[i]? = some (.ref c) ∧ p ≠ c ∧
    H.cells H.next = none ∧ p ≠ H.next ∧ c ≠ H.next

/-- The well-formed entry: both components at count one. -/
def WellFormedEntry (H : Heap) (p c : Ref) (i : Nat) : Prop :=
  CountedEntry H p c i 1 1

/-- The boundary state of the protocol: the parent cell has the placeholder in
its selected slot, the child cell is unchanged, the pair is gone, and the
counts are exactly the entry counts. Exclusivity is exactly the count-one and
non-persistence condition on the corresponding entry object.

This is the concrete accounting; `takeOut` transfers the handles rather than
duplicating them, and the parent's and child's two counted references during
the sequence are the pair's edge and the projected owned handle. The pair free
removes one of each, returning the counts to their entry values. -/
theorem protocol_boundary {H : Heap} {p c : Ref} {i : Nat} {op oc : Obj}
    (hPcell : H.cells p = some op) (hCcell : H.cells c = some oc)
    (hpc : p ≠ c) (hpn : p ≠ H.next) (hcn : c ≠ H.next) :
    let B := protocol H p c i
    B.1 = H.next ∧
      B.2.cells p =
        some { op with fields := op.fields.setIfInBounds i (.scalar 0) } ∧
      B.2.cells c = some oc ∧
      B.2.cells B.1 = none ∧
      B.2.rc p = op.rc ∧ B.2.rc c = oc.rc ∧
      (Heap.Exclusive B.2 p ↔ op.rc = 1 ∧ op.persistent = false) ∧
      (Heap.Exclusive B.2 c ↔ oc.rc = 1 ∧ oc.persistent = false) := by
  let parent' : Obj := { op with fields := op.fields.setIfInBounds i (.scalar 0) }
  let H1 : Heap := (takeOut H p c i).2
  have hH1p : H1.cells p = some parent' := by
    simpa [H1, parent'] using takeOut_cells_parent (H := H) (p := p) (c := c) (i := i) hPcell hpn
  have hH1c : H1.cells c = some oc := by
    simpa [H1] using
      takeOut_cells_child (H := H) (p := p) (c := c) (i := i) hCcell hcn (Ne.symm hpc)
  have htraffic : (protocol H p c i).2 =
      pairFree (pairInc H1 p c) p c H.next := by
    show pairTraffic H1 H.next = _
    exact pairTraffic_takeOut hpn hcn
  have hcellsp : (protocol H p c i).2.cells p = some parent' := by
    rw [htraffic]
    exact pairFree_inc_cells_parent hH1p hpc hpn
  have hcellsc : (protocol H p c i).2.cells c = some oc := by
    rw [htraffic]
    exact pairFree_inc_cells_child hH1c hpc hcn
  have hcellspair : (protocol H p c i).2.cells (protocol H p c i).1 = none := by
    have hfst : (protocol H p c i).1 = H.next := rfl
    rw [hfst, htraffic]
    exact pairFree_cells_pair (pairInc H1 p c) p c H.next
  refine ⟨rfl, ?_, hcellsc, hcellspair, ?_, ?_, ?_, ?_⟩
  · simpa [parent'] using hcellsp
  · simpa [parent'] using rc_of_cells hcellsp
  · exact rc_of_cells hcellsc
  · simpa [parent'] using exclusive_iff hcellsp
  · exact exclusive_iff hcellsc

/-- The protocol boundary proves the parent and child counts and liveness, the
pair's absence, and both components' exclusivity. -/
theorem pair_accounting {H : Heap} {p c : Ref} {i : Nat}
    (hw : WellFormedEntry H p c i) :
    let B := protocol H p c i
    B.2.rc p = 1 ∧ B.2.rc c = 1 ∧ B.2.cells p ≠ none ∧
      B.2.cells c ≠ none ∧ B.2.cells B.1 = none ∧
      Heap.Exclusive B.2 p ∧ Heap.Exclusive B.2 c ∧
      B.2.rc p = H.rc p ∧ B.2.rc c = H.rc c := by
  rcases hw with ⟨op, oc, hPcell, hCcell, hPrc, hCrc, hPpers, hCpers, _,
    hpc, _, hpn, hcn⟩
  have hb := protocol_boundary (i := i) hPcell hCcell hpc hpn hcn
  rcases hb with ⟨_, hcellsp, hcellsc, hpair, hrcp, hrcc, hexp, hexc⟩
  refine ⟨?_, ?_, ?_, ?_, hpair, ?_, ?_, ?_, ?_⟩
  · rw [hrcp, hPrc]
  · rw [hrcc, hCrc]
  · rw [hcellsp]; simp
  · rw [hcellsc]; simp
  · exact hexp.mpr ⟨hPrc, hPpers⟩
  · exact hexc.mpr ⟨hCrc, hCpers⟩
  · rw [hrcp, rc_of_cells hPcell]
  · rw [hrcc, rc_of_cells hCcell]

/-- The pair traffic is neutral at the boundary: the parent and child counts are
their entry counts, the child cell is the entry cell, and the temporary pair is
gone. The parent's cell differs from the entry cell only by the take-out's
placeholder write, which is the model's take-out transition rather than pair
traffic. -/
theorem pair_traffic_neutral {H : Heap} {p c : Ref} {i : Nat}
    (hw : WellFormedEntry H p c i) :
    let B := protocol H p c i
    B.2.rc p = H.rc p ∧ B.2.rc c = H.rc c ∧ B.2.cells c = H.cells c ∧
      B.2.cells B.1 = none := by
  have h := pair_accounting hw
  rcases h with ⟨_, _, _, _, hpair, _, _, heqcp, heqcc⟩
  rcases hw with ⟨_, _, hPcell, hCcell, _, _, _, _, _, hpc, _, hpn, hcn⟩
  have hb := protocol_boundary (i := i) hPcell hCcell hpc hpn hcn
  rcases hb with ⟨_, _, hcellsc, _, _, _, _, _⟩
  refine ⟨heqcp, heqcc, ?_, hpair⟩
  rw [hCcell]
  exact hcellsc

/-- The boundary corresponds to the ownership heap's own `rc` and `Exclusive`
predicates for the parent and child. -/
theorem boundary_correspondence {H : Heap} {p c : Ref} {i : Nat}
    (hw : WellFormedEntry H p c i) :
    let B := protocol H p c i
    B.2.rc p = H.rc p ∧ B.2.rc c = H.rc c ∧
      Heap.Exclusive B.2 p ∧ Heap.Exclusive B.2 c ∧
      B.2.exclusive? p = true ∧ B.2.exclusive? c = true := by
  have h := pair_accounting hw
  rcases h with ⟨hrcp, hrcc, hlivep, hlivec, hpair, hexp, hexc, heqcp, heqcc⟩
  exact ⟨heqcp, heqcc, hexp, hexc,
    (Heap.exclusive?_eq_true).mpr hexp, (Heap.exclusive?_eq_true).mpr hexc⟩

/-! ## Negative controls -/

/-- Omitting the pair decrement leaves both components at count two: the pair's
edge and the projected owned handle. The pair remains live. -/
theorem no_free_components_not_exclusive {H : Heap} {p c : Ref} {i : Nat}
    (hw : WellFormedEntry H p c i) :
    let B := protocolNoFree H p c i
    B.2.rc p = 2 ∧ B.2.rc c = 2 ∧ ¬ Heap.Exclusive B.2 p ∧
      ¬ Heap.Exclusive B.2 c ∧ B.2.cells B.1 ≠ none := by
  rcases hw with ⟨op, oc, hPcell, hCcell, hPrc, hCrc, hPpers, hCpers, _,
    hpc, _, hpn, hcn⟩
  let parent' : Obj := { op with fields := op.fields.setIfInBounds i (.scalar 0) }
  let H1 : Heap := (takeOut H p c i).2
  have hH1p : H1.cells p = some parent' := by
    simpa [H1, parent'] using takeOut_cells_parent (H := H) (p := p) (c := c) (i := i) hPcell hpn
  have hH1c : H1.cells c = some oc := by
    simpa [H1] using
      takeOut_cells_child (H := H) (p := p) (c := c) (i := i) hCcell hcn (Ne.symm hpc)
  have hcellsp : (protocolNoFree H p c i).2.cells p =
      some { parent' with rc := parent'.rc + 1 } := by
    show (incPairComponents H1 H.next).cells p = _
    rw [incPairComponents_eq (H := H1) (pair := H.next) (p := p) (c := c)
      (o := ⟨pairFields p c, 1, false⟩) (takeOut_cells_pair hpn)
      (by simp [pairFields]) (by simp [pairFields]) (Ne.symm hpn)]
    exact pairInc_cells_parent hH1p hpc
  have hcellsc : (protocolNoFree H p c i).2.cells c =
      some { oc with rc := oc.rc + 1 } := by
    show (incPairComponents H1 H.next).cells c = _
    rw [incPairComponents_eq (H := H1) (pair := H.next) (p := p) (c := c)
      (o := ⟨pairFields p c, 1, false⟩) (takeOut_cells_pair hpn)
      (by simp [pairFields]) (by simp [pairFields]) (Ne.symm hpn)]
    exact pairInc_cells_child hH1c hpc
  have hpair : (protocolNoFree H p c i).2.cells (protocolNoFree H p c i).1 ≠ none := by
    have hfst : (protocolNoFree H p c i).1 = H.next := rfl
    rw [hfst]
    show (incPairComponents H1 H.next).cells H.next ≠ none
    rw [incPairComponents_eq (H := H1) (pair := H.next) (p := p) (c := c)
      (o := ⟨pairFields p c, 1, false⟩) (takeOut_cells_pair hpn)
      (by simp [pairFields]) (by simp [pairFields]) (Ne.symm hpn)]
    rw [pairInc_cells_other (Ne.symm hpn) (Ne.symm hcn)]
    rw [takeOut_cells_pair hpn]
    simp
  refine ⟨?_, ?_, ?_, ?_, hpair⟩
  · rw [rc_of_cells hcellsp]
    simp [parent', hPrc]
  · rw [rc_of_cells hcellsc]
    simp [hCrc]
  · intro he
    have hrc : (protocolNoFree H p c i).2.rc p = 2 := by
      rw [rc_of_cells hcellsp]
      simp [parent', hPrc]
    exact not_exclusive_of_rc_ne_one (by rw [hrc]; decide) he
  · intro he
    have hrc : (protocolNoFree H p c i).2.rc c = 2 := by
      rw [rc_of_cells hcellsc]
      simp [hCrc]
    exact not_exclusive_of_rc_ne_one (by rw [hrc]; decide) he

/-- A retained counted alias to the parent leaves the boundary parent at count
two, so it is not exclusive; the child is unaffected and remains exclusive. -/
theorem retained_alias_not_exclusive {H : Heap} {p c : Ref} {i : Nat}
    (hw : WellFormedEntry H p c i) :
    let B := protocol H p c i
    let A := (B.2.inc p 1)
    A.rc p = 2 ∧ ¬ Heap.Exclusive A p ∧ A.rc c = 1 ∧ Heap.Exclusive A c := by
  have h := pair_accounting hw
  rcases h with ⟨hrcp, hrcc, hlivep, hlivec, hpair, hexp, hexc, heqcp, heqcc⟩
  rcases hw with ⟨op, oc, hPcell, hCcell, hPrc, hCrc, hPpers, hCpers, _,
    hpc, _, hpn, hcn⟩
  have hb := protocol_boundary (i := i) hPcell hCcell hpc hpn hcn
  rcases hb with ⟨_, hcellsp, hcellsc, hpair', hrcp, hrcc', hexp', hexc'⟩
  have hrc2 : ((protocol H p c i).2.inc p 1).rc p = 2 := by
    rw [Heap.rc_inc_self hcellsp, hrcp, hPrc]
  have hcc : ((protocol H p c i).2.inc p 1).cells c = some oc := by
    rw [Heap.inc_other (H := (protocol H p c i).2) (r := p) (r' := c) (n := 1) (Ne.symm hpc)]
    exact hcellsc
  refine ⟨hrc2, ?_, ?_, ?_⟩
  · exact not_exclusive_of_rc_ne_one (by rw [hrc2]; decide)
  · rw [rc_of_cells hcc, hCrc]
  · exact ⟨oc, hcc, hCrc, hCpers⟩

/-- A shared child at entry (count two) stays at count two through the
protocol and is not exclusive at the boundary. -/
theorem shared_child_not_exclusive {H : Heap} {p c : Ref} {i : Nat}
    (hw : CountedEntry H p c i 1 2) :
    let B := protocol H p c i
    B.2.rc c = 2 ∧ ¬ Heap.Exclusive B.2 c := by
  rcases hw with ⟨op, oc, hPcell, hCcell, hPrc, hCrc, hPpers, hCpers, _,
    hpc, _, hpn, hcn⟩
  have hb := protocol_boundary (i := i) hPcell hCcell hpc hpn hcn
  rcases hb with ⟨_, _, _, _, _, hrcc, _, _⟩
  refine ⟨?_, ?_⟩
  · rw [hrcc, hCrc]
  · intro he
    have hrc : (protocol H p c i).2.rc c = 2 := by rw [hrcc, hCrc]
    exact not_exclusive_of_rc_ne_one (by rw [hrc]; decide) he

/-- A shared parent at entry (count two) stays at count two through the
protocol and is not exclusive at the boundary. -/
theorem shared_parent_not_exclusive {H : Heap} {p c : Ref} {i : Nat}
    (hw : CountedEntry H p c i 2 1) :
    let B := protocol H p c i
    B.2.rc p = 2 ∧ ¬ Heap.Exclusive B.2 p := by
  rcases hw with ⟨op, oc, hPcell, hCcell, hPrc, hCrc, hPpers, hCpers, _,
    hpc, _, hpn, hcn⟩
  have hb := protocol_boundary (i := i) hPcell hCcell hpc hpn hcn
  rcases hb with ⟨_, _, _, _, hrcp, _, _, _⟩
  refine ⟨?_, ?_⟩
  · rw [hrcp, hPrc]
  · intro he
    have hrc : (protocol H p c i).2.rc p = 2 := by rw [hrcp, hPrc]
    exact not_exclusive_of_rc_ne_one (by rw [hrc]; decide) he

end CountedPair
end Ownership
