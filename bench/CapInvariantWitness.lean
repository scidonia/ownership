import Cap.Reconstruction

open Cap
open Cap.Reconstruction

/-!
Regression and admissibility controls for the strengthened reconstruction
invariant.

The two witnesses are the adversarial examples of the audit, encoded against the
predicates the previous revision maintained. `OldInv` is exactly
`Covered ∧ Valid ∧ Accounts`; `oldWrite` is exactly the previous write guard,
which did not inspect the fragment's allocation.

* `witnessA` — a suspension whose recorded parent share is `4` while its actual
  frontier carries `1 + 1`. It satisfies `OldInv`, and `suspended_frontier_realizes`'s
  subtree-budget premise fails at it. Coherence rejects it.
* `witnessB` — a single leaf whose allocation field is `99` inside a component
  whose allocation is `0`. It satisfies `OldInv`, and the old write guard accepts
  a write that updates allocation `0`. Scope rejects it and the new guard refuses
  the write.

The module then records the negative controls the repair relies on and positive
controls showing the worked lifecycle still satisfies the stronger invariant.
-/

namespace CapInvariantWitness

/-! ### The previous predicates -/

/-- The reconstruction invariant before the repair: coverage, rule validity and
the ownership accounts. -/
def OldInv (s : State) : Prop := s.Covered ∧ s.forest.Valid ∧ s.Accounts

/-- The previous write operation: the guard did not require the fragment's
allocation to be the component's. -/
def oldWrite (s : State) (id : CapId) (i : Nat) (v : UInt8) : Option State :=
  match s.forest.findLeaf? id with
  | none => none
  | some c =>
      if h : c.state = .active ∧ c.q = s.D ∧ c.ceiling = .readWrite ∧
              c.lo ≤ i ∧ i < c.hi then
        match s.heap.write? s.alloc i v with
        | some h' => some { s with heap := h' }
        | none => none
      else none

/-! ### Finding A: a suspended parent overstates its live resource -/

private def aLeaf (id : CapId) (q : Nat) (hq : 0 < q) : Leaf :=
  { id := id, alloc := ⟨0⟩, lo := 0, hi := 1, ordered := by decide,
    q := q, pos := hq, ceiling := .readWrite, state := .active }

private def aParent : Leaf := aLeaf ⟨20⟩ 4 (by decide)
private def aLeftRule : Leaf := aLeaf ⟨21⟩ 2 (by decide)
private def aRightRule : Leaf := aLeaf ⟨22⟩ 2 (by decide)
private def aLeft : Leaf := aLeaf ⟨23⟩ 1 (by decide)
private def aRight : Leaf := aLeaf ⟨24⟩ 1 (by decide)

/-- The audit's witness: parent share `4`, actual frontier `1 + 1`, an acyclic
one-record chain from dormant lender `10` to borrower `20`. -/
def witnessA : State :=
  { alloc := ⟨0⟩, len := 1, D := 2,
    forest := .split .fractional aParent aLeftRule aRightRule (.leaf aLeft) (.leaf aRight),
    heap := Heap.alloc Heap.empty ⟨0⟩ 1,
    issued := [⟨10⟩, ⟨20⟩, ⟨21⟩, ⟨22⟩, ⟨23⟩, ⟨24⟩],
    retired := [],
    restores := [{ lender := ⟨10⟩, borrower := ⟨20⟩, alloc := ⟨0⟩, lo := 0, hi := 1,
                   q := 4, ceiling := .readWrite }] }

/-- The old predicate accepts the overstated suspension. -/
theorem witnessA_old_inv : OldInv witnessA := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hx1 : x < 1 := by simpa [witnessA] using hx
    have hx0 : x = 0 := by omega
    subst hx0
    decide
  · refine ⟨?_, trivial, trivial⟩
    decide
  · refine
      { nodeIds_nodup := by decide
        issue_covers := by decide
        retired_absent := by decide
        restores_issued := by decide
        borrowers_nodup := by decide
        lenders_nodup := by decide
        lender_ne_borrower := by decide
        dormant_absent := by decide
        borrower_not_rule := by decide
        restore_realized := by
          intro r hr
          have hr' : r = { lender := ⟨10⟩, borrower := ⟨20⟩, alloc := ⟨0⟩, lo := 0,
                           hi := 1, q := 4, ceiling := .readWrite } := by
            simpa [witnessA] using hr
          subst hr'
          exact Or.inl ⟨aParent, by simp [witnessA, Forest.nodes], rfl,
            ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
        node_agrees := by
          intro r hr c hc hcid
          have hr' : r = { lender := ⟨10⟩, borrower := ⟨20⟩, alloc := ⟨0⟩, lo := 0,
                           hi := 1, q := 4, ceiling := .readWrite } := by
            simpa [witnessA] using hr
          subst hr'
          simp only [witnessA, Forest.nodes, List.mem_cons, List.mem_singleton,
            List.mem_append, List.nil_append, List.cons_append, List.mem_nil_iff,
            or_false] at hc
          rcases hc with rfl | rfl | rfl
          · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
          · exact absurd hcid (by decide)
          · exact absurd hcid (by decide)
        nested_agrees := by
          intro r hr r' hr' hrel
          have hr1 : r = { lender := ⟨10⟩, borrower := ⟨20⟩, alloc := ⟨0⟩, lo := 0,
                           hi := 1, q := 4, ceiling := .readWrite } := by
            simpa [witnessA] using hr
          have hr2 : r' = { lender := ⟨10⟩, borrower := ⟨20⟩, alloc := ⟨0⟩, lo := 0,
                            hi := 1, q := 4, ceiling := .readWrite } := by
            simpa [witnessA] using hr'
          subst hr1
          subst hr2
          exact absurd hrel (by decide)
        restore_order := by
          intro r hr r' hr' hdep
          have hr1 : r = { lender := ⟨10⟩, borrower := ⟨20⟩, alloc := ⟨0⟩, lo := 0,
                           hi := 1, q := 4, ceiling := .readWrite } := by
            simpa [witnessA] using hr
          have hr2 : r' = { lender := ⟨10⟩, borrower := ⟨20⟩, alloc := ⟨0⟩, lo := 0,
                            hi := 1, q := 4, ceiling := .readWrite } := by
            simpa [witnessA] using hr'
          subst hr1
          subst hr2
          exact absurd hdep (by decide)
        rule_fragments_issued := by decide }

/-- The intended property fails at the witness: the recorded parent share is `4`
while the actual frontier carries `2`. -/
theorem witnessA_frontier_overstated :
    witnessA.forest.budget 0 = 2 ∧ (Forest.leaf aParent).budget 0 = 4 := by
  decide

/-- The witness is not coherent: the left current subtree does not realize its
recorded rule fragment. -/
theorem witnessA_not_coherent : ¬ witnessA.forest.Coherent := by
  intro h
  have hL : (Forest.leaf aLeft).Realizes aLeftRule := h.2.1
  have hb := hL.1 0
  have hbad : (1 : Nat) = 2 := by
    simpa [Forest.budget, Leaf.budget, aLeft, aLeftRule, aLeaf] using hb
  exact absurd hbad (by decide)

/-- The strengthened invariant excludes the witness. -/
theorem witnessA_not_inv : ¬ witnessA.Inv := fun h => witnessA_not_coherent h.coherent

/-- The hypothesis `suspended_frontier_realizes` previously required is not
derivable from the old predicate; it fails at the witness. -/
theorem witnessA_premise_fails :
    ¬ (∀ x, (Forest.leaf aLeft).budget x = (Forest.leaf aLeftRule).budget x) := by
  intro h
  have hb := h 0
  have hbad : (1 : Nat) = 2 := by
    simpa [Forest.budget, Leaf.budget, aLeft, aLeftRule, aLeaf] using hb
  exact absurd hbad (by decide)

/-! ### Finding B: a leaf whose allocation is not the component's -/

/-- The audit's second witness: the root leaf of a one-byte allocation carries
allocation `99` while the component's allocation is `0`. -/
private def bLeaf : Leaf :=
  { id := ⟨1⟩, alloc := ⟨99⟩, lo := 0, hi := 1, ordered := by decide,
    q := 2, pos := by decide, ceiling := .readWrite, state := .active }

def witnessB : State :=
  { State.initial ⟨0⟩ 1 2 (by decide) ⟨1⟩ ⟨2⟩ with forest := .leaf bLeaf }

/-- The old predicate accepts the malformed allocation label. -/
theorem witnessB_old_inv : OldInv witnessB := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hx1 : x < 1 := by simpa [witnessB, State.initial] using hx
    have hx0 : x = 0 := by omega
    subst hx0
    decide
  · trivial
  · refine
      { nodeIds_nodup := by decide
        issue_covers := by decide
        retired_absent := by decide
        restores_issued := by simp [witnessB, State.initial]
        borrowers_nodup := by simp [witnessB, State.initial]
        lenders_nodup := by simp [witnessB, State.initial]
        lender_ne_borrower := by simp [witnessB, State.initial]
        dormant_absent := by simp [witnessB, State.initial]
        borrower_not_rule := by simp [witnessB, State.initial]
        restore_realized := by simp [witnessB, State.initial]
        node_agrees := by simp [witnessB, State.initial]
        nested_agrees := by simp [witnessB, State.initial]
        restore_order := by simp [witnessB, State.initial, State.RestoreOrder]
        rule_fragments_issued := by simp [witnessB, State.initial, Forest.ruleIds] }

/-- The old write guard accepts the write through the mislabelled leaf, and the
write reaches allocation `0`. -/
theorem witnessB_old_write_accepts :
    ∃ s', oldWrite witnessB ⟨1⟩ 0 7 = some s' ∧ s'.heap.read? ⟨0⟩ 0 = some 7 := by
  refine ⟨_, rfl, ?_⟩
  decide

/-- The strengthened scope rejects the malformed allocation label: the current
leaf's allocation must be the component's. -/
theorem witnessB_not_scope : ¬ witnessB.Scope := by
  intro h
  have hc : bLeaf ∈ witnessB.forest.nodes := by
    simp [witnessB, bLeaf, Forest.nodes]
  have hleaf := h.node_scope _ hc
  have : (⟨99⟩ : AllocId) = ⟨0⟩ := hleaf.1
  exact absurd this (by decide)

/-- The malformed-allocation witness still satisfies storage agreement for the
component's allocation, which is the audit's point: coverage and storage alone do
not bind the fragment's allocation label. -/
theorem witnessB_storage : witnessB.Storage :=
  State.Storage.of_heap rfl rfl rfl
    (State.initial_storage ⟨0⟩ 1 2 (by decide) ⟨1⟩ ⟨2⟩)

/-- The strengthened invariant excludes the second witness. -/
theorem witnessB_not_inv : ¬ witnessB.Inv := fun h => witnessB_not_scope h.scope

/-- The repaired write guard refuses the mislabelled authority: the allocation
conjunct is what binds authority to the bytes written. -/
theorem witnessB_write_refused : witnessB.write ⟨1⟩ 0 7 = none := by
  decide

/-- The guard theorem exposes the allocation binding for an accepted write. -/
theorem witnessB_no_accepted_write :
    ¬ ∃ s', witnessB.write ⟨1⟩ 0 7 = some s' := by
  intro h
  obtain ⟨s', hs'⟩ := h
  rw [witnessB_write_refused] at hs'
  cases hs'

/-! ### Further negative controls -/

private def rp : Leaf :=
  { id := ⟨3⟩, alloc := ⟨0⟩, lo := 0, hi := 64, ordered := by decide,
    q := 64, pos := by decide, ceiling := .readWrite, state := .active }

private def rl : Leaf := { rp with id := ⟨4⟩, hi := 32, ordered := by decide }
private def rr : Leaf := { rp with id := ⟨5⟩, lo := 32, ordered := by decide }

/-- A spatial split whose left actual child has the wrong ceiling: the rule is
valid, but coherence fails because the child does not realize the rule fragment. -/
private def ceilingForest : Forest :=
  .split .spatial rp rl rr (.leaf { rl with ceiling := .readOnly }) (.leaf rr)

/-- A mismatched ceiling is not coherent. -/
theorem ceiling_mismatch_not_coherent : ¬ ceilingForest.Coherent := by
  intro h
  have hL : (Forest.leaf { rl with ceiling := .readOnly }).Realizes rl := h.2.1
  have hw := hL.2 { rl with ceiling := .readOnly } (by simp [Forest.nodes])
  simp only [rl] at hw
  exact absurd hw.2.2.2.1 (by decide)

/-- Reconstruction refuses a child whose ceiling does not agree with the rule. -/
theorem ceiling_mismatch_reconstruct_refused :
    ceilingForest.reconstructAt ⟨3⟩ = none := by
  decide

/-- An interval beyond the component's extent is out of scope. -/
private def wLeaf : Leaf :=
  { id := ⟨1⟩, alloc := ⟨0⟩, lo := 0, hi := 65, ordered := by decide,
    q := 64, pos := by decide, ceiling := .readWrite, state := .active }

def wideState : State :=
  { State.initial ⟨0⟩ 64 64 (by decide) ⟨1⟩ ⟨2⟩ with forest := .leaf wLeaf }

/-- The out-of-scope interval is rejected. -/
theorem wideState_not_scope : ¬ wideState.Scope := by
  intro h
  have hc : wLeaf ∈ wideState.forest.nodes := by
    simp [wideState, wLeaf, Forest.nodes]
  have hleaf := h.node_scope _ hc
  have : (65 : Nat) ≤ 64 := hleaf.2.1
  exact absurd this (by decide)

/-- A zero-length allocation is admitted: its single fragment is empty and the
whole allocation is empty. -/
theorem zero_length_initial_scope :
    (State.initial ⟨0⟩ 0 2 (by decide) ⟨1⟩ ⟨2⟩).Scope :=
  (State.initial_inv ⟨0⟩ 0 2 (by decide) ⟨1⟩ ⟨2⟩).scope

/-- A zero-length fragment inside a non-empty allocation is not in scope. -/
private def zLeaf : Leaf :=
  { id := ⟨1⟩, alloc := ⟨0⟩, lo := 0, hi := 0, ordered := by decide,
    q := 2, pos := by decide, ceiling := .readWrite, state := .active }

def zeroLeafState : State :=
  { State.initial ⟨0⟩ 1 2 (by decide) ⟨1⟩ ⟨2⟩ with forest := .leaf zLeaf }

/-- The zero-length fragment is rejected by the empty-range policy. -/
theorem zeroLeafState_not_scope : ¬ zeroLeafState.Scope := by
  intro h
  have hc : zLeaf ∈ zeroLeafState.forest.nodes := by
    simp [zeroLeafState, zLeaf, Forest.nodes]
  have hleaf := h.node_scope _ hc
  have hne : (0 < 0 ∨ 1 = 0) := hleaf.2.2.1
  exact absurd hne (by decide)

/-- A spatial split that would create an empty side of a non-empty allocation is
refused by the state-level guard. -/
theorem empty_side_split_refused :
    (State.initial ⟨0⟩ 64 64 (by decide) ⟨1⟩ ⟨2⟩).splitSpatial
      ⟨1⟩ ⟨3⟩ ⟨4⟩ 0 0 0 64 = none := by
  decide

/-- The corresponding non-empty split is accepted — the affirmative control for
the refusal above. -/
theorem nonempty_split_accepted :
    ((State.initial ⟨0⟩ 64 64 (by decide) ⟨1⟩ ⟨2⟩).splitSpatial
      ⟨1⟩ ⟨3⟩ ⟨4⟩ 0 32 32 64).isSome = true := by
  decide

/-! ### Positive controls: the worked lifecycle still satisfies the invariant -/

/-- The whole `[0,64)` allocation. -/
private def own : State := State.initial ⟨0⟩ 64 64 (by decide) ⟨1⟩ ⟨2⟩

/-- The root borrowed to `⟨3⟩`. -/
private def borrowed : State :=
  match own.borrow ⟨1⟩ ⟨3⟩ with
  | some s => s
  | none => own

/-- Spatially subdivided into `[0,32)` and `[32,64)`. -/
private def split : State :=
  match borrowed.splitSpatial ⟨3⟩ ⟨4⟩ ⟨5⟩ 0 32 32 64 with
  | some s => s
  | none => borrowed

/-- Reconstructed and returned. -/
private def returned : State :=
  match split.reconstruct ⟨3⟩ with
  | some s =>
      match s.return ⟨3⟩ with
      | some s' => s'
      | none => s
  | none => split

/-- The borrowed state is accepted and satisfies the invariant. -/
theorem borrowed_inv : borrowed.Inv :=
  State.borrow_inv (lender := ⟨1⟩) (borrower := ⟨3⟩) rfl
    (State.initial_inv ⟨0⟩ 64 64 (by decide) ⟨1⟩ ⟨2⟩)

/-- The subdivided state is accepted and satisfies the invariant. -/
theorem split_inv : split.Inv :=
  State.splitSpatial_inv (parentId := ⟨3⟩) (c1 := ⟨4⟩) (c2 := ⟨5⟩)
    (lo1 := 0) (hi1 := 32) (lo2 := 32) (hi2 := 64) rfl borrowed_inv

/-- The reconstructed-then-returned lifecycle is accepted and satisfies the
invariant. -/
theorem returned_inv : returned.Inv := by
  unfold returned
  split
  · rename_i s hrec
    split
    · rename_i s' hret
      exact State.return_inv hret (State.reconstruct_inv hrec split_inv)
    · exact State.reconstruct_inv hrec split_inv
  · exact split_inv

/-- The outstanding obligation of the borrowed state lies in its restoration
list. -/
theorem borrowed_restore_mem :
    ({ lender := ⟨1⟩, borrower := ⟨3⟩, alloc := ⟨0⟩, lo := 0, hi := 64,
       q := 64, ceiling := .readWrite } : Restore) ∈ borrowed.restores := by
  decide

/-- Terminal resource realization at the strengthened invariant: the outstanding
obligation reaches a node whose recorded resource is realized by the frontier
below it. No subtree-budget hypothesis is supplied. -/
theorem borrowed_terminal_frontier :
    ∃ r' c, borrowed.RestoreTerminal r' c ∧
      (r' = { lender := ⟨1⟩, borrower := ⟨3⟩, alloc := ⟨0⟩, lo := 0, hi := 64,
              q := 64, ceiling := .readWrite } ∨
       State.RestoreReaches borrowed
         { lender := ⟨1⟩, borrower := ⟨3⟩, alloc := ⟨0⟩, lo := 0, hi := 64,
           q := 64, ceiling := .readWrite } r') ∧
      borrowed.forest.NodeRealized c := by
  obtain ⟨r', c, hterm, hpath, -, hrealized⟩ :=
    borrowed_inv.restore_terminal_frontier borrowed_restore_mem
  exact ⟨r', c, hterm, hpath, hrealized⟩

end CapInvariantWitness
