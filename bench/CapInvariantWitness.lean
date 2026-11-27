import Cap.Reconstruction

open Cap
open Cap.Reconstruction

/-!
Regression and admissibility controls for the strengthened reconstruction
invariant.

The witnesses are the adversarial examples of the two audits, encoded against the
predicates the earlier revisions maintained. `PrevAccounts` is the ownership
account exactly as `5effd62` states it: the same fields without the
lender-retirement condition. `OldInv` is exactly `Covered ∧ Valid ∧
PrevAccounts`; `PrevInv` adds coherence and scope, which is the whole invariant of
`5effd62`. `oldWrite` is exactly the write guard before the allocation binding.

* `witnessA` — a suspension whose recorded parent share is `4` while its actual
  frontier carries `1 + 1`. It satisfies `OldInv`, and `suspended_frontier_realizes`'s
  subtree-budget premise fails at it. Coherence rejects it.
* `witnessB` — a single leaf whose allocation field is `99` inside a component
  whose allocation is `0`. It satisfies `OldInv`, and the old write guard accepts
  a write that updates allocation `0`. Scope rejects it and the new guard refuses
  the write.
* `retiredLender` — a realized terminal resource whose recorded lender has
  already been retired. It satisfies `PrevInv`; `State.return` refuses it because
  the return target is unusable, and the strengthened account excludes it.
* `renamedChild` — a coherent fractional split whose actual leaves carry
  identities no restoration record explains. It satisfies `PrevInv`; the
  identities are not recoverable, reconstruction is refused, and the identity
  recovery component of the invariant excludes it.

The module then records the negative controls the repair relies on and positive
controls showing the worked lifecycle satisfies the stronger invariant, including
a borrowed child whose changed name is explained by its restoration chain.
-/

namespace CapInvariantWitness

/-! ### The previous predicates -/

/-- The ownership accounts as `5effd62` maintains them: node distinctness,
issuance coverage, retirement, dormant lenders, restoration realization,
resource agreement and restoration order — no lender-retirement condition. -/
structure PrevAccounts (s : State) : Prop where
  nodeIds_nodup : (s.forest.nodes.map Leaf.id).Nodup
  issue_covers : ∀ id ∈ s.forest.ids, id ∈ s.issued
  retired_absent : ∀ id ∈ s.forest.nodes.map Leaf.id, id ∉ s.retired
  restores_issued : ∀ r ∈ s.restores, r.lender ∈ s.issued ∧ r.borrower ∈ s.issued
  borrowers_nodup : (s.restores.map Restore.borrower).Nodup
  lenders_nodup : (s.restores.map Restore.lender).Nodup
  lender_ne_borrower : ∀ r ∈ s.restores, r.lender ≠ r.borrower
  dormant_absent : ∀ r ∈ s.restores, r.lender ∉ s.forest.nodes.map Leaf.id
  borrower_not_rule : ∀ r ∈ s.restores, r.borrower ∉ s.forest.ruleIds
  restore_realized : ∀ r ∈ s.restores,
      (∃ c ∈ s.forest.nodes, c.id = r.borrower ∧ r.Agrees c) ∨
      (∃ r' ∈ s.restores, r'.lender = r.borrower)
  node_agrees : ∀ r ∈ s.restores, ∀ c ∈ s.forest.nodes,
      c.id = r.borrower → r.Agrees c
  nested_agrees : ∀ r ∈ s.restores, ∀ r' ∈ s.restores,
      r'.lender = r.borrower → r.SameResource r'
  restore_order : s.RestoreOrder
  rule_fragments_issued : ∀ id ∈ s.forest.ruleIds, id ∈ s.issued

/-- The reconstruction invariant before the coherence and scope repair. -/
def OldInv (s : State) : Prop := s.Covered ∧ s.forest.Valid ∧ PrevAccounts s

/-- The reconstruction invariant of `5effd62`: coverage, rule validity, the
written accounts, recursive coherence and component scope. -/
def PrevInv (s : State) : Prop :=
  s.Covered ∧ s.forest.Valid ∧ PrevAccounts s ∧ s.Coherent ∧ s.Scope

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

/-! ### Finding C: a dormant lender already retired

The follow-up audit's first witness: a one-byte allocation with denominator `2`
whose single live leaf realizes the outstanding obligation, but whose recorded
lender `1` has already been retired. -/

private def cLeaf : Leaf :=
  { id := ⟨20⟩, alloc := ⟨0⟩, lo := 0, hi := 1, ordered := by decide,
    q := 2, pos := by decide, ceiling := .readWrite, state := .active }

private def cRestore : Restore :=
  { lender := ⟨1⟩, borrower := ⟨20⟩, alloc := ⟨0⟩, lo := 0, hi := 1,
    q := 2, ceiling := .readWrite }

/-- The follow-up audit's first witness: a realized terminal resource whose
recorded return target has already been retired. -/
def retiredLender : State :=
  { alloc := ⟨0⟩, len := 1, D := 2,
    forest := .leaf cLeaf,
    heap := Heap.alloc Heap.empty ⟨0⟩ 1,
    issued := [⟨1⟩, ⟨2⟩, ⟨20⟩],
    retired := [⟨1⟩],
    restores := [cRestore] }

/-- The invariant of `5effd62` accepts the retired lender: coverage, validity,
the written accounts, coherence and scope all hold. -/
theorem retiredLender_prev_inv : PrevInv retiredLender := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hx1 : x < 1 := by simpa [retiredLender] using hx
    have hx0 : x = 0 := by omega
    subst hx0
    decide
  · trivial
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
          have hr' : r = cRestore := by simpa [retiredLender] using hr
          subst hr'
          exact Or.inl ⟨cLeaf, by simp [retiredLender, Forest.nodes], rfl,
            ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
        node_agrees := by
          intro r hr c hc hcid
          have hr' : r = cRestore := by simpa [retiredLender] using hr
          have hc' : c = cLeaf := by simpa [retiredLender, Forest.nodes] using hc
          subst hr'
          subst hc'
          exact ⟨rfl, rfl, rfl, rfl, rfl⟩
        nested_agrees := by
          intro r hr r' hr' hrel
          have hr1 : r = cRestore := by simpa [retiredLender] using hr
          have hr2 : r' = cRestore := by simpa [retiredLender] using hr'
          subst hr1
          subst hr2
          exact absurd hrel (by decide)
        restore_order := by
          intro r hr r' hr' hdep
          have hr1 : r = cRestore := by simpa [retiredLender] using hr
          have hr2 : r' = cRestore := by simpa [retiredLender] using hr'
          subst hr1
          subst hr2
          exact absurd hdep (by decide)
        rule_fragments_issued := by decide }
  · exact (show retiredLender.forest.Coherent from trivial)
  · refine ⟨by decide, ?_, ?_⟩
    · intro c hc
      simp only [retiredLender, Forest.nodes, List.mem_singleton] at hc
      rcases hc with rfl
      exact ⟨rfl, Nat.le_refl _, Or.inl (by decide), Nat.le_refl _⟩
    · intro r hr
      have hr' : r = cRestore := by simpa [retiredLender] using hr
      subst hr'
      exact ⟨rfl, by decide, by decide, by decide⟩

/-- The intended return is refused: the recorded lender is retired. -/
theorem retiredLender_return_refused : retiredLender.return ⟨20⟩ = none := by
  decide

/-- The strengthened account rejects the retired lender. -/
theorem retiredLender_not_accounts : ¬ retiredLender.Accounts := by
  intro h
  have hr : cRestore ∈ retiredLender.restores := by simp [retiredLender]
  exact h.lenders_not_retired cRestore hr (by simp [retiredLender, cRestore])

/-- The strengthened invariant excludes the witness. -/
theorem retiredLender_not_inv : ¬ retiredLender.Inv :=
  fun h => retiredLender_not_accounts h.accounts

/-! ### Finding D: coherent children with unexplained identities

The follow-up audit's second witness: a fractional split whose actual leaves
realize the recorded rule resources but carry access identities no restoration
record explains. -/

private def dLeaf (id : CapId) : Leaf :=
  { id := id, alloc := ⟨0⟩, lo := 0, hi := 1, ordered := by decide,
    q := 1, pos := by decide, ceiling := .readWrite, state := .active }

private def dParent : Leaf := { dLeaf ⟨1⟩ with q := 2, pos := by decide }

/-- The follow-up audit's second witness: all names issued, nothing retired, no
outstanding obligation, and the actual leaves `5` and `6` do not recover the rule
identities `3` and `4`. -/
def renamedChild : State :=
  { alloc := ⟨0⟩, len := 1, D := 2,
    forest := .split .fractional dParent (dLeaf ⟨3⟩) (dLeaf ⟨4⟩)
      (.leaf (dLeaf ⟨5⟩)) (.leaf (dLeaf ⟨6⟩)),
    heap := Heap.alloc Heap.empty ⟨0⟩ 1,
    issued := [⟨1⟩, ⟨3⟩, ⟨4⟩, ⟨5⟩, ⟨6⟩],
    retired := [],
    restores := [] }

/-- The actual left subtree realizes the left rule resource. -/
theorem renamedChild_left_realizes :
    (Forest.leaf (dLeaf ⟨5⟩)).Realizes (dLeaf ⟨3⟩) :=
  ⟨fun _ => rfl, by
    intro d hd
    simp only [Forest.nodes, List.mem_singleton] at hd
    rcases hd with rfl
    exact ⟨rfl, Nat.le_refl _, Nat.le_refl _, rfl, Nat.le_refl _⟩⟩

/-- The actual right subtree realizes the right rule resource. -/
theorem renamedChild_right_realizes :
    (Forest.leaf (dLeaf ⟨6⟩)).Realizes (dLeaf ⟨4⟩) :=
  ⟨fun _ => rfl, by
    intro d hd
    simp only [Forest.nodes, List.mem_singleton] at hd
    rcases hd with rfl
    exact ⟨rfl, Nat.le_refl _, Nat.le_refl _, rfl, Nat.le_refl _⟩⟩

/-- The witness is coherent: the resources line up, and no name equality is
required. -/
theorem renamedChild_coherent : renamedChild.forest.Coherent :=
  ⟨by decide, renamedChild_left_realizes, renamedChild_right_realizes, trivial, trivial⟩

/-- The invariant of `5effd62` accepts the unexplained identities: coverage,
validity, the written accounts, coherence and scope all hold. -/
theorem renamedChild_prev_inv : PrevInv renamedChild := by
  refine ⟨?_, ?_, ?_, renamedChild_coherent, ?_⟩
  · intro x hx
    have hx1 : x < 1 := by simpa [renamedChild] using hx
    have hx0 : x = 0 := by omega
    subst hx0
    decide
  · exact (show renamedChild.forest.Valid from ⟨by decide, trivial, trivial⟩)
  · refine
      { nodeIds_nodup := by decide
        issue_covers := by decide
        retired_absent := by decide
        restores_issued := by simp [renamedChild]
        borrowers_nodup := by simp [renamedChild]
        lenders_nodup := by simp [renamedChild]
        lender_ne_borrower := by simp [renamedChild]
        dormant_absent := by simp [renamedChild]
        borrower_not_rule := by simp [renamedChild]
        restore_realized := by simp [renamedChild]
        node_agrees := by simp [renamedChild]
        nested_agrees := by simp [renamedChild]
        restore_order := by simp [renamedChild, State.RestoreOrder]
        rule_fragments_issued := by decide }
  · refine ⟨by decide, ?_, ?_⟩
    · intro c hc
      simp only [renamedChild, Forest.nodes, List.mem_cons, List.mem_append,
        List.mem_singleton, List.nil_append, List.cons_append, List.mem_nil_iff,
        or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact ⟨rfl, Nat.le_refl _, Or.inl (by decide), by decide⟩
      · exact ⟨rfl, Nat.le_refl _, Or.inl (by decide), by decide⟩
      · exact ⟨rfl, Nat.le_refl _, Or.inl (by decide), by decide⟩
    · intro r hr
      simp [renamedChild] at hr

/-- Reconstruction of the parent is refused: the left child does not carry the
rule identity. -/
theorem renamedChild_reconstruct_refused : renamedChild.reconstruct ⟨1⟩ = none := by
  decide

/-- The witness's left rule identity is not recoverable from its actual leaf:
there is no restoration chain from `3` to `5`. -/
theorem renamedChild_left_not_recoverable :
    ¬ (Forest.leaf (dLeaf ⟨5⟩)).Recovers renamedChild.restores ⟨3⟩ := by
  intro h
  cases h with
  | leaf =>
      rename_i hchain
      simp [renamedChild] at hchain
      exact absurd (Forest.RestoreChain.nil_left hchain) (by decide)

/-- Identity recovery excludes the witness. -/
theorem renamedChild_not_recovers : ¬ renamedChild.Recovers := by
  intro h
  exact renamedChild_left_not_recoverable h.1

/-- The strengthened invariant excludes the witness: resource coherence holds,
identity recovery does not. -/
theorem renamedChild_not_inv : ¬ renamedChild.Inv :=
  fun h => renamedChild_not_recovers h.recoverable

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

/-! ### Positive control: a borrowed child whose restoration chain explains it

A one-byte fractional split borrowed on its left side. The bookkeeping is the
contrast with `renamedChild`: the left leaf's changed name is reached by a
restoration record, so identity recovery holds, and returning the loan restores
the rule identity and makes the suspension reconstructible again. -/

private def oneRoot : Leaf :=
  { id := ⟨1⟩, alloc := ⟨0⟩, lo := 0, hi := 1, ordered := by decide,
    q := 2, pos := by decide, ceiling := .readWrite, state := .active }

private def oneLeft : Leaf := { oneRoot with id := ⟨3⟩, q := 1, pos := by decide }
private def oneRight : Leaf := { oneRoot with id := ⟨4⟩, q := 1, pos := by decide }
private def oneBorrowed : Leaf := { oneLeft with id := ⟨5⟩ }

private def oneOwn : State := State.initial ⟨0⟩ 1 2 (by decide) ⟨1⟩ ⟨2⟩

private def oneSplit : State :=
  match oneOwn.splitFraction ⟨1⟩ ⟨3⟩ ⟨4⟩ 1 1 with
  | some s => s
  | none => oneOwn

private def oneBorrowedState : State :=
  match oneSplit.borrow ⟨3⟩ ⟨5⟩ with
  | some s => s
  | none => oneSplit

private def oneReturnedState : State :=
  match oneBorrowedState.return ⟨5⟩ with
  | some s => s
  | none => oneBorrowedState

private def oneRejoined : State :=
  match oneReturnedState.reconstruct ⟨1⟩ with
  | some s => s
  | none => oneReturnedState

/-- The borrowed state's forest: the left child now carries the borrower name. -/
theorem oneBorrowedState_forest :
    oneBorrowedState.forest =
      .split .fractional oneRoot oneLeft oneRight (.leaf oneBorrowed) (.leaf oneRight) := by
  rfl

/-- The restoration record links the left rule identity to the borrowed name. -/
theorem oneBorrowedState_record :
    ({ lender := ⟨3⟩, borrower := ⟨5⟩, alloc := ⟨0⟩, lo := 0, hi := 1,
       q := 1, ceiling := .readWrite } : Restore) ∈ oneBorrowedState.restores := by
  decide

/-- The changed identity is explained by a restoration chain from the rule
identity to the actual leaf. -/
theorem oneBorrowedState_chain :
    Forest.RestoreChain oneBorrowedState.restores ⟨3⟩ ⟨5⟩ :=
  Forest.RestoreChain.single oneBorrowedState_record

/-- The left child recovers the rule identity the suspension records. -/
theorem oneBorrowedState_left_recovers :
    (Forest.leaf oneBorrowed).Recovers oneBorrowedState.restores ⟨3⟩ :=
  Forest.Recovers.leaf oneBorrowed oneBorrowedState_chain

/-- The borrowed state is accepted: its changed name is accounted for. -/
theorem oneBorrowedState_inv : oneBorrowedState.Inv :=
  State.borrow_inv (lender := ⟨3⟩) (borrower := ⟨5⟩) rfl
    (State.splitFraction_inv (parentId := ⟨1⟩) (c1 := ⟨3⟩) (c2 := ⟨4⟩)
      (q1 := 1) (q2 := 1) rfl
      (State.initial_inv ⟨0⟩ 1 2 (by decide) ⟨1⟩ ⟨2⟩))

/-- The suspension of the borrowed state records identity recovery for both
children, no caller-supplied chain. -/
theorem oneBorrowedState_suspension_recovers :
    (Forest.leaf oneBorrowed).Recovers oneBorrowedState.restores ⟨3⟩ ∧
    (Forest.leaf oneRight).Recovers oneBorrowedState.restores ⟨4⟩ := by
  exact ⟨oneBorrowedState_left_recovers,
    Forest.Recovers.leaf oneRight (Forest.RestoreChain.nil ⟨4⟩)⟩

/-- The returned state is accepted. -/
theorem oneReturnedState_inv : oneReturnedState.Inv :=
  State.return_inv (borrower := ⟨5⟩) rfl oneBorrowedState_inv

/-- Reconstructing the suspension after the return is accepted: the recovered
identity is directly present again. -/
theorem oneRejoined_succeeds : oneReturnedState.reconstruct ⟨1⟩ ≠ none := by
  decide

/-- The rejoined state is accepted and its frontier is the whole resource. -/
theorem oneRejoined_inv : oneRejoined.Inv := by
  unfold oneRejoined
  split
  · rename_i s hrec
    exact State.reconstruct_inv hrec oneReturnedState_inv
  · exact oneReturnedState_inv

end CapInvariantWitness
