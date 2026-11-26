import Cap.Reconstruction

open Cap
open Cap.Reconstruction

/-!
Executable controls for the restoration dependency order.

`LegacyAccounts` is the accounting predicate without the dependency-order field:
exactly the fields the account had before the order was added. The two-edge
cycle satisfies that predicate, so realization and nested agreement alone do not
exclude it. The repaired `State.Accounts` rejects the cycle and a longer cycle,
accepts a valid nested borrow, and rejects an obligation whose borrower is
neither a forest node nor a further obligation.
-/

namespace CapRestorationOrder

/-! ### Fixtures -/

/-- The whole `[0,64)` allocation of the worked example. -/
private def own : State :=
  State.initial ⟨0⟩ 64 64 (by decide) ⟨1⟩ ⟨2⟩

/-- One obligation from `lender` to `borrower` over the whole allocation. -/
private def obligation (lender borrower : CapId) : Restore :=
  { lender := lender, borrower := borrower, alloc := ⟨0⟩, lo := 0, hi := 64,
    q := 64, ceiling := .readWrite }

/-- Two obligations that justify each other: `⟨20⟩` lends `⟨21⟩` and back. -/
private def cycleState : State :=
  { own with
    issued := [⟨20⟩, ⟨21⟩, ⟨1⟩, ⟨2⟩],
    restores := [obligation ⟨20⟩ ⟨21⟩, obligation ⟨21⟩ ⟨20⟩] }

/-- A three-edge cycle `⟨20⟩ → ⟨21⟩ → ⟨22⟩ → ⟨20⟩`. -/
private def cycle3State : State :=
  { own with
    issued := [⟨22⟩, ⟨21⟩, ⟨20⟩, ⟨1⟩, ⟨2⟩],
    restores :=
      [obligation ⟨20⟩ ⟨21⟩, obligation ⟨21⟩ ⟨22⟩, obligation ⟨22⟩ ⟨20⟩] }

/-- A single obligation with no represented terminal and no onward record. -/
private def missingState : State :=
  { own with
    issued := [⟨20⟩, ⟨21⟩, ⟨1⟩, ⟨2⟩],
    restores := [obligation ⟨20⟩ ⟨21⟩] }

/-- The valid nested borrow: `⟨1⟩` lends to `⟨20⟩`, which lends to `⟨21⟩`. -/
private def nestedA : State :=
  match own.borrow ⟨1⟩ ⟨20⟩ with
  | some s => s
  | none => own

/-- The second, nested borrow. -/
private def nestedB : State :=
  match nestedA.borrow ⟨20⟩ ⟨21⟩ with
  | some s => s
  | none => nestedA

/-! ### The legacy account without the dependency order -/

/-- The accounting fields that precede the dependency order. This is a
regression statement about the earlier predicate, kept beside the controls so a
cycle that only the order excludes is visible. -/
def LegacyAccounts (s : State) : Prop :=
  (s.forest.nodes.map Leaf.id).Nodup ∧
  (∀ id ∈ s.forest.ids, id ∈ s.issued) ∧
  (∀ id ∈ s.forest.nodes.map Leaf.id, id ∉ s.retired) ∧
  (∀ r ∈ s.restores, r.lender ∈ s.issued ∧ r.borrower ∈ s.issued) ∧
  (s.restores.map Restore.borrower).Nodup ∧
  (s.restores.map Restore.lender).Nodup ∧
  (∀ r ∈ s.restores, r.lender ≠ r.borrower) ∧
  (∀ r ∈ s.restores, r.lender ∉ s.forest.nodes.map Leaf.id) ∧
  (∀ r ∈ s.restores, r.borrower ∉ s.forest.ruleIds) ∧
  (∀ r ∈ s.restores,
      (∃ c ∈ s.forest.nodes, c.id = r.borrower ∧ r.Agrees c) ∨
      (∃ r' ∈ s.restores, r'.lender = r.borrower)) ∧
  (∀ r ∈ s.restores, ∀ c ∈ s.forest.nodes,
      c.id = r.borrower → r.Agrees c) ∧
  (∀ r ∈ s.restores, ∀ r' ∈ s.restores,
      r'.lender = r.borrower → r.SameResource r') ∧
  (∀ id ∈ s.forest.ruleIds, id ∈ s.issued)

/-- The repaired account still implies every legacy field. -/
private theorem accounts_to_legacy {s : State} (h : s.Accounts) :
    LegacyAccounts s :=
  ⟨h.nodeIds_nodup, h.issue_covers, h.retired_absent, h.restores_issued,
   h.borrowers_nodup, h.lenders_nodup, h.lender_ne_borrower, h.dormant_absent,
   h.borrower_not_rule, h.restore_realized, h.node_agrees, h.nested_agrees,
   h.rule_fragments_issued⟩

/-! ### The two-edge cycle the order excludes -/

/-- The two-edge cycle satisfies every accounting field except the order. -/
theorem legacy_two_edge_cycle : LegacyAccounts cycleState := by
  have hmem : ∀ r ∈ cycleState.restores,
      r = obligation ⟨20⟩ ⟨21⟩ ∨ r = obligation ⟨21⟩ ⟨20⟩ := by
    intro r hr
    simpa [cycleState] using hr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [cycleState, own, State.initial, Forest.nodes]
  · intro id hid
    simp [cycleState, own, State.initial, Forest.ids] at hid
    subst hid
    simp [cycleState]
  · intro id _ hret
    simp [cycleState, own, State.initial] at hret
  · intro r hr
    rcases hmem r hr with rfl | rfl <;> simp [cycleState, obligation]
  · simp [cycleState, obligation]
  · simp [cycleState, obligation]
  · intro r hr
    rcases hmem r hr with rfl | rfl <;> decide
  · intro r hr hm
    rcases hmem r hr with rfl | rfl <;>
      (simp [cycleState, own, State.initial, Forest.nodes, obligation] at hm)
  · intro r hr hm
    rcases hmem r hr with rfl | rfl <;>
      (simp [cycleState, own, State.initial, Forest.ruleIds] at hm)
  · intro r hr
    rcases hmem r hr with rfl | rfl
    · exact Or.inr ⟨obligation ⟨21⟩ ⟨20⟩, by simp [cycleState], by decide⟩
    · exact Or.inr ⟨obligation ⟨20⟩ ⟨21⟩, by simp [cycleState], by decide⟩
  · intro r hr c hc hcid
    rcases hmem r hr with rfl | rfl
    · simp only [cycleState, own, State.initial, Forest.nodes,
        List.mem_singleton] at hc
      subst c
      simp [obligation] at hcid
    · simp only [cycleState, own, State.initial, Forest.nodes,
        List.mem_singleton] at hc
      subst c
      simp [obligation] at hcid
  · intro r hr r' hr' _hrel
    rcases hmem r hr with rfl | rfl <;> rcases hmem r' hr' with rfl | rfl <;>
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · intro id hid
    simp [cycleState, own, State.initial, Forest.ruleIds] at hid

/-- The two-edge cycle is rejected by the repaired account. -/
theorem two_edge_cycle_not_accounts : ¬ cycleState.Accounts := by
  intro h
  have hord := h.restore_order
  have hbad :
      cycleState.restores.idxOf (obligation ⟨21⟩ ⟨20⟩) <
        cycleState.restores.idxOf (obligation ⟨20⟩ ⟨21⟩) :=
    hord (obligation ⟨20⟩ ⟨21⟩) (by decide)
      (obligation ⟨21⟩ ⟨20⟩) (by decide) (by decide)
  exact absurd hbad (by decide)

/-- The repaired reconstruction invariant rejects the cycle. -/
theorem two_edge_cycle_not_inv : ¬ cycleState.Inv :=
  fun h => two_edge_cycle_not_accounts h.2.2

/-! ### A longer cycle is rejected -/

/-- The repaired account rejects the three-edge cycle. -/
theorem three_edge_cycle_not_accounts : ¬ cycle3State.Accounts := by
  intro h
  have hord := h.restore_order
  have hbad :
      cycle3State.restores.idxOf (obligation ⟨21⟩ ⟨22⟩) <
        cycle3State.restores.idxOf (obligation ⟨20⟩ ⟨21⟩) :=
    hord (obligation ⟨20⟩ ⟨21⟩) (by decide)
      (obligation ⟨21⟩ ⟨22⟩) (by decide) (by decide)
  exact absurd hbad (by decide)

/-- The repaired reconstruction invariant rejects the three-edge cycle. -/
theorem three_edge_cycle_not_inv : ¬ cycle3State.Inv :=
  fun h => three_edge_cycle_not_accounts h.2.2

/-! ### A missing terminal is rejected -/

/-- No forest node and no onward obligation realizes the borrower. -/
theorem legacy_missing_terminal_rejected : ¬ LegacyAccounts missingState := by
  intro h
  obtain ⟨-, -, -, -, -, -, -, -, -, hreal, -, -, -⟩ := h
  have hr : obligation ⟨20⟩ ⟨21⟩ ∈ missingState.restores := by
    simp [missingState]
  rcases hreal _ hr with ⟨c, hc, hcid, _⟩ | ⟨r', hr', hrel⟩
  · simp only [missingState, own, State.initial, Forest.nodes,
      List.mem_singleton] at hc
    subst c
    simp [obligation] at hcid
  · simp only [missingState, List.mem_singleton] at hr'
    subst r'
    simp [obligation] at hrel

/-- The repaired account rejects the missing terminal. -/
theorem missing_terminal_not_accounts : ¬ missingState.Accounts :=
  fun h => legacy_missing_terminal_rejected (accounts_to_legacy h)

/-- The repaired reconstruction invariant rejects the missing terminal. -/
theorem missing_terminal_not_inv : ¬ missingState.Inv :=
  fun h => missing_terminal_not_accounts h.2.2

/-! ### A valid nested borrow is accepted -/

/-- The first borrow is accepted. -/
private theorem borrowA_accepted : own.borrow ⟨1⟩ ⟨20⟩ = some nestedA := rfl

/-- The nested borrow is accepted. -/
private theorem borrowB_accepted : nestedA.borrow ⟨20⟩ ⟨21⟩ = some nestedB := rfl

/-- The valid nested borrow satisfies the reconstruction invariant. -/
theorem nested_inv : nestedB.Inv :=
  State.borrow_inv borrowB_accepted
    (State.borrow_inv borrowA_accepted
      (State.initial_inv ⟨0⟩ 64 64 (by decide) ⟨1⟩ ⟨2⟩))

/-- The valid nested borrow satisfies the repaired account. -/
theorem nested_accounts : nestedB.Accounts := nested_inv.2.2

/-- The nested obligations are ordered: the inner obligation precedes the outer
one and the dependency runs from the outer to the inner. -/
theorem nested_restore_order : nestedB.RestoreOrder :=
  nested_accounts.restore_order

/-- Both nested obligations reach a terminal forest node whose resource agrees
along the delegation path. -/
theorem nested_terminal_realization :
    ∀ r ∈ nestedB.restores, ∃ r' : Restore, ∃ c : Leaf,
      nestedB.RestoreTerminal r' c ∧
      (r' = r ∨ State.RestoreReaches nestedB r r') ∧ r.Agrees c :=
  fun r hr => nested_accounts.restore_reaches_terminal hr

end CapRestorationOrder
