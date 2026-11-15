import Cap.Core

open Cap

/-- A capability is never fresh alongside itself. -/
example (o : Owner) (id : CapId) : ¬ o.FreshIds id id := by
  intro h
  exact h.2.2 rfl

/-- Duplicate child identifiers are refused by the checker. -/
example (o : Owner) (D : Nat) (id : CapId) (cs : List Cmd) :
    check o D (Cmd.splitAt id ⟨1⟩ ⟨1⟩ 4 :: cs) = .error msgFresh := by
  have h : ¬ o.FreshIds ⟨1⟩ ⟨1⟩ := by
    intro hh
    exact hh.2.2 rfl
  simp [check, h]

/-- Reusing the parent's identifier as a child is refused: the parent is in the
owner's identifiers, so it cannot be fresh. -/
example (D : Nat) (cs : List Cmd) :
    check (Owner.init ⟨0⟩ 8 8 (by decide) ⟨0⟩ ⟨9⟩) D
        (Cmd.splitAt ⟨0⟩ ⟨0⟩ ⟨5⟩ 4 :: cs) = .error msgFresh := by
  have hmem : (⟨0⟩ : CapId) ∈ (Owner.init ⟨0⟩ 8 8 (by decide) ⟨0⟩ ⟨9⟩).ids := by
    simp [Owner.ids, Tree.ids, Owner.init]
  have h : ¬ (Owner.init ⟨0⟩ 8 8 (by decide) ⟨0⟩ ⟨9⟩).FreshIds ⟨0⟩ ⟨5⟩ := by
    intro hh
    exact hh.1 hmem
  simp [check, h]
