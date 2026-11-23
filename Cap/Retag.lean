/-
Capability retagging for the live-borrower accounting model.

A borrow does not add a second whole-share leaf. The lender's active leaf is
retagged to the borrower identity, so the decomposition continues to carry the
allocation's share exactly once. The loan record stores the original lender
identity for restoration. Retagging changes only leaf identifiers, not
footprints, shares, states or ceilings, so the byte budget and coverage are
unchanged.
-/
import Cap.Ledger

namespace Cap

/-- Rename every occurrence of `old` to `new`; the leaf's other fields are kept. -/
def Tree.retag (old new : CapId) : Tree → Tree
  | .leaf c => .leaf (if c.id = old then { c with id := new } else c)
  | .frac i l r => .frac i (l.retag old new) (r.retag old new)
  | .spatial i l r => .spatial i (l.retag old new) (r.retag old new)

/-- Retagging preserves the byte budget: the budget reads footprints, shares and
    states, never identifiers. -/
theorem Tree.retag_budget (t : Tree) (old new : CapId) (x : Nat) :
    (t.retag old new).budget x = t.budget x := by
  induction t with
  | leaf c => by_cases h : c.id = old <;>
      simp [Tree.retag, Tree.budget, Leaf.budget, h]
  | frac i l r ihl ihr => simp [Tree.retag, Tree.budget, ihl, ihr]
  | spatial i l r ihl ihr => simp [Tree.retag, Tree.budget, ihl, ihr]

/-- Retag an active leaf to a fresh identifier. -/
def Owner.retagLeaf? (o : Owner) (old new : CapId) : Option Owner :=
  match o.root.find? old with
  | none => none
  | some c =>
    if c.state = .active then
      if new ∉ o.root.ids then
        some { o with root := o.root.retag old new }
      else none
    else none

/-- A successful retag preserves the byte budget everywhere. -/
theorem Owner.retagLeaf?_budget {o o' : Owner} {old new : CapId} {x : Nat}
    (h : o.retagLeaf? old new = some o') :
    o'.root.budget x = o.root.budget x := by
  unfold Owner.retagLeaf? at h
  cases hf : o.root.find? old with
  | none => simp [hf] at h
  | some c =>
    simp only [hf] at h
    by_cases hstate : c.state = .active
    · by_cases hfresh : new ∉ o.root.ids
      · simp [hstate, hfresh] at h
        cases h
        exact Tree.retag_budget o.root old new x
      · simp [hstate, hfresh] at h
    · simp [hstate] at h

/-- A successful retag leaves the owner length unchanged. -/
theorem Owner.retagLeaf?_len {o o' : Owner} {old new : CapId}
    (h : o.retagLeaf? old new = some o') : o'.len = o.len := by
  unfold Owner.retagLeaf? at h
  cases hf : o.root.find? old with
  | none => simp [hf] at h
  | some c =>
    simp only [hf] at h
    by_cases hstate : c.state = .active
    · by_cases hfresh : new ∉ o.root.ids
      · simp [hstate, hfresh] at h
        cases h
        rfl
      · simp [hstate, hfresh] at h
    · simp [hstate] at h

/-- A successful retag preserves coverage at the same denominator. -/
theorem Owner.retagLeaf?_covered {o o' : Owner} {old new : CapId} {D : Nat}
    (h : o.retagLeaf? old new = some o') :
    o'.Covered D ↔ o.Covered D := by
  unfold Owner.Covered
  constructor
  · intro hc x hx
    rw [← Owner.retagLeaf?_budget h]
    exact hc x (by simpa [Owner.retagLeaf?_len h] using hx)
  · intro hc x hx
    rw [Owner.retagLeaf?_budget h]
    exact hc x (by simpa [Owner.retagLeaf?_len h] using hx)

/-- A successful retag starts from an active leaf. -/
theorem Owner.retagLeaf?_active {o o' : Owner} {old new : CapId}
    (h : o.retagLeaf? old new = some o') :
    ∃ c, o.root.find? old = some c ∧ c.state = .active := by
  unfold Owner.retagLeaf? at h
  cases hf : o.root.find? old with
  | none => simp [hf] at h
  | some c =>
    simp only [hf] at h
    by_cases hstate : c.state = .active
    · by_cases hfresh : new ∉ o.root.ids
      · simp [hstate, hfresh] at h
        exact ⟨c, rfl, hstate⟩
      · simp [hstate, hfresh] at h
    · simp [hstate] at h

/-- A successful retag targets a fresh identifier in the owner's current tree. -/
theorem Owner.retagLeaf?_fresh {o o' : Owner} {old new : CapId}
    (h : o.retagLeaf? old new = some o') :
    new ∉ o.root.ids := by
  unfold Owner.retagLeaf? at h
  cases hf : o.root.find? old with
  | none => simp [hf] at h
  | some c =>
    simp only [hf] at h
    by_cases hstate : c.state = .active
    · by_cases hfresh : new ∉ o.root.ids
      · simp [hstate, hfresh] at h
        exact hfresh
      · simp [hstate, hfresh] at h
    · simp [hstate] at h

end Cap
