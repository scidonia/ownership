import Cap.Ledger

open Cap

/-!
Negative controls for the ledger's guards, as checked theorems rather than a test
script: a read-only leaf, a consumed leaf and a half-share leaf cannot authorise a
write; an alias of one capability is not a join pair.
-/

private def alloc0 : AllocId := ⟨0⟩

private def roLeaf : Leaf :=
  { id := ⟨1⟩, alloc := alloc0, lo := 0, hi := 8, ordered := by decide,
    q := 64, pos := by decide, ceiling := .readOnly, state := .active }

private def consumedLeaf : Leaf :=
  { id := ⟨2⟩, alloc := alloc0, lo := 0, hi := 8, ordered := by decide,
    q := 64, pos := by decide, ceiling := .readWrite, state := .consumed }

private def halfLeaf : Leaf :=
  { id := ⟨3⟩, alloc := alloc0, lo := 0, hi := 16, ordered := by decide,
    q := 32, pos := by decide, ceiling := .readWrite, state := .active }

private def roOwner : Owner :=
  { alloc := alloc0, len := 8, root := .leaf roLeaf, disposal := ⟨9⟩ }

private def consumedOwner : Owner :=
  { alloc := alloc0, len := 8, root := .leaf consumedLeaf, disposal := ⟨9⟩ }

private def halfOwner : Owner :=
  { alloc := alloc0, len := 16, root := .leaf halfLeaf, disposal := ⟨9⟩ }

private theorem roFind : roOwner.root.find? ⟨1⟩ = some roLeaf := by
  simp [roOwner, Tree.find?, roLeaf]

private theorem consumedFind : consumedOwner.root.find? ⟨2⟩ = some consumedLeaf := by
  simp [consumedOwner, Tree.find?, consumedLeaf]

private theorem halfFind : halfOwner.root.find? ⟨3⟩ = some halfLeaf := by
  simp [halfOwner, Tree.find?, halfLeaf]

/-- A read-only leaf cannot authorise a write. -/
example : ¬ roOwner.Writable 64 ⟨1⟩ 0 := by
  intro h
  exact Owner.readOnly_not_writable h (by
    intro c hc
    rw [roFind] at hc
    cases hc
    rfl)

/-- A consumed leaf cannot authorise a write. -/
example : ¬ consumedOwner.Writable 64 ⟨2⟩ 0 := by
  intro h
  exact Owner.consumed_not_writable h (by
    intro c hc
    rw [consumedFind] at hc
    cases hc
    rfl)

/-- A half share cannot authorise a write at the whole share. -/
example : ¬ halfOwner.Writable 64 ⟨3⟩ 0 := by
  intro h
  obtain ⟨c, hc, hstate, hq, hceil, hlo, hhi⟩ := h
  rw [halfFind] at hc
  cases hc
  exact absurd hq (by decide)

/-- One identifier is not a join pair. -/
example : halfOwner.canJoin ⟨3⟩ ⟨3⟩ = false := Owner.canJoin_self_false _ _
