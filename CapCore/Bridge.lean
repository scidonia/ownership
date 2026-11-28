import CapCore.Context
import Cap.Reconstruction

namespace CapCore

open _root_.Cap

/-- The abstract checker context agrees with the reconstruction state's current
active frontier: same denominator and length, and a bijection between current
capabilities and active leaves preserving id, range and share. -/
def Matches (c : Ctx) (s : Reconstruction.State) : Prop :=
  c.D = s.D ∧ c.len = s.len ∧
  (∀ cap ∈ c.caps, ∃ leaf ∈ s.forest.leaves,
      leaf.id.val = cap.id ∧
      leaf.lo = cap.region.lo ∧ leaf.hi = cap.region.hi ∧
      leaf.q = cap.q ∧ leaf.state = .active) ∧
  (∀ leaf ∈ s.forest.leaves, ∃ cap ∈ c.caps,
      leaf.id.val = cap.id ∧
      leaf.lo = cap.region.lo ∧ leaf.hi = cap.region.hi ∧
      leaf.q = cap.q ∧ leaf.state = .active)

/-- Allocation establishes the bridge. -/
theorem new_matches_initial (a : AllocId) (n D root : Nat) (hD : 0 < D)
    (rootId disposalId : CapId) (hroot : rootId.val = root) :
    Matches (Ctx.new D n root hD)
      (Reconstruction.State.initial a n D hD rootId disposalId) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro cap hcap
    simp [Ctx.new] at hcap
    subst hcap
    refine ⟨{ id := rootId, alloc := a, lo := 0, hi := n,
              ordered := Nat.zero_le n, q := D, pos := hD,
              ceiling := .readWrite, state := .active }, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Reconstruction.State.initial, Reconstruction.Forest.leaves]
    · exact hroot
    · rfl
    · rfl
    · rfl
    · rfl
  · intro leaf hleaf
    simp [Reconstruction.State.initial, Reconstruction.Forest.leaves] at hleaf
    subst hleaf
    refine ⟨{ id := root, region := ⟨0, 0, n⟩, q := D, pos := hD }, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Ctx.new]
    · exact hroot
    · rfl
    · rfl
    · rfl
    · rfl

/-- Allocation establishes the bridge to a state that satisfies the full
reconstruction invariant. -/
theorem new_matches_initial_inv (a : AllocId) (n D root : Nat) (hD : 0 < D)
    (rootId disposalId : CapId) (hroot : rootId.val = root) :
    Matches (Ctx.new D n root hD)
      (Reconstruction.State.initial a n D hD rootId disposalId) ∧
    (Reconstruction.State.initial a n D hD rootId disposalId).Inv :=
  ⟨new_matches_initial a n D root hD rootId disposalId hroot,
   Reconstruction.State.initial_inv a n D hD rootId disposalId⟩

end CapCore

