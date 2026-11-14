/-
The budget algebra of the ledger.

A capability is a leaf of a decomposition tree: a footprint, a share, a ceiling
and a state. Internal nodes record fractional and spatial splits; their budget is
the sum of their children's, so a split preserves the byte budget and a join
restores it. This is stage 2a: the tree and its arithmetic. The context (forest,
disposal entitlement, lifetimes, loans) and the executable transitions are the
next slice, and the `Realizes` invariant is stated over this budget.

Theorems:
* `frac_split_budget` / `frac_join_budget` — a fractional split and its sibling
  join preserve the budget at every byte.
* `spatial_split_budget` / `spatial_join_budget` — a spatial split at `k` and its
  join preserve the budget; the children partition the parent's range.
-/
import Cap.Id

namespace Cap

inductive Ceiling where
  | readOnly
  | readWrite
deriving DecidableEq, Repr

inductive CapState where
  | active
  | retired
  | consumed
deriving DecidableEq, Repr

structure Leaf where
  id : CapId
  alloc : AllocId
  lo : Nat
  hi : Nat
  ordered : lo ≤ hi
  q : Nat
  pos : 0 < q
  ceiling : Ceiling
  state : CapState

def Leaf.budget (c : Leaf) (x : Nat) : Nat :=
  if c.state = .consumed then 0
  else if c.lo ≤ x ∧ x < c.hi then c.q else 0

inductive Tree where
  | leaf (c : Leaf)
  | frac (id : CapId) (l r : Tree)
  | spatial (id : CapId) (l r : Tree)

namespace Tree

def budget (x : Nat) : Tree → Nat
  | leaf c => c.budget x
  | frac _ l r => l.budget x + r.budget x
  | spatial _ l r => l.budget x + r.budget x

end Tree

/-- A fractional split replaces one leaf's budget by its two children's. -/
theorem frac_split_budget {c c1 c2 : Leaf} {x : Nat}
    (hstate1 : c1.state = c.state) (hstate2 : c2.state = c.state)
    (hlo1 : c1.lo = c.lo) (hhi1 : c1.hi = c.hi)
    (hlo2 : c2.lo = c.lo) (hhi2 : c2.hi = c.hi)
    (hq : c1.q + c2.q = c.q) :
    (Tree.frac c1.id (.leaf c1) (.leaf c2)).budget x = (Tree.leaf c).budget x := by
  by_cases hc : c.state = .consumed
  · simp [Tree.budget, Leaf.budget, hstate1, hstate2, hc]
  · by_cases hx : c.lo ≤ x ∧ x < c.hi
    · have hx1 : c1.lo ≤ x ∧ x < c1.hi := by rw [hlo1, hhi1]; exact hx
      have hx2 : c2.lo ≤ x ∧ x < c2.hi := by rw [hlo2, hhi2]; exact hx
      simp [Tree.budget, Leaf.budget, hstate1, hstate2, hc, hx, hx1, hx2]
      omega
    · have hx1 : ¬ (c1.lo ≤ x ∧ x < c1.hi) := by rw [hlo1, hhi1]; exact hx
      have hx2 : ¬ (c2.lo ≤ x ∧ x < c2.hi) := by rw [hlo2, hhi2]; exact hx
      simp [Tree.budget, Leaf.budget, hstate1, hstate2, hc, hx, hx1, hx2]

/-- A spatial split at `k`: the children partition the parent's range. -/
theorem spatial_split_budget {c c1 c2 : Leaf} {x k : Nat}
    (hstate1 : c1.state = c.state) (hstate2 : c2.state = c.state)
    (hlo1 : c1.lo = c.lo) (hhi1 : c1.hi = k)
    (hlo2 : c2.lo = k) (hhi2 : c2.hi = c.hi)
    (hq1 : c1.q = c.q) (hq2 : c2.q = c.q)
    (hk1 : c.lo ≤ k) (hk2 : k ≤ c.hi) :
    (Tree.spatial c1.id (.leaf c1) (.leaf c2)).budget x = (Tree.leaf c).budget x := by
  by_cases hc : c.state = .consumed
  · simp [Tree.budget, Leaf.budget, hstate1, hstate2, hc]
  · by_cases hx : c.lo ≤ x ∧ x < c.hi
    · by_cases hxk : x < k
      · have hx1 : c1.lo ≤ x ∧ x < c1.hi := by rw [hlo1, hhi1]; exact ⟨hx.1, hxk⟩
        have hx2 : ¬ (c2.lo ≤ x ∧ x < c2.hi) := by rw [hlo2, hhi2]; exact fun h => by omega
        simp [Tree.budget, Leaf.budget, hstate1, hstate2, hc, hx, hx1, hx2, hq1]
      · have hx1 : ¬ (c1.lo ≤ x ∧ x < c1.hi) := by rw [hlo1, hhi1]; exact fun h => by omega
        have hx2 : c2.lo ≤ x ∧ x < c2.hi := by rw [hlo2, hhi2]; exact ⟨by omega, hx.2⟩
        simp [Tree.budget, Leaf.budget, hstate1, hstate2, hc, hx, hx1, hx2, hq2]
    · have hx1 : ¬ (c1.lo ≤ x ∧ x < c1.hi) := by rw [hlo1, hhi1]; exact fun h => hx ⟨h.1, by omega⟩
      have hx2 : ¬ (c2.lo ≤ x ∧ x < c2.hi) := by rw [hlo2, hhi2]; exact fun h => hx ⟨by omega, h.2⟩
      simp [Tree.budget, Leaf.budget, hstate1, hstate2, hc, hx, hx1, hx2]

/-- Joining the two children restores the parent's budget (sibling join). -/
theorem frac_join_budget {c c1 c2 : Leaf} {x : Nat}
    (hstate1 : c1.state = c.state) (hstate2 : c2.state = c.state)
    (hlo1 : c1.lo = c.lo) (hhi1 : c1.hi = c.hi)
    (hlo2 : c2.lo = c.lo) (hhi2 : c2.hi = c.hi)
    (hq : c.q = c1.q + c2.q) :
    (Tree.leaf c).budget x = (Tree.frac c1.id (.leaf c1) (.leaf c2)).budget x := by
  rw [frac_split_budget hstate1 hstate2 hlo1 hhi1 hlo2 hhi2 (by omega)]

theorem spatial_join_budget {c c1 c2 : Leaf} {x k : Nat}
    (hstate1 : c1.state = c.state) (hstate2 : c2.state = c.state)
    (hlo1 : c1.lo = c.lo) (hhi1 : c1.hi = k)
    (hlo2 : c2.lo = k) (hhi2 : c2.hi = c.hi)
    (hq1 : c1.q = c.q) (hq2 : c2.q = c.q)
    (hk1 : c.lo ≤ k) (hk2 : k ≤ c.hi) :
    (Tree.leaf c).budget x = (Tree.spatial c1.id (.leaf c1) (.leaf c2)).budget x := by
  rw [spatial_split_budget hstate1 hstate2 hlo1 hhi1 hlo2 hhi2 hq1 hq2 hk1 hk2]

-- Concrete checks: a whole-capability read budget and a spatial split.
namespace LedgerExamples

private def root : Leaf :=
  { id := ⟨0⟩, alloc := ⟨0⟩, lo := 0, hi := 8, ordered := by decide,
    q := 8, pos := by decide, ceiling := .readWrite, state := .active }

private def left : Leaf :=
  { id := ⟨1⟩, alloc := ⟨0⟩, lo := 0, hi := 4, ordered := by decide,
    q := 8, pos := by decide, ceiling := .readWrite, state := .active }

private def right : Leaf :=
  { id := ⟨2⟩, alloc := ⟨0⟩, lo := 4, hi := 8, ordered := by decide,
    q := 8, pos := by decide, ceiling := .readWrite, state := .active }

example : root.budget 3 = 8 := by decide
example : root.budget 8 = 0 := by decide
example : (Tree.spatial ⟨9⟩ (.leaf left) (.leaf right)).budget 5 = 8 := by decide

end LedgerExamples

end Cap
