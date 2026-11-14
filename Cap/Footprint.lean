/-
Bounded intervals and views.

An interval is half-open, `[lo, hi)`, with its ordering proof. A view names an
allocation and an interval; the interval must lie within the allocation's length,
which is a separate hypothesis `Within`. Splitting at a point yields the two
children with their disjointness and coverage proved here.
-/

import Cap.Id

namespace Cap

structure Interval where
  lo : Nat
  hi : Nat
  ordered : lo ≤ hi
deriving Repr

/-- Half-open intervals `[lo, hi)`. -/
def Interval.Disjoint (a b : Interval) : Prop :=
  a.hi ≤ b.lo ∨ b.hi ≤ a.lo

def Interval.Adjacent (a b : Interval) : Prop :=
  a.hi = b.lo

/-- Split at `k`, which must lie in the interval. -/
def Interval.splitAt (i : Interval) (k : Nat) (h1 : i.lo ≤ k) (h2 : k ≤ i.hi) :
    Interval × Interval :=
  (⟨i.lo, k, h1⟩, ⟨k, i.hi, h2⟩)

theorem splitAt_disjoint (i : Interval) (k : Nat) (h1 : i.lo ≤ k) (h2 : k ≤ i.hi) :
    (Interval.splitAt i k h1 h2).1.Disjoint (Interval.splitAt i k h1 h2).2 := by
  left
  show k ≤ k
  exact Nat.le_refl k

theorem splitAt_adjacent (i : Interval) (k : Nat) (h1 : i.lo ≤ k) (h2 : k ≤ i.hi) :
    (Interval.splitAt i k h1 h2).1.Adjacent (Interval.splitAt i k h1 h2).2 := rfl

theorem splitAt_cover (i : Interval) (k : Nat) (h1 : i.lo ≤ k) (h2 : k ≤ i.hi) :
    (Interval.splitAt i k h1 h2).1.lo = i.lo ∧
      (Interval.splitAt i k h1 h2).2.hi = i.hi := ⟨rfl, rfl⟩

/-- A view names an allocation and a footprint in it. -/
structure View where
  alloc : AllocId
  range : Interval
deriving Repr

/-- The footprint lies within an allocation of length `len`. -/
def Within (len : Nat) (v : View) : Prop := v.range.hi ≤ len

theorem splitAt_within {len : Nat} {v : View} (hv : Within len v) (k : Nat)
    (h1 : v.range.lo ≤ k) (h2 : k ≤ v.range.hi) :
    Within len ⟨v.alloc, (Interval.splitAt v.range k h1 h2).1⟩ ∧
      Within len ⟨v.alloc, (Interval.splitAt v.range k h1 h2).2⟩ := by
  unfold Within Interval.splitAt at *
  simp_all
  omega

example : Interval.Disjoint ⟨0, 32, by decide⟩ ⟨32, 64, by decide⟩ :=
  Or.inl (by decide)
example : ¬ Interval.Disjoint ⟨0, 32, by decide⟩ ⟨31, 64, by decide⟩ := by
  unfold Interval.Disjoint
  decide

end Cap
