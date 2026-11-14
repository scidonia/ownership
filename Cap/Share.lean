/-
Exact shares, with a common denominator per context.

A context fixes a denominator `D`. A share is a positive numerator `q` with
`q ≤ D`, so the fraction is `q / D` exactly; there is no rounding and no zero
capability. The two transitions are the fractional split, whose children add up
to the parent, and the write, which needs the whole unit `D`.

The common denominator is a representation choice: it makes the arithmetic
decidable and the proofs linear, and a context can always be rescaled. The
per-share rational model in the design is the same algebra with denominators
normalized per share.
-/

import Cap.Id

namespace Cap

/-- A share is well formed in a context of denominator `D`. -/
def ShareWf (D q : Nat) : Prop := 0 < q ∧ q ≤ D

/-- A fractional split: the children's shares add up to the parent's. -/
def Splits (q q1 q2 : Nat) : Prop := q1 + q2 = q

/-- A write needs the whole unit. A read needs only `0 < q`. -/
def Writable (D q : Nat) : Prop := q = D

theorem splits_positive {q q1 q2 : Nat} (h : Splits q q1 q2) (h1 : 0 < q1) : 0 < q := by
  unfold Splits at h
  omega

/-- A child never exceeds its parent. The parent's bound `q ≤ D` is a side
condition of the split rule, not a consequence of the children being shares: two
children each at most `D` can sum to `2D`. -/
theorem split_le_parent_left {q q1 q2 : Nat} (h : Splits q q1 q2) : q1 ≤ q := by
  unfold Splits at h
  omega

theorem split_le_parent_right {q q1 q2 : Nat} (h : Splits q q1 q2) : q2 ≤ q := by
  unfold Splits at h
  omega

/-- A unit context cannot split into two writable halves. -/
theorem no_two_writes {D q q1 q2 : Nat} (h : Splits q q1 q2) (h1 : 0 < q1)
    (hw1 : Writable D q1) (hw2 : Writable D q2) (hq : q ≤ D) : False := by
  unfold Splits Writable at *
  omega

/-- A join stays within the unit. -/
theorem join_le {D q1 q2 q : Nat} (h : q1 + q2 = q) (hq : q ≤ D) : q1 + q2 ≤ D := by
  omega

/-- Splitting off the whole parent leaves an empty remainder. -/
theorem split_whole {q q1 q2 : Nat} (h : Splits q q1 q2) (h1 : q1 = q) : q2 = 0 := by
  unfold Splits at h
  omega

example : Splits 4 1 3 := rfl
example : ¬ Splits 4 3 2 := by unfold Splits; decide
example : Writable 8 8 := rfl
example : ¬ Writable 8 7 := by unfold Writable; decide
example : ShareWf 8 3 := by unfold ShareWf; decide

end Cap
