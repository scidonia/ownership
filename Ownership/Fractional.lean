/-
The fractional reading of the accounting relation.

A cell's stored count is the number of holders of its unit permission: the owning
variables that denote it plus the heap fields that reference it. Each holder holds
`1 / rc`, and the shares sum to one. Uniqueness is the case where the whole
permission is held by a single holder; shared ownership is the graded case where
`n` holders each hold `1/n`, which is why a write needs count one rather than
merely a single name.

This is the correspondence to fractional-uniqueness type systems: their fractions
are our multiplicities, and their uniqueness type is our count-one case.
-/
import Ownership.CompleteAccounting

open Ownership

namespace Ownership

/-- The share a holder of a cell of count `n` holds. -/
def Share (n : Nat) : Rat := 1 / (n : Rat)

/-- The accounting equation read as a fractional sum: the owning variables and the
incoming edges together hold the whole permission. -/
theorem fractional_accounting {support : List Var} {H : Heap} {env : Env} {c : Ctx}
    (h : Accounted support H env c) (r : Ref) (hpos : 0 < H.rc r) :
    ((EnvOwnerCount c support r : Rat) + (IncomingCount H r : Rat)) * Share (H.rc r) = 1 := by
  have hcount := h.count r
  have hcast : ((H.rc r : Nat) : Rat) =
      (EnvOwnerCount c support r : Rat) + (IncomingCount H r : Rat) := by
    rw [hcount]
    push_cast
    rw [Rat.add_comm]
  unfold Share
  rw [← hcast]
  have hne : ((H.rc r : Nat) : Rat) ≠ 0 := by
    exact_mod_cast (Nat.pos_iff_ne_zero.mp hpos)
  rw [Rat.div_def, Rat.one_mul]
  exact Rat.mul_inv_cancel _ hne

/-- Uniqueness is the whole permission in a single holder: at multiplicity one the
holders are one owning variable with no edge, or one edge with no owning variable,
and the share is exactly one. -/
theorem unique_whole_permission {support : List Var} {H : Heap} {env : Env} {c : Ctx}
    (h : Accounted support H env c) {r : Ref} (hm : c.mult r = 1) :
    ((EnvOwnerCount c support r = 1 ∧ IncomingCount H r = 0) ∨
        (EnvOwnerCount c support r = 0 ∧ IncomingCount H r = 1)) ∧
      ((EnvOwnerCount c support r : Rat) + (IncomingCount H r : Rat)) * Share 1 = 1 := by
  refine ⟨Accounted.count_one_dichotomy h hm, ?_⟩
  have hrc : H.rc r = 1 := by rw [h.count r, ← Accounted.mult_eq h r, hm]
  have hf := fractional_accounting h r (by rw [hrc]; decide)
  simpa [hrc] using hf

/-- Shared ownership is the graded case: `n` holders of a count-`n` cell each hold
`1/n`, and the shares still sum to one. -/
theorem shared_share {n : Nat} (hn : 0 < n) : (n : Rat) * Share n = 1 := by
  unfold Share
  have hne : (n : Rat) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hn)
  rw [Rat.div_def, Rat.one_mul]
  exact Rat.mul_inv_cancel _ hne

end Ownership
