/-
The loan-state invariant.

`World.LoansOK` states what an outstanding loan means for the world: loan
identifiers are distinct, lenders are distinct, every loan's lifetime is live,
and every loan's lender still occurs as a `retired` leaf of a live owner. The
guards proved before this module are what make it maintainable: a lender's leaf
cannot be split (both splitters require an active leaf), cannot be merged away
(the join refuses non-active children), and the owner cannot be freed while the
lender remains live (`freeChecked_refused_of_loan`).

This module states the invariant and proves it for the initial worlds and for
writes. Preservation for the remaining commands is the next step.
-/
import Cap.Unified
import Cap.TopInvariant
import Cap.History

namespace Cap

/-- Every loan's lender still occurs as a retired leaf of a live owner. -/
def World.LenderRetired (w : World) : Prop :=
  ∀ l ∈ w.ctx.loans.loans, ∃ o, o ∈ w.ctx.owners ∧
    ∃ c, o.root.find? l.lender = some c ∧ c.state = .retired

/-- The loan-state invariant. -/
def World.LoansOK (w : World) : Prop :=
  (w.ctx.loans.loans.map (·.id)).Nodup
  ∧ (w.ctx.loans.loans.map (·.lender)).Nodup
  ∧ (∀ l ∈ w.ctx.loans.loans, w.ctx.loans.live l.lifetime = true)
  ∧ w.LenderRetired

/-- The empty world has no loans, so the invariant holds. -/
theorem World.emptyWorld_loansOK : World.LoansOK World.emptyWorld := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · intro l hl
    simp [World.emptyWorld, LoanCtx.rootOnly] at hl
  · intro l hl
    simp [World.emptyWorld, LoanCtx.rootOnly] at hl

/-- The concrete 64-byte world has no loans. -/
theorem uWorld_loansOK : World.LoansOK uWorld := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · intro l hl
    simp [uWorld, LoanCtx.rootOnly] at hl
  · intro l hl
    simp [uWorld, LoanCtx.rootOnly] at hl

/-- A write leaves the context, hence the loan state, unchanged. -/
theorem World.loansOK_write {w w' : World} {a : AllocId} {id : CapId} {i : Nat}
    {v : UInt8} (hw : w.writeChecked a id i v = .ok w') (h : w.LoansOK) :
    w'.LoansOK := by
  obtain ⟨_, _, _, _, _, _, _, hctx, _⟩ := World.writeChecked_sound hw
  unfold World.LoansOK World.LenderRetired at h
  unfold World.LoansOK World.LenderRetired
  rw [hctx]
  exact h

end Cap
