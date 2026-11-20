/-
The combined invariant carried by sealed executions.

The world invariant `World.WellFormed`, the issuance history `Ctx.HistoryOK` and
the loan-state invariant `World.LoansOK` are each preserved by the checker. This
module bundles them and proves the bundle preserved by whole runs, so a sealed
world can carry one proof instead of three, and clients do not assemble the
components themselves.

`FullInv` is the invariant of this stage: world well-formedness, history and
loans. The delegation invariant is not yet part of it (reborrowing is not yet an
executable operation).
-/
import Cap.TopInvariant
import Cap.LoansInv

namespace Cap

/-- The combined invariant: the world bundle, the issuance history and the
loan-state invariant. -/
def World.FullInv (w : World) : Prop := w.TopInv ∧ w.LoansOK

theorem World.fullInv_wf {w : World} (h : w.FullInv) : w.WellFormed := h.1.1

theorem World.fullInv_history {w : World} (h : w.FullInv) : Ctx.HistoryOK w.ctx := h.1.2

theorem World.fullInv_loans {w : World} (h : w.FullInv) : w.LoansOK := h.2

/-- The canonical empty world satisfies the combined invariant. -/
theorem World.emptyWorld_fullInv : World.FullInv World.emptyWorld :=
  ⟨World.emptyWorld_top, World.emptyWorld_loansOK⟩

/-- An accepted execution preserves the combined invariant. -/
theorem World.checkWorld_fullInv : ∀ (w w' : World) (cs : List UCmd),
    checkWorld w cs = .ok w' → w.FullInv → w'.FullInv := by
  intro w w' cs
  induction cs generalizing w with
  | nil =>
    intro h hinv
    simp [checkWorld] at h
    cases h
    exact hinv
  | cons c cs ih =>
    intro h hinv
    obtain ⟨hwf, hh⟩ := hinv.1
    have hloans := hinv.2
    cases c with
    | nop =>
      simp [checkWorld] at h
      exact ih w h ⟨⟨hwf, hh⟩, hloans⟩
    | write a id i v =>
      cases hw : w.writeChecked a id i v with
      | error e => simp [checkWorld, hw] at h
      | ok w'' =>
        simp [checkWorld, hw] at h
        exact ih w'' h ⟨⟨World.writeChecked_wf hw hwf,
          World.historyOK_write hw hh⟩, World.loansOK_write hw hloans⟩
    | splitAt a id id1 id2 k =>
      cases hw : w.splitAtChecked a id id1 id2 k with
      | error e => simp [checkWorld, hw] at h
      | ok w'' =>
        simp [checkWorld, hw] at h
        exact ih w'' h ⟨⟨World.splitAtChecked_wf hw hwf,
          World.historyOK_splitAtChecked hw hwf hh⟩,
          World.loansOK_splitAtChecked hw hwf hloans⟩
    | splitFraction a id id1 id2 q1 q2 =>
      by_cases hq : 0 < q1 ∧ 0 < q2
      · cases hw : w.splitFractionChecked a id id1 id2 q1 q2 hq.1 hq.2 with
        | error e => simp [checkWorld, hq, hw] at h
        | ok w'' =>
          simp [checkWorld, hq, hw] at h
          exact ih w'' h ⟨⟨World.splitFractionChecked_wf hw hwf,
            World.historyOK_splitFractionChecked hw hwf hh⟩,
            World.loansOK_splitFractionChecked hw hwf hloans⟩
      · simp [checkWorld, hq] at h
    | join a node newId =>
      cases hw : w.joinChecked a node newId with
      | error e => simp [checkWorld, hw] at h
      | ok w'' =>
        simp [checkWorld, hw] at h
        exact ih w'' h ⟨⟨World.joinChecked_wf hw hwf,
          World.historyOK_joinChecked hw hh⟩,
          World.loansOK_joinChecked hw hwf hloans⟩
    | free a d =>
      cases hw : w.freeChecked a d with
      | error e => simp [checkWorld, hw] at h
      | ok w'' =>
        simp [checkWorld, hw] at h
        exact ih w'' h ⟨⟨World.freeChecked_wf hw hwf,
          World.historyOK_freeChecked hw hh⟩,
          World.loansOK_freeChecked hw hwf hloans⟩
    | alloc n rootId disposal =>
      by_cases hpos : 0 < w.ctx.D
      · cases hw : w.allocChecked n rootId disposal hpos with
        | error e => simp [checkWorld, hpos, hw] at h
        | ok w'' =>
          simp [checkWorld, hpos, hw] at h
          exact ih w'' h ⟨⟨World.allocChecked_wf hw hwf,
            World.historyOK_allocChecked hw hh⟩,
            World.loansOK_allocChecked hw hloans⟩
      · simp [checkWorld, hpos] at h
    | beginLoan a lender loanId =>
      cases hw : w.beginLoanChecked a lender loanId with
      | error e => simp [checkWorld, hw] at h
      | ok w'' =>
        simp [checkWorld, hw] at h
        exact ih w'' h ⟨⟨World.beginLoanChecked_wf hw hwf,
          World.historyOK_beginLoanChecked hw hh⟩,
          World.loansOK_beginLoanChecked hw hwf hloans hh⟩
    | endLoan a loanId =>
      cases hw : w.endLoanChecked a loanId with
      | error e => simp [checkWorld, hw] at h
      | ok w'' =>
        simp [checkWorld, hw] at h
        exact ih w'' h ⟨⟨World.endLoanChecked_wf hw hwf,
          World.historyOK_endLoanChecked hw hh⟩,
          World.loansOK_endLoanChecked hw hwf hloans⟩

end Cap
