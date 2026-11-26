/-
The combined invariant carried by sealed executions.

The world invariant `World.TopInv` and the delegation invariant `World.BorrowOK`
are each preserved by the checker. This module bundles them and proves the
bundle preserved by whole runs, so a sealed world can carry one proof instead of
two, and clients do not assemble the components themselves.

`FullInv` is the invariant of this stage: world well-formedness, issuance
history, loan readiness and the integrated distinct-borrower delegation
invariant.
-/
import Cap.TopInvariant
import Cap.Borrow

namespace Cap

/-- The combined invariant: the top-level bundle and the delegation invariant. -/
def World.FullInv (w : World) : Prop := w.TopInv ∧ w.BorrowOK

theorem World.fullInv_wf {w : World} (h : w.FullInv) : w.WellFormed := h.1.1

theorem World.fullInv_history {w : World} (h : w.FullInv) : Ctx.HistoryOK w.ctx := h.1.2

theorem World.fullInv_borrow {w : World} (h : w.FullInv) : w.BorrowOK := h.2

/-- `FullInv` gives the command carrier used by the preservation table. -/
theorem World.fullInv_commandInv {w : World} (h : w.FullInv) : w.CommandInv :=
  ⟨h.1.1, h.1.2, World.borrowOK_loansReady h.2⟩

/-- The canonical empty world satisfies the combined invariant. -/
theorem World.emptyWorld_fullInv : World.FullInv World.emptyWorld :=
  ⟨World.emptyWorld_top, by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [World.LoansDistinctOK, World.LoansNonAliasOK, World.LoansIssuedOK,
        World.LifetimesBoundedOK, World.LoansAllocOK, World.LoansDetachedOK,
        World.LoansBaseOK, World.LoansTerminalOK, World.LoansAgreeOK,
        World.LoansOrderOK, World.BorrowAcyclic, World.emptyWorld, LoanCtx.rootOnly]⟩

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
    have htop := hinv.1
    have hborrow := hinv.2
    have hcarrier := World.fullInv_commandInv hinv
    cases c with
    | nop =>
      simp [checkWorld] at h
      exact ih w h hinv
    | write a id i v =>
      cases hw : w.writeChecked a id i v with
      | error e => simp [checkWorld, hw] at h
      | ok w'' =>
        simp [checkWorld, hw] at h
        exact ih w'' h ⟨⟨World.writeChecked_wf hw hcarrier.1,
          World.historyOK_write hw hcarrier.2.1⟩, World.borrowOK_write hw hborrow⟩
    | splitAt a id id1 id2 k =>
      cases hw : w.splitAtChecked a id id1 id2 k with
      | error e => simp [checkWorld, hw] at h
      | ok w'' =>
        simp [checkWorld, hw] at h
        exact ih w'' h ⟨⟨World.splitAtChecked_wf hw hcarrier.1,
          World.historyOK_splitAtChecked hw hcarrier.1 hcarrier.2.1⟩,
          World.borrowOK_splitAtChecked hw hcarrier.1 hborrow⟩
    | splitFraction a id id1 id2 q1 q2 =>
      by_cases hq : 0 < q1 ∧ 0 < q2
      · cases hw : w.splitFractionChecked a id id1 id2 q1 q2 hq.1 hq.2 with
        | error e => simp [checkWorld, hq, hw] at h
        | ok w'' =>
          simp [checkWorld, hq, hw] at h
          exact ih w'' h ⟨⟨World.splitFractionChecked_wf hw hcarrier.1,
            World.historyOK_splitFractionChecked hw hcarrier.1 hcarrier.2.1⟩,
            World.borrowOK_splitFractionChecked hw hcarrier.1 hborrow⟩
      · simp [checkWorld, hq] at h
    | join a node newId =>
      cases hw : w.joinChecked a node newId with
      | error e => simp [checkWorld, hw] at h
      | ok w'' =>
        simp [checkWorld, hw] at h
        exact ih w'' h ⟨⟨World.joinChecked_wf hw hcarrier.1,
          World.historyOK_joinChecked hw hcarrier.2.1⟩,
          World.borrowOK_joinChecked hw hcarrier.1 hborrow⟩
    | free a d =>
      cases hw : w.freeChecked a d with
      | error e => simp [checkWorld, hw] at h
      | ok w'' =>
        simp [checkWorld, hw] at h
        exact ih w'' h ⟨⟨World.freeChecked_wf hw hcarrier.1,
          World.historyOK_freeChecked hw hcarrier.2.1⟩,
          World.borrowOK_freeChecked hw hborrow⟩
    | alloc n rootId disposal =>
      by_cases hpos : 0 < w.ctx.D
      · cases hw : w.allocChecked n rootId disposal hpos with
        | error e => simp [checkWorld, hpos, hw] at h
        | ok w'' =>
          simp [checkWorld, hpos, hw] at h
          exact ih w'' h ⟨⟨World.allocChecked_wf hw hcarrier.1,
            World.historyOK_allocChecked hw hcarrier.2.1⟩,
            World.borrowOK_allocChecked hw hborrow⟩
      · simp [checkWorld, hpos] at h
    | beginBorrow a lender borrower loanId =>
      cases hw : w.beginBorrowChecked a lender borrower loanId with
      | error e => simp [checkWorld, hw] at h
      | ok w'' =>
        simp [checkWorld, hw] at h
        exact ih w'' h ⟨⟨World.beginBorrowChecked_wf hw hcarrier,
          World.historyOK_beginBorrow hw hcarrier.2.1⟩,
          World.borrowOK_beginBorrow hw hcarrier hborrow⟩
    | endBorrow a loanId =>
      cases hw : w.endBorrowChecked a loanId with
      | error e => simp [checkWorld, hw] at h
      | ok w'' =>
        simp [checkWorld, hw] at h
        exact ih w'' h ⟨⟨World.endBorrowChecked_wf hw hcarrier,
          World.historyOK_endBorrow hw hcarrier.2.1 hcarrier.2.2⟩,
          World.borrowOK_endBorrow hw hcarrier hborrow⟩

/-- The borrow command preserves the combined invariant. -/
theorem World.fullInv_beginBorrowChecked {w w' : World} {a : AllocId}
    {lender borrower : CapId} {loanId : LoanId}
    (hw : w.beginBorrowChecked a lender borrower loanId = .ok w')
    (h : w.FullInv) : w'.FullInv := by
  have hstep : checkWorld w [UCmd.beginBorrow a lender borrower loanId] = .ok w' := by
    change (match w.beginBorrowChecked a lender borrower loanId with
      | Except.ok w => Except.ok w
      | Except.error e => Except.error e) = Except.ok w'
    rw [hw]
  exact World.checkWorld_fullInv w w' _ hstep h

/-- The return command preserves the combined invariant. -/
theorem World.fullInv_endBorrowChecked {w w' : World} {a : AllocId}
    {loanId : LoanId} (hw : w.endBorrowChecked a loanId = .ok w')
    (h : w.FullInv) : w'.FullInv := by
  have hstep : checkWorld w [UCmd.endBorrow a loanId] = .ok w' := by
    change (match w.endBorrowChecked a loanId with
      | Except.ok w => Except.ok w
      | Except.error e => Except.error e) = Except.ok w'
    rw [hw]
  exact World.checkWorld_fullInv w w' _ hstep h

/-- An accepted borrow step preserves the combined invariant. -/
theorem World.checkWorld_beginBorrow {w w' : World} {a : AllocId}
    {lender borrower : CapId} {loanId : LoanId}
    (h : checkWorld w [UCmd.beginBorrow a lender borrower loanId] = .ok w')
    (hinv : w.FullInv) : w'.FullInv :=
  World.checkWorld_fullInv w w' _ h hinv

/-- An accepted return step preserves the combined invariant. -/
theorem World.checkWorld_endBorrow {w w' : World} {a : AllocId} {loanId : LoanId}
    (h : checkWorld w [UCmd.endBorrow a loanId] = .ok w')
    (hinv : w.FullInv) : w'.FullInv :=
  World.checkWorld_fullInv w w' _ h hinv

end Cap
