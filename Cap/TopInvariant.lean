/-
The combined top-level invariant: world well-formedness together with the
issuance history.

Every checked world command preserves it, and so does a whole execution
(`checkWorld_top`). The concrete initial worlds satisfy it.
-/
import Cap.History
import Cap.Unified
import Cap.Runner

namespace Cap

/-- The top-level invariant: the world is well formed and its context's
issuance history is sound. -/
def World.TopInv (w : World) : Prop :=
  w.WellFormed ∧ Ctx.HistoryOK w.ctx

theorem World.topInv_wf {w : World} (h : w.TopInv) : w.WellFormed := h.1

theorem World.topInv_history {w : World} (h : w.TopInv) : Ctx.HistoryOK w.ctx := h.2

/-- A write leaves the context unchanged. -/
theorem World.historyOK_write {w w' : World} {a : AllocId} {id : CapId} {i : Nat}
    {v : UInt8} (hw : w.writeChecked a id i v = .ok w') (hh : Ctx.HistoryOK w.ctx) :
    Ctx.HistoryOK w'.ctx := by
  obtain ⟨_, _, _, _, _, _, _, hctx, _⟩ := World.writeChecked_sound hw
  rw [hctx]
  exact hh

/-- A checked spatial split preserves the history. -/
theorem World.historyOK_splitAtChecked {w w' : World} {a : AllocId}
    {id id1 id2 : CapId} {k : Nat}
    (hw : w.splitAtChecked a id id1 id2 k = .ok w')
    (hwf : w.WellFormed) (hh : Ctx.HistoryOK w.ctx) : Ctx.HistoryOK w'.ctx := by
  unfold World.splitAtChecked at hw
  split at hw
  · simp at hw
  · rename_i o hfind
    split at hw
    · rename_i hfr
      split at hw
      · rename_i C' hs
        simp only [Except.ok.injEq] at hw
        cases hw
        have hmem : o ∈ w.ctx.owners := List.mem_of_find?_eq_some hfind
        have hoids : o.ids.Nodup := Ctx.owner_ids_nodup hwf.1.2.2 hmem
        unfold Ctx.splitAtOwner? at hs
        cases ho : o.splitAt? id id1 id2 k with
        | none => simp [ho] at hs
        | some o' =>
          simp only [ho, Option.map_some, Option.some.injEq] at hs
          rw [← hs]
          exact Ctx.historyOK_split hh hoids hmem ho hfr.2.2.2.1 hfr.2.2.2.2.1 hfr.1.2.2
      · simp at hw
    · simp at hw

/-- A checked fractional split preserves the history. -/
theorem World.historyOK_splitFractionChecked {w w' : World} {a : AllocId}
    {id id1 id2 : CapId} {q1 q2 : Nat} {p1 : 0 < q1} {p2 : 0 < q2}
    (hw : w.splitFractionChecked a id id1 id2 q1 q2 p1 p2 = .ok w')
    (hwf : w.WellFormed) (hh : Ctx.HistoryOK w.ctx) : Ctx.HistoryOK w'.ctx := by
  unfold World.splitFractionChecked at hw
  split at hw
  · simp at hw
  · rename_i o hfind
    split at hw
    · rename_i hfr
      split at hw
      · rename_i C' hs
        simp only [Except.ok.injEq] at hw
        cases hw
        have hmem : o ∈ w.ctx.owners := List.mem_of_find?_eq_some hfind
        have hoids : o.ids.Nodup := Ctx.owner_ids_nodup hwf.1.2.2 hmem
        unfold Ctx.splitFractionOwner? at hs
        cases ho : o.splitFraction? id id1 id2 q1 q2 p1 p2 with
        | none => simp [ho] at hs
        | some o' =>
          simp only [ho, Option.map_some, Option.some.injEq] at hs
          rw [← hs]
          exact Ctx.historyOK_splitFraction hh hoids hmem ho hfr.2.2.2.1 hfr.2.2.2.2.1 hfr.1.2.2
      · simp at hw
    · simp at hw

/-- A checked fractional join preserves the history. -/
theorem World.historyOK_joinChecked {w w' : World} {a : AllocId}
    {node newId : CapId}
    (hw : w.joinChecked a node newId = .ok w') (hh : Ctx.HistoryOK w.ctx) :
    Ctx.HistoryOK w'.ctx := by
  unfold World.joinChecked at hw
  split at hw
  · simp at hw
  · rename_i o hfind
    split at hw
    · rename_i hfresh
      split at hw
      · rename_i C' hs
        simp only [Except.ok.injEq] at hw
        cases hw
        have hmem : o ∈ w.ctx.owners := List.mem_of_find?_eq_some hfind
        unfold Ctx.joinFractionOwner? at hs
        cases ho : o.joinFraction? node newId with
        | none => simp [ho] at hs
        | some o' =>
          simp only [ho, Option.map_some, Option.some.injEq] at hs
          rw [← hs]
          exact Ctx.historyOK_join hh hmem ho hfresh.2
      · simp at hw
    · simp at hw

/-- Disposal preserves the history. -/
theorem World.historyOK_freeChecked {w w' : World} {a : AllocId} {d : CapId}
    (hw : w.freeChecked a d = .ok w') (hh : Ctx.HistoryOK w.ctx) :
    Ctx.HistoryOK w'.ctx := by
  unfold World.freeChecked at hw
  split at hw
  · simp at hw
  · rename_i o hfind
    split at hw
    · rename_i hloan
      cases hf : w.freeWith? a d with
      | none => simp [hf] at hw
      | some w1 =>
        simp [hf] at hw
        cases hw
        unfold World.freeWith? at hf
        cases hc : w.ctx.freeWith? a d with
        | none => simp [hc] at hf
        | some ctx' =>
          simp [hc] at hf
          cases hf
          have heq : ctx' = w.ctx.free a := Ctx.freeWith?_eq_free hc
          rw [heq]
          exact Ctx.historyOK_free hh
    · simp at hw

/-- Allocation preserves the history. -/
theorem World.historyOK_allocChecked {w w' : World} {n : Nat}
    {rootId disposal : CapId} {po : 0 < w.ctx.D}
    (hw : w.allocChecked n rootId disposal po = .ok w')
    (hh : Ctx.HistoryOK w.ctx) : Ctx.HistoryOK w'.ctx := by
  unfold World.allocChecked at hw
  split at hw
  · rename_i hf
    split at hw
    · rename_i hfresh
      simp only [Except.ok.injEq] at hw
      cases hw
      exact Ctx.historyOK_alloc (hf := hf) hh hfresh.2.2.2.1 hfresh.2.2.2.2 hfresh.2.2.1
    · simp at hw
  · simp at hw

/-- Suspension preserves the history: the replacement keeps the identifier set. -/
theorem World.historyOK_suspendChecked {w w' : World} {a : AllocId} {id : CapId}
    (hw : w.suspendChecked a id = .ok w') (hh : Ctx.HistoryOK w.ctx) :
    Ctx.HistoryOK w'.ctx := by
  unfold World.suspendChecked at hw
  split at hw
  · simp at hw
  · rename_i o hfind
    split at hw
    · rename_i C' hs
      simp only [Except.ok.injEq] at hw
      cases hw
      have hmem : o ∈ w.ctx.owners := List.mem_of_find?_eq_some hfind
      have hids : C'.ids = o.ids := Owner.suspendLeaf?_ids hs
      exact Ctx.historyOK_update_owner hh hmem hids
    · simp at hw

/-- Restoration preserves the history. -/
theorem World.historyOK_resumeChecked {w w' : World} {a : AllocId} {id : CapId}
    (hw : w.resumeChecked a id = .ok w') (hh : Ctx.HistoryOK w.ctx) :
    Ctx.HistoryOK w'.ctx := by
  unfold World.resumeChecked at hw
  split at hw
  · simp at hw
  · rename_i o hfind
    split at hw
    · rename_i C' hs
      simp only [Except.ok.injEq] at hw
      cases hw
      have hmem : o ∈ w.ctx.owners := List.mem_of_find?_eq_some hfind
      have hids : C'.ids = o.ids := Owner.resumeLeaf?_ids hs
      exact Ctx.historyOK_update_owner hh hmem hids
    · simp at hw

/-- Beginning a loan preserves the history: the context change is the lender's
suspension, whose identifier set is unchanged. -/
theorem World.historyOK_beginLoanChecked {w w' : World} {a : AllocId}
    {lender : CapId} {loanId : LoanId}
    (hw : w.beginLoanChecked a lender loanId = .ok w') (hh : Ctx.HistoryOK w.ctx) :
    Ctx.HistoryOK w'.ctx := by
  unfold World.beginLoanChecked at hw
  split at hw
  · simp at hw
  · rename_i o hfind
    split at hw
    · simp at hw
    · rename_i c hc
      split at hw
      · rename_i hact
        split at hw
        · rename_i hfresh
          split at hw
          · rename_i hlive
            split at hw
            · simp at hw
            · rename_i o' hs
              simp only [Except.ok.injEq] at hw
              cases hw
              have hmem : o ∈ w.ctx.owners := List.mem_of_find?_eq_some hfind
              have hids : o'.ids = o.ids := Owner.suspendLeaf?_ids hs
              exact Ctx.historyOK_update_owner hh hmem hids
          · simp at hw
        · simp at hw
      · simp at hw

/-- Ending a loan preserves the history: the context change is the lender's
restoration, whose identifier set is unchanged. -/
theorem World.historyOK_endLoanChecked {w w' : World} {a : AllocId}
    {loanId : LoanId}
    (hw : w.endLoanChecked a loanId = .ok w') (hh : Ctx.HistoryOK w.ctx) :
    Ctx.HistoryOK w'.ctx := by
  unfold World.endLoanChecked at hw
  split at hw
  · simp at hw
  · rename_i loan hl
    split at hw
    · simp at hw
    · rename_i o hfind
      split at hw
      · simp at hw
      · rename_i o' hs
        simp only [Except.ok.injEq] at hw
        cases hw
        have hmem : o ∈ w.ctx.owners := List.mem_of_find?_eq_some hfind
        have hids : o'.ids = o.ids := Owner.resumeLeaf?_ids hs
        exact Ctx.historyOK_update_owner hh hmem hids

/-- Every checked execution preserves the top-level invariant. -/
theorem checkWorld_top : ∀ (w w' : World) (cs : List UCmd),
    checkWorld w cs = .ok w' → w.TopInv → w'.TopInv := by
  intro w w' cs
  induction cs generalizing w with
  | nil =>
    intro h hinv
    simp [checkWorld] at h
    cases h
    exact hinv
  | cons c cs ih =>
    intro h hinv
    obtain ⟨hwf, hh⟩ := hinv
    cases c with
    | nop =>
      simp [checkWorld] at h
      exact ih w h ⟨hwf, hh⟩
    | write a id i v =>
      cases hw : w.writeChecked a id i v with
      | error e => simp [checkWorld, hw] at h
      | ok w'' =>
        simp [checkWorld, hw] at h
        exact ih w'' h ⟨World.writeChecked_wf hw hwf, World.historyOK_write hw hh⟩
    | splitAt a id id1 id2 k =>
      cases hw : w.splitAtChecked a id id1 id2 k with
      | error e => simp [checkWorld, hw] at h
      | ok w'' =>
        simp [checkWorld, hw] at h
        exact ih w'' h ⟨World.splitAtChecked_wf hw hwf, World.historyOK_splitAtChecked hw hwf hh⟩
    | splitFraction a id id1 id2 q1 q2 =>
      by_cases hq : 0 < q1 ∧ 0 < q2
      · cases hw : w.splitFractionChecked a id id1 id2 q1 q2 hq.1 hq.2 with
        | error e => simp [checkWorld, hq, hw] at h
        | ok w'' =>
          simp [checkWorld, hq, hw] at h
          exact ih w'' h ⟨World.splitFractionChecked_wf hw hwf,
            World.historyOK_splitFractionChecked hw hwf hh⟩
      · simp [checkWorld, hq] at h
    | join a node newId =>
      cases hw : w.joinChecked a node newId with
      | error e => simp [checkWorld, hw] at h
      | ok w'' =>
        simp [checkWorld, hw] at h
        exact ih w'' h ⟨World.joinChecked_wf hw hwf, World.historyOK_joinChecked hw hh⟩
    | free a d =>
      cases hw : w.freeChecked a d with
      | error e => simp [checkWorld, hw] at h
      | ok w'' =>
        simp [checkWorld, hw] at h
        exact ih w'' h ⟨World.freeChecked_wf hw hwf, World.historyOK_freeChecked hw hh⟩
    | alloc n rootId disposal =>
      by_cases hpos : 0 < w.ctx.D
      · cases hw : w.allocChecked n rootId disposal hpos with
        | error e => simp [checkWorld, hpos, hw] at h
        | ok w'' =>
          simp [checkWorld, hpos, hw] at h
          exact ih w'' h ⟨World.allocChecked_wf hw hwf, World.historyOK_allocChecked hw hh⟩
      · simp [checkWorld, hpos] at h
    | beginLoan a lender loanId =>
      cases hw : w.beginLoanChecked a lender loanId with
      | error e => simp [checkWorld, hw] at h
      | ok w'' =>
        simp [checkWorld, hw] at h
        exact ih w'' h ⟨World.beginLoanChecked_wf hw hwf, World.historyOK_beginLoanChecked hw hh⟩
    | endLoan a loanId =>
      cases hw : w.endLoanChecked a loanId with
      | error e => simp [checkWorld, hw] at h
      | ok w'' =>
        simp [checkWorld, hw] at h
        exact ih w'' h ⟨World.endLoanChecked_wf hw hwf, World.historyOK_endLoanChecked hw hh⟩

/-- The empty world's history is sound: no identifiers have been issued. -/
theorem World.emptyWorld_historyOK : Ctx.HistoryOK World.emptyWorld.ctx := by
  refine ⟨by decide, ?_⟩
  intro c hc
  simp [World.emptyWorld, Ctx.ids] at hc

/-- The empty world satisfies the top-level invariant. -/
theorem World.emptyWorld_top : World.TopInv World.emptyWorld :=
  ⟨World.emptyWorld_wf, World.emptyWorld_historyOK⟩

/-- The concrete 64-byte world's history is exactly its live identifier set. -/
theorem uWorld_historyOK : Ctx.HistoryOK uWorld.ctx := by
  refine ⟨by decide, ?_⟩
  intro c hc
  simp [uWorld, uOwner, Ctx.ids, Owner.ids, Owner.init, Tree.ids] at hc ⊢
  rcases hc with rfl | rfl
  · simp
  · simp

/-- The concrete 64-byte world satisfies the top-level invariant. -/
theorem uWorld_top : uWorld.TopInv :=
  ⟨uWorld_wf, uWorld_historyOK⟩

end Cap
