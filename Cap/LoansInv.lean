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
  ∧ (∀ l ∈ w.ctx.loans.loans, l.lender ∈ w.ctx.issued)
  ∧ w.LenderRetired

/-- The empty world has no loans, so the invariant holds. -/
theorem World.emptyWorld_loansOK : World.LoansOK World.emptyWorld := by
  refine ⟨by decide, by decide, ?_, ?_, ?_⟩
  · intro l hl
    simp [World.emptyWorld, LoanCtx.rootOnly] at hl
  · intro l hl
    simp [World.emptyWorld, LoanCtx.rootOnly] at hl
  · intro l hl
    simp [World.emptyWorld, LoanCtx.rootOnly] at hl

/-- The concrete 64-byte world has no loans. -/
theorem uWorld_loansOK : World.LoansOK uWorld := by
  refine ⟨by decide, by decide, ?_, ?_, ?_⟩
  · intro l hl
    simp [uWorld, LoanCtx.rootOnly] at hl
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

/-- Allocation preserves the loan invariant: the loan list is unchanged and the
existing owners (hence every lender's retired leaf) survive the insertion. -/
theorem World.loansOK_allocChecked {w w' : World} {n : Nat} {rootId disposal : CapId}
    {po : 0 < w.ctx.D}
    (hw : w.allocChecked n rootId disposal po = .ok w') (h : w.LoansOK) :
    w'.LoansOK := by
  unfold World.allocChecked at hw
  split at hw
  · rename_i hf
    split at hw
    · rename_i hfresh
      simp only [Except.ok.injEq] at hw
      cases hw
      unfold World.LoansOK World.LenderRetired at h ⊢
      refine ⟨h.1, h.2.1, h.2.2.1, ?_, ?_⟩
      · intro l hl
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (h.2.2.2.1 l hl))
      · intro l hl
        obtain ⟨o, ho, c, hc, hstate⟩ := h.2.2.2.2 l hl
        exact ⟨o, List.mem_cons_of_mem _ ho, c, hc, hstate⟩
    · simp at hw
  · simp at hw

/-- Disposal preserves the loan invariant: it is refused while a lender is live in
the owner being freed, so every lender's retired leaf survives in another owner. -/
theorem World.loansOK_freeChecked {w w' : World} {a : AllocId} {d : CapId}
    (hw : w.freeChecked a d = .ok w') (hwf : w.WellFormed) (h : w.LoansOK) :
    w'.LoansOK := by
  unfold World.freeChecked at hw
  split at hw
  · simp at hw
  · rename_i o0 hfind
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
          unfold World.LoansOK World.LenderRetired at h ⊢
          refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
          intro l hl
          obtain ⟨o, ho, c, hc', hstate⟩ := h.2.2.2.2 l hl
          have hlender : l.lender ∈ o.ids := by
            have hroot : l.lender ∈ o.root.ids :=
              Tree.mem_ids_of_exists_find? ⟨c, hc'⟩
            exact List.mem_cons_of_mem _ hroot
          have hoalloc : o.alloc ≠ a := by
            intro hcontra
            have hoo : o = o0 := hwf.2.1 a o0 o hfind ho hcontra
            rw [hoo] at hlender
            exact hloan l hl hlender
          exact ⟨o, List.mem_filter.mpr ⟨ho, by simpa using hoalloc⟩, c, hc', hstate⟩
    · simp at hw

end Cap
