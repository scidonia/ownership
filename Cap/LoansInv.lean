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

/-- An identifier that occurs in no leaf is found by no lookup. -/
theorem Tree.find?_eq_none_of_not_mem_ids {t : Tree} {id : CapId} (h : id ∉ t.ids) :
    t.find? id = none := by
  cases hf : t.find? id with
  | none => rfl
  | some c => exact absurd (Tree.mem_ids_of_exists_find? ⟨c, hf⟩) h

/-- A spatial split preserves the loan invariant: the split leaf is active while
every lender's leaf is retired, the replacement's identifiers are historically
fresh, and other owners are untouched. -/
theorem World.loansOK_splitAtChecked {w w' : World} {a : AllocId}
    {id id1 id2 : CapId} {k : Nat}
    (hw : w.splitAtChecked a id id1 id2 k = .ok w')
    (hwf : w.WellFormed) (h : w.LoansOK) : w'.LoansOK := by
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
        unfold Ctx.splitAtOwner? at hs
        cases ho : o.splitAt? id id1 id2 k with
        | none => simp [ho] at hs
        | some o' =>
          simp only [ho, Option.map_some, Option.some.injEq] at hs
          subst C'
          unfold World.LoansOK World.LenderRetired at h ⊢
          obtain ⟨hid, hlend, hlife, hiss, hret⟩ := h
          refine ⟨hid, hlend, hlife, ?_, ?_⟩
          · intro l hl
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hiss l hl))
          · intro l hl
            obtain ⟨own, hown, cl, hcl, hst⟩ := hret l hl
            have hne1 : l.lender ≠ id1 := fun heq => hfr.2.2.2.1 (heq ▸ hiss l hl)
            have hne2 : l.lender ≠ id2 := fun heq => hfr.2.2.2.2.1 (heq ▸ hiss l hl)
            unfold Owner.splitAt? at ho
            cases hfid : o.root.find? id with
            | none => simp [hfid] at ho
            | some csplit =>
              cases hsp : csplit.splitSpatial? id1 id2 k with
              | none => simp [hfid, hsp] at ho
              | some t =>
                simp only [hfid, hsp, Option.map_some, Option.some.injEq] at ho
                subst ho
                obtain ⟨_, _, ht⟩ := Leaf.splitSpatial?_some hsp
                have htids : t.ids = [id1, id2] := by
                  rw [ht]
                  rfl
                have htnone : t.find? l.lender = none := by
                  apply Tree.find?_eq_none_of_not_mem_ids
                  rw [htids]
                  simp [hne1, hne2]
                by_cases hownO : own = o
                · rw [hownO] at hcl hown
                  have hneid : l.lender ≠ id := by
                    intro heq
                    obtain ⟨ca, hca, hca_state⟩ := hfr.2.2.2.2.2
                    rw [heq] at hcl
                    have hca_eq : ca = cl := Option.some.inj (hca.symm.trans hcl)
                    rw [hca_eq] at hca_state
                    rw [hst] at hca_state
                    exact absurd hca_state (by decide)
                  have hrep : ∀ c', o.root.find? id = some c' → t.find? l.lender = none :=
                    fun _ _ => htnone
                  have hfind' : (Tree.replace id (fun _ => t) o.root).find? l.lender
                      = some cl := by
                    rw [Tree.find?_replace_ne o.root id l.lender (fun _ => t) hneid hrep]
                    exact hcl
                  exact ⟨{ o with root := Tree.replace id (fun _ => t) o.root },
                    List.mem_map.mpr ⟨o, hown, by simp⟩, cl, hfind', hst⟩
                · have hoalloc : own.alloc ≠ o.alloc := by
                    intro heq
                    have hmemO : o ∈ w.ctx.owners := List.mem_of_find?_eq_some hfind
                    have hfindO : w.ctx.findOwner? own.alloc = some own :=
                      Ctx.findOwner?_eq_some_of_mem_of_functional hwf.2.1 hown
                    have := hwf.2.1 own.alloc own o hfindO hmemO heq.symm
                    exact hownO this.symm
                  exact ⟨own, List.mem_map.mpr ⟨own, hown, by simp [hoalloc]⟩,
                    cl, hcl, hst⟩
      · simp at hw
    · simp at hw

/-- A fractional split preserves the loan invariant, by the same argument as the
spatial split: the split leaf is active, lenders are retired, the replacement's
identifiers are fresh, and other owners are untouched. -/
theorem World.loansOK_splitFractionChecked {w w' : World} {a : AllocId}
    {id id1 id2 : CapId} {q1 q2 : Nat} {p1 : 0 < q1} {p2 : 0 < q2}
    (hw : w.splitFractionChecked a id id1 id2 q1 q2 p1 p2 = .ok w')
    (hwf : w.WellFormed) (h : w.LoansOK) : w'.LoansOK := by
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
        unfold Ctx.splitFractionOwner? at hs
        cases ho : o.splitFraction? id id1 id2 q1 q2 p1 p2 with
        | none => simp [ho] at hs
        | some o' =>
          simp only [ho, Option.map_some, Option.some.injEq] at hs
          subst C'
          unfold World.LoansOK World.LenderRetired at h ⊢
          obtain ⟨hid, hlend, hlife, hiss, hret⟩ := h
          refine ⟨hid, hlend, hlife, ?_, ?_⟩
          · intro l hl
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hiss l hl))
          · intro l hl
            obtain ⟨own, hown, cl, hcl, hst⟩ := hret l hl
            have hne1 : l.lender ≠ id1 := fun heq => hfr.2.2.2.1 (heq ▸ hiss l hl)
            have hne2 : l.lender ≠ id2 := fun heq => hfr.2.2.2.2.1 (heq ▸ hiss l hl)
            unfold Owner.splitFraction? at ho
            cases hfid : o.root.find? id with
            | none => simp [hfid] at ho
            | some csplit =>
              cases hsp : csplit.splitFractionTree id1 id2 q1 q2 p1 p2 with
              | none => simp [hfid, hsp] at ho
              | some t =>
                simp only [hfid, hsp, Option.map_some, Option.some.injEq] at ho
                subst ho
                have htids : t.ids = [id1, id2] := by
                  unfold Leaf.splitFractionTree at hsp
                  split at hsp
                  · simp only [Option.some.injEq] at hsp
                    subst hsp
                    rfl
                  · simp at hsp
                have htnone : t.find? l.lender = none := by
                  apply Tree.find?_eq_none_of_not_mem_ids
                  rw [htids]
                  simp [hne1, hne2]
                by_cases hownO : own = o
                · rw [hownO] at hcl hown
                  have hneid : l.lender ≠ id := by
                    intro heq
                    obtain ⟨ca, hca, hca_state⟩ := hfr.2.2.2.2.2
                    rw [heq] at hcl
                    have hca_eq : ca = cl := Option.some.inj (hca.symm.trans hcl)
                    rw [hca_eq] at hca_state
                    rw [hst] at hca_state
                    exact absurd hca_state (by decide)
                  have hrep : ∀ c', o.root.find? id = some c' →
                      t.find? l.lender = none := fun _ _ => htnone
                  have hfind' : (Tree.replace id (fun _ => t) o.root).find? l.lender
                      = some cl := by
                    rw [Tree.find?_replace_ne o.root id l.lender (fun _ => t) hneid hrep]
                    exact hcl
                  exact ⟨{ o with root := Tree.replace id (fun _ => t) o.root },
                    List.mem_map.mpr ⟨o, hown, by simp⟩, cl, hfind', hst⟩
                · have hoalloc : own.alloc ≠ o.alloc := by
                    intro heq
                    have hmemO : o ∈ w.ctx.owners := List.mem_of_find?_eq_some hfind
                    have hfindO : w.ctx.findOwner? own.alloc = some own :=
                      Ctx.findOwner?_eq_some_of_mem_of_functional hwf.2.1 hown
                    have := hwf.2.1 own.alloc own o hfindO hmemO heq.symm
                    exact hownO this.symm
                  exact ⟨own, List.mem_map.mpr ⟨own, hown, by simp [hoalloc]⟩,
                    cl, hcl, hst⟩
      · simp at hw
    · simp at hw
/-- Replacing a fractional node by a subtree that does not contain `id'` leaves
the lookup of `id'` unchanged, provided `id'` is not an identifier of the
replaced fragment. -/
theorem Tree.find?_replaceNode_outside (t : Tree) (node id' : CapId) (t' : Tree)
    (hnew : t'.find? id' = none)
    (hout : ∀ frag, t.findFrac? node = some frag → id' ∉ frag.ids) :
    (Tree.replaceNode node t' t).find? id' = t.find? id' := by
  induction t with
  | leaf c => rfl
  | frac i l r ihl ihr =>
    simp only [Tree.replaceNode]
    by_cases hin : i = node
    · rw [if_pos hin]
      rw [hnew]
      have hfrag : Tree.findFrac? node (.frac i l r) = some (.frac i l r) := by
        simp [Tree.findFrac?, hin]
      exact (Tree.find?_eq_none_of_not_mem_ids (hout _ hfrag)).symm
    · rw [if_neg hin]
      cases hl : l.findFrac? node with
      | some frag =>
        dsimp only
        have hrepL : ∀ frag', l.findFrac? node = some frag' → id' ∉ frag'.ids := by
          intro frag' hf
          exact hout frag' (by simp [Tree.findFrac?, hin, hf])
        simp only [Tree.find?]
        rw [ihl hrepL]
      | none =>
        dsimp only
        have hrepR : ∀ frag', r.findFrac? node = some frag' → id' ∉ frag'.ids := by
          intro frag' hf
          exact hout frag' (by simp [Tree.findFrac?, hin, hl, hf])
        cases hl' : l.find? id' with
        | some c => simp only [Tree.find?, hl']
        | none =>
          simp only [Tree.find?]
          rw [ihr hrepR]
  | spatial i l r ihl ihr =>
    simp only [Tree.replaceNode]
    cases hl : l.findFrac? node with
    | some frag =>
      dsimp only
      have hrepL : ∀ frag', l.findFrac? node = some frag' → id' ∉ frag'.ids := by
        intro frag' hf
        exact hout frag' (by simp [Tree.findFrac?, hf])
      simp only [Tree.find?]
      rw [ihl hrepL]
    | none =>
      dsimp only
      have hrepR : ∀ frag', r.findFrac? node = some frag' → id' ∉ frag'.ids := by
        intro frag' hf
        exact hout frag' (by simp [Tree.findFrac?, hl, hf])
      cases hl' : l.find? id' with
      | some c => simp only [Tree.find?, hl']
      | none =>
        simp only [Tree.find?]
        rw [ihr hrepR]

end Cap
