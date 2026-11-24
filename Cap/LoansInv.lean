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
import Cap.Join
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
    · rename_i halloc
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
    · rename_i halloc
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
    · rename_i halloc
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

/-- A fractional join preserves the loan invariant: the joined children are
active while every lender's leaf is retired, so no lender lies in the replaced
fragment; the joined leaf's identifier is fresh, so its lookup is empty; and
other owners are untouched. -/
theorem World.loansOK_joinChecked {w w' : World} {a : AllocId}
    {node newId : CapId}
    (hw : w.joinChecked a node newId = .ok w')
    (hwf : w.WellFormed) (h : w.LoansOK) : w'.LoansOK := by
  unfold World.joinChecked at hw
  cases hf : w.ctx.findOwner? a with
  | none => simp [hf] at hw
  | some o =>
    simp only [hf] at hw
    by_cases hfresh : newId ∉ w.ctx.ids ∧ newId ∉ w.ctx.issued
    · rw [if_pos hfresh] at hw
      cases hs : w.ctx.joinFractionOwner? o node newId with
      | none => simp [hs] at hw
      | some C' =>
        simp only [hs, Except.ok.injEq] at hw
        subst hw
        unfold World.LoansOK World.LenderRetired at h
        obtain ⟨hid, hlend, hlife, hiss, hret⟩ := h
        unfold Ctx.joinFractionOwner? at hs
        cases hj : o.joinFraction? node newId with
        | none => simp [hj] at hs
        | some o' =>
          simp only [hj, Option.map_some, Option.some.injEq] at hs
          subst C'
          unfold Owner.joinFraction? at hj
          cases hfrag : o.root.findFrac? node with
          | none => simp [hfrag] at hj
          | some frag =>
            cases hjc : frag.joinChildren? newId with
            | none => simp [hfrag, hjc] at hj
            | some t' =>
              simp only [hfrag, hjc, Option.map_some, Option.some.injEq] at hj
              subst hj
              obtain ⟨i, c1, c2, hnode, hcids, ht'ids, -⟩ :=
                Tree.joinChildren?_some hjc
              obtain ⟨-, -, -, -, hc1act, hc2act⟩ := Tree.joinChildren?_active hjc
              have hmemO : o ∈ w.ctx.owners := List.mem_of_find?_eq_some hf
              have hrootnd : o.root.ids.Nodup :=
                List.nodup_cons.mp (Ctx.owner_ids_nodup hwf.1.2.2 hmemO) |>.2
              unfold World.LoansOK World.LenderRetired at ⊢
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · simpa [Ctx.update] using hid
              · simpa [Ctx.update] using hlend
              · intro l' hl'
                simpa [Ctx.update] using hlife l' (by simpa [Ctx.update] using hl')
              · intro l' hl'
                exact List.mem_cons_of_mem _
                  (hiss l' (by simpa [Ctx.update] using hl'))
              · intro l' hl'
                obtain ⟨own, hown, cl, hcl, hst⟩ :=
                  hret l' (by simpa [Ctx.update] using hl')
                have hneNew : l'.lender ≠ newId :=
                  fun heq => hfresh.2 (heq ▸ hiss l' (by simpa [Ctx.update] using hl'))
                have hclid : cl.id = l'.lender := Tree.find?_id_eq hcl
                have hout : ∀ frag', o.root.findFrac? node = some frag' →
                    l'.lender ∉ frag'.ids := by
                  intro frag' hfrag'
                  have hfeq : frag' = frag := by
                    rw [hfrag] at hfrag'
                    exact (Option.some.inj hfrag').symm
                  have hc1leaf : c1 ∈ o.root.leaves :=
                    Tree.findFrac?_leaves_sub hfrag (by
                      rw [hnode]
                      simp [Tree.leaves])
                  have hc2leaf : c2 ∈ o.root.leaves :=
                    Tree.findFrac?_leaves_sub hfrag (by
                      rw [hnode]
                      simp [Tree.leaves])
                  intro hmem
                  obtain ⟨-, -, -, -, hc1active, hc2active⟩ := Tree.joinChildren?_active hjc
                  have hfragids : frag'.ids = [c1.id, c2.id] := by
                    rw [hfeq, hnode]
                    rfl
                  rw [hfragids] at hmem
                  rcases List.mem_cons.mp hmem with hc1 | hc2
                  · have hc1id : c1.id = l'.lender := by rw [← hc1]
                    exfalso
                    by_cases hownO : own = o
                    · rw [hownO] at hcl hown
                      have hclleaf : cl ∈ o.root.leaves := Tree.find?_mem_leaves hcl
                      have hmap : (o.root.leaves.map Leaf.id).Nodup := by
                        rw [← Tree.ids_eq_map_leaves]
                        exact hrootnd
                      have hcl_c1 : cl = c1 :=
                        List.nodup_map_leaf_id_inj hmap cl hclleaf c1 hc1leaf
                          (by rw [hclid, hc1id])
                      obtain ⟨i', c1', c2', hnode', ha, hb⟩ :=
                        Tree.joinChildren?_active hjc
                      have heq : Tree.frac i (.leaf c1) (.leaf c2)
                          = Tree.frac i' (.leaf c1') (.leaf c2') :=
                        hnode.symm.trans hnode'
                      have hc1' : c1 = c1' := by
                        injection heq with _ hl _
                        injection hl with h
                      rw [← hc1'] at ha
                      rw [hcl_c1] at hst
                      rw [hst] at ha
                      exact absurd ha (by decide)
                    · have hoalloc : own.alloc ≠ o.alloc := by
                        intro heq
                        have hfindOwn : w.ctx.findOwner? own.alloc = some own :=
                          Ctx.findOwner?_eq_some_of_mem_of_functional hwf.2.1 hown
                        have := hwf.2.1 own.alloc own o hfindOwn hmemO heq.symm
                        exact hownO this.symm
                      have hne : own ≠ o := fun heq => hoalloc (heq ▸ rfl)
                      have hownmem : l'.lender ∈ own.ids :=
                        List.mem_cons_of_mem _ (Tree.find?_mem_ids hcl)
                      have homem : l'.lender ∈ o.ids := by
                        have hrootmem : l'.lender ∈ o.root.ids := by
                          rw [← hc1id]
                          exact Tree.findFrac?_ids_sub hfrag (by
                            rw [hnode]
                            simp [Tree.ids])
                        exact List.mem_cons_of_mem _ hrootmem
                      exact Ctx.ids_disjoint_of_ne hwf.1.2.2 hown hmemO hne
                        l'.lender hownmem homem
                  · have hc2eq : l'.lender = c2.id := List.mem_singleton.mp hc2
                    have hc2id : c2.id = l'.lender := hc2eq.symm
                    exfalso
                    by_cases hownO : own = o
                    · rw [hownO] at hcl hown
                      have hclleaf : cl ∈ o.root.leaves := Tree.find?_mem_leaves hcl
                      have hmap : (o.root.leaves.map Leaf.id).Nodup := by
                        rw [← Tree.ids_eq_map_leaves]
                        exact hrootnd
                      have hcl_c2 : cl = c2 :=
                        List.nodup_map_leaf_id_inj hmap cl hclleaf c2 hc2leaf
                          (by rw [hclid, hc2id])
                      obtain ⟨i', c1', c2', hnode', ha, hb⟩ :=
                        Tree.joinChildren?_active hjc
                      have heq : Tree.frac i (.leaf c1) (.leaf c2)
                          = Tree.frac i' (.leaf c1') (.leaf c2') :=
                        hnode.symm.trans hnode'
                      have hc2' : c2 = c2' := by
                        injection heq with _ _ hr
                        injection hr with h
                      rw [← hc2'] at hb
                      rw [hcl_c2] at hst
                      rw [hst] at hb
                      exact absurd hb (by decide)
                    · have hoalloc : own.alloc ≠ o.alloc := by
                        intro heq
                        have hfindOwn : w.ctx.findOwner? own.alloc = some own :=
                          Ctx.findOwner?_eq_some_of_mem_of_functional hwf.2.1 hown
                        have := hwf.2.1 own.alloc own o hfindOwn hmemO heq.symm
                        exact hownO this.symm
                      have hne : own ≠ o := fun heq => hoalloc (heq ▸ rfl)
                      have hownmem : l'.lender ∈ own.ids :=
                        List.mem_cons_of_mem _ (Tree.find?_mem_ids hcl)
                      have homem : l'.lender ∈ o.ids := by
                        have hrootmem : l'.lender ∈ o.root.ids := by
                          rw [← hc2id]
                          exact Tree.findFrac?_ids_sub hfrag (by
                            rw [hnode]
                            simp [Tree.ids])
                        exact List.mem_cons_of_mem _ hrootmem
                      exact Ctx.ids_disjoint_of_ne hwf.1.2.2 hown hmemO hne
                        l'.lender hownmem homem
                have hnew : t'.find? l'.lender = none := by
                  apply Tree.find?_eq_none_of_not_mem_ids
                  rw [ht'ids]
                  simp [hneNew]
                by_cases hownO : own = o
                · rw [hownO] at hcl hown
                  have hfind' : (Tree.replaceNode node t' o.root).find? l'.lender
                      = some cl := by
                    rw [Tree.find?_replaceNode_outside o.root node l'.lender t' hnew hout]
                    exact hcl
                  exact ⟨{ o with root := Tree.replaceNode node t' o.root },
                    List.mem_map.mpr ⟨o, hown, by simp⟩, cl, hfind', hst⟩
                · have hoalloc : own.alloc ≠ o.alloc := by
                    intro heq
                    have hfindOwn : w.ctx.findOwner? own.alloc = some own :=
                      Ctx.findOwner?_eq_some_of_mem_of_functional hwf.2.1 hown
                    have := hwf.2.1 own.alloc own o hfindOwn hmemO heq.symm
                    exact hownO this.symm
                  exact ⟨own, List.mem_map.mpr ⟨own, hown, by simp [hoalloc]⟩,
                    cl, hcl, hst⟩
    · rw [if_neg hfresh] at hw
      simp at hw

/-- Beginning a loan preserves the invariant: the lender's leaf is retired by the
suspension, the guard requires it active so no earlier loan shares the lender, and
the new loan is recorded against the live root lifetime with an issued lender. -/
theorem World.loansOK_beginLoanChecked {w w' : World} {a : AllocId}
    {lender : CapId} {loanId : LoanId}
    (hw : w.beginLoanChecked a lender loanId = .ok w')
    (hwf : w.WellFormed) (h : w.LoansOK) (hh : Ctx.HistoryOK w.ctx) :
    w'.LoansOK := by
  unfold World.beginLoanChecked at hw
  cases hf : w.ctx.findOwner? a with
  | none => simp [hf] at hw
  | some o =>
    simp only [hf] at hw
    cases hfind : o.root.find? lender with
    | none => simp [hfind] at hw
    | some c =>
      simp only [hfind] at hw
      by_cases hc : c.state = .active
      · rw [if_pos hc] at hw
        by_cases hfresh : loanId ∉ w.ctx.loans.loans.map (·.id)
        · rw [if_pos hfresh] at hw
          by_cases hlive : w.ctx.loans.live ⟨0⟩
          · rw [if_pos hlive] at hw
            cases hs : o.suspendLeaf? lender with
            | none => simp [hs] at hw
            | some o' =>
              simp only [hs, Except.ok.injEq] at hw
              subst hw
              obtain ⟨hid, hlend, hlife, hiss, hret⟩ := h
              obtain ⟨c0, hfold, hc0act, hnewlookup⟩ := Owner.suspendLeaf?_find? hs
              have hc0c : c0 = c := by
                rw [hfold] at hfind
                exact Option.some.inj hfind
              rw [hc0c] at hnewlookup
              have hmemO : o ∈ w.ctx.owners := List.mem_of_find?_eq_some hf
              -- no earlier loan shares the lender
              let fs : Leaf → Tree := fun c' => .leaf { c' with state := .retired }
              have ho'eq : o' = { o with root := Tree.replace lender fs o.root } := by
                obtain ⟨d, _, _, hod⟩ := Owner.suspendLeaf?_eq hs
                simpa [fs] using hod
              have hold_lender_ne : ∀ l ∈ w.ctx.loans.loans, l.lender ≠ lender := by
                intro l hl heq
                obtain ⟨own, hown, cl, hcl, hst⟩ := hret l hl
                rw [heq] at hcl
                by_cases hownO : own = o
                · rw [hownO] at hcl hown
                  have hclc : cl = c := by
                    rw [hcl] at hfind
                    exact Option.some.inj hfind
                  rw [hclc] at hst
                  rw [hst] at hc
                  exact absurd hc (by decide)
                · have hoalloc : own.alloc ≠ o.alloc := by
                    intro heq'
                    have hfindOwn : w.ctx.findOwner? own.alloc = some own :=
                      Ctx.findOwner?_eq_some_of_mem_of_functional hwf.2.1 hown
                    have := hwf.2.1 own.alloc own o hfindOwn hmemO heq'.symm
                    exact hownO this.symm
                  have hne : own ≠ o := fun heq' => hoalloc (heq' ▸ rfl)
                  have hownmem : lender ∈ own.ids :=
                    List.mem_cons_of_mem _ (Tree.find?_mem_ids hcl)
                  have homem : lender ∈ o.ids :=
                    List.mem_cons_of_mem _ (Tree.find?_mem_ids hfind)
                  exact Ctx.ids_disjoint_of_ne hwf.1.2.2 hown hmemO hne
                    lender hownmem homem
              -- the new loan
              unfold World.LoansOK World.LenderRetired at ⊢
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · have : (w.ctx.loans.loans.map (·.id) ++ [loanId]).Nodup := by
                  rw [List.nodup_append]
                  refine ⟨hid, by simp, ?_⟩
                  intro a ha b hb
                  simp only [List.mem_singleton] at hb
                  subst hb
                  exact fun heq => hfresh (heq ▸ ha)
                simpa [List.map_append] using this
              · have : (w.ctx.loans.loans.map (·.lender) ++ [lender]).Nodup := by
                  rw [List.nodup_append]
                  refine ⟨hlend, by simp, ?_⟩
                  intro a ha b hb
                  simp only [List.mem_singleton] at hb
                  subst hb
                  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
                  exact hold_lender_ne l hl
                simpa [List.map_append] using this
              · intro l hl
                rcases List.mem_append.mp hl with hl' | hl'
                · change w.ctx.loans.live l.lifetime = true
                  exact hlife l hl'
                · simp only [List.mem_singleton] at hl'
                  subst hl'
                  change w.ctx.loans.live ⟨0⟩ = true
                  exact hlive
              · intro l hl
                rcases List.mem_append.mp hl with hl' | hl'
                · change l.lender ∈ w.ctx.issued
                  exact hiss l hl'
                · simp only [List.mem_singleton] at hl'
                  subst hl'
                  exact Ctx.ids_sub_issued hh lender
                    (Ctx.owner_ids_sub_ids hmemO lender
                      (List.mem_cons_of_mem _ (Tree.find?_mem_ids hfind)))
              · intro l hl
                rcases List.mem_append.mp hl with hl' | hl'
                · obtain ⟨own, hown, cl, hcl, hst⟩ := hret l hl'
                  have hne : l.lender ≠ lender := hold_lender_ne l hl'
                  by_cases hownO : own = o
                  · rw [hownO] at hcl hown
                    have hrep : ∀ c', o.root.find? lender = some c' →
                        (Tree.leaf { c' with state := .retired }).find? l.lender = none := by
                      intro c' hc'
                      change (if c'.id = l.lender then some { c' with state := .retired } else none) = none
                      rw [if_neg]
                      intro heq
                      exact hne ((Tree.find?_id_eq hc').symm.trans heq).symm
                    have hfind' : (Tree.replace lender
                        (fun c' => .leaf { c' with state := .retired }) o.root).find? l.lender
                        = some cl := by
                      rw [Tree.find?_replace_ne o.root lender l.lender
                        (fun c' => .leaf { c' with state := .retired }) hne hrep]
                      exact hcl
                    let f : Leaf → Tree := fun c' => .leaf { c' with state := .retired }
                    let o'' : Owner := { o with root := Tree.replace lender f o.root }
                    have hmem : o'' ∈ (w.ctx.update o.alloc o'').owners := by
                      apply List.mem_map.mpr
                      exact ⟨o, hown, by simp [o'']⟩
                    rw [ho'eq]
                    exact ⟨o'', hmem, cl, hfind', hst⟩
                  · have hoalloc : own.alloc ≠ o.alloc := by
                      intro heq
                      have hfindOwn : w.ctx.findOwner? own.alloc = some own :=
                        Ctx.findOwner?_eq_some_of_mem_of_functional hwf.2.1 hown
                      have := hwf.2.1 own.alloc own o hfindOwn hmemO heq.symm
                      exact hownO this.symm
                    exact ⟨own, List.mem_map.mpr ⟨own, hown, by simp [hoalloc]⟩,
                      cl, hcl, hst⟩
                · simp only [List.mem_singleton] at hl'
                  subst hl'
                  exact ⟨o', List.mem_map.mpr ⟨o, hmemO, by simp⟩,
                    ({ c with state := .retired } : Leaf), hnewlookup, rfl⟩
          · rw [if_neg hlive] at hw
            cases hw
        · rw [if_neg hfresh] at hw
          cases hw
      · rw [if_neg hc] at hw
        cases hw

/-- Ending a loan preserves the invariant: resuming the lender's leaf leaves every
other loan's retired leaf in place (the remaining loans are a sublist with a
different lender, and the resumed leaf is a fresh leaf at the removed loan's
lender), and the removed loan is gone. -/
theorem World.loansOK_endLoanChecked {w w' : World} {a : AllocId} {loanId : LoanId}
    (hw : w.endLoanChecked a loanId = .ok w')
    (hwf : w.WellFormed) (h : w.LoansOK) : w'.LoansOK := by
  unfold World.endLoanChecked at hw
  cases hl : w.ctx.loans.findLoan? loanId with
  | none => simp [hl] at hw
  | some loan =>
    simp only [hl] at hw
    cases hf : w.ctx.findOwner? a with
    | none => simp [hf] at hw
    | some o =>
      simp only [hf] at hw
      cases hr : o.resumeLeaf? loan.lender with
      | none => simp [hr] at hw
      | some o' =>
        simp only [hr, Except.ok.injEq] at hw
        subst hw
        obtain ⟨hid, hlend, hlife, hiss, hret⟩ := h
        have hmemO : o ∈ w.ctx.owners := List.mem_of_find?_eq_some hf
        have hloan_mem : loan ∈ w.ctx.loans.loans := List.mem_of_find?_eq_some hl
        have hloan_id : loan.id = loanId := by
          have := List.find?_some (p := fun l : Loan => decide (l.id = loanId))
            (by simpa [LoanCtx.findLoan?] using hl)
          simpa using this
        let fr : Leaf → Tree := fun c' => .leaf { c' with state := .active }
        have ho'eq : o' = { o with root := Tree.replace loan.lender fr o.root } := by
          obtain ⟨d, _, _, hod⟩ := Owner.resumeLeaf?_eq hr
          simpa [fr] using hod
        unfold World.LoansOK World.LenderRetired at ⊢
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · have hsub : ((w.ctx.loans.loans.filter (fun l : Loan => l.id ≠ loanId)).map
              (·.id)).Sublist (w.ctx.loans.loans.map (·.id)) :=
            (List.filter_sublist (p := fun l : Loan => l.id ≠ loanId)).map (·.id)
          exact hsub.nodup hid
        · have hsub : ((w.ctx.loans.loans.filter (fun l : Loan => l.id ≠ loanId)).map
              (·.lender)).Sublist (w.ctx.loans.loans.map (·.lender)) :=
            (List.filter_sublist (p := fun l : Loan => l.id ≠ loanId)).map (·.lender)
          exact hsub.nodup hlend
        · intro l hl'
          obtain ⟨hlmem, -⟩ := List.mem_filter.mp hl'
          change w.ctx.loans.live l.lifetime = true
          exact hlife l hlmem
        · intro l hl'
          obtain ⟨hlmem, -⟩ := List.mem_filter.mp hl'
          change l.lender ∈ w.ctx.issued
          exact hiss l hlmem
        · intro l hl'
          obtain ⟨hlmem, hneid⟩ := List.mem_filter.mp hl'
          have hne : l.id ≠ loanId := by simpa using hneid
          have hlne : l ≠ loan := by
            intro heq
            subst heq
            exact hne hloan_id
          have hldne : l.lender ≠ loan.lender := by
            intro heq
            exact hlne (List.nodup_map_inj hlend l hlmem loan hloan_mem heq)
          obtain ⟨own, hown, cl, hcl, hst⟩ := hret l hlmem
          by_cases hownO : own = o
          · rw [hownO] at hcl hown
            let o'' : Owner := { o with root := Tree.replace loan.lender fr o.root }
            have hrep : ∀ c', o.root.find? loan.lender = some c' →
                (Tree.leaf { c' with state := .active }).find? l.lender = none := by
              intro c' hc'
              change (if c'.id = l.lender then some { c' with state := .active } else none) = none
              rw [if_neg]
              intro heq
              exact hldne ((Tree.find?_id_eq hc').symm.trans heq).symm
            have hfind' : (Tree.replace loan.lender fr o.root).find? l.lender = some cl := by
              rw [Tree.find?_replace_ne o.root loan.lender l.lender fr hldne hrep]
              exact hcl
            have hmem : o'' ∈ (w.ctx.update o.alloc o'').owners := by
              apply List.mem_map.mpr
              exact ⟨o, hown, by simp [o'']⟩
            rw [ho'eq]
            exact ⟨o'', hmem, cl, hfind', hst⟩
          · have hoalloc : own.alloc ≠ o.alloc := by
              intro heq
              have hfindOwn : w.ctx.findOwner? own.alloc = some own :=
                Ctx.findOwner?_eq_some_of_mem_of_functional hwf.2.1 hown
              have := hwf.2.1 own.alloc own o hfindOwn hmemO heq.symm
              exact hownO this.symm
            exact ⟨own, List.mem_map.mpr ⟨own, hown, by simp [hoalloc]⟩,
              cl, hcl, hst⟩

end Cap
