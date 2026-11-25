/-
Executable distinct-borrower transitions on the retag accounting model.

`beginBorrowChecked` retags the active lender leaf to a fresh borrower identity
and records the original lender in the loan list. No second share-bearing leaf is
created, so the allocation's byte budget still counts the authority once. The
borrower therefore uses the ordinary read/write guards. `endBorrowChecked`
restores the lender identity and removes the loan record.

This slice does not yet update `World.LoansOK`, whose older definition is tied to
a retired lender leaf. That integration is the next step.
-/
import Cap.Retag
import Cap.Unified

namespace Cap

/-- Begin a borrow by retagging the active lender leaf to a fresh borrower name. -/
def World.beginBorrowChecked (w : World) (a : AllocId) (lender borrower : CapId)
    (loanId : LoanId) : Except String World :=
  match w.ctx.findOwner? a with
  | none => .error "beginBorrow: no owner for the allocation"
  | some o =>
    match o.retagLeaf? lender borrower with
    | none => .error "beginBorrow: lender is missing, inactive, or borrower is not fresh"
    | some o' =>
      if borrower ∈ w.ctx.issued then
        .error "beginBorrow: borrower identifier was already issued"
      else if borrower ∈ o.root.ids then
        .error "beginBorrow: borrower is not fresh for the owner"
      else if loanId ∈ w.ctx.loans.loans.map (·.id) then
        .error "beginBorrow: loan identifier is not fresh"
      else if w.ctx.loans.live ⟨0⟩ then
        .ok { w with
              ctx := { (w.ctx.update o.alloc o') with
                issued := borrower :: w.ctx.issued,
                loans := { w.ctx.loans with
                  loans := w.ctx.loans.loans ++
                    [{ id := loanId, alloc := a, lender := lender, borrower := borrower,
                       lifetime := ⟨0⟩ }] } } }
      else .error "beginBorrow: the root lifetime is not live"

/-- End a borrow by restoring the recorded lender identity. -/
def World.endBorrowChecked (w : World) (a : AllocId) (loanId : LoanId) :
    Except String World :=
  match w.ctx.loans.findLoan? loanId with
  | none => .error "endBorrow: no such loan"
  | some loan =>
    match w.ctx.findOwner? a with
    | none => .error "endBorrow: no owner for the allocation"
    | some o =>
      if ∃ l ∈ w.ctx.loans.loans, l.id ≠ loanId ∧ l.lender = loan.borrower then
        .error "endBorrow: a loan borrowed from this borrower is still live"
      else if w.ctx.loans.hasDescendant loan.lifetime then
        .error "endBorrow: a nested loan is still live"
      else
        match o.retagLeaf? loan.borrower loan.lender with
        | none => .error "endBorrow: borrower is missing, inactive, or lender is not fresh"
        | some o' =>
          .ok { w with
                ctx := { (w.ctx.update o.alloc o') with
                  loans := { w.ctx.loans with
                    loans := w.ctx.loans.loans.filter (fun l => l.id ≠ loanId) } } }

end Cap

namespace Cap

/-- Positive-length reachability along loan edges: a loan's lender delegates to
its borrower. The step bound is supplied by the caller and prevents unbounded
search. -/
def BorrowReaches (loans : List Loan) : Nat → CapId → CapId → Bool
  | 0, _, _ => false
  | n + 1, a, b =>
      loans.any (fun l => l.lender = a && (l.borrower = b || BorrowReaches loans n l.borrower b))

/-- No loan's lender is reachable from itself by a positive-length delegation
path. The bound is the number of outstanding loans, which exceeds the length of
any simple cycle. -/
def World.BorrowAcyclic (w : World) : Prop :=
  ∀ l ∈ w.ctx.loans.loans,
    BorrowReaches w.ctx.loans.loans (w.ctx.loans.loans.length + 1)
      l.lender l.lender = false

/-- The retag-aware delegation invariant: loans are distinct, allocation-bound,
historically issued and live. A borrower is either the active terminal holder or
has delegated onward to another recorded loan; the delegation edges are acyclic. -/
def World.BorrowOK (w : World) : Prop :=
  (w.ctx.loans.loans.map (·.id)).Nodup
  ∧ (w.ctx.loans.loans.map (·.lender)).Nodup
  ∧ (w.ctx.loans.loans.map (·.borrower)).Nodup
  ∧ (∀ l ∈ w.ctx.loans.loans, l.lender ≠ l.borrower)
  ∧ (∀ l ∈ w.ctx.loans.loans, l.lender ∈ w.ctx.issued)
  ∧ (∀ l ∈ w.ctx.loans.loans, l.borrower ∈ w.ctx.issued)
  ∧ (∀ l ∈ w.ctx.loans.loans, w.ctx.loans.live l.lifetime = true)
  ∧ (∀ l ∈ w.ctx.loans.loans, ∃ o, w.ctx.findOwner? l.alloc = some o ∧
      ((∃ c, o.root.find? l.borrower = some c ∧ c.state = .active) ∨
       (∃ m ∈ w.ctx.loans.loans, m.lender = l.borrower)))
  ∧ w.BorrowAcyclic

private theorem borrow_findOwner_alloc {C : Ctx} {a : AllocId} {o : Owner}
    (h : C.findOwner? a = some o) : o.alloc = a := by
  unfold Ctx.findOwner? at h
  have hp : (fun x : Owner => decide (x.alloc = a)) o = true :=
    List.find?_some (p := fun x : Owner => decide (x.alloc = a)) h
  exact of_decide_eq_true hp

/-- A fresh allocation does not change lookup of a different allocation. -/
theorem Ctx.findOwner?_alloc_of_ne {C : Ctx} {a b : AllocId} {n : Nat}
    {pos : 0 < C.D} {rootId disposal : CapId}
    (hf : a ∉ C.owners.map (·.alloc)) (hne : b ≠ a) :
    (C.alloc a n pos rootId disposal hf).findOwner? b = C.findOwner? b := by
  unfold Ctx.alloc Ctx.findOwner?
  simp [Owner.init, hne.symm]

/-- Allocation preserves the delegation invariant: loans and borrower leaves are
unchanged, issuance only grows, and the fresh owner cannot be the target of an
existing loan. -/
theorem World.borrowOK_allocChecked {w w' : World} {n : Nat}
    {rootId disposal : CapId} {po : 0 < w.ctx.D}
    (hw : w.allocChecked n rootId disposal po = .ok w') (h : w.BorrowOK) :
    w'.BorrowOK := by
  unfold World.allocChecked at hw
  split at hw
  · rename_i hf
    split at hw
    · rename_i hfr
      simp only [Except.ok.injEq] at hw
      subst hw
      unfold World.BorrowOK at h ⊢
      refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_, ?_, ?_, ?_, ?_⟩
      · intro l hl
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (h.2.2.2.2.1 l hl))
      · intro l hl
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (h.2.2.2.2.2.1 l hl))
      · intro l hl
        simpa [Ctx.alloc] using h.2.2.2.2.2.2.1 l hl
      · intro l hl
        obtain ⟨o, hfind, hcond⟩ := h.2.2.2.2.2.2.2.1 l hl
        have hmemO : o ∈ w.ctx.owners :=
          List.mem_of_find?_eq_some (by simpa [Ctx.findOwner?] using hfind)
        have hoalloc : o.alloc = l.alloc := borrow_findOwner_alloc hfind
        have hmem : l.alloc ∈ w.ctx.owners.map (·.alloc) := by
          rw [← hoalloc]
          exact List.mem_map_of_mem hmemO
        have hne : l.alloc ≠ ⟨w.ctx.nextAlloc⟩ := by
          intro heq
          apply hf
          rwa [heq] at hmem
        refine ⟨o, ?_, hcond⟩
        rw [Ctx.findOwner?_alloc_of_ne (C := w.ctx) (a := ⟨w.ctx.nextAlloc⟩)
          (b := l.alloc) hf hne]
        exact hfind
      · simpa [World.BorrowAcyclic, Ctx.alloc] using h.2.2.2.2.2.2.2.2
    · simp at hw
  · simp at hw

/-- A successful spatial split has no outstanding loan for the allocation. -/
theorem World.splitAtChecked_no_loan {w w' : World} {a : AllocId}
    {id id1 id2 : CapId} {k : Nat}
    (hw : w.splitAtChecked a id id1 id2 k = .ok w') :
    ∀ l ∈ w.ctx.loans.loans, l.alloc ≠ a := by
  unfold World.splitAtChecked at hw
  split at hw
  · simp at hw
  · rename_i o hf
    split at hw
    · rename_i halloc
      split at hw
      · exact halloc
      · simp at hw
    · simp at hw

/-- Success facts for a fractional split. -/
private theorem splitFractionChecked_sound {w w' : World} {a : AllocId}
    {id id1 id2 : CapId} {q1 q2 : Nat} {p1 : 0 < q1} {p2 : 0 < q2}
    (hw : w.splitFractionChecked a id id1 id2 q1 q2 p1 p2 = .ok w') :
    ∃ o C', w.ctx.findOwner? a = some o ∧ o.FreshIds id1 id2 ∧
      id1 ∉ w.ctx.ids ∧ id2 ∉ w.ctx.ids ∧
      w.ctx.splitFractionOwner? o id id1 id2 q1 q2 p1 p2 = some C' ∧
      w' = { w with ctx := { C' with issued := id1 :: id2 :: w.ctx.issued } } := by
  unfold World.splitFractionChecked at hw
  split at hw
  · simp at hw
  · rename_i o hf
    split at hw
    · rename_i halloc
      split at hw
      · rename_i hfr
        split at hw
        · rename_i C' hs
          simp only [Except.ok.injEq] at hw
          exact ⟨o, C', hf, hfr.1, hfr.2.1, hfr.2.2.1, hs, hw.symm⟩
        · simp at hw
      · simp at hw
    · simp at hw

/-- A successful fractional split has no outstanding loan for the allocation. -/
theorem World.splitFractionChecked_no_loan {w w' : World} {a : AllocId}
    {id id1 id2 : CapId} {q1 q2 : Nat} {p1 : 0 < q1} {p2 : 0 < q2}
    (hw : w.splitFractionChecked a id id1 id2 q1 q2 p1 p2 = .ok w') :
    ∀ l ∈ w.ctx.loans.loans, l.alloc ≠ a := by
  unfold World.splitFractionChecked at hw
  split at hw
  · simp at hw
  · rename_i o hf
    split at hw
    · rename_i halloc
      split at hw
      · exact halloc
      · simp at hw
    · simp at hw

/-- Success facts for a join. -/
private theorem joinChecked_sound {w w' : World} {a : AllocId}
    {node newId : CapId} (hw : w.joinChecked a node newId = .ok w') :
    ∃ o C', w.ctx.findOwner? a = some o ∧
      newId ∉ w.ctx.ids ∧ newId ∉ w.ctx.issued ∧
      w.ctx.joinFractionOwner? o node newId = some C' ∧
      w' = { w with ctx := { C' with issued := newId :: w.ctx.issued } } := by
  unfold World.joinChecked at hw
  split at hw
  · simp at hw
  · rename_i o hf
    split at hw
    · rename_i halloc
      split at hw
      · rename_i hfresh
        split at hw
        · rename_i C' hs
          simp only [Except.ok.injEq] at hw
          exact ⟨o, C', hf, hfresh.1, hfresh.2, hs, hw.symm⟩
        · simp at hw
      · simp at hw
    · simp at hw

/-- A successful join has no outstanding loan for the allocation. -/
theorem World.joinChecked_no_loan {w w' : World} {a : AllocId}
    {node newId : CapId} (hw : w.joinChecked a node newId = .ok w') :
    ∀ l ∈ w.ctx.loans.loans, l.alloc ≠ a := by
  unfold World.joinChecked at hw
  split at hw
  · simp at hw
  · rename_i o hf
    split at hw
    · rename_i halloc
      split at hw
      · exact halloc
      · simp at hw
    · simp at hw

/-- Replacing one owner leaves lookup of a different allocation unchanged. -/
theorem Ctx.findOwner?_update_of_ne (C : Ctx) (a : AllocId) (o' : Owner)
    {b : AllocId} (h : b ≠ a) (ho' : o'.alloc = a) :
    (C.update a o').findOwner? b = C.findOwner? b := by
  unfold Ctx.update Ctx.findOwner?
  induction C.owners with
  | nil => rfl
  | cons o os ih =>
    by_cases hb : o.alloc = b
    · have hba : o.alloc ≠ a := by intro ha; exact h (hb.symm.trans ha)
      simp [List.map, List.find?, hb, h]
    · by_cases ha : o.alloc = a
      · have hb' : o'.alloc ≠ b := by rw [ho']; exact h.symm
        have hba : ¬ a = b := fun h' => h h'.symm
        simp [List.map, List.find?, hb, ha, hb', hba, ih]
      · simp [List.map, List.find?, hb, ha, ih]

/-- A lookup for a different allocation survives freeing. -/
theorem Ctx.findOwner?_free_of_ne (C : Ctx) {a b : AllocId} (h : b ≠ a) :
    (C.free a).findOwner? b = C.findOwner? b := by
  unfold Ctx.free Ctx.findOwner?
  rw [List.find?_filter]
  congr 1
  funext o
  by_cases hb : o.alloc = b
  · have hba : ¬ b = a := h
    simp [hb, hba]
  · simp [hb]

/-- Checked disposal preserves the delegation invariant: it is refused while any
loan names the allocation, and every other loan's borrower witness survives the
owner filter. -/
theorem World.borrowOK_freeChecked {w w' : World} {a : AllocId} {d : CapId}
    (hw : w.freeChecked a d = .ok w') (h : w.BorrowOK) : w'.BorrowOK := by
  unfold World.freeChecked at hw
  split at hw
  · simp at hw
  · rename_i o hfind
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
            have hctx : ctx' = w.ctx.free a := Ctx.freeWith?_eq_free hc
            subst ctx'
            unfold World.BorrowOK at h ⊢
            refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_, ?_, ?_, ?_, ?_⟩
            · intro l hl
              exact h.2.2.2.2.1 l hl
            · intro l hl
              exact h.2.2.2.2.2.1 l hl
            · intro l hl
              simpa [Ctx.free] using h.2.2.2.2.2.2.1 l hl
            · intro l hl
              obtain ⟨own, hown, hcond⟩ := h.2.2.2.2.2.2.2.1 l hl
              have hne : l.alloc ≠ a := halloc l hl
              refine ⟨own, ?_, hcond⟩
              rw [Ctx.findOwner?_free_of_ne (C := w.ctx) (a := a) (b := l.alloc) hne]
              exact hown
            · simpa [World.BorrowAcyclic, Ctx.free] using h.2.2.2.2.2.2.2.2
      · simp at hw
    · simp at hw

/-- A spatial split preserves the delegation invariant: the guard excludes every
loan on the target allocation, and the owner update frames all other lookups. -/
theorem World.borrowOK_splitAtChecked {w w' : World} {a : AllocId}
    {id id1 id2 : CapId} {k : Nat}
    (hw : w.splitAtChecked a id id1 id2 k = .ok w') (h : w.BorrowOK) :
    w'.BorrowOK := by
  obtain ⟨o, C', hfind, _hfids, _hfresh1, _hfresh2, hs, hw'⟩ :=
    World.splitAtChecked_sound hw
  have hno := World.splitAtChecked_no_loan hw
  have hoalloc : o.alloc = a := borrow_findOwner_alloc hfind
  unfold Ctx.splitAtOwner? at hs
  cases ho : o.splitAt? id id1 id2 k with
  | none => simp [ho] at hs
  | some o' =>
    simp only [ho, Option.map_some, Option.some.injEq] at hs
    subst C'
    have ho'alloc : o'.alloc = o.alloc := Owner.splitAt?_alloc ho
    rw [hw']
    unfold World.BorrowOK at h ⊢
    refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_, ?_, ?_, ?_, ?_⟩
    · intro l hl
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (h.2.2.2.2.1 l hl))
    · intro l hl
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (h.2.2.2.2.2.1 l hl))
    · intro l hl
      simpa [Ctx.update] using h.2.2.2.2.2.2.1 l hl
    · intro l hl
      obtain ⟨own, hown, hcond⟩ := h.2.2.2.2.2.2.2.1 l hl
      have hne : l.alloc ≠ o.alloc := by
        rw [hoalloc]
        exact hno l hl
      refine ⟨own, ?_, hcond⟩
      change (Ctx.update w.ctx o.alloc o').findOwner? l.alloc = _
      rw [Ctx.findOwner?_update_of_ne w.ctx o.alloc o' hne ho'alloc]
      exact hown
    · simpa [World.BorrowAcyclic, Ctx.update] using h.2.2.2.2.2.2.2.2

/-- A fractional split preserves the delegation invariant by the same framing
argument as a spatial split. -/
theorem World.borrowOK_splitFractionChecked {w w' : World} {a : AllocId}
    {id id1 id2 : CapId} {q1 q2 : Nat} {p1 : 0 < q1} {p2 : 0 < q2}
    (hw : w.splitFractionChecked a id id1 id2 q1 q2 p1 p2 = .ok w')
    (h : w.BorrowOK) : w'.BorrowOK := by
  obtain ⟨o, C', hfind, _hfids, _hfresh1, _hfresh2, hs, hw'⟩ :=
    splitFractionChecked_sound hw
  have hno := World.splitFractionChecked_no_loan hw
  have hoalloc : o.alloc = a := borrow_findOwner_alloc hfind
  unfold Ctx.splitFractionOwner? at hs
  cases ho : o.splitFraction? id id1 id2 q1 q2 p1 p2 with
  | none => simp [ho] at hs
  | some o' =>
    simp only [ho, Option.map_some, Option.some.injEq] at hs
    subst C'
    have ho'alloc : o'.alloc = o.alloc := Owner.splitFraction?_alloc ho
    rw [hw']
    unfold World.BorrowOK at h ⊢
    refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_, ?_, ?_, ?_, ?_⟩
    · intro l hl
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (h.2.2.2.2.1 l hl))
    · intro l hl
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (h.2.2.2.2.2.1 l hl))
    · intro l hl
      simpa [Ctx.update] using h.2.2.2.2.2.2.1 l hl
    · intro l hl
      obtain ⟨own, hown, hcond⟩ := h.2.2.2.2.2.2.2.1 l hl
      have hne : l.alloc ≠ o.alloc := by
        rw [hoalloc]
        exact hno l hl
      refine ⟨own, ?_, hcond⟩
      change (Ctx.update w.ctx o.alloc o').findOwner? l.alloc = _
      rw [Ctx.findOwner?_update_of_ne w.ctx o.alloc o' hne ho'alloc]
      exact hown
    · simpa [World.BorrowAcyclic, Ctx.update] using h.2.2.2.2.2.2.2.2

/-- A fractional join preserves the delegation invariant. -/
theorem World.borrowOK_joinChecked {w w' : World} {a : AllocId}
    {node newId : CapId}
    (hw : w.joinChecked a node newId = .ok w') (h : w.BorrowOK) :
    w'.BorrowOK := by
  obtain ⟨o, C', hfind, _hfresh1, _hfresh2, hs, hw'⟩ := joinChecked_sound hw
  have hno := World.joinChecked_no_loan hw
  have hoalloc : o.alloc = a := borrow_findOwner_alloc hfind
  unfold Ctx.joinFractionOwner? at hs
  cases ho : o.joinFraction? node newId with
  | none => simp [ho] at hs
  | some o' =>
    simp only [ho, Option.map_some, Option.some.injEq] at hs
    subst C'
    have ho'alloc : o'.alloc = o.alloc := Owner.joinFraction_alloc ho
    rw [hw']
    unfold World.BorrowOK at h ⊢
    refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_, ?_, ?_, ?_, ?_⟩
    · intro l hl
      exact List.mem_cons_of_mem _ (h.2.2.2.2.1 l hl)
    · intro l hl
      exact List.mem_cons_of_mem _ (h.2.2.2.2.2.1 l hl)
    · intro l hl
      simpa [Ctx.update] using h.2.2.2.2.2.2.1 l hl
    · intro l hl
      obtain ⟨own, hown, hcond⟩ := h.2.2.2.2.2.2.2.1 l hl
      have hne : l.alloc ≠ o.alloc := by
        rw [hoalloc]
        exact hno l hl
      refine ⟨own, ?_, hcond⟩
      change (Ctx.update w.ctx o.alloc o').findOwner? l.alloc = _
      rw [Ctx.findOwner?_update_of_ne w.ctx o.alloc o' hne ho'alloc]
      exact hown
    · simpa [World.BorrowAcyclic, Ctx.update] using h.2.2.2.2.2.2.2.2

/-- A checked write changes only the backend, so delegation bookkeeping is unchanged. -/
theorem World.borrowOK_write {w w' : World} {a : AllocId} {id : CapId} {i : Nat}
    {v : UInt8} (hw : w.writeChecked a id i v = .ok w') (h : w.BorrowOK) :
    w'.BorrowOK := by
  obtain ⟨_, _, _, _, _, _, _, hctx, _⟩ := World.writeChecked_sound hw
  unfold World.BorrowOK at h ⊢
  simpa [World.BorrowAcyclic, hctx] using h

/-- The concrete 64-byte world has no loans. -/
theorem World.uWorld_borrowOK : World.BorrowOK uWorld := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    intro l hl <;> simp [uWorld, LoanCtx.rootOnly] at hl

end Cap
