/-
A unified checked execution for the command language.

One instruction language with value operands, a checker that is also the
interpreter over a `World`, and preservation of the world relation. Acceptance
therefore yields the executed world, not a separate permission certificate.

The language covers writes, both splits, joins, free, allocation, distinct-borrower
borrow and return, and no-op. Snapshot observation and the sealed runner's full-path
state threading remain outside this module.
-/
import Cap.World
import Cap.Backend
import Cap.Core
import Cap.WorldInvariant
import Cap.Retag

namespace Cap

/-- A value-carrying execution command. -/
inductive UCmd where
  | write (a : AllocId) (id : CapId) (i : Nat) (v : UInt8)
  | splitAt (a : AllocId) (id id1 id2 : CapId) (k : Nat)
  | splitFraction (a : AllocId) (id id1 id2 : CapId) (q1 q2 : Nat)
  | join (a : AllocId) (node newId : CapId)
  | free (a : AllocId) (d : CapId)
  | alloc (n : Nat) (rootId disposal : CapId)
  | beginBorrow (a : AllocId) (lender borrower : CapId) (loanId : LoanId)
  | endBorrow (a : AllocId) (loanId : LoanId)
  | nop

namespace Ctx

/-- The chain base a borrow from `lender` inherits: the base of the loan whose
borrower is `lender`, or `lender` itself when it is the chain's base. -/
def borrowBase (C : Ctx) (lender : CapId) : CapId :=
  ((C.loans.loans.find? (fun m => m.borrower = lender)).map (·.base)).getD lender

/-- The lifetime of the loan whose borrower is `lender`: the created lifetime
of a child borrow. -/
def borrowParent (C : Ctx) (lender : CapId) : Option LifetimeId :=
  (C.loans.loans.find? (fun m => m.borrower = lender)).map (·.lifetime)

/-- The context of an accepted borrow. -/
def beginBorrowNext (C : Ctx) (a : AllocId) (o o' : Owner) (c : Leaf)
    (lender borrower : CapId) (loanId : LoanId) : Ctx :=
  { (C.update o.alloc o') with
    issued := borrower :: C.issued,
    loans := { C.loans with
      lifetimes := { id := ⟨C.loans.nextLifetime⟩, parent := C.borrowParent lender,
                     state := .live } :: C.loans.lifetimes,
      loans := C.loans.loans ++
        [{ id := loanId, alloc := a, base := C.borrowBase lender, lender := lender,
           borrower := borrower, lifetime := ⟨C.loans.nextLifetime⟩,
           lo := c.lo, hi := c.hi, q := c.q, ceiling := c.ceiling }],
      nextLifetime := C.loans.nextLifetime + 1 } }

/-- The context of an accepted return. -/
def endBorrowNext (C : Ctx) (o o' : Owner) (loan : Loan) : Ctx :=
  { (C.update o.alloc o') with loans := LoanCtx.endBorrowBookkeeping C.loans loan }

/-- The issued list of a begun borrow. -/
@[simp] theorem beginBorrowNext_issued (C : Ctx) (a : AllocId) (o o' : Owner)
    (c : Leaf) (lender borrower : CapId) (loanId : LoanId) :
    (C.beginBorrowNext a o o' c lender borrower loanId).issued = borrower :: C.issued := rfl

/-- The identifier list of a begun borrow is the retagged update's. -/
@[simp] theorem beginBorrowNext_ids (C : Ctx) (a : AllocId) (o o' : Owner)
    (c : Leaf) (lender borrower : CapId) (loanId : LoanId) :
    (C.beginBorrowNext a o o' c lender borrower loanId).ids =
      (C.update o.alloc o').ids := rfl

/-- The issued list of a return. -/
@[simp] theorem endBorrowNext_issued (C : Ctx) (o o' : Owner) (loan : Loan) :
    (C.endBorrowNext o o' loan).issued = C.issued := rfl

/-- The identifier list of a return is the retagged update's. -/
@[simp] theorem endBorrowNext_ids (C : Ctx) (o o' : Owner) (loan : Loan) :
    (C.endBorrowNext o o' loan).ids = (C.update o.alloc o').ids := rfl


/-- Begin a borrow by retagging the active lender leaf to a fresh borrower name.
The guards are the base route's, in its order, with its messages. -/
def beginBorrow? (C : Ctx) (a : AllocId) (lender borrower : CapId)
    (loanId : LoanId) : Except String Ctx :=
  match C.findOwner? a with
  | none => .error "beginBorrow: no owner for the allocation"
  | some o =>
    match o.retagLeafFind? lender borrower with
    | none => .error "beginBorrow: lender is missing, inactive, or borrower is not fresh"
    | some (o', c) =>
      if borrower ∈ C.issued then
        .error "beginBorrow: borrower identifier was already issued"
      else if borrower ∈ o.root.ids then
        .error "beginBorrow: borrower is not fresh for the owner"
      else if loanId ∈ C.loans.loans.map (·.id) then
        .error "beginBorrow: loan identifier is not fresh"
      else if C.loans.live LoanCtx.rootLifetime then
        .ok (C.beginBorrowNext a o o' c lender borrower loanId)
      else .error "beginBorrow: the root lifetime is not live"

/-- End a borrow by restoring the recorded lender identity. The guards are the
base route's, in its order, with its messages. -/
def endBorrow? (C : Ctx) (a : AllocId) (loanId : LoanId) : Except String Ctx :=
  match C.loans.findLoan? loanId with
  | none => .error "endBorrow: no such loan"
  | some loan =>
    match C.findOwner? a with
    | none => .error "endBorrow: no owner for the allocation"
    | some o =>
      if ∃ l ∈ C.loans.loans, l.id ≠ loanId ∧ l.lender = loan.borrower then
        .error "endBorrow: a loan borrowed from this borrower is still live"
      else if C.loans.hasDescendant loan.lifetime then
        .error "endBorrow: a nested loan is still live"
      else
        match o.retagLeaf? loan.borrower loan.lender with
        | none => .error "endBorrow: borrower is missing, inactive, or lender is not fresh"
        | some o' => .ok (C.endBorrowNext o o' loan)

/-- Success facts of `Ctx.beginBorrow?`, including the exact resulting context. -/
theorem beginBorrow?_sound {C C' : Ctx} {a : AllocId} {lender borrower : CapId}
    {loanId : LoanId} (h : C.beginBorrow? a lender borrower loanId = .ok C') :
    ∃ own own' c, C.findOwner? a = some own ∧
      own.retagLeafFind? lender borrower = some (own', c) ∧
      borrower ∉ C.issued ∧ borrower ∉ own.root.ids ∧
      loanId ∉ C.loans.loans.map (·.id) ∧
      C.loans.live LoanCtx.rootLifetime = true ∧
      C' = C.beginBorrowNext a own own' c lender borrower loanId := by
  unfold Ctx.beginBorrow? at h
  cases hf : C.findOwner? a with
  | none => simp [hf] at h
  | some o =>
    cases hr : o.retagLeafFind? lender borrower with
    | none => simp [hf, hr] at h
    | some p =>
      rcases p with ⟨oRetag, cLeaf⟩
      simp only [hf, hr] at h
      by_cases hiss : borrower ∈ C.issued
      · simp [hiss] at h
      · rw [if_neg hiss] at h
        by_cases hroot : borrower ∈ o.root.ids
        · simp [hroot] at h
        · rw [if_neg hroot] at h
          by_cases hloan : loanId ∈ C.loans.loans.map (·.id)
          · simp [hloan] at h
          · rw [if_neg hloan] at h
            by_cases hlive : C.loans.live LoanCtx.rootLifetime = true
            · rw [if_pos hlive] at h
              simp only [Except.ok.injEq] at h
              exact ⟨o, oRetag, cLeaf, rfl, hr, hiss, hroot, hloan, hlive, h.symm⟩
            · simp [hlive] at h

/-- Success facts of `Ctx.endBorrow?`, including the exact resulting context. -/
theorem endBorrow?_sound {C C' : Ctx} {a : AllocId} {loanId : LoanId}
    (h : C.endBorrow? a loanId = .ok C') :
    ∃ loan o o', C.loans.findLoan? loanId = some loan ∧
      C.findOwner? a = some o ∧ o.retagLeaf? loan.borrower loan.lender = some o' ∧
      (∀ m ∈ C.loans.loans, m.id ≠ loanId → m.lender ≠ loan.borrower) ∧
      C.loans.hasDescendant loan.lifetime = false ∧
      C' = C.endBorrowNext o o' loan := by
  unfold Ctx.endBorrow? at h
  split at h
  · simp at h
  · rename_i loan hloan
    split at h
    · simp at h
    · rename_i o hfind
      split at h
      · simp at h
      · rename_i hsuc
        split at h
        · simp at h
        · rename_i hdesc
          split at h
          · simp at h
          · rename_i o' hret
            simp only [Except.ok.injEq] at h
            have hsuc' : ∀ m ∈ C.loans.loans, m.id ≠ loanId →
                m.lender ≠ loan.borrower := by
              intro m hm hmid heq
              exact hsuc ⟨m, hm, hmid, heq⟩
            have hdesc' : C.loans.hasDescendant loan.lifetime = false := by simpa using hdesc
            exact ⟨loan, o, o', hloan, hfind, hret, hsuc', hdesc', h.symm⟩

end Ctx

namespace World

/-- Check and execute one write: the owner guard and the backend must both accept,
and the backend is replaced at the allocation. -/
def writeChecked (w : World) (a : AllocId) (id : CapId) (i : Nat) (v : UInt8) :
    Except String World :=
  match w.ctx.findOwner? a with
  | none => .error "write: no owner for the allocation"
  | some o =>
    match w.heaps a with
    | none => .error "write: no backend for the allocation"
    | some b =>
      if _hw : o.writableB w.ctx.D id i then
        match b.write i v with
        | none => .error "write: index out of range"
        | some b' =>
          .ok { w with heaps := fun x => if x = a then some b' else w.heaps x }
      else .error "write: capability is not writable at this index"

/-- An accepted write names the owner, its ledger guard, the backend and the
replacement. -/
theorem writeChecked_sound {w w' : World} {a : AllocId} {id : CapId} {i : Nat}
    {v : UInt8} (h : w.writeChecked a id i v = .ok w') :
    ∃ o b b', w.ctx.findOwner? a = some o ∧ o.Writable w.ctx.D id i ∧
      w.heaps a = some b ∧ b.write i v = some b' ∧
      w'.ctx = w.ctx ∧
      w'.heaps = (fun x => if x = a then some b' else w.heaps x) := by
  unfold World.writeChecked at h
  cases hf : w.ctx.findOwner? a with
  | none => simp [hf] at h
  | some o =>
    cases hb : w.heaps a with
    | none => simp [hf, hb] at h
    | some b =>
      by_cases hw : o.writableB w.ctx.D id i
      · cases hbw : b.write i v with
        | none => simp [hf, hb, hw, hbw] at h
        | some b' =>
          simp [hf, hb, hw, hbw] at h
          cases h
          exact ⟨o, b, b', rfl, Owner.writableB_sound hw, rfl, hbw, rfl, rfl⟩
      · simp [hf, hb, hw] at h

/-- Acceptance preserves the world relation. -/
theorem writeChecked_rel {w w' : World} {a : AllocId} {id : CapId} {i : Nat}
    {v : UInt8} (h : w.writeChecked a id i v = .ok w') (hr : w.Rel) : w'.Rel := by
  obtain ⟨o, b, b', hf, _hw, hb, hbw, hctx, hheaps⟩ := writeChecked_sound h
  refine ⟨?_, ?_⟩
  · rw [hctx]; exact hr.1
  · intro o' ho'
    rw [hctx] at ho'
    obtain ⟨b0, hb0, hlen⟩ := hr.2 o' ho'
    by_cases hx : o'.alloc = a
    · have hb0a : w.heaps a = some b0 := by simpa [hx] using hb0
      have hb_eq : b0 = b := by
        rw [hb] at hb0a
        exact (Option.some.inj hb0a).symm
      subst hb_eq
      refine ⟨b', ?_, ?_⟩
      · simp [hheaps, hx]
      · rw [Backend.write_preserves_len hbw]; exact hlen
    · refine ⟨b0, ?_, hlen⟩
      simp [hheaps, hx, hb0]

/-- An accepted write preserves the world invariant: the context is unchanged
and the backend is replaced by one of the same length. -/
theorem writeChecked_wf {w w' : World} {a : AllocId} {id : CapId} {i : Nat}
    {v : UInt8} (h : w.writeChecked a id i v = .ok w') (hwf : w.WellFormed) :
    w'.WellFormed := by
  obtain ⟨o, b, b', hf, _hw, hb, hbw, hctx, hheaps⟩ := writeChecked_sound h
  refine ⟨?_, ?_, ?_⟩
  · rw [hctx]; exact hwf.1
  · rw [hctx]; exact hwf.2.1
  · intro a' o' hfind
    rw [hctx] at hfind
    obtain ⟨b0, hb0, hlen⟩ := hwf.2.2 a' o' hfind
    by_cases ha : a' = a
    · subst a'
      have hb_eq : b0 = b := by
        rw [hb] at hb0
        exact (Option.some.inj hb0).symm
      subst hb_eq
      refine ⟨b', ?_, ?_⟩
      · simp [hheaps]
      · rw [Backend.write_preserves_len hbw, hlen]
    · refine ⟨b0, ?_, hlen⟩
      simp [hheaps, ha, hb0]

/-- The command-language carrier: well-formedness, the issuance history and the
three loan-readiness facts the borrow route's proofs consume. -/
def CommandInv (w : World) : Prop :=
  w.WellFormed ∧ Ctx.HistoryOK w.ctx ∧ Ctx.LoansReady w.ctx

theorem commandInv_wf {w : World} (h : w.CommandInv) : w.WellFormed := h.1

theorem commandInv_history {w : World} (h : w.CommandInv) : Ctx.HistoryOK w.ctx := h.2.1

theorem commandInv_loans {w : World} (h : w.CommandInv) : Ctx.LoansReady w.ctx := h.2.2

/-- Begin a borrow: the context transition, wrapped with the base four arguments. -/
def beginBorrowChecked (w : World) (a : AllocId) (lender borrower : CapId)
    (loanId : LoanId) : Except String World :=
  match w.ctx.beginBorrow? a lender borrower loanId with
  | .ok C => .ok { w with ctx := C }
  | .error e => .error e

/-- End a borrow: the context transition, wrapped with the base three arguments. -/
def endBorrowChecked (w : World) (a : AllocId) (loanId : LoanId) :
    Except String World :=
  match w.ctx.endBorrow? a loanId with
  | .ok C => .ok { w with ctx := C }
  | .error e => .error e

/-- Success facts of `World.beginBorrowChecked`. -/
theorem beginBorrowChecked_sound {w w' : World} {a : AllocId} {lender borrower : CapId}
    {loanId : LoanId} (h : w.beginBorrowChecked a lender borrower loanId = .ok w') :
    ∃ C, w.ctx.beginBorrow? a lender borrower loanId = .ok C ∧
      w' = { w with ctx := C } := by
  unfold World.beginBorrowChecked at h
  cases hc : w.ctx.beginBorrow? a lender borrower loanId with
  | error e => simp [hc] at h
  | ok C =>
    simp [hc] at h
    exact ⟨C, rfl, h.symm⟩

/-- Success facts of `World.endBorrowChecked`. -/
theorem endBorrowChecked_sound {w w' : World} {a : AllocId} {loanId : LoanId}
    (h : w.endBorrowChecked a loanId = .ok w') :
    ∃ C, w.ctx.endBorrow? a loanId = .ok C ∧ w' = { w with ctx := C } := by
  unfold World.endBorrowChecked at h
  cases hc : w.ctx.endBorrow? a loanId with
  | error e => simp [hc] at h
  | ok C =>
    simp [hc] at h
    exact ⟨C, rfl, h.symm⟩

/-- A successful borrow preserves the world invariant from the command carrier. -/
theorem beginBorrowChecked_wf {w w' : World} {a : AllocId} {lender borrower : CapId}
    {loanId : LoanId} (h : w.beginBorrowChecked a lender borrower loanId = .ok w')
    (hinv : w.CommandInv) : w'.WellFormed := by
  obtain ⟨hwf, hh, hlr⟩ := hinv
  obtain ⟨C, hC, hw'⟩ := beginBorrowChecked_sound h
  obtain ⟨o, o', c, hfind, hretag, hissued, _hroot, _hloan, _hlive, hCeq⟩ :=
    Ctx.beginBorrow?_sound hC
  subst hCeq
  subst hw'
  have hmem : o ∈ w.ctx.owners := List.mem_of_find?_eq_some hfind
  have hoa : o.alloc = a := by
    have := List.find?_some (p := fun x : Owner => decide (x.alloc = a))
      (by simpa [Ctx.findOwner?] using hfind)
    simpa using this
  have hrect : o.retagLeaf? lender borrower = some o' := Owner.retagLeafFind?_fst hretag
  have hoid : o.ids.Nodup := Ctx.owner_ids_nodup hwf.1.2.2 hmem
  have hnewCids : borrower ∉ w.ctx.ids := by
    intro hm; exact hissued (hh.2 borrower hm)
  have hdisp : borrower ≠ o.disposal := by
    intro heq
    have hmemid : o.disposal ∈ w.ctx.ids :=
      List.mem_flatMap.mpr ⟨o, hmem, by simp [Owner.ids]⟩
    exact hnewCids (heq ▸ hmemid)
  have ho'nd : o'.ids.Nodup := Owner.retagLeaf?_ids_nodup hrect hoid hdisp
  have ho'alloc : o'.alloc = o.alloc := Owner.retagLeaf?_alloc hrect
  have ho'len : o'.len = o.len := Owner.retagLeaf?_len hrect
  have hctxwf : Ctx.WellFormed (w.ctx.update o.alloc o') := by
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · apply Ctx.update_covered
      · exact (Owner.retagLeaf?_covered hrect).mpr (hwf.1.1.1 o hmem)
      · intro x hx _; exact hwf.1.1.1 x hx
    · exact Ctx.update_nodup ho'alloc hwf.1.1.2
    · exact Ctx.update_wellFormed_owners
        (Owner.retagLeaf?_wellFormed hrect (hwf.1.2.1 o hmem))
        (fun x hx _ => hwf.1.2.1 x hx)
    · exact Ctx.update_ids_nodup_of_sub (C := w.ctx) (a := o.alloc) (o := o) (o' := o')
        hwf.1.1 hmem rfl hwf.1.2.2 ho'nd (Owner.retagLeaf?_ids_sub hrect) hnewCids
  have hfun : (w.ctx.update o.alloc o').Functional :=
    Ctx.update_functional ho'alloc hwf.1.1.2
  have hfa : w.ctx.findOwner? o.alloc = some o := by simpa [hoa] using hfind
  have hst : ({ w with ctx := w.ctx.update o.alloc o' } : World).StorageMatches :=
    World.update_storage hwf hfa ho'alloc ho'len
  refine ⟨?_, ?_, ?_⟩
  · exact hctxwf
  · exact hfun
  · exact hst

/-- A successful return preserves the world invariant from the command carrier. -/
theorem endBorrowChecked_wf {w w' : World} {a : AllocId} {loanId : LoanId}
    (h : w.endBorrowChecked a loanId = .ok w') (hinv : w.CommandInv) :
    w'.WellFormed := by
  obtain ⟨hwf, hh, hlr⟩ := hinv
  obtain ⟨C, hC, hw'⟩ := endBorrowChecked_sound h
  obtain ⟨loan, o, o', hloan, hfind, hret, _hsuc, _hdesc, hCeq⟩ :=
    Ctx.endBorrow?_sound hC
  subst hCeq
  subst hw'
  have hmem : o ∈ w.ctx.owners := List.mem_of_find?_eq_some hfind
  have hoa : o.alloc = a := by
    have := List.find?_some (p := fun x : Owner => decide (x.alloc = a))
      (by simpa [Ctx.findOwner?] using hfind)
    simpa using this
  have hloanmem : loan ∈ w.ctx.loans.loans := List.mem_of_find?_eq_some hloan
  have hoid : o.ids.Nodup := Ctx.owner_ids_nodup hwf.1.2.2 hmem
  have hnewCids : loan.lender ∉ w.ctx.ids := hlr.2.1 loan hloanmem
  have hdisp : loan.lender ≠ o.disposal := by
    intro heq
    have hmemid : o.disposal ∈ w.ctx.ids :=
      List.mem_flatMap.mpr ⟨o, hmem, by simp [Owner.ids]⟩
    exact hnewCids (heq ▸ hmemid)
  have ho'nd : o'.ids.Nodup := Owner.retagLeaf?_ids_nodup hret hoid hdisp
  have ho'alloc : o'.alloc = o.alloc := Owner.retagLeaf?_alloc hret
  have ho'len : o'.len = o.len := Owner.retagLeaf?_len hret
  have hctxwf : Ctx.WellFormed (w.ctx.update o.alloc o') := by
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · apply Ctx.update_covered
      · exact (Owner.retagLeaf?_covered hret).mpr (hwf.1.1.1 o hmem)
      · intro x hx _; exact hwf.1.1.1 x hx
    · exact Ctx.update_nodup ho'alloc hwf.1.1.2
    · exact Ctx.update_wellFormed_owners
        (Owner.retagLeaf?_wellFormed hret (hwf.1.2.1 o hmem))
        (fun x hx _ => hwf.1.2.1 x hx)
    · exact Ctx.update_ids_nodup_of_sub (C := w.ctx) (a := o.alloc) (o := o) (o' := o')
        hwf.1.1 hmem rfl hwf.1.2.2 ho'nd (Owner.retagLeaf?_ids_sub hret) hnewCids
  have hfun : (w.ctx.update o.alloc o').Functional :=
    Ctx.update_functional ho'alloc hwf.1.1.2
  have hfa : w.ctx.findOwner? o.alloc = some o := by simpa [hoa] using hfind
  have hst : ({ w with ctx := w.ctx.update o.alloc o' } : World).StorageMatches :=
    World.update_storage hwf hfa ho'alloc ho'len
  refine ⟨?_, ?_, ?_⟩
  · exact hctxwf
  · exact hfun
  · exact hst

/-- A borrow preserves the issuance history. -/
theorem Ctx.historyOK_beginBorrowNext {C : Ctx} {a : AllocId} {o o' : Owner}
    {c : Leaf} {lender borrower : CapId} {loanId : LoanId}
    (hh : C.HistoryOK) (hsub : ∀ x ∈ o'.ids, x ∈ C.ids ∨ x = borrower)
    (hfresh : borrower ∉ C.issued) :
    (C.beginBorrowNext a o o' c lender borrower loanId).HistoryOK := by
  refine ⟨?_, ?_⟩
  · rw [Ctx.beginBorrowNext_issued]
    exact List.nodup_cons.mpr ⟨hfresh, hh.1⟩
  · intro x hx
    have hx' : x ∈ (C.update o.alloc o').ids := by
      simpa using (hx : x ∈ (C.beginBorrowNext a o o' c lender borrower loanId).ids)
    rcases Ctx.ids_update_sub (C := C) (a := o.alloc) (o' := o') x hx' with hold | hnew
    · exact List.mem_cons_of_mem _ (hh.2 x hold)
    · rcases hsub x hnew with hold | rfl
      · exact List.mem_cons_of_mem _ (hh.2 x hold)
      · exact List.mem_cons_self ..

/-- A return preserves the issuance history. -/
theorem Ctx.historyOK_endBorrowNext {C : Ctx} {o o' : Owner} {loan : Loan}
    (hh : C.HistoryOK) (hsub : ∀ x ∈ o'.ids, x ∈ C.ids ∨ x = loan.lender)
    (hissued : loan.lender ∈ C.issued) :
    (C.endBorrowNext o o' loan).HistoryOK := by
  refine ⟨?_, ?_⟩
  · rw [Ctx.endBorrowNext_issued]
    exact hh.1
  · intro x hx
    have hx' : x ∈ (C.update o.alloc o').ids := by
      simpa using (hx : x ∈ (C.endBorrowNext o o' loan).ids)
    rcases Ctx.ids_update_sub (C := C) (a := o.alloc) (o' := o') x hx' with hold | hnew
    · exact hh.2 x hold
    · rcases hsub x hnew with hold | rfl
      · exact hh.2 x hold
      · exact hissued

/-- A borrow preserves the issuance history. -/
theorem historyOK_beginBorrow {w w' : World} {a : AllocId} {lender borrower : CapId}
    {loanId : LoanId} (hw : w.beginBorrowChecked a lender borrower loanId = .ok w')
    (hh : Ctx.HistoryOK w.ctx) : Ctx.HistoryOK w'.ctx := by
  obtain ⟨C, hC, hw'⟩ := beginBorrowChecked_sound hw
  obtain ⟨o, o', c, hfind, hretag, hissued, _hroot, _hloan, _hlive, hCeq⟩ :=
    Ctx.beginBorrow?_sound hC
  subst hCeq
  subst hw'
  have hrect : o.retagLeaf? lender borrower = some o' := Owner.retagLeafFind?_fst hretag
  have hsub : ∀ x ∈ o'.ids, x ∈ w.ctx.ids ∨ x = borrower := by
    intro x hx
    rcases Owner.retagLeaf?_ids_sub hrect x hx with h | h
    · exact Or.inl (Ctx.owner_ids_sub_ids (List.mem_of_find?_eq_some hfind) x h)
    · exact Or.inr h
  exact Ctx.historyOK_beginBorrowNext hh hsub hissued

/-- A return preserves the issuance history. -/
theorem historyOK_endBorrow {w w' : World} {a : AllocId} {loanId : LoanId}
    (hw : w.endBorrowChecked a loanId = .ok w')
    (hh : Ctx.HistoryOK w.ctx) (hlr : Ctx.LoansReady w.ctx) :
    Ctx.HistoryOK w'.ctx := by
  obtain ⟨C, hC, hw'⟩ := endBorrowChecked_sound hw
  obtain ⟨loan, o, o', hloan, hfind, hret, _hsuc, _hdesc, hCeq⟩ :=
    Ctx.endBorrow?_sound hC
  subst hCeq
  subst hw'
  have hloanmem : loan ∈ w.ctx.loans.loans := List.mem_of_find?_eq_some hloan
  have hsub : ∀ x ∈ o'.ids, x ∈ w.ctx.ids ∨ x = loan.lender := by
    intro x hx
    rcases Owner.retagLeaf?_ids_sub hret x hx with h | h
    · exact Or.inl (Ctx.owner_ids_sub_ids (List.mem_of_find?_eq_some hfind) x h)
    · exact Or.inr h
  exact Ctx.historyOK_endBorrowNext hh hsub (hlr.2.2 loan hloanmem)

/-- A write leaves the context unchanged, so the history is untouched. -/
theorem historyOK_write {w w' : World} {a : AllocId} {id : CapId} {i : Nat}
    {v : UInt8} (hw : w.writeChecked a id i v = .ok w') (hh : Ctx.HistoryOK w.ctx) :
    Ctx.HistoryOK w'.ctx := by
  obtain ⟨_, _, _, _, _, _, _, hctx, _⟩ := World.writeChecked_sound hw
  rw [hctx]
  exact hh

/-- A write leaves the loans untouched, so loan readiness is unchanged. -/
theorem loansReady_writeChecked {w w' : World} {a : AllocId} {id : CapId} {i : Nat}
    {v : UInt8} (hw : w.writeChecked a id i v = .ok w')
    (hlr : Ctx.LoansReady w.ctx) : Ctx.LoansReady w'.ctx := by
  obtain ⟨_, _, _, _, _, _, _, hctx, _⟩ := World.writeChecked_sound hw
  rw [hctx]
  exact hlr

/-- A borrow preserves loan readiness. -/
theorem loansReady_beginBorrow {w w' : World} {a : AllocId} {lender borrower : CapId}
    {loanId : LoanId} (hw : w.beginBorrowChecked a lender borrower loanId = .ok w')
    (hinv : w.CommandInv) : Ctx.LoansReady w'.ctx := by
  obtain ⟨hwf, hh, hlr⟩ := hinv
  obtain ⟨C, hC, hw'⟩ := beginBorrowChecked_sound hw
  obtain ⟨o, o', c, hfind, hretag, hissued, _hroot, _hloan, _hlive, hCeq⟩ :=
    Ctx.beginBorrow?_sound hC
  subst hCeq
  subst hw'
  have hmem : o ∈ w.ctx.owners := List.mem_of_find?_eq_some hfind
  have hoa : o.alloc = a := by
    have := List.find?_some (p := fun x : Owner => decide (x.alloc = a))
      (by simpa [Ctx.findOwner?] using hfind)
    simpa using this
  have hrect : o.retagLeaf? lender borrower = some o' := Owner.retagLeafFind?_fst hretag
  obtain ⟨hc, _hact, _hfresh⟩ := Owner.retagLeafFind?_leaf hretag
  have hoid : o.ids.Nodup := Ctx.owner_ids_nodup hwf.1.2.2 hmem
  have hlendid_owner : lender ∈ o.ids :=
    List.mem_cons_of_mem o.disposal (Tree.mem_ids_of_find? hc)
  have hlendid : lender ∈ w.ctx.ids :=
    Ctx.owner_ids_sub_ids hmem lender hlendid_owner
  have hlendiss : lender ∈ w.ctx.issued := hh.2 lender hlendid
  have hnewCids : borrower ∉ w.ctx.ids := by
    intro hm; exact hissued (hh.2 borrower hm)
  have hdisp : borrower ≠ o.disposal := by
    intro heq
    have hmemid : o.disposal ∈ w.ctx.ids :=
      List.mem_flatMap.mpr ⟨o, hmem, by simp [Owner.ids]⟩
    exact hnewCids (heq ▸ hmemid)
  have ho'nd : o'.ids.Nodup := Owner.retagLeaf?_ids_nodup hrect hoid hdisp
  have hsub : ∀ x ∈ o'.ids, x ∈ o.ids ∨ x = borrower := Owner.retagLeaf?_ids_sub hrect
  have hnewDetach : lender ∉ (w.ctx.update o.alloc o').ids :=
    Ctx.not_mem_ids_update_of_owner hwf.1.1 hwf.1.2.2 hmem rfl hlendid_owner
      (Owner.retagLeaf?_detached hrect hoid)
  have holdDetach : ∀ m ∈ w.ctx.loans.loans,
      m.lender ∉ (w.ctx.update o.alloc o').ids := by
    intro m hm hmemx
    rcases (flatMap_update_ids_nodup_of_sub w.ctx.owners o.alloc o o' borrower
      hwf.1.1.2 hwf.1.2.2 hmem rfl ho'nd hsub hnewCids).2 m.lender hmemx with
      hold | heq
    · exact hlr.2.1 m hm hold
    · exact hissued (heq ▸ hlr.2.2 m hm)
  unfold Ctx.LoansReady
  refine ⟨?_, ?_, ?_⟩
  · -- lender names distinct after appending the new loan
    simp only [Ctx.beginBorrowNext, List.map_append]
    rw [List.nodup_append]
    refine ⟨hlr.1, by simp, ?_⟩
    intro y hy z hz hyz
    have hz' : z = lender := by simpa using hz
    rw [hz'] at hyz
    rcases List.mem_map.mp hy with ⟨m, hm, rfl⟩
    exact hlr.2.1 m hm (hyz ▸ hlendid)
  · -- every lender detached
    intro l hl
    simp only [Ctx.beginBorrowNext] at hl
    simp only [List.mem_append] at hl
    rcases hl with hl | hl
    · exact holdDetach l hl
    · simp only [List.mem_singleton] at hl
      subst hl
      simpa using hnewDetach
  · -- every lender issued
    intro l hl
    simp only [Ctx.beginBorrowNext] at hl
    simp only [List.mem_append] at hl
    rcases hl with hl | hl
    · simpa using (List.mem_cons_of_mem _ (hlr.2.2 l hl))
    · simp only [List.mem_singleton] at hl
      subst hl
      simpa using (List.mem_cons_of_mem _ hlendiss)

/-- A return preserves loan readiness. -/
theorem loansReady_endBorrow {w w' : World} {a : AllocId} {loanId : LoanId}
    (hw : w.endBorrowChecked a loanId = .ok w')
    (hlr : Ctx.LoansReady w.ctx) : Ctx.LoansReady w'.ctx := by
  obtain ⟨C, hC, hw'⟩ := endBorrowChecked_sound hw
  obtain ⟨loan, o, o', hloan, hfind, hret, _hsuc, _hdesc, hCeq⟩ :=
    Ctx.endBorrow?_sound hC
  subst hCeq
  subst hw'
  have hret' : o.retagLeaf? loan.borrower loan.lender = some o' := hret
  have hsub : ∀ x ∈ o'.ids, x ∈ o.ids ∨ x = loan.lender :=
    Owner.retagLeaf?_ids_sub hret'
  unfold Ctx.LoansReady
  refine ⟨?_, ?_, ?_⟩
  · -- lender names distinct: a filtered sublist of the old list
    simp only [Ctx.endBorrowNext, LoanCtx.endBorrowBookkeeping]
    exact List.Sublist.nodup
      (List.Sublist.map (fun m => m.lender)
        (List.filter_sublist (l := w.ctx.loans.loans)
          (p := fun m => m.id ≠ loan.id))) hlr.1
  · -- every remaining lender detached
    intro l hl
    simp only [Ctx.endBorrowNext] at hl
    simp only [LoanCtx.endBorrowBookkeeping, List.mem_filter] at hl
    obtain ⟨hlorig, hlid⟩ := hl
    intro hmem
    have hmem' : l.lender ∈ (w.ctx.update o.alloc o').ids := by
      simpa using hmem
    rcases Ctx.ids_update_sub (C := w.ctx) (a := o.alloc) (o' := o') l.lender hmem' with
      hold | hnew
    · exact hlr.2.1 l hlorig hold
    · rcases hsub l.lender hnew with hold | heq
      · exact hlr.2.1 l hlorig (Ctx.owner_ids_sub_ids
          (List.mem_of_find?_eq_some hfind) l.lender hold)
      · -- two remaining loans share a lender
        have hlender : l.lender = loan.lender := heq
        have hneq : l ≠ loan := by
          intro hEq
          subst hEq
          simpa using hlid
        exact hneq (List.nodup_map_inj hlr.1 l hlorig loan
          (List.mem_of_find?_eq_some hloan) hlender)
  · -- issued is unchanged
    intro l hl
    simp only [Ctx.endBorrowNext] at hl
    simp only [LoanCtx.endBorrowBookkeeping, List.mem_filter] at hl
    simpa using hlr.2.2 l hl.1

end World

/-- The checker is the interpreter: an accepted program returns the world it
executed. -/
def checkWorld : World → List UCmd → Except String World
  | w, [] => .ok w
  | w, .nop :: cs => checkWorld w cs
  | w, .write a id i v :: cs =>
    match w.writeChecked a id i v with
    | .ok w' => checkWorld w' cs
    | .error e => .error e
  | w, .splitAt a id id1 id2 k :: cs =>
    match w.splitAtChecked a id id1 id2 k with
    | .ok w' => checkWorld w' cs
    | .error e => .error e
  | w, .splitFraction a id id1 id2 q1 q2 :: cs =>
    if hq : 0 < q1 ∧ 0 < q2 then
      match w.splitFractionChecked a id id1 id2 q1 q2 hq.1 hq.2 with
      | .ok w' => checkWorld w' cs
      | .error e => .error e
    else .error "split: non-positive share"
  | w, .join a node newId :: cs =>
    match w.joinChecked a node newId with
    | .ok w' => checkWorld w' cs
    | .error e => .error e
  | w, .free a d :: cs =>
    match w.freeChecked a d with
    | .ok w' => checkWorld w' cs
    | .error e => .error e
  | w, .alloc n rootId disposal :: cs =>
    if hpos : 0 < w.ctx.D then
      match w.allocChecked n rootId disposal hpos with
      | .ok w' => checkWorld w' cs
      | .error e => .error e
    else .error "alloc: non-positive denominator"
  | w, .beginBorrow a lender borrower loanId :: cs =>
    match w.beginBorrowChecked a lender borrower loanId with
    | .ok w' => checkWorld w' cs
    | .error e => .error e
  | w, .endBorrow a loanId :: cs =>
    match w.endBorrowChecked a loanId with
    | .ok w' => checkWorld w' cs
    | .error e => .error e

/-- An accepted execution preserves the command carrier: well-formedness, the
issuance history and loan readiness. -/
theorem checkWorld_commandInv : ∀ (w w' : World) (cs : List UCmd),
    checkWorld w cs = .ok w' → w.CommandInv → w'.CommandInv := by
  intro w w' cs
  induction cs generalizing w with
  | nil =>
    intro h hinv
    simp [checkWorld] at h
    cases h
    exact hinv
  | cons c cs ih =>
    intro h hinv
    obtain ⟨hwf, hh, hlr⟩ := hinv
    cases c with
    | nop =>
      simp [checkWorld] at h
      exact ih w h ⟨hwf, hh, hlr⟩
    | write a id i v =>
      cases hw : w.writeChecked a id i v with
      | error e => simp [checkWorld, hw] at h
      | ok w'' =>
        simp [checkWorld, hw] at h
        exact ih w'' h ⟨World.writeChecked_wf hw hwf,
          World.historyOK_write hw hh, World.loansReady_writeChecked hw hlr⟩
    | splitAt a id id1 id2 k =>
      cases hw : w.splitAtChecked a id id1 id2 k with
      | error e => simp [checkWorld, hw] at h
      | ok w'' =>
        simp [checkWorld, hw] at h
        exact ih w'' h ⟨World.splitAtChecked_wf hw hwf,
          World.historyOK_splitAtChecked hw hwf hh,
          World.loansReady_splitAtChecked hw hwf hlr⟩
    | splitFraction a id id1 id2 q1 q2 =>
      by_cases hq : 0 < q1 ∧ 0 < q2
      · cases hw : w.splitFractionChecked a id id1 id2 q1 q2 hq.1 hq.2 with
        | error e => simp [checkWorld, hq, hw] at h
        | ok w'' =>
          simp [checkWorld, hq, hw] at h
          exact ih w'' h ⟨World.splitFractionChecked_wf hw hwf,
            World.historyOK_splitFractionChecked hw hwf hh,
            World.loansReady_splitFractionChecked hw hwf hlr⟩
      · simp [checkWorld, hq] at h
    | join a node newId =>
      cases hw : w.joinChecked a node newId with
      | error e => simp [checkWorld, hw] at h
      | ok w'' =>
        simp [checkWorld, hw] at h
        exact ih w'' h ⟨World.joinChecked_wf hw hwf,
          World.historyOK_joinChecked hw hh, World.loansReady_joinChecked hw hlr⟩
    | free a d =>
      cases hw : w.freeChecked a d with
      | error e => simp [checkWorld, hw] at h
      | ok w'' =>
        simp [checkWorld, hw] at h
        exact ih w'' h ⟨World.freeChecked_wf hw hwf,
          World.historyOK_freeChecked hw hh, World.loansReady_freeChecked hw hlr⟩
    | alloc n rootId disposal =>
      by_cases hpos : 0 < w.ctx.D
      · cases hw : w.allocChecked n rootId disposal hpos with
        | error e => simp [checkWorld, hpos, hw] at h
        | ok w'' =>
          simp [checkWorld, hpos, hw] at h
          exact ih w'' h ⟨World.allocChecked_wf hw hwf,
            World.historyOK_allocChecked hw hh, World.loansReady_allocChecked hw hlr⟩
      · simp [checkWorld, hpos] at h
    | beginBorrow a lender borrower loanId =>
      cases hw : w.beginBorrowChecked a lender borrower loanId with
      | error e => simp [checkWorld, hw] at h
      | ok w'' =>
        simp [checkWorld, hw] at h
        exact ih w'' h ⟨World.beginBorrowChecked_wf hw ⟨hwf, hh, hlr⟩,
          World.historyOK_beginBorrow hw hh,
          World.loansReady_beginBorrow hw ⟨hwf, hh, hlr⟩⟩
    | endBorrow a loanId =>
      cases hw : w.endBorrowChecked a loanId with
      | error e => simp [checkWorld, hw] at h
      | ok w'' =>
        simp [checkWorld, hw] at h
        exact ih w'' h ⟨World.endBorrowChecked_wf hw ⟨hwf, hh, hlr⟩,
          World.historyOK_endBorrow hw hh hlr,
          World.loansReady_endBorrow hw hlr⟩

/-- An accepted execution preserves the world invariant from the command carrier. -/
theorem checkWorld_wf : ∀ (w w' : World) (cs : List UCmd),
    checkWorld w cs = .ok w' → w.CommandInv → w'.WellFormed := by
  intro w w' cs h hinv
  exact (checkWorld_commandInv w w' cs h hinv).1

/-- An accepted execution preserves the world relation from the command carrier. -/
theorem checkWorld_rel : ∀ (w w' : World) (cs : List UCmd),
    checkWorld w cs = .ok w' → w.CommandInv → w'.Rel := by
  intro w w' cs h hinv
  exact World.rel_of_wellFormed (checkWorld_wf w w' cs h hinv)

/-- The concrete owner: one 64-byte whole-share leaf. -/
def uOwner : Owner := Owner.init ⟨0⟩ 64 64 (by decide) ⟨1⟩ ⟨2⟩

/-- The concrete world: one 64-byte owner and its backend. -/
def uWorld : World :=
  { ctx := { owners := [uOwner], D := 64, nextAlloc := 1, issued := [⟨2⟩, ⟨1⟩], loans := .rootOnly },
    heaps := fun a => if a = ⟨0⟩ then some (Backend.empty 64) else none,
}

/-- The concrete 64-byte world is well formed. -/
theorem uWorld_wf : uWorld.WellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · -- Ctx.WellFormed
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro o ho
        simp [uWorld] at ho
        rcases ho with rfl
        exact Owner.init_covered ⟨0⟩ 64 64 (by decide) ⟨1⟩ ⟨2⟩
      · simp [uWorld]
    · intro o ho
      simp [uWorld] at ho
      rcases ho with rfl
      exact Owner.init_wellFormed ⟨0⟩ 64 64 (by decide) ⟨1⟩ ⟨2⟩
    · decide
  · exact Ctx.functional_of_nodup (by simp [uWorld])
  · intro a o hfind
    unfold uWorld at hfind
    simp [Ctx.findOwner?, uOwner] at hfind
    have ho : o = uOwner := hfind.2.symm
    have ha : a = uOwner.alloc := hfind.1.symm
    subst ha
    subst o
    exact ⟨Backend.empty 64, rfl, rfl⟩

theorem uWorld_rel : uWorld.Rel := by

  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro o ho
      simp [uWorld] at ho
      rcases ho with rfl
      exact Owner.init_covered ⟨0⟩ 64 64 (by decide) ⟨1⟩ ⟨2⟩
    · simp [uWorld]
  · intro o ho
    simp [uWorld] at ho
    rcases ho with rfl
    refine ⟨Backend.empty 64, ?_, ?_⟩
    · rfl
    · rfl

/-- The concrete world's history is exactly its live identifier set. -/
theorem uWorld_historyOK : Ctx.HistoryOK uWorld.ctx := by
  refine ⟨by decide, ?_⟩
  intro c hc
  simp [uWorld, uOwner, Ctx.ids, Owner.ids, Owner.init, Tree.ids] at hc ⊢
  rcases hc with rfl | rfl
  · simp
  · simp

/-- The concrete world satisfies the command carrier. -/
theorem uWorld_commandInv : uWorld.CommandInv :=
  ⟨uWorld_wf, uWorld_historyOK, Ctx.loansReady_of_loans_nil rfl⟩

/-- Fill `n` bytes from `lo` with `v` through one capability. -/
def fillCmds (id : CapId) (lo n : Nat) (v : UInt8) : List UCmd :=
  (List.range n).map (fun k => UCmd.write ⟨0⟩ id (lo + k) v)

def uProgram : List UCmd := fillCmds ⟨1⟩ 0 32 1 ++ fillCmds ⟨1⟩ 32 32 2

def uRun : Option (List UInt8) :=
  match checkWorld uWorld uProgram with
  | .ok w => (w.heaps ⟨0⟩).map (fun b => b.buf)
  | .error _ => none

theorem uRun_snapshot :
    uRun = some (List.replicate 32 (1 : UInt8) ++ List.replicate 32 (2 : UInt8)) := by
  decide
/-- The concrete program is accepted. -/
theorem uProgram_ok : (checkWorld uWorld uProgram).isOk = true := by
  decide
theorem uProgram_rel : ∃ w, checkWorld uWorld uProgram = .ok w ∧ w.Rel := by
  have hok : (checkWorld uWorld uProgram).isOk = true := by decide
  cases h : checkWorld uWorld uProgram with
  | error e =>
    have hfalse : (checkWorld uWorld uProgram).isOk = false := by
      rw [h]
      rfl
    rw [hfalse] at hok
    cases hok
  | ok w => exact ⟨w, rfl, checkWorld_rel uWorld w uProgram h uWorld_commandInv⟩

/-- A lifecycle program through the unified route: allocate a fresh 4-byte
owner, write one byte, split it spatially, write the left half, split it
fractionally, join the halves, write again, then dispose it. The pre-existing
64-byte owner is untouched. -/
def uLifecycle : List UCmd :=
  [ .alloc 4 ⟨3⟩ ⟨4⟩,
    .write ⟨1⟩ ⟨3⟩ 0 7,
    .splitAt ⟨1⟩ ⟨3⟩ ⟨5⟩ ⟨6⟩ 2,
    .write ⟨1⟩ ⟨5⟩ 0 8,
    .splitFraction ⟨1⟩ ⟨5⟩ ⟨7⟩ ⟨8⟩ 32 32,
    .join ⟨1⟩ ⟨7⟩ ⟨9⟩,
    .write ⟨1⟩ ⟨9⟩ 1 9,
    .free ⟨1⟩ ⟨4⟩ ]

/-- The lifecycle program is accepted and preserves the pre-existing snapshot. -/
def uLifecycleSnapshot : Option (Option (List UInt8)) :=
  match checkWorld uWorld uLifecycle with
  | .ok w => some ((w.heaps ⟨0⟩).map (fun b => b.buf))
  | .error _ => none

/-- The lifecycle leaves the pre-existing 64-byte backend at its initial value:
the commands act only on the freshly allocated owner. -/
theorem uLifecycle_snapshot :
    uLifecycleSnapshot = some (some (List.replicate 64 (0 : UInt8))) := by
  decide

/-- The lifecycle program is accepted. -/
theorem uLifecycle_ok : (checkWorld uWorld uLifecycle).isOk = true := by
  decide

/-- The lifecycle program's final world is well formed. -/
theorem uLifecycle_wf : ∃ w, checkWorld uWorld uLifecycle = .ok w ∧ w.WellFormed := by
  have hok : (checkWorld uWorld uLifecycle).isOk = true := uLifecycle_ok
  cases h : checkWorld uWorld uLifecycle with
  | error e =>
    rw [h] at hok
    cases hok
  | ok w => exact ⟨w, rfl, checkWorld_wf uWorld w uLifecycle h uWorld_commandInv⟩

/-- The loan prefix: allocate a fresh 4-byte owner and write one byte through
its root capability. -/
def uLoanPre : List UCmd := [.alloc 4 ⟨3⟩ ⟨4⟩, .write ⟨1⟩ ⟨3⟩ 0 7]

/-- Positive control: the write at index 1 is accepted before the loan
begins. -/
theorem uLoan_write_before :
    (checkWorld uWorld (uLoanPre ++ [.write ⟨1⟩ ⟨3⟩ 1 9])).isOk = true := by
  decide

/-- While the loan is outstanding the lender's leaf has been retagged to the
borrower, so the same write through it is refused. -/
theorem uLoan_borrower_write_refused :
    (checkWorld uWorld
      (uLoanPre ++ [.beginBorrow ⟨1⟩ ⟨3⟩ ⟨5⟩ ⟨0⟩, .write ⟨1⟩ ⟨3⟩ 1 9])).isOk = false := by
  decide

/-- The loan run: allocate and write, begin a distinct-borrower borrow on the
root capability, end it, write again — accepted now that the lender is
restored — and dispose. -/
def uLoanRun : List UCmd :=
  uLoanPre ++
    [.beginBorrow ⟨1⟩ ⟨3⟩ ⟨5⟩ ⟨0⟩, .endBorrow ⟨1⟩ ⟨0⟩, .write ⟨1⟩ ⟨3⟩ 1 9,
     .free ⟨1⟩ ⟨4⟩]

/-- The loan run is accepted. -/
theorem uLoanRun_ok : (checkWorld uWorld uLoanRun).isOk = true := by
  decide

/-- The loan run's final world is well formed. -/
theorem uLoanRun_wf : ∃ w, checkWorld uWorld uLoanRun = .ok w ∧ w.WellFormed := by
  have hok : (checkWorld uWorld uLoanRun).isOk = true := uLoanRun_ok
  cases h : checkWorld uWorld uLoanRun with
  | error e =>
    rw [h] at hok
    cases hok
  | ok w => exact ⟨w, rfl, checkWorld_wf uWorld w uLoanRun h uWorld_commandInv⟩

/-- The loan run's snapshot of the pre-existing 64-byte backend. -/
def uLoanSnapshot : Option (Option (List UInt8)) :=
  match checkWorld uWorld uLoanRun with
  | .ok w => some ((w.heaps ⟨0⟩).map (fun b => b.buf))
  | .error _ => none

/-- The loan run leaves the pre-existing 64-byte backend at its initial value:
the commands act only on the freshly allocated owner. -/
theorem uLoan_snapshot :
    uLoanSnapshot = some (some (List.replicate 64 (0 : UInt8))) := by
  decide

end Cap
