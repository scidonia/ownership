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
