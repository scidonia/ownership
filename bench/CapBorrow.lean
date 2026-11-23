import Cap.Borrow

open Cap

/-!
Executable controls for the distinct-borrower retag model. The lender identity is
unavailable while the borrower is live, and the original lender is restored after
the loan ends.
-/

private def borrowed : World :=
  match uWorld.beginBorrowChecked ⟨0⟩ ⟨1⟩ ⟨3⟩ ⟨9⟩ with
  | .ok w => w
  | .error _ => uWorld

private def returned : World :=
  match borrowed.endBorrowChecked ⟨0⟩ ⟨9⟩ with
  | .ok w => w
  | .error _ => uWorld

#guard (uWorld.beginBorrowChecked ⟨0⟩ ⟨1⟩ ⟨3⟩ ⟨9⟩).isOk
#guard (match uWorld.beginBorrowChecked ⟨0⟩ ⟨1⟩ ⟨3⟩ ⟨9⟩ with
  | .ok w => (w.writeChecked ⟨0⟩ ⟨3⟩ 0 7).isOk
  | .error _ => false)
#guard (match uWorld.beginBorrowChecked ⟨0⟩ ⟨1⟩ ⟨3⟩ ⟨9⟩ with
  | .ok w => (w.writeChecked ⟨0⟩ ⟨1⟩ 0 7).isOk
  | .error _ => false) = false

#guard (borrowed.ctx.loans.findLoan? ⟨9⟩).isSome
#guard borrowed.ctx.loans.loans.length = 1
#guard (borrowed.endBorrowChecked ⟨0⟩ ⟨9⟩).isOk
#guard (match borrowed.endBorrowChecked ⟨0⟩ ⟨9⟩ with
  | .ok w => (w.writeChecked ⟨0⟩ ⟨1⟩ 0 7).isOk
  | .error _ => false)
#guard (match borrowed.endBorrowChecked ⟨0⟩ ⟨9⟩ with
  | .ok w => (w.writeChecked ⟨0⟩ ⟨3⟩ 0 7).isOk
  | .error _ => false) = false
