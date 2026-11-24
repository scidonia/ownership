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

#guard (match uWorld.beginBorrowChecked ⟨0⟩ ⟨1⟩ ⟨3⟩ ⟨9⟩ with
  | .error _ => false
  | .ok w => (w.freeChecked ⟨0⟩ ⟨2⟩).isOk = false)

#guard (match borrowed.endBorrowChecked ⟨0⟩ ⟨9⟩ with
  | .error _ => false
  | .ok w => (w.ctx.loans.findLoan? ⟨9⟩).isNone)

#guard (match borrowed.endBorrowChecked ⟨0⟩ ⟨9⟩ with
  | .error _ => false
  | .ok w => (w.freeChecked ⟨0⟩ ⟨2⟩).isOk)

#guard (match borrowed.endBorrowChecked ⟨0⟩ ⟨9⟩ with
  | .error _ => false
  | .ok w => (w.beginBorrowChecked ⟨0⟩ ⟨1⟩ ⟨3⟩ ⟨11⟩).isOk = false)

private def innerBorrowed : World :=
  match borrowed.beginBorrowChecked ⟨0⟩ ⟨3⟩ ⟨4⟩ ⟨10⟩ with
  | .ok w => w
  | .error _ => uWorld

#guard (match borrowed.beginBorrowChecked ⟨0⟩ ⟨3⟩ ⟨4⟩ ⟨10⟩ with
  | .error _ => false
  | .ok w => (w.ctx.loans.loans.length == 2) && (w.writeChecked ⟨0⟩ ⟨4⟩ 0 9).isOk)

#guard (match borrowed.beginBorrowChecked ⟨0⟩ ⟨3⟩ ⟨4⟩ ⟨10⟩ with
  | .error _ => false
  | .ok w => (w.endBorrowChecked ⟨0⟩ ⟨9⟩).isOk = false)

#guard (match borrowed.beginBorrowChecked ⟨0⟩ ⟨3⟩ ⟨4⟩ ⟨10⟩ with
  | .error _ => false
  | .ok w =>
      (match w.endBorrowChecked ⟨0⟩ ⟨10⟩ with
       | .error _ => false
       | .ok w1 => (w1.endBorrowChecked ⟨0⟩ ⟨9⟩).isOk))

#guard (match uWorld.beginBorrowChecked ⟨0⟩ ⟨1⟩ ⟨3⟩ ⟨9⟩ with
  | .error _ => false
  | .ok w => (w.splitAtChecked ⟨0⟩ ⟨3⟩ ⟨5⟩ ⟨6⟩ 32).isOk = false)

#guard (match borrowed.endBorrowChecked ⟨0⟩ ⟨9⟩ with
  | .error _ => false
  | .ok w => (w.splitAtChecked ⟨0⟩ ⟨1⟩ ⟨5⟩ ⟨6⟩ 32).isOk)
