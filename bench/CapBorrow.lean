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

#guard (match uWorld.splitFractionChecked ⟨0⟩ ⟨1⟩ ⟨3⟩ ⟨4⟩ 32 32 (by decide) (by decide) with
  | .error _ => false
  | .ok w1 =>
    match w1.beginBorrowChecked ⟨0⟩ ⟨3⟩ ⟨5⟩ ⟨9⟩ with
    | .error _ => false
    | .ok w2 => (w2.joinChecked ⟨0⟩ ⟨3⟩ ⟨6⟩).isOk = false)

#guard (match uWorld.splitFractionChecked ⟨0⟩ ⟨1⟩ ⟨3⟩ ⟨4⟩ 32 32 (by decide) (by decide) with
  | .error _ => false
  | .ok w1 =>
    match w1.beginBorrowChecked ⟨0⟩ ⟨3⟩ ⟨5⟩ ⟨9⟩ with
    | .error _ => false
    | .ok w2 =>
      match w2.endBorrowChecked ⟨0⟩ ⟨9⟩ with
      | .error _ => false
      | .ok w3 => (w3.joinChecked ⟨0⟩ ⟨3⟩ ⟨6⟩).isOk)

/-- The `3 → 4` edge of the cycle fixture. -/
private def cycleOuter : Loan :=
  { id := ⟨9⟩, alloc := ⟨0⟩, base := ⟨3⟩, lender := ⟨3⟩, borrower := ⟨4⟩,
    lifetime := ⟨1⟩, lo := 0, hi := 64, q := 64, ceiling := .readWrite }

/-- The `4 → 3` edge of the cycle fixture. -/
private def cycleInner : Loan :=
  { id := ⟨10⟩, alloc := ⟨0⟩, base := ⟨3⟩, lender := ⟨4⟩, borrower := ⟨3⟩,
    lifetime := ⟨2⟩, lo := 0, hi := 64, q := 64, ceiling := .readWrite }

private def cyclicWorld : World :=
  { uWorld with
    ctx := { uWorld.ctx with
      issued := [⟨3⟩, ⟨4⟩],
      loans := { uWorld.ctx.loans with
        lifetimes := [{ id := ⟨1⟩, parent := none, state := .live },
                      { id := ⟨2⟩, parent := some ⟨1⟩, state := .live }],
        loans := [cycleOuter, cycleInner],
        nextLifetime := 3 } } }

/-- A cycle `3 → 4 → 3` is rejected by the acyclicity conjunct. -/
example : ¬ World.BorrowOK cyclicWorld := by
  intro h
  have hcy := h.2.2.2.2.2.2.2.2.2.2
  have htrue : BorrowReaches cyclicWorld.ctx.loans.loans
      (cyclicWorld.ctx.loans.loans.length + 1) cycleOuter.lender cycleOuter.lender = true := by
    native_decide
  have hfalse := hcy cycleOuter (by simp [cyclicWorld, cycleOuter, cycleInner])
  rw [htrue] at hfalse
  cases hfalse
