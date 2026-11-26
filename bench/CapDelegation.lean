import Cap.Borrow

open Cap

/-!
Executable controls for distinct-borrower delegation.

Each negative control is paired with the affirmative control named beside it, on
the same fixture and through the same detector, so a refusal is never a
wholesale rejection of the fixture. The fixtures are the accepted worlds of the
nested lifecycle: `b1` borrows from the root, `b2` reborrows from the borrower,
`r2` and `r1` return them in order, `f` disposes the allocation, and `sf`,
`sfb`, `sfr` run the same borrow through a fractional split.
-/

/-- One borrow from the root capability `⟨1⟩` to the fresh borrower `⟨3⟩`. -/
private def b1 : World :=
  match uWorld.beginBorrowChecked ⟨0⟩ ⟨1⟩ ⟨3⟩ ⟨9⟩ with
  | .ok w => w
  | .error _ => uWorld

/-- A reborrow from the borrowed holder `⟨3⟩` to the fresh borrower `⟨4⟩`. -/
private def b2 : World :=
  match b1.beginBorrowChecked ⟨0⟩ ⟨3⟩ ⟨4⟩ ⟨10⟩ with
  | .ok w => w
  | .error _ => b1

/-- The world after returning the inner loan. -/
private def r2 : World :=
  match b2.endBorrowChecked ⟨0⟩ ⟨10⟩ with
  | .ok w => w
  | .error _ => b2

/-- The world after returning the outer loan. -/
private def r1 : World :=
  match r2.endBorrowChecked ⟨0⟩ ⟨9⟩ with
  | .ok w => w
  | .error _ => r2

/-- The world after disposing the allocation through its disposal capability. -/
private def f : World :=
  match r1.freeChecked ⟨0⟩ ⟨2⟩ with
  | .ok w => w
  | .error _ => r1

/-- The fractional split of the root leaf into the halves `⟨3⟩` and `⟨4⟩`. -/
private def sf : World :=
  match uWorld.splitFractionChecked ⟨0⟩ ⟨1⟩ ⟨3⟩ ⟨4⟩ 32 32 (by decide) (by decide) with
  | .ok w => w
  | .error _ => uWorld

/-- A borrow from the fractional half `⟨3⟩`. -/
private def sfb : World :=
  match sf.beginBorrowChecked ⟨0⟩ ⟨3⟩ ⟨5⟩ ⟨9⟩ with
  | .ok w => w
  | .error _ => sf

/-- The world after returning the fractional half's loan. -/
private def sfr : World :=
  match sfb.endBorrowChecked ⟨0⟩ ⟨9⟩ with
  | .ok w => w
  | .error _ => sfb

/-! ### Control 1–3: the borrow succeeds and hides the lender's leaf -/

/- Control 1: the borrow from the root capability is accepted. -/
#guard (uWorld.beginBorrowChecked ⟨0⟩ ⟨1⟩ ⟨3⟩ ⟨9⟩).isOk

/- Control 2: the write through the root is accepted before the borrow — the
affirmative control for control 3's detector. -/
#guard (uWorld.writeChecked ⟨0⟩ ⟨1⟩ 0 7).isOk

/- Control 3: the same write is refused while the borrower holds the retagged
leaf. -/
#guard (b1.writeChecked ⟨0⟩ ⟨1⟩ 0 7).isOk = false

/-! ### Control 4–5: only the active holder lends -/

/- Control 4: the unavailable lender `⟨1⟩` cannot lend. -/
#guard (b1.beginBorrowChecked ⟨0⟩ ⟨1⟩ ⟨4⟩ ⟨11⟩).isOk = false

/- Control 5: the active holder `⟨3⟩` can lend — the affirmative control for 4. -/
#guard (b1.beginBorrowChecked ⟨0⟩ ⟨3⟩ ⟨4⟩ ⟨10⟩).isOk

/-! ### Control 6–7: authority is terminal -/

/- Control 6: the terminal borrower may write. -/
#guard (b2.writeChecked ⟨0⟩ ⟨4⟩ 0 9).isOk

/- Control 7: the delegated lender may not — the affirmative control is 6. -/
#guard (b2.writeChecked ⟨0⟩ ⟨3⟩ 0 9).isOk = false

/-! ### Control 8–10: returns happen innermost first -/

/- Control 8: the outer loan cannot be returned while the inner one is live. -/
#guard (b2.endBorrowChecked ⟨0⟩ ⟨9⟩).isOk = false

/- Control 9: the inner loan returns, restoring `⟨3⟩` — the affirmative control
for 8. -/
#guard (b2.endBorrowChecked ⟨0⟩ ⟨10⟩).isOk
#guard (r2.writeChecked ⟨0⟩ ⟨3⟩ 0 9).isOk

/- Control 10: the outer loan then returns, restoring the root — the affirmative
control for 8's ordering. -/
#guard (r2.endBorrowChecked ⟨0⟩ ⟨9⟩).isOk
#guard (r1.writeChecked ⟨0⟩ ⟨1⟩ 0 9).isOk

/-! ### Control 11–13: disposal waits for the restoration -/

/- Control 11: disposal is refused while the loan is outstanding. -/
#guard (b1.freeChecked ⟨0⟩ ⟨2⟩).isOk = false

/- Control 12: disposal is accepted once both loans are returned — the
affirmative control for 11. -/
#guard (r1.freeChecked ⟨0⟩ ⟨2⟩).isOk

/- Control 13: the fixture is live while it refuses disposal: the borrower's
write is accepted, then the disposal is refused for the outstanding loan. -/
#guard (b1.writeChecked ⟨0⟩ ⟨3⟩ 0 7).isOk
#guard (b1.freeChecked ⟨0⟩ ⟨2⟩).isOk = false

/-! ### Control 14: a disposed allocation is gone -/

/- Control 14: the disposed world has no owner, so every old route is
refused... -/
#guard (f.writeChecked ⟨0⟩ ⟨1⟩ 0 7).isOk = false
#guard (f.writeChecked ⟨0⟩ ⟨3⟩ 0 7).isOk = false
#guard (f.freeChecked ⟨0⟩ ⟨2⟩).isOk = false

/-- ...and a fresh allocation accepts its own root, not the old name. -/
private def fresh : World :=
  match f.allocChecked 64 ⟨11⟩ ⟨12⟩ (by decide) with
  | .ok w => w
  | .error _ => f

#guard (f.allocChecked 64 ⟨11⟩ ⟨12⟩ (by decide)).isOk
#guard (fresh.writeChecked ⟨1⟩ ⟨11⟩ 0 7).isOk
#guard (fresh.writeChecked ⟨1⟩ ⟨1⟩ 0 7).isOk = false

/-! ### Control 15: a loan identifier is used once -/

/- Control 15a: a fresh loan identifier is accepted — the affirmative control
for 15b. -/
#guard (b1.beginBorrowChecked ⟨0⟩ ⟨3⟩ ⟨5⟩ ⟨13⟩).isOk

/- Control 15b: the recorded identifier `⟨9⟩` cannot be reused. -/
#guard (b1.beginBorrowChecked ⟨0⟩ ⟨3⟩ ⟨5⟩ ⟨9⟩).isOk = false

/-! ### Control 16: a return derives a fresh lifetime -/

private def reissued : World :=
  match r1.beginBorrowChecked ⟨0⟩ ⟨1⟩ ⟨7⟩ ⟨15⟩ with
  | .ok w => w
  | .error _ => r1

/- Control 16: the new borrow derives lifetime `⟨3⟩`, and the ended lifetimes
stay ended — `⟨1⟩` is ended and differs from the derived `⟨3⟩`, so it was not
reissued. -/
#guard (r1.beginBorrowChecked ⟨0⟩ ⟨1⟩ ⟨7⟩ ⟨15⟩).isOk
#guard (match reissued.ctx.loans.findLoan? ⟨15⟩ with
  | some l => l.lifetime == ⟨3⟩
  | none => false)
#guard (match reissued.ctx.loans.findLifetime? ⟨1⟩ with
  | some lt => lt.state == .ended
  | none => false)
#guard (match reissued.ctx.loans.findLifetime? ⟨3⟩ with
  | some lt => lt.state == .live
  | none => false)

/-! ### Control 17: an issued borrower is not issued again -/

/- Control 17a: a fresh borrower is accepted — the affirmative control for
17b. -/
#guard (b2.beginBorrowChecked ⟨0⟩ ⟨4⟩ ⟨11⟩ ⟨13⟩).isOk

/- Control 17b: the already-issued `⟨3⟩` cannot borrow. -/
#guard (b2.beginBorrowChecked ⟨0⟩ ⟨4⟩ ⟨3⟩ ⟨14⟩).isOk = false

/-! ### Control 18: splits and joins wait for the restoration -/

/- Control 18a: a spatial split is refused while the loan is outstanding... -/
#guard (b1.splitAtChecked ⟨0⟩ ⟨3⟩ ⟨5⟩ ⟨6⟩ 32).isOk = false

/- ...and accepted after both returns — the affirmative control for 18a. -/
#guard (r1.splitAtChecked ⟨0⟩ ⟨1⟩ ⟨5⟩ ⟨6⟩ 32).isOk

/- Control 18b: on the fractional fixture the join is refused while the loan is
outstanding... -/
#guard (sfb.joinChecked ⟨0⟩ ⟨3⟩ ⟨6⟩).isOk = false

/- ...and accepted after the return — the affirmative control for 18b. -/
#guard (sfr.joinChecked ⟨0⟩ ⟨3⟩ ⟨6⟩).isOk

/-! ### Control 19: issued order rejects the cycle -/

/-- The `3 → 4` edge of the cycle fixture. -/
private def cycleOuter : Loan :=
  { id := ⟨9⟩, alloc := ⟨0⟩, base := ⟨3⟩, lender := ⟨3⟩, borrower := ⟨4⟩,
    lifetime := ⟨1⟩, lo := 0, hi := 64, q := 64, ceiling := .readWrite }

/-- The `4 → 3` edge of the cycle fixture. -/
private def cycleInner : Loan :=
  { id := ⟨10⟩, alloc := ⟨0⟩, base := ⟨3⟩, lender := ⟨4⟩, borrower := ⟨3⟩,
    lifetime := ⟨2⟩, lo := 0, hi := 64, q := 64, ceiling := .readWrite }

/-- Two loans forming the cycle `3 → 4 → 3`, over live lifetimes and with both
loans' identifiers issued. -/
private def cyclicWorld : World :=
  { uWorld with
    ctx := { uWorld.ctx with
      issued := [⟨3⟩, ⟨4⟩],
      loans := { uWorld.ctx.loans with
        lifetimes := [{ id := ⟨1⟩, parent := none, state := .live },
                      { id := ⟨2⟩, parent := some ⟨1⟩, state := .live }],
        loans := [cycleOuter, cycleInner],
        nextLifetime := 3 } } }

/-- Control 19: the issued order fails on the `3 → 4` edge: the borrower `⟨4⟩`
was issued after its lender `⟨3⟩`. -/
example : ¬ World.LoansOrderOK cyclicWorld := by
  intro h
  have hord := h cycleOuter (by simp [cyclicWorld, cycleOuter, cycleInner])
  have hb : cyclicWorld.ctx.issued.idxOf cycleOuter.borrower = 1 := by decide
  have hl : cyclicWorld.ctx.issued.idxOf cycleOuter.lender = 0 := by decide
  rw [hb, hl] at hord
  exact absurd hord (by decide)

/-- Control 19: an ordered chain satisfies the detector — the affirmative
control for the cycle refusal above. -/
example : World.LoansOrderOK b2 := by
  unfold World.LoansOrderOK
  decide

/- Control 19: the reachability detector finds the cycle... -/
#guard (BorrowReaches cyclicWorld.ctx.loans.loans
  (cyclicWorld.ctx.loans.loans.length + 1) ⟨3⟩ ⟨3⟩)

/- ...and invents none on the ordered pair — the same detector, false here. -/
#guard (BorrowReaches b2.ctx.loans.loans (b2.ctx.loans.loans.length + 1) ⟨1⟩ ⟨1⟩) = false

/-! ### Control 20: the retag detaches the lender and preserves the budget -/

/- Control 20: per-byte budget equality, identifier-list length equality, and
the lender's absence from the live identifiers, with the borrower present. -/
#guard (List.range 64).all (fun x =>
  match uWorld.ctx.findOwner? ⟨0⟩, b1.ctx.findOwner? ⟨0⟩ with
  | some o0, some o1 => o0.root.budget x == o1.root.budget x
  | _, _ => false)
#guard (b1.ctx.ids.length == uWorld.ctx.ids.length)
#guard (⟨3⟩ ∈ b1.ctx.ids)

/- Control 20: the reciprocal twin — the lender `⟨1⟩` is live before the borrow
and absent after it. -/
#guard (⟨1⟩ ∈ uWorld.ctx.ids)
#guard (⟨1⟩ ∉ b1.ctx.ids)
