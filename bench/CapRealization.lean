import Cap.Discipline

open Cap

/-!
Executable realization controls for the coupled state: the delegation chain
projected onto the world's loan ledger, driven through the checked borrow,
write, and return operations.

The single-path lifecycle borrows the root capability `⟨1⟩` to `⟨3⟩`, writes
through the terminal borrower, returns, and then writes through the restored
root. The lemmas prove every intermediate state satisfies `State.OK` and that
the byte written by the borrower is still observed after the restoration.

The nested lifecycle borrows `⟨1⟩ → ⟨3⟩` and then `⟨3⟩ → ⟨4⟩`, refuses the
outer return while the inner loan is live, returns the inner loan, then the
outer one. Every state satisfies `State.OK`, and the final ledger is empty.

Each acceptance control is paired with the refusal it explains, through the
same detector: the lender's write is refused while borrowed and accepted after
the return, and the outer return is refused before its successor ends.
-/

namespace CapRealization

open Discipline

/-! ### The single-path lifecycle -/

/-- One borrow from the root capability `⟨1⟩` to the fresh borrower `⟨3⟩`. -/
def borrowed : State :=
  match Discipline.initialState.beginBorrow ⟨3⟩ ⟨9⟩ with
  | some s => s
  | none => Discipline.initialState

/-- The world accepted the borrow. -/
theorem borrow_accepted : Discipline.initialState.beginBorrow ⟨3⟩ ⟨9⟩ = some borrowed :=
  rfl

/-- The borrowed state satisfies the correspondence. -/
theorem borrowed_OK : borrowed.OK :=
  Discipline.State.beginBorrow_OK (s := Discipline.initialState) (s' := borrowed)
    (borrower := ⟨3⟩) (loanId := ⟨9⟩) borrow_accepted Discipline.initialState_OK

/-- A write through the terminal borrower. -/
def written : State :=
  match borrowed.write 7 with
  | some s => s
  | none => borrowed

/-- The write was accepted. -/
theorem write_accepted : borrowed.write 7 = some written := rfl

/-- The written state satisfies the correspondence. -/
theorem written_OK : written.OK :=
  Discipline.State.write_OK (s := borrowed) (s' := written) (v := 7)
    write_accepted borrowed_OK

/-- The return of the outer loan. -/
def restored : State :=
  match written.endBorrow ⟨9⟩ with
  | some s => s
  | none => written

/-- The return was accepted. -/
theorem return_accepted : written.endBorrow ⟨9⟩ = some restored := rfl

/-- The restored state satisfies the correspondence. -/
theorem restored_OK : restored.OK :=
  Discipline.State.endBorrow_OK (s := written) (s' := restored) (loanId := ⟨9⟩)
    return_accepted written_OK

/-- A write through the restored root capability. -/
def restoredWritten : State :=
  match restored.write 9 with
  | some s => s
  | none => restored

/-- The write through the restored lender was accepted. -/
theorem restored_write_accepted : restored.write 9 = some restoredWritten := rfl

/-- The final state satisfies the correspondence. -/
theorem restoredWritten_OK : restoredWritten.OK :=
  Discipline.State.write_OK (s := restored) (s' := restoredWritten) (v := 9)
    restored_write_accepted restored_OK

/-- The byte an allocation's backend holds at offset `i`. -/
def byteAt (s : State) (i : Nat) : Option UInt8 :=
  (s.world.heaps s.chain.alloc).bind (fun b => b.read i)

/-- The borrower's write survives the return: the restored world still holds
byte `7` at offset `0`. -/
theorem restored_observes_write : byteAt restored 0 = some 7 := rfl

/-- The restored lender's write is observed in the final state. -/
theorem final_observes_restored_write : byteAt restoredWritten 0 = some 9 := rfl

/-! ### The nested lifecycle -/

/-- A reborrow from the borrowed holder `⟨3⟩` to the fresh borrower `⟨4⟩`. -/
def nested : State :=
  match borrowed.beginBorrow ⟨4⟩ ⟨10⟩ with
  | some s => s
  | none => borrowed

/-- The nested borrow was accepted. -/
theorem nested_borrow_accepted : borrowed.beginBorrow ⟨4⟩ ⟨10⟩ = some nested := rfl

/-- The nested state satisfies the correspondence. -/
theorem nested_OK : nested.OK :=
  Discipline.State.beginBorrow_OK (s := borrowed) (s' := nested)
    (borrower := ⟨4⟩) (loanId := ⟨10⟩) nested_borrow_accepted borrowed_OK

/-- The state after returning the inner loan. -/
def innerReturned : State :=
  match nested.endBorrow ⟨10⟩ with
  | some s => s
  | none => nested

/-- The inner return was accepted. -/
theorem inner_return_accepted : nested.endBorrow ⟨10⟩ = some innerReturned := rfl

/-- Returning the inner loan preserves the correspondence. -/
theorem innerReturned_OK : innerReturned.OK :=
  Discipline.State.endBorrow_OK (s := nested) (s' := innerReturned)
    (loanId := ⟨10⟩) inner_return_accepted nested_OK

/-- The final state after returning the outer loan. -/
def fullyReturned : State :=
  match innerReturned.endBorrow ⟨9⟩ with
  | some s => s
  | none => innerReturned

/-- The outer return was accepted once the inner loan had ended. -/
theorem outer_return_accepted : innerReturned.endBorrow ⟨9⟩ = some fullyReturned := rfl

/-- Returning the outer loan preserves the correspondence. -/
theorem fullyReturned_OK : fullyReturned.OK :=
  Discipline.State.endBorrow_OK (s := innerReturned) (s' := fullyReturned)
    (loanId := ⟨9⟩) outer_return_accepted innerReturned_OK

/-- The inner return is refused while it is still the innermost loan: the outer
loan cannot be returned first. -/
theorem outer_first_refused : nested.endBorrow ⟨9⟩ = none := rfl

/-- Both loans are gone from the ledger after the returns. -/
theorem final_ledger_empty : fullyReturned.world.ctx.loans.loans = [] := rfl

/-- The chain's projection is empty as well. -/
theorem final_projection_empty : fullyReturned.chain.toLoans = [] := rfl

/-! ### Executable controls -/

/- G2: the borrow is accepted, and the same lender write that was accepted
before the borrow is refused while the borrower holds the authority. -/
#guard (Discipline.initialState.beginBorrow ⟨3⟩ ⟨9⟩).isSome
#guard (Discipline.initialState.write 7).isSome
#guard (borrowed.world.writeChecked ⟨0⟩ ⟨1⟩ 0 7).isOk = false

/- G2: the terminal borrower may write, and its write is observed after the
return through the restored root. -/
#guard (borrowed.write 7).isSome
#guard (written.endBorrow ⟨9⟩).isSome
#guard (byteAt restored 0 == some 7)
#guard (restored.world.writeChecked ⟨0⟩ ⟨1⟩ 0 9).isOk

/- G2: the restored root's write is the final observed byte. -/
#guard (restored.write 9).isSome
#guard (byteAt restoredWritten 0 == some 9)

/- G3: the outer return is refused while the inner loan is live, and the
intermediate holder cannot write. -/
#guard (nested.endBorrow ⟨9⟩).isNone
#guard (nested.world.writeChecked ⟨0⟩ ⟨3⟩ 0 7).isOk = false

/- G3: the inner return succeeds, restoring `⟨3⟩`, then the outer return
succeeds, restoring `⟨1⟩`. -/
#guard (nested.endBorrow ⟨10⟩).isSome
#guard (innerReturned.world.writeChecked ⟨0⟩ ⟨3⟩ 0 7).isOk
#guard (innerReturned.endBorrow ⟨9⟩).isSome
#guard (fullyReturned.world.writeChecked ⟨0⟩ ⟨1⟩ 0 7).isOk

/- G3: the ledger and the chain projection are empty after the returns. -/
#guard (fullyReturned.world.ctx.loans.loans.length == 0)
#guard (fullyReturned.chain.toLoans.length == 0)

/-! ### The missing-storage diagnostic -/

/-- The 64-byte context with the chain unchanged, but no backing heap. -/
def noStorageWorld : World := { uWorld with heaps := fun _ => none }

def noStorageState : Discipline.State :=
  { Discipline.initialState with world := noStorageWorld }

/-- `State.OK` rejects the context-without-storage state: the integrated
invariant includes `World.WellFormed`, hence storage agreement. -/
example : ¬ Discipline.State.OK noStorageState := by
  intro h
  have hfind : noStorageWorld.ctx.findOwner? ⟨0⟩ = some Cap.uOwner := by
    change uWorld.ctx.findOwner? ⟨0⟩ = some Cap.uOwner
    simp [uWorld, uOwner, Ctx.findOwner?, Owner.init]
  obtain ⟨b, hb, _⟩ := h.world_storage ⟨0⟩ Cap.uOwner hfind
  have hb' : (none : Option Backend) = some b := by
    simpa [noStorageState, noStorageWorld] using hb
  cases hb'

end CapRealization
