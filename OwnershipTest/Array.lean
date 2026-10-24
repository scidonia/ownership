/-
Concrete acceptance and rejection for the array-write fragment.

`execSet` is the measured write prefix; `aliasSet` duplicates the array's handle
before the write. The first must be accepted and the second rejected; both are
compile-time checks, and the theorems beside them are the kernel statements.
-/
import Ownership.Entry

open Ownership

namespace OwnershipTest

open Ownership.Runner

#guard (check (initCtx 0) (execSet 0 3 1 2)).isSome
#guard (check (initCtx 0) (aliasSet 0 3 1 2)).isNone

/-- The held-pair/alias shape at the context level: the element is named by
two handles, so the write's `multOf = 1` rule rejects it. -/
def heldCtx : Ctx :=
  { us := fun x =>
      if x = 0 then .owned
      else if x = 1 then .scalar
      else if x = 2 then .scalar
      else .dead
    refOf := fun x => if x = 0 then some 0 else none
    mult := fun r' => if r' = 0 then 2 else 0 }

#guard (check heldCtx (execSet 0 3 1 2)).isNone

example : ¬ Entry.UniqueTree Entry.repeatedChildHeap 1 := Entry.repeatedChild_not_unique
example : ¬ Entry.ClientSeparated Entry.repeatedChildHeap 1 [0] :=
  Entry.clientRetained_not_separated

example : check (initCtx 0) (execSet 0 3 1 2) = some ((initCtx 0).move 0 3) :=
  execSet_check 0

example : check (initCtx 0) (aliasSet 0 3 1 2) = none :=
  aliasSet_rejected 0

#print axioms Ownership.check_sound
#print axioms Ownership.Runner.artifact
#print axioms Ownership.Entry.artifact_entry

end OwnershipTest
