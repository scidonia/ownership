/-
The recursive contract: a second extraction from the same array and the same
slot, taken before the first extraction is put back, is refused by the
client-facing checker.

The fixture is local and deterministic. `H` holds one array cell (`ref 0`) whose
slot 0 holds the unique element `ref 1`; the environment names the array at
variable 0 and the index at scalar variable 1; `ctx0` counts the array and the
element once each, so the single extraction is admissible on this heap.

`good` is that single extraction and is the affirmative detector control: the
checker must accept it. `bad` extracts the element, leaves the array and slot
open, extracts from the same array and slot again, and only then returns; the
first extraction has already replaced the slot with `.scalar 0`, so the runtime
faults there. The rejection the contract names is `checkN` returning `none` for
`bad`, not the runtime fault, which is a passing control on this heap.
-/
import Ownership.Nested

open Ownership
open Ownership.Nested

namespace OwnershipTest.Recursive

def arrayObj : Obj := ⟨#[.ref 1], 1, false⟩
def elemObj : Obj := ⟨#[], 1, false⟩

def H : Heap :=
  { cells := fun r =>
      if r = 0 then some arrayObj
      else if r = 1 then some elemObj
      else none
    next := 2 }

def env0 : Env :=
  fun x =>
    if x = 0 then some (.ref 0)
    else if x = 1 then some (.scalar 0)
    else none

def ctx0 : Ctx :=
  { us := fun x =>
      if x = 0 then .owned
      else if x = 1 then .scalar
      else .dead
    refOf := fun x => if x = 0 then some 0 else none
    mult := fun r => if r = 0 then 1 else if r = 1 then 1 else 0 }

/-- The accepted control: extract the element once and return it. -/
def good : NCode :=
  .takeOut 0 1 2 3 1 (.ret 3)

/-- The refused program: extract the element, then extract again from the same
array and slot before any put-back, then return. -/
def bad : NCode :=
  .takeOut 0 1 2 3 1 (.takeOut 2 1 4 5 1 (.ret 5))

-- The affirmative control: the checker accepts the single extraction.
#guard (checkN ctx0 good).isSome

-- The contract: the checker refuses the second extraction from the emptied slot.
#guard (checkN ctx0 bad).isNone

-- The invalid program faults at the second take-out on this heap.
#guard (runN bad env0 H).ok == false

end OwnershipTest.Recursive
