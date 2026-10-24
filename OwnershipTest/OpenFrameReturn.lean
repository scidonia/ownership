/-
The open-frame return contract: returning the parent array while its own
extraction frame is still open is refused by the client-facing checker.

The fixture is local and deterministic. `H` holds one array cell (`ref 0`) whose
slot 0 holds the unique child `ref 1`; `env0` names the array at variable 0 and
the index at scalar variable 1; `ctx0` counts the array and the child once each
and leaves the take-out binders 2 and 3 dead.

`good` extracts the child, binding the parent array to variable 2 and the child
to variable 3, and returns the child; it is the affirmative detector control.
`bad` is the same program with only the returned variable changed to 2, the
parent array whose slot 0 the open frame has emptied. The rejection the
contract names is `checkN` returning `none` for `bad`.
-/
import Ownership.Nested

open Ownership
open Ownership.Nested

namespace OwnershipTest.OpenFrameReturn

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

/-- The accepted exit: extract the child and return it. -/
def good : NCode :=
  .takeOut 0 1 2 3 1 (.ret 3)

/-- The refused exit: extract the child and return the parent array, whose
slot 0 the open frame has emptied. -/
def bad : NCode :=
  .takeOut 0 1 2 3 1 (.ret 2)

-- The affirmative control: the checker accepts returning the extracted child.
#guard (checkN ctx0 good).isSome

-- The contract: the checker refuses returning the parent while its frame is open.
#guard (checkN ctx0 bad).isNone

end OwnershipTest.OpenFrameReturn
