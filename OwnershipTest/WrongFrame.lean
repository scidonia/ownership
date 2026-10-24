/-
The wrong-frame contract: a taken-out element restored into a different owned
array than the one the take-out emptied is refused by the client-facing
checker.

The fixture is local and deterministic. `H` holds two separate owned arrays:
`r0` (reference 0) whose slot 0 holds the unique element `r2` (reference 2), and
`r1` (reference 1) whose slot 0 holds a scalar. `ctx0` names source variable 0
as `r0`, the distinct destination variable 8 as `r1`, and index variable 1 as
`.scalar 0`, counting every array and the element once; `env0` binds those same
variables on the heap.

The programs differ in one variable only. `good` extracts the element from `r0`
and restores it to `r0`, through the take-out's moved array variable 2. `bad`
restores to variable 8, which names `r1`; the element variable 3 and index
variable 1 are identical in both. The rejection the contract names is `checkN`
returning `none` for `bad`, with `checkN` accepting `good` as the affirmative
control so the refusal is not a wholesale rejection of restoration.
-/
import Ownership.Nested

open Ownership
open Ownership.Nested

namespace OwnershipTest.WrongFrame

/-- The source array `r0`: slot 0 holds the unique element `ref 2`. -/
def sourceObj : Obj := ⟨#[.ref 2], 1, false⟩

/-- The destination array `r1`: slot 0 holds a scalar. -/
def destObj : Obj := ⟨#[.scalar 0], 1, false⟩

/-- The extracted element `r2`. -/
def elemObj : Obj := ⟨#[], 1, false⟩

def H : Heap :=
  { cells := fun r =>
      if r = 0 then some sourceObj
      else if r = 1 then some destObj
      else if r = 2 then some elemObj
      else none
    next := 3 }

def env0 : Env :=
  fun x =>
    if x = 0 then some (.ref 0)
    else if x = 8 then some (.ref 1)
    else if x = 1 then some (.scalar 0)
    else none

def ctx0 : Ctx :=
  { us := fun x =>
      if x = 0 then .owned
      else if x = 8 then .owned
      else if x = 1 then .scalar
      else .dead
    refOf := fun x =>
      if x = 0 then some 0
      else if x = 8 then some 1
      else none
    mult := fun r =>
      if r = 0 then 1
      else if r = 1 then 1
      else if r = 2 then 1
      else 0 }

/-- The accepted control: extract the element from `r0` and restore it to `r0`
(the take-out binds the source array to variable 2). -/
def good : NCode :=
  .takeOut 0 1 2 3 2 (.putBack 2 3 1 9 (.ret 9))

/-- The refused program: the same extraction, restored to the different array
`r1` at variable 8, with the same element and index variables. -/
def bad : NCode :=
  .takeOut 0 1 2 3 2 (.putBack 8 3 1 9 (.ret 9))

-- The affirmative control: the checker accepts restoring to the source array.
#guard (checkN ctx0 good).isSome

-- The contract: the checker refuses restoring the extracted element to `r1`.
#guard (checkN ctx0 bad).isNone

end OwnershipTest.WrongFrame
