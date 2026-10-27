/-
The recursive-frame contract: a recursive call's embedded body that opens the
suspended parent frame's own emptied array is refused by the client-facing
checker, even though the handle it returns is the call's own state, because the
body is checked as its own program with only the call's state, path and index
exposed.

The fixture is local and deterministic. `H` is the two-level heap: the root
array `ref 0`'s slot 0 holds the child array `ref 1`, the child's slot 0 holds
the leaf `ref 2`, and each live cell is counted once. `env0` names the root and
the call's scalar arguments on that heap; `ctx0` counts the root, child and leaf
once each, marks variable 0 as the root, variables 1, 4 and 7 as scalars, and
leaves the extraction binders 2 and 3 and the call result 9 dead.

Both programs extract the child from the root — moving the emptied parent to
variable 2 and the child to variable 3 — and issue a `.callAt` on that child
with an embedded body. `good`'s body is `.ret 3`, the child the call was handed.
`bad`'s body takes the leaf out of variable 2, the parent array whose slot the
outer extraction emptied and whose handle the suspended frame still holds, puts
it back, and then returns variable 3 — the same child `good` returns — so the
body's own exit names the call's state and only the handle it opens, reaching
outside the call's extracted subtree, is refused.
-/
import Ownership.Nested

open Ownership
open Ownership.Nested

namespace OwnershipTest.RecursiveFrame

/-- The root array: slot 0 holds the child array `ref 1`. -/
def rootObj : Obj := ⟨#[.ref 1], 1, false⟩

/-- The child array: slot 0 holds the leaf `ref 2`. -/
def childObj : Obj := ⟨#[.ref 2], 1, false⟩

/-- The leaf the recursive body's subtree reaches. -/
def leafObj : Obj := ⟨#[.scalar 0], 1, false⟩

/-- Root → child → leaf, each live cell counted once. -/
def H : Heap :=
  { cells := fun r =>
      if r = 0 then some rootObj
      else if r = 1 then some childObj
      else if r = 2 then some leafObj
      else none
    next := 3 }

/-- Variable 0 names the root, 1 names the root's slot, and 4 and 7 name the
recursive call's scalar path and index arguments. -/
def env0 : Env :=
  fun x =>
    if x = 0 then some (.ref 0)
    else if x = 1 then some (.scalar 0)
    else if x = 4 then some (.scalar 0)
    else if x = 7 then some (.scalar 0)
    else none

/-- The root and the index are counted once, as are the child and leaf the
extraction opens; the extraction binders 2 and 3 and the call result 9 are
dead. -/
def ctx0 : Ctx :=
  { us := fun x =>
      if x = 0 then .owned
      else if x = 1 then .scalar
      else if x = 4 then .scalar
      else if x = 7 then .scalar
      else .dead
    refOf := fun x => if x = 0 then some 0 else none
    mult := fun r => if r = 0 then 1 else if r = 1 then 1 else if r = 2 then 1 else 0 }

/-- The accepted program: extract the child from the root, call the recursive
body on the child, and return the body's result. The body names only the child
it was handed. -/
def good : NCode :=
  .takeOut 0 1 2 3 1
    (.callAt 3 4 7 9 (.ret 3) (.ret 9))

/-- The refused program: the same extraction and call, whose body takes the leaf
out of variable 2, the parent array the extraction emptied and the open frame
still holds, puts it back, and returns variable 3, the child the call was
handed. Its exit and returned handle are the accepted program's; only the array
it opens lies outside the call's own subtree. -/
def bad : NCode :=
  .takeOut 0 1 2 3 1
    (.callAt 3 4 7 9
      (.takeOut 2 4 5 6 2 (.putBack 5 6 4 8 (.ret 3)))
      (.ret 9))

-- The affirmative control: the checker accepts a body confined to the state
-- the call hands it.
#guard (checkN ctx0 good).isSome

-- The contract: the checker refuses a body that opens the suspended frame's own
-- parent array, even though the handle it returns is the call's state.
#guard (checkN ctx0 bad).isNone

end OwnershipTest.RecursiveFrame
