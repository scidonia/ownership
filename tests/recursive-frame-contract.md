# Recursive frame contracts

Behavior contracts for the frame isolation of a recursive `callAt` body. Each
contract below is executed by the Lean fixture named in it, run from the
repository root with `lake env lean OwnershipTest/RecursiveFrame.lean` after
`lake build Ownership`; the fixture carries the assertion and this page records
the intent it encodes.

### N5

**Actor** A Lean client asking `Ownership.Nested.checkN` whether a two-level
recursive write program with an embedded body is admissible.

**Given** the two-level heap `root → child → leaf`: the root array `r0` at
reference 0 whose slot 0 holds the child `r1` at reference 1, whose slot 0
holds the leaf `r2` at reference 2, and no other cells
(`OwnershipTest/RecursiveFrame.lean`, `H`). The context `ctx0` names variable 0
as `r0` — `ctx0.refOf 0 = some 0` — and variable 1 as `.scalar 0`, counts
`r0`, `r1` and `r2` once each, marks variable 4 as the recursive call's scalar
path argument and variable 7 as its scalar index argument, and leaves the
extraction binders 2 and 3 and the call result 9 dead; the environment `env0`
binds variable 0 to `.ref 0` and variables 1, 4 and 7 to `.scalar 0` on that
heap. The same fixture holds the accepted program `good`,
`.takeOut 0 1 2 3 1 (.callAt 3 4 7 9 (.ret 3) (.ret 9))`, which takes the child
out of the root — moving the emptied parent to variable 2 and the child to
variable 3 — calls the embedded body on the child, and returns the body's
result; and the refused program `bad`,
`.takeOut 0 1 2 3 1 (.callAt 3 4 7 9 (.takeOut 2 4 5 6 2 (.putBack 5 6 4 8
(.ret 3))) (.ret 9))`, whose body takes the leaf out of variable 2 — the parent
array whose slot the outer extraction emptied — puts it back, and returns
variable 3, the child the call was handed, so the body's exit returns exactly
the handle `good` returns while the body additionally opens the suspended
parent's own array.

**When** The client submits the entire program `bad` to `checkN` on the
untouched context `ctx0`.

**Then** `checkN ctx0 bad` is `none`: the embedded body is checked as its own
program, with every variable but the call's state, path and index forced
`.dead`, so the parent array variable 2 is dead inside the body and the body's
take-out of it finds no owned handle to open. As the affirmative control,
`checkN ctx0 good` is `some` on the same context with the same outer take-out
and call, so the refusal is not a wholesale rejection of recursive calls; the
two bodies return the same variable 3 and the same reference — the call's own
state — so the only difference a refusal can rest on is the parent array the
refused body opens, and the fixture checks the accepted program first, so the
refused one is the first failing assertion.

**Why** The outer extraction suspends a frame: the parent array's selected slot
holds a placeholder and the array's handle sits in variable 2 while the frame is
open. A recursive body runs inside that state, so a body that opens the parent
array works on a handle whose slot the suspended frame has not restored, even
when the handle it returns is the call's own; the caller would be handed a body
result computed against an array whose slots no longer match the heap the frame
will restore. Checking the body under the isolated context confines it to the
extracted child it was given, so the parent array is not exposed and the only
handle the body can open or return is the one the call owns.
