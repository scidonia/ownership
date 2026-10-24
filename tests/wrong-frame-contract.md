# Wrong-frame restoration contracts

Behavior contracts for the restoration frame of the nested `Path.index`
ownership protocol. Each contract below is executed by the Lean fixture named in
it, run from the repository root with `lake env lean OwnershipTest/WrongFrame.lean`
after `lake build Ownership`; the fixture carries the assertion and this page
records the intent it encodes.

### N2

**Actor** A Lean client asking `Ownership.Nested.checkN` whether a nested write
program may return a taken-out element to an array.

**Given** a heap with two separate owned arrays, `r0` at reference 0 and `r1` at
reference 1, each counted once, plus the unique element `r2` at reference 2,
counted once (`OwnershipTest/WrongFrame.lean`, `H`). `r0`'s slot 0 holds
`.ref 2`; `r1`'s slot 0 holds a scalar. The context `ctx0` names source variable
0 as `r0`, the distinct destination variable 8 as `r1`, and index variable 1 as
`.scalar 0`, and counts `r2` once; the environment `env0` binds those same three
variables to those values. The same fixture holds the accepted restoration
`good`, which extracts the element with `.takeOut 0 1 2 3 2` and restores it
with `.putBack 2 3 1 9 (.ret 9)` — array variable 2 is the source array `r0`
after the take-out's move — and the refused restoration `bad`, which changes
only the put-back's array variable to 8, so it writes to the different array
`r1` while the element variable 3 and index variable 1 stay identical.

**When** The client submits the entire program `bad` to `checkN` on the
untouched context `ctx0`.

**Then** `checkN ctx0 bad` is `none`: the checker refuses a restoration whose
target array is not the array the take-out emptied. As the affirmative control,
`checkN ctx0 good` is `some` on the same context and an otherwise identical
program, so the refusal is not a wholesale rejection of restoration. The
fixture checks the accepted restoration first, so the refused one is the first
failing assertion.

**Why** The take-out leaves `r0`'s slot 0 scalar and binds the open frame to
`r0`; restoring into `r1` instead writes the element into a different array and
leaves the emptied source slot unrestored. A checker that validates the
restoration's array, element and index independently — without tying the
restoration target to the open frame's source array — accepts that program and
certifies a write the frame does not permit.
