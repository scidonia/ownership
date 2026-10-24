# Open-frame return contracts

Behavior contracts for the exit rule of the nested `Path.index` ownership
protocol. Each contract below is executed by the Lean fixture named in it, run
from the repository root with `lake env lean OwnershipTest/OpenFrameReturn.lean`
after `lake build Ownership`; the fixture carries the assertion and this page
records the intent it encodes.

### N3

**Actor** A Lean client asking `Ownership.Nested.checkN` whether an extracted
array program's return is admissible.

**Given** a heap with one array `r0` at reference 0 whose slot 0 holds the
unique child `r1` at reference 1, and no other cells
(`OwnershipTest/OpenFrameReturn.lean`, `H`). The context `ctx0` names source
variable 0 as `r0` — `ctx0.refOf 0 = some 0` — and index variable 1 as
`.scalar 0`, counts `r0` and `r1` once each (`ctx0.mult 0 = ctx0.mult 1 = 1`),
and leaves the binder variables 2 and 3 dead; the environment `env0` binds
variable 0 to `.ref 0` and variable 1 to `.scalar 0` on that heap. The same
fixture holds the accepted exit `good`, `.takeOut 0 1 2 3 1 (.ret 3)`, which
opens the one frame at array variable 2 and returns the extracted child variable
3, and the refused exit `bad`, `.takeOut 0 1 2 3 1 (.ret 2)`, which differs only
in the returned variable: 2 is the parent array `r0`, while the frame that
emptied its slot 0 is still open and the slot holds a placeholder.

**When** The client submits the entire program `bad` to `checkN` on the
untouched context `ctx0`.

**Then** `checkN ctx0 bad` is `none`: the checker refuses to return the parent
array `r0` while its own selected slot is still a placeholder, since `r0`'s
count was moved to variable 2 but the extraction it opened has not been
restored. As the affirmative control, `checkN ctx0 good` is `some` on the same
context and an otherwise identical program, and in the context after the
take-out, `((ctx0.move 0 2).bindOwned 3 1).refOf` binds variable 2 to the parent
`r0` at reference 0 and variable 3 to the extracted child `r1` at reference 1,
while the entry `ctx0.refOf` binds only source variable 0 to reference 0 and
neither return variable, so the refusal distinguishes which heap reference
leaves the open frame rather than rejecting any return. The fixture
checks the accepted exit first, so the refused one is the first failing
assertion.

**Why** A take-out empties the array's selected slot and moves the array handle
into the first binder; the extracted child is the only owned value the frame
offers at exit. Returning the parent array instead hands back a handle whose
slot is a placeholder, so the caller would hold an array that no longer matches
the heap it names. A checker that admits any owned variable at `.ret` accepts
that exit and certifies a program whose returned parent is not the value the
frame left intact.
