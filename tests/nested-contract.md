# Nested extraction contracts

Behavior contracts for the nested `Path.index` ownership protocol. Each contract
below is executed by the Lean fixture named in it, run from the repository root
with `lake env lean OwnershipTest/Recursive.lean` after `lake build Ownership`;
the fixture carries the assertion and this page records the intent it encodes.

### N1

**Actor** A Lean client asking `Ownership.Nested.checkN` whether a nested write
program is admissible.

**Given** a heap with one array cell `def H`-style — the array `r0` at variable
0, whose slot 0 holds the unique child `r1`, and no other cells — an
environment that names the array at variable 0 and the index at scalar variable
1, and a context counting both the array and the element once
(`OwnershipTest/Recursive.lean`, `H`, `env0`, `ctx0`). The same fixture holds
the accepted single extraction `good` and the nested program `bad`, which
extracts from the array and then, before any put-back, extracts from the same
array and the same slot.

**When** The client submits the entire nested program `bad` to `checkN` on the
untouched context `ctx0`.

**Then** `checkN ctx0 bad` is `none`: the checker refuses a second extraction
from a slot the first extraction has already emptied and not yet restored; as
the affirmative control, `checkN ctx0 good` is `some` on the same heap, so the
refusal is not a wholesale rejection of extraction.

**Why** The first extraction replaces the selected slot with `.scalar 0`, so the
second extraction cannot obtain the exclusive element it names; a checker that
accepts it would certify a program that faults, and the certificate would be
false. The runtime fault on `bad` is recorded as a control, not as the
rejection: `checkN` must refuse the program statically.
