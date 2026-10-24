# Distinct take-out binder contracts

Behavior contracts for the binder shape of the nested `Path.index` ownership
protocol. Each contract below is executed by the Lean fixture named in it, run
from the repository root with `lake env lean OwnershipTest/DistinctBinders.lean`
after `lake build Ownership`; the fixture carries the assertion and this page
records the intent it encodes.

### N4

**Actor** A Lean client asking `Ownership.Nested.checkN` whether a take-out
with two binders is admissible.

**Given** a heap with one array `r0` at reference 0 whose slot 0 holds the
unique child `r1` at reference 1, and no other cells
(`OwnershipTest/DistinctBinders.lean`, `H`). The context `ctx0` names source
variable 0 as `r0` — `ctx0.refOf 0 = some 0` — and index variable 1 as
`.scalar 0`, counts `r0` and `r1` once each (`ctx0.mult 0 = ctx0.mult 1 = 1`),
and leaves the binder variables 2 and 3 dead; the environment `env0` binds
variable 0 to `.ref 0` and variable 1 to `.scalar 0` on that heap. The same
fixture holds the accepted take-out `good`, `.takeOut 0 1 2 3 1 (.ret 3)`,
whose array binder is variable 2 and whose element binder is variable 3, and
the refused take-out `bad`, `.takeOut 0 1 3 3 1 (.ret 3)`, which differs only in
the array binder: it names the same variable 3 as the element binder.

**When** The client submits the entire program `bad` to `checkN` on the
untouched context `ctx0`.

**Then** `checkN ctx0 bad` is `none`: the checker refuses a take-out whose two
binders are the same variable. As the affirmative control, `checkN ctx0 good` is
`some` on the same context and an otherwise identical program, so the refusal
is not a wholesale rejection of take-out. The fixture checks the accepted
take-out first, so the refused one is the first failing assertion.

**Why** A take-out binds the array handle and the extracted element into two
variables by two successive environment writes. With both binders the same
variable, the element write overwrites the array handle that the first write
just installed, so the client's later use of that variable names the child
rather than the array whose slot is open. A checker that requires each binder to
be dead before the take-out, but never requires them to differ, accepts that
program and certifies two bindings where only one survives.
