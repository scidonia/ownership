# Runtime and artifact evidence for the certified nested path

Date: 27 October 2026
Repository: `scidonia/ownership`, main at `6fc90a8`
Pinned sibling: `lean-examples` at `66e64334a1c968d829903b8aec8d22f7e3b9fd3f` (clean)
Toolchain: Lean `4.35.0-rc3` from the repository flake

This note records what has been measured for the nested update path and what the
measurements do and do not establish. They are supporting evidence, not a
refinement proof: no theorem below relates the model's counts to physical
counted references.

## Commands and results

| Command | Result |
| --- | --- |
| `(cd ../lean-examples && nix develop -c lake exe inplace)` | exit 0; all cases `ok` |
| `(cd ../lean-examples && nix develop -c lake build ScidoniaTest)` | 38 jobs, exit 0; every IR requirement `ok` |
| `scripts/check_artifacts.sh` | exits 0; both captured artifacts regenerate byte-identically |

The in-place harness observes the layout write path at the pinned revision,
including the nested cases: `layout5-unique`, `layout5-right`, `layout5-last`,
`layout5-out-of-bounds`, `layout5-nest`, `layout5-nest-aliased`,
`layout5-shared-copies`, and the checked children `layout5-checked-unique`,
`layout5-checked-shared`, `layout5-checked-nest` and
`layout5-checked-nest-shared`. The unique and nested cases keep the array's
buffer and the struct at the written index at the same address and land the
write; the shared and aliased cases change the address and keep the outside
reference's values. The harness runs with the check off in the parent and with
`SCIDONIA_CHECK_INPLACE=1` in the child processes, so both the no-copy and the
loud-check behaviours are observed.

The IR gate reads the post-reference-counting IR of the write paths: the
take-out names `Array.getInternal` beside a placeholder `Array.set`, the
structured executor's `set` names `Array.set!` bound to the array check's
result, and `Array.getInternalBorrowed` appears in the bounds read with the
read interpreter as its control. It asserts shape, not ownership.

## What is measured, and what is not

Measured: the pinned toolchain's emitted code for the layout write path has the
take-out/put-back shape, and at run time an exclusively owned array is updated
in place while a live second reference forces a copy. This supports the
update-disposition contract (A8/N11) on that path.

Not measured or proved: the model-to-runtime refinement; reference-count
equality in general; the specific nested `setAt` `Path.index` declaration's
runtime behaviour (the harness measures `Layout5.setLeaf`/`setAt` at the same
revision, not the model's built program); allocation and free behaviour; and
the emitted recursive callee and continuation.

## Count accounting for the certified path

| Item | Model | Runtime |
| --- | --- | --- |
| Counted roots | the root array variable, count one | the parent's owned variables and the harness's external alias in the shared case |
| Heap edges | root slot → child, child slot → leaf, each count one | the array's field references, each a counted edge |
| Multiplicity | `mult r = 1` for every footprint cell | `lean_is_exclusive` is the test the runtime applies at the write |
| Take-out pair | two handles (parent, element) plus the pair object | emitted `inc` of both projections and `dec` of the pair (N2) |
| External handles | not represented | the harness's live second reference, which forces the copy |
| Borrows | `Check`/`let` borrows in the model | `Array.getInternalBorrowed` in the bounds read; non-owning |
| Persistence | `persistent = true` cells are outside the mutable footprint | literal arrays are persistent and never exclusively owned |

## Replay to backend input

The LCNF replay is the impure pipeline (`saveMono` onward, then the impure
passes). `scripts/check_artifacts.sh` ties the committed artifacts to the
sibling revision and toolchain. The IR gate reads the post-reference-counting
IR that the pinned toolchain compiled into the olean. The actual backend input
after the backend passes is not captured; the replay assumptions remain those
recorded in `OwnershipLcnf/Semantics.lean` (A10), including specialization and
inlining choices. No custom compiler options are passed.

## Build gate

`scripts/check_artifacts.sh` is the current gate: sibling pin, flake Lean, and
byte-for-byte artifacts. It does not bind a linked executable, the C runtime
revision, or the selected implementation; that remains outstanding.

## Borrow inference (compiler decision log)

The compiler's borrow inference decides which parameters a declaration owns.
`-Dtrace.Compiler.inferBorrow=true` prints the decisions and their reasons. The
replayed signatures of the pinned declarations are:

| Declaration | Inferred signature | Borrowed | Owned |
| --- | --- | --- | --- |
| `setAt` | `x.1 @&x.2 x.3` | the replacement value (`x.2`) | the path (`x.1`), the state (`x.3`) |
| `takeOut` | `s @&i d` | the index | the array, the default |
| `execP` | `a x.1` | — | the array, the tree |

The mapping follows the source: `setAt : {d} → (p : Path d) → State (At p) → State d → State d`,
so `x.2` is the replacement value and `x.3` the owned state. An owned parameter is
a reference-management convention, not evidence of exclusivity; a borrowed
replacement does not make the updated state borrowed.

The reasons are the compiler's own: the probe copy of `execP` logs
`own a: owned function argument`, `own x.56: bkwd projection propagation k.60`,
`own k.60: argument to closure call`, and similar. The private declarations'
inference ran when the pinned sibling's module was compiled, so the replay does
not re-emit their "own" lines; the signature is the recorded decision. The raw
log and its provenance are in `docs/notes/artifacts/borrow-inference.txt`.

This is a decision log, not a linearity certificate: it reports no pass-rate,
and an owned parameter is a deliberate ownership decision (the value is consumed
or used non-linearly at the callee), not a failure.

## Outstanding

- The backend-input capture and the replay-to-backend argument.
- A runtime count measurement for the certified path itself, not the sibling's
  layout harness.
- The linked-executable build gate.
- The emitted recursive callee and continuation, and physical reference counts.

## Context sensitivity of the in-place observation

A committed reproducer (`runtime-bridge/`) measures the same path write in
several compiled contexts with `addressIO` before and after and no post-write
use of the original. Results (check off; check on in parentheses):

| Mode | Construction | Result |
| --- | --- | --- |
| `separate-exact`, `separate-spare` | parameterized function, exact/spare capacity | in place (exit 0) |
| `inline-exact`, `inline-spare` | pure closed construction, inline in `main` | copied (abort, exit 1) |
| `inline-io` | IO construction, inline in `main` | in place (exit 0) |
| `closed-case` | parameterless function with the pure construction | copied (abort, exit 1) |
| `sealed` | `Structured.runFresh` | writes `(true, true)` (exit 0) |

The emitted C explains it: the inline and parameterless pure constructions are
lifted into `___closed` initializers called through `lean_obj_once` (excerpt in
`runtime-bridge/emitted/closed-lifting.txt`). The array is a shared constant, so
each access holds a reference and the write copies. The parameterized function
and the IO construction are not closed, stay local, and are exclusive.

This corrects the earlier wording of this note: the copy is not caused by the
`do` block as such, and the earlier borrowed-parameter and closure observations
used the same closed pure construction, so the constant lifting explains them
too. The compiler's separate decision to copy when a `@&` parameter is passed to
an owning call (`user annotation blocked owning`) is real, but it was not
isolated by this reproducer.

The practical rule: construct the array in `IO` or from a runtime parameter, not
as a closed pure expression. The sealed `runFresh` interface already does this;
direct layout helpers on a closed constant copy. The armed check turns the copy
into an abort instead of a silent copy.
