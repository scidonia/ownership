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

## Outstanding

- The backend-input capture and the replay-to-backend argument.
- A runtime count measurement for the certified path itself, not the sibling's
  layout harness.
- The linked-executable build gate.
- The emitted recursive callee and continuation, and physical reference counts.
