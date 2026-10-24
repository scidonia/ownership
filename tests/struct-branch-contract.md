# Structured branch contracts

Behavior contracts for the branch-local record the measurement CLI reports for
the structured write path. Each contract below is executed by
`tests/struct-branch-assert.sh`, which invokes the measurement script
`scripts/dump_executor.lean` once from the sibling checkout and reads what the
CLI printed.

## Sibling checkout setup

Each contract invokes the CLI from the sibling `../lean-examples` checkout. The
contracts themselves reach neither the network nor the checkout's creation:
both read the CLI's output from a checkout prepared beforehand. From the
ownership repository root, provision that checkout when it is absent:

```sh
set -e
if [ ! -e ../lean-examples ]; then
  git clone --no-checkout https://github.com/scidonia/lean-examples.git ../lean-examples
  git -C ../lean-examples checkout --detach 66e64334a1c968d829903b8aec8d22f7e3b9fd3f
  (cd ../lean-examples && nix develop -c lake build Scidonia)
fi
test "$(git -C ../lean-examples rev-parse HEAD)" = 66e64334a1c968d829903b8aec8d22f7e3b9fd3f
test -f ../lean-examples/.lake/build/lib/lean/Scidonia/FracPerm/StateVar/Layout5.olean
test -f ../lean-examples/.lake/build/lib/lean/Scidonia/FracPerm/Structured/Executor.olean
```

The clone reads the public repository over HTTPS, so it needs network access to
GitHub; the build runs through `nix develop`, so it needs the Nix toolchain.
`../lean-examples/lakefile.toml` defines the `Scidonia` library, and
`../lean-examples/AGENTS.md` prescribes the Nix/Lake shell and build, with the
sibling's tracked `flake.lock`, `lake-manifest.json` and toolchain pinning both.
A checkout that is already present is not switched, rebuilt or otherwise
modified: the clone branch is skipped, and the checks then require the pinned
revision and both module oleans. A checkout that disagrees with them is left
untouched; stop there rather than switching or rebuilding it. The revision and
olean checks establish which sources and build artifacts are present, not that
those oleans are the input the replay compiled against.

Run each contract from the ownership repository root:

    bash tests/struct-branch-assert.sh left
    bash tests/struct-branch-assert.sh right

The record is a report about the replayed impure declaration, written from
within the same invocation: the CLI's own account of which `Path` constructor
the write path branches on, which state component the branch updates, which
component it retains, and whether the exclusive branch reuses the struct cell or
the shared branch copies it. What these contracts establish is that the report
is complete for the constructor the invocation asks about: exactly one labelled
record line whose `ctor` field names that constructor, with the selected and
retained components and the exclusive and shared dispositions each bound to its
key, alongside the index shape the dump already measures. They read the labels
the report carries and require all five keys to be present exactly once; they do
not establish that those labels follow from the compiler's AST.

The report alone therefore does not prove the branch-local structure of the
replayed impure LCNF, nor the identity of the compiled backend. Establishing
that needs a separate focused check of the AST, which is not a promise this
page, or the invocation it describes, makes.

### S1

**Actor** A local Lean client invoking the measurement CLI
`scripts/dump_executor.lean` from the repository.

**Given** the sibling `../lean-examples` checkout, whose local toolchain
supplies the oleans for `Scidonia.FracPerm.StateVar.Layout5.setAt`, and the
`Path.left` write that `setAt` specifies as recursing into the state's first
component while retaining the second
(`../lean-examples/Scidonia/FracPerm/StateVar/Layout5.lean`, `setAt`).

**When** The client invokes the CLI once and reads the record the CLI prints for
that `Path` constructor.

**Then** The CLI exits 0, and its output carries exactly one structured record
whose `ctor` field names this `Path.left` constructor

    setAt branch report: ctor=Path.left; selected=0; retained=1; exclusive=reuse; shared=copy

whose values are the labels the report carries: the constructor named by the
report is `Path.left`, the labelled selected component is field 0, the labelled
retained component is field 1, the exclusive branch is labelled `reuse`, and the
shared branch is labelled `copy`, with each of the five keys bound exactly once
to its value. These are reported values — the record states them — and nothing
in this invocation establishes that the compiler's AST derives them. As the
affirmative control, the same invocation's output carries the existing
`setAt index shape:` record with its named labels, found by the same line
detector, so an invocation that never reached the structured write path is told
apart from a constructor the CLI did not report.

**Why** The left-constructor branch is the one that writes the first component
in place, and the report is complete only when the CLI emits one labelled
record for the requested constructor; a report that omits `Path.left`, or folds
both constructors into a single line, leaves the request unanswered while the
index-shape control stays green. The property is completeness of the report,
not validation that the compiler's AST branches as labelled.

### S2

**Actor** A local Lean client invoking the measurement CLI
`scripts/dump_executor.lean` from the repository.

**Given** the sibling `../lean-examples` checkout, whose local toolchain
supplies the oleans for `Scidonia.FracPerm.StateVar.Layout5.setAt`, and the
`Path.right` write that `setAt` specifies as recursing into the state's second
component while retaining the first
(`../lean-examples/Scidonia/FracPerm/StateVar/Layout5.lean`, `setAt`).

**When** The client invokes the CLI once and reads the record the CLI prints for
that `Path` constructor.

**Then** The CLI exits 0, and its output carries exactly one structured record
whose `ctor` field names this `Path.right` constructor

    setAt branch report: ctor=Path.right; selected=1; retained=0; exclusive=reuse; shared=copy

whose values are the labels the report carries: the constructor named by the
report is `Path.right`, the labelled selected component is field 1, the labelled
retained component is field 0, the exclusive branch is labelled `reuse`, and the
shared branch is labelled `copy`, with each of the five keys bound exactly once
to its value. These are reported values — the record states them — and nothing
in this invocation establishes that the compiler's AST derives them. As the
affirmative control, the same invocation's output carries the existing
`setAt index shape:` record with its named labels, found by the same line
detector, so an invocation that never reached the structured write path is told
apart from a constructor the CLI did not report.

**Why** The right-constructor branch is the one that writes the second component
in place, and the report is complete only when the CLI emits one labelled
record for the requested constructor; a report that omits `Path.right`, or folds
both constructors into a single line, leaves the request unanswered while the
index-shape control stays green. The property is completeness of the report,
not validation that the compiler's AST branches as labelled.
