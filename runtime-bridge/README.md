# runtime-bridge probe

Priority 1 reproducer for the context-sensitive in-place observation: the same
`Layout5.setLeaf` path write is in place in one compiled context and copies in
another. It depends on the pinned sibling by path and does not modify it.

## Build and run

```sh
cd runtime-bridge
nix develop -c lake build
nix develop -c lake exe probe <mode>
```

The sibling must be at `66e64334a1c968d829903b8aec8d22f7e3b9fd3f` and clean; the
toolchain is the repository flake's Lean 4.35.0-rc3. Run a mode with and without
`SCIDONIA_CHECK_INPLACE=1`.

## Modes and results

| Mode | Array construction | Check off | Check on |
| --- | --- | --- | --- |
| `separate-exact` | parameterized function, exact capacity | in place, exit 0 | exit 0 |
| `separate-spare` | parameterized function, one spare slot | in place, exit 0 | — |
| `inline-exact` | pure closed construction, inline in `main` | copied, exit 0 | abort, exit 1 |
| `inline-spare` | pure closed construction, inline, spare slot | copied, exit 0 | — |
| `inline-io` | IO construction, inline in `main` | in place, exit 0 | exit 0 |
| `closed-case` | parameterless function with the pure construction | copied, exit 0 | abort, exit 1 |
| `sealed` | `Structured.runFresh` | writes `(true, true)`, exit 0 | exit 0; a mismatch exits `1`, not `2` |
| `differential` | the model's predicate corpus: unique, alias (count two), drop-back-to-one, persistent literal, closure-held | all six predictions agree, exit 0 | — (the copy cases would abort under the armed check) |

"In place" means `exclusive_before = true`, the array buffer and the focused
struct keep their addresses, and `ok = true`. Each mode asserts its observed
exclusivity, address, functional value and sealed result; an ordinary mismatch
returns `2` for every observation mode except `sealed`, which returns `1` on a
mismatch (`runtime-bridge/RuntimeBridge/Probe.lean`, `sealedCase`) and so cannot
be distinguished from the exclusivity abort by status alone. No configuration of
the current corpus drives `sealed`'s mismatch path, so no check exercises it. The
armed check's intended exclusivity abort is exit `1` together with its
diagnostic, and the gate requires both for the abort controls. Usage errors
return `64`.

## Cause

The emitted C lifts the inline/parameterless cases' pure closed computations into
`___closed` initializers called through `lean_obj_once`. The array is then a
shared constant: each access holds a reference, so the write sees a count above
one and copies. The parameterized and IO constructions are not closed, stay
local, and are exclusive. See `docs/notes/OWNERSHIP_RUNTIME_EVIDENCE.md` and
`emitted/closed-lifting.txt` for the emitted-code excerpt.

The practical rule: a user-facing path must construct its array in `IO` or from a
runtime parameter, not as a closed pure expression. The sealed `runFresh`
interface already does this; direct layout helpers on a closed constant copy, and
the armed check aborts instead of copying silently.
