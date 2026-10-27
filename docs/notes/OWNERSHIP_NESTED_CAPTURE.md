# Captured nested update prefix and provenance

Date: 27 October 2026
Repository: `scidonia/ownership`, main at `dc0f281`
Pinned sibling: `lean-examples` at `66e64334a1c968d829903b8aec8d22f7e3b9fd3f`
Toolchain: Lean `4.35.0-rc3` from the repository flake
Artifact: `docs/notes/artifacts/setAt-nested.lcnf.txt`

## Acquisition route

```sh
cd ../lean-examples
nix develop -c lake env lean ../ownership/scripts/capture_nested.lean \
  > ../ownership/docs/notes/artifacts/setAt-nested.lcnf.txt
```

The script reads each declaration's mono IR from the imported olean, replays the
remainder of the mono pipeline after `saveMono` and then the full impure
pipeline, and prints the impure declaration with its size and content digest.
This is the same pass sequence `scripts/dump_executor.lean` uses. The compiler
runs in a separate `lean` process from the sibling checkout; no custom compiler
options are passed, so the captured code is the flake's default pipeline at the
pinned sibling revision.

## Captured declarations

| Declaration | Size | Digest |
| --- | --- | --- |
| `setAt` (private) | 81 | `17644656787385327013` |
| `takeOut` (private) | 3 | `6417109891623298338` |
| `inBounds` (private) | 21 | `15393521060650254261` |
| `stateDefault` | 33 | `4430873225874980118` |
| `assertExclusiveArrayImpl` | 1 | `14543362650369266955` |
| `assertExclusiveArrayImpl._redArg` | 18 | `17616022044830371737` |
| `assertExclusiveImpl` | 1 | `5884188167294317440` |
| `assertExclusiveImpl._redArg` | 10 | `7992479402402180708` |

The `Path.index` alternative of `setAt` is the nested target: projections and
increments for the path's array, index and continuation; the node's decrement;
the `Array.size`/`Nat.decLt` bounds test; the exclusive-array assertion; the
default state; the `takeOut` pair; the pair projections and increments; the
child exclusivity assertion; the recursive `setAt` call with the parent array,
the index and the asserted child; the `Array.set` restore; and the index
decrement before the return.

## Runtime configuration

The two assertion helpers test `Scidonia.FracPerm.inplaceCheck`, which is
initialized from `SCIDONIA_CHECK_INPLACE == "1"`. The capture is static, so the
recorded code contains both branches: the reporting branch and the exclusive
branch. The ownership model corresponds to the exclusive branch; the reporting
branch is runtime instrumentation and is not given a model counterpart.

## Not captured

- The `Array.size`, `Array.getInternal`, `Array.set` and `Nat.decLt`
  primitives.
- The continuation `k` behind the closed constants, and the body of the
  recursive callee beyond the call itself.
- The reference-counting effects of the index's `inc`/`dec` pair; those are
  named non-claims in the boundary note.
