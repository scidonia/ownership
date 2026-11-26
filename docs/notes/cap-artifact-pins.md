# Artifact pins and verification record

Baseline: `aaf94d033a774ef5fc23e4410e560bacd85dc2d2`. Code source and
verified build: `a98a4bb84e56ed65fc055e4938a1821ae3da0326`. This record is the
commit that adds this file and changes no code.

## Toolchains

| Package | Pin | Build observed |
| --- | --- | --- |
| ownership `Cap` | `leanprover/lean4:v4.35.0-rc3` | `Lean (version 4.35.0-rc3, Release)` |
| `llvm-bridge` and sibling LeanLLVM `e88ee2d` | `leanprover/lean4:v4.35.0` | `Lean (version 4.35.0, Release)`, `Lake version 5.0.0-src` |

The rc3 closure was copied to the worker as a realised Nix closure. The two
builds are separate and neither is presented as evidence for the other pin.

## Ownership gates (rc3)

```
nix develop . -c bash -c 'cd .../ownership && lake build Cap'
nix develop . -c bash scripts/check_cap_controls.sh
nix develop . -c lake env lean scripts/check_cap_axioms.lean
bash scripts/check_cap_docs.sh --rev WORKTREE
lake build capuf
./.lake/build/bin/capuf
```

Observed: `lake build Cap` completed (the later executable build reports 74 jobs
for the package plus driver); `capability controls: OK`; the axiom audit exited
`0` with no `sorryAx` and only the standard `propext`, `Classical.choice`,
`Quot.sound` footprints; the docs census reported `OK (126 rows)`.

The compiled driver printed:

```
capuf: roots 0,0,0; parents (some [0, 0, 0, 0, 0]); unrelated (some [5, 0, 0])
```

It executes two successive general finds through `Sealed`, then repeats them
with an unrelated allocation, failing if a root, parent array or unrelated byte
differs. It is a five-byte fixture, not a large-scale performance result.

## Bridge

`llvm-bridge/EVIDENCE.md` records the release-toolchain build of the composed
`store8` theorem, the LeanLLVM commit `e88ee2d`, the clang emission and the IR
reproduction. The rc3 run above covers `Cap` only; the composed bridge theorem is
not claimed as an rc3 artifact.

## Manuscript

`paper/sealed-ownership.pdf` (16 pages) and `report/capability-report.pdf`
(18 pages) were rebuilt with `latexmk -g -pdf -interaction=nonstopmode` from the
changed sources.

## Stated gaps

- `Cap/UFGeneric.WriteFrame` frames observations, not a per-allocation
  `Storage` component; no separate storage-frame lemma is claimed.
- The parent representation caps `n ≤ 256`.
- The bridge covers one allocation and one caller-supplied window; the
  multi-allocation address map, ABI, native installation and copied-handle
  replay remain outside the proved boundary.
