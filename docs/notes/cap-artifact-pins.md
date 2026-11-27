# Artifact pins and verification record

Baseline: `aaf94d033a774ef5fc23e4410e560bacd85dc2d2`. Code source and
verified build: `985f2b0a67a554cfde30dc1edefa4c56a246a0b6`. This record is the
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

Observed: `lake build Cap` completed (the committed-tree executable build reports 76 jobs
for the package plus driver); `capability controls: OK`; the axiom audit exited
`0` with no `sorryAx` and only the standard `propext`, `Classical.choice`,
`Quot.sound` footprints; the docs census reported `OK (159 rows)`.

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

`paper/sealed-ownership.pdf` (18 pages) and `report/capability-report.pdf`
(20 pages) were rebuilt with `latexmk -g -pdf -interaction=nonstopmode` from the
changed sources.

## Stated gaps

- The invariant repair adds `Forest.Coherent` and `State.Scope`, an allocation-binding write guard, and `State.Inv.restore_terminal_frontier`; the two audit witnesses are kernel-checked regressions in `bench/CapInvariantWitness.lean`.
- `Cap/UFGeneric.WriteFrame` now equates every unrelated allocation's full
  `Reconstruction.State`, with `component_other`, `storage_other` and
  `rel_write`. The command-list frame follows from `State.run_frames_other` and
  `Sealed.run_frames_other` (`Sealed.RunFrame`), with `Rel.run_other` carrying it
  across a list for the address map. The bridge's `MemRepMap.write` carries the
  same frame into `lean-llvm`'s byte memory for the one written range.
- `Cap/AddressMap.lean` is a finite logical window model with disjointness and
  alloc/free/write framing; `LlvmBridge/MultiAlloc.lean` relates it to the
  bridge's byte memory (`MemRepMap`, `MemRepMap.write`,
  `sealed_store8_write_comp_map`), so it is wired into `llvm-bridge`. It is
  still not a loader's address assignment.
- The parent representation caps `n ≤ 256`.
- The bridge's proved boundary covers one allocation against one caller-supplied
  window (`LlvmBridge/Ownership.lean`) and the finite multi-allocation map with
  its two-allocation concrete model (`LlvmBridge/MultiAlloc.lean`). A loader's
  address assignment, ABI, native installation and copied-handle replay remain
  outside the proved boundary. The trust split is recorded in
  `docs/notes/executable-edge-contract.md`.
