# Evidence: the `store8` kernel refinement

Recorded 2026-11-26. No Lean, Lake, Nix or clang command was run on the local
machine. Every compilation and every build below ran on the worker, reached
over IAP; the local side only copied files and ran `sed`.

## Inputs

| Input | Value |
| --- | --- |
| ownership base commit | `6453893`; it already tracks `llvm-bridge/c/store8.c` (the kernel source was committed by the repository owner at 13:10 during the work), and the rest of `llvm-bridge/` plus one `README.md` hunk are this change's working-tree delta |
| sibling LeanLLVM commit | `e88ee2d` (`2026-11-26 JSON: the residue table follows the walk's own statuses`) |
| sibling core modules | clean: `git status --short` empty for `Basic`, `Syntax`, `Semantics`, `Memory`, `Frames`, `Parser`, `Printer`, `Binary64`, `lean-toolchain` |
| bridge toolchain | `leanprover/lean4:v4.35.0` (the sibling's; ownership's own packages are at `v4.35.0-rc3`) |
| worker | GCE instance over IAP, `hostname` `nixos`, Linux 6.18.63, NixOS `26.05.20261116.f684076` |
| lake | `Lake version 5.0.0-src (Lean version 4.35.0)`, `Lean (version 4.35.0, Release)` |
| clang | `clang version 21.1.8` |
| llvm-as | `LLVM (http://llvm.org/): 26.05.20261116.f684076 (Yarara)` — a second LLVM on the image; it accepted clang 21's emission |

## IR provenance

`ir/store8.raw.ll` and `ir/store8.ll` are the outputs of

```
clang -std=c11 -S -emit-llvm -O1 -o store8.raw.ll store8.c
llvm-as store8.raw.ll -o /dev/null
sed -E -f project-ir.sed store8.raw.ll > store8.ll
```

run by `scripts/emit-ir.sh` in the worker's `llvm/emit` directory. The
reproduction check (same script, `--check`) observed

```
clang: clang version 21.1.8
emit-ir: the committed IR reproduces from c/store8.c on the worker
```

hashes of the committed files:

```
sha256 c/store8.c       = eb4685867ffbbce05431fb0d01a6c0e2f6d7286379de498af4a1f9ad50ed0ae4
sha256 ir/store8.raw.ll = b19cb873ee1541cc0c78d4a857b85990ac7dda10894fd8fa077111c9ec7de5c2
sha256 ir/store8.ll     = 27c4d010cc92b6b955a7a35cad69dd878dc69b0ee120e61e64b76e8166724b8f
```

`LlvmBridge/Store8.lean` embeds `ir/store8.ll` through `include_str` and pins
the parser's result against the literal AST:

```lean
#guard decide (firstFunction store8Text = some store8IR)
```

so a drift between the committed IR file and the `Function` the theorems mention
fails `lake build`.

## Build

Command (on the local side; the build itself ran on the worker):

```
scripts/build-remote.sh --session <worker-session> \
  --remote /path/to/gcloud-remote.ts \
  --lake /nix/store/bkkg0bxfw5xl46icjwkd1ap9d0f19rd3-lean4-4.35.0/bin/lake
```

The worker's `lake` on `PATH` is a project wrapper that injects lean-llvm's
package set and fails without its stamps directory, so the plain binary is named
explicitly. Before this run, `~/llvm/lean-llvm/.lake` and
`~/llvm/llvm-bridge/.lake` were deleted on the worker, so the transcript below is
a from-source build of the pushed tree, not a replay of earlier artifacts.

```
lake: /nix/store/bkkg0bxfw5xl46icjwkd1ap9d0f19rd3-lean4-4.35.0/bin/lake
Lake version 5.0.0-src (Lean version 4.35.0)
Lean (version 4.35.0, Release)
clang version 21.1.8
✔ [3/13] Built LeanLLVM.Basic (842ms)
✔ [4/13] Built LeanLLVM.Syntax (1.6s)
✔ [5/13] Built LeanLLVM.Printer (544ms)
⚠ [6/13] Built LeanLLVM.Binary64 (2.8s)
✔ [7/13] Built LeanLLVM.Parser (2.0s)
⚠ [8/13] Built LeanLLVM.Semantics (7.7s)
⚠ [9/13] Built LeanLLVM.Memory (6.4s)
✔ [10/13] Built LeanLLVM.Frames (315ms)
✔ [11/13] Built LlvmBridge.Store8 (608ms)
✔ [12/13] Built LlvmBridge (204ms)
Build completed successfully (13 jobs).
'LlvmBridge.runFuel_store8IR_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'LlvmBridge.Beh_store8IR_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'LlvmBridge.store8IR_refines_model' depends on axioms: [propext, Classical.choice, Quot.sound]
'LlvmBridge.store8IR_completes' depends on axioms: [propext, Classical.choice, Quot.sound]
'LlvmBridge.store8IR_frame' depends on axioms: [propext]
'LlvmBridge.store8Model_replay_read' depends on axioms: [propext]
'LlvmBridge.Beh_store8Ref_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'LlvmBridge.store8IR_refines_store8Ref' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`⚠` marks a build that emitted warnings, not a failed module; the warnings are
LeanLLVM's own (deprecated `if_pos`/`if_neg` spellings and unused simp arguments
in `Binary64`, `Semantics`, `Memory`), elided from this excerpt, and none comes
from `LlvmBridge`. The full transcript is 232 lines and contains no `error`.

Two things the transcript shows about the check itself:

* `LlvmBridge.Store8` was elaborated, not replayed, in this run — the theorems
  and the two `#guard` pins were re-checked against the pushed IR file.
* The axiom lines are the ones `scripts/check-axioms.lean` prints; the same
  footprints are pinned inside the module with `#guard_msgs`, and a mismatch
  fails the build. A `sorryAx` entry was observed while the module was being
  developed (a failed proof left a hole and the pin refused it), which is what
  makes the clean footprint a check rather than a print.

## What this record establishes

One kernel-checked refinement exists for a clang-emitted body, with no `sorry`
and no axiom beyond the repository's standard `propext`/`Classical.choice`/
`Quot.sound` floor: the emitted `store8` runs to `void` and writes the argument
byte at `p + i`, and every behaviour of the compiled body is a behaviour of a
reference kernel whose meaning is the model byte store. The IR the theorem is
about is the committed emission, and the emission reproduces from the committed
C on the worker.

It does not itself relate that byte memory to the ownership invariant; the
section below records the build of the composition that does.

# Evidence: the composed ownership theorem

Recorded 2026-11-26, after the record above. No Lean, Lake, Nix or clang command
was run on the local machine for this section; every compilation below ran on the
worker.

## Inputs

| Input | Value |
| --- | --- |
| ownership sources | `git archive HEAD` of commit `68dc7f5` — `Cap/` and `Cap.lean` |
| this change's ownership delta | `Cap/Integrated.lean` from the working tree — `Sealed.state`, `Sealed.state_inv`, `Sealed.eq_of_state`, `Sealed.write_ok_iff` — and `Cap/Sealed.lean`, whose observation text names the read-only projection (`maxRecDepth` is raised on its `decide` check because the claim string grew) |
| sibling LeanLLVM | `e88ee2d`, pushed from the sibling checkout (unchanged) |
| bridge toolchain | `leanprover/lean4:v4.35.0` |
| worker | GCE instance over IAP, `hostname` `nixos`, Linux 6.18.63, NixOS `26.05.20261116.f684076` |
| lake | `Lake version 5.0.0-src (Lean version 4.35.0)`, `Lean (version 4.35.0, Release)` |
| worker-side base | a fresh directory `llvm-compose` under the login home, used for the final build below |

`sha256` of the Lean and Lake inputs the build compiled:

```
caefba53655cb3a3116e9a4229c592a2a513308058f479d4f0bbec3f5f6e434d  Cap/Integrated.lean
953f1c3cc92651786024e67fbae85611e47b2eff8678c0c6b5228f119137fdea  Cap/Sealed.lean
483b6c5117c8bb1db20dc07b32def8b3e7387200a024ab9f81a553d56f94fe2c  LlvmBridge/Ownership.lean
67f9af68135cb58d357c31c4cd352785d062ce6483cf5d1e38807d5b6d0a9e8b  lakefile.toml
bf19df2b7f5a2c21f61c8a79902990cab162b148908ab69ea9b13ae73e01976d  scripts/worker-ownership-lakefile.toml
```

### Why the sources are a snapshot

The live working tree contained an uncommitted, in-progress addition to
`Cap/Reconstruction.lean` (1058 added lines) and untracked `Cap/Authority.lean`
and `Cap/UFIntegrated.lean`, none of it part of this change. A build of that
live tree fails inside the added proofs: the first build attempted for this
change observed 33 errors, the first at `Cap/Reconstruction.lean:499:44` —

```
Application type mismatch: The argument
  List.mem_append.mpr (Or.inl hm)
has type
  c1 ∈ List.map Leaf.id l.nodes ++ ?m.189
but is expected to have type
  c1 ∈ List.map Leaf.id (l.nodes ++ r.nodes)
```

so the record pins its inputs to the committed tree plus this change's
`Cap/Integrated.lean`:

```bash
snap=<snapshot directory>
git archive HEAD Cap Cap.lean | tar -x -C "$snap"
cp Cap/Integrated.lean "$snap/Cap/Integrated.lean"
cp Cap/Sealed.lean "$snap/Cap/Sealed.lean"
```

## Command

```bash
cd llvm-bridge
LLVM_BRIDGE_REMOTE=<path to gcloud-remote.ts> scripts/build-remote.sh \
  --session <worker-session> \
  --lake /nix/store/bkkg0bxfw5xl46icjwkd1ap9d0f19rd3-lean4-4.35.0/bin/lake \
  --ownership <snapshot directory> \
  --dir llvm-compose
```

The three `.lake` directories of the worker-side base were deleted before the
run, so the transcript is a from-source build of the pushed tree.

## Transcript

```
lake: /nix/store/bkkg0bxfw5xl46icjwkd1ap9d0f19rd3-lean4-4.35.0/bin/lake
Lake version 5.0.0-src (Lean version 4.35.0)
Lean (version 4.35.0, Release)
clang version 21.1.8
✔ [4/30] Built Cap.Id (412ms)
✔ [5/30] Built LeanLLVM.Basic (1.1s)
⚠ [6/30] Built Cap.Bytes (694ms)
✔ [7/30] Built Cap.Backend (435ms)
⚠ [8/30] Built Cap.Ledger (1.3s)
⚠ [9/30] Built Cap.Retag (1.3s)
⚠ [10/30] Built Cap.Loans (1.3s)
⚠ [11/30] Built Cap.Join (1.5s)
✔ [12/30] Built LeanLLVM.Syntax (2.9s)
⚠ [13/30] Built Cap.Context (471ms)
⚠ [14/30] Built Cap.World (641ms)
✔ [15/30] Built LeanLLVM.Printer (1.1s)
⚠ [16/30] Built Cap.Invariant (1.3s)
⚠ [17/30] Built LeanLLVM.Binary64 (4.8s)
⚠ [18/30] Built Cap.History (427ms)
⚠ [19/30] Built Cap.WorldInvariant (1.0s)
⚠ [20/30] Built Cap.Reconstruction (2.1s)
✔ [21/30] Built LeanLLVM.Parser (4.9s)
⚠ [22/30] Built Cap.Integrated (2.8s)
✔ [23/30] Built Cap.Sealed (2.1s)
⚠ [24/30] Built LeanLLVM.Semantics (10s)
⚠ [25/30] Built LeanLLVM.Memory (6.6s)
✔ [26/30] Built LeanLLVM.Frames (377ms)
✔ [27/30] Built LlvmBridge.Store8 (734ms)
✔ [28/30] Built LlvmBridge.Ownership (477ms)
✔ [29/30] Built LlvmBridge (253ms)
Build completed successfully (30 jobs).
'LlvmBridge.runFuel_store8IR_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'LlvmBridge.Beh_store8IR_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'LlvmBridge.store8IR_refines_model' depends on axioms: [propext, Classical.choice, Quot.sound]
'LlvmBridge.store8IR_completes' depends on axioms: [propext, Classical.choice, Quot.sound]
'LlvmBridge.store8IR_frame' depends on axioms: [propext]
'LlvmBridge.store8Model_replay_read' depends on axioms: [propext]
'LlvmBridge.Beh_store8Ref_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'LlvmBridge.store8IR_refines_store8Ref' depends on axioms: [propext, Classical.choice, Quot.sound]
'LlvmBridge.store8_exec_write_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'LlvmBridge.sealed_store8_write_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'LlvmBridge.write_authority' depends on axioms: [propext]
'LlvmBridge.runFuel_store8_at_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'LlvmBridge.store8IR_refines_model_at_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`⚠` marks a build that emitted warnings, not a failed module. The full transcript
is 793 lines: no line contains `error` and no line contains `sorry`. The 165
warning lines are `Cap`'s and `LeanLLVM`'s own under Lean 4.35.0 (deprecated
`if_pos`, `if_neg`, `dif_pos`, `dif_neg` spellings and unused simp arguments);
neither `LlvmBridge` module emits a warning.

## What this record establishes

* The `Cap` closure the bridge imports — `Cap.Id`, `Cap.Bytes`, `Cap.Backend`,
  `Cap.Ledger`, `Cap.Retag`, `Cap.Loans`, `Cap.Join`, `Cap.Context`, `Cap.World`,
  `Cap.Invariant`, `Cap.History`, `Cap.WorldInvariant`, `Cap.Reconstruction`,
  `Cap.Integrated`, `Cap.Sealed` — compiles under Lean 4.35.0 from the pinned
  snapshot, including this change's additions to `Cap/Integrated.lean`.
* The composed statement is kernel-checked with no `sorry` and no axiom beyond
  the floor: `store8_exec_write_comp` and `sealed_store8_write_comp` depend on
  `[propext, Classical.choice, Quot.sound]`, `write_authority` on `[propext]`,
  and the memory-parametric kernel lemmas on the same floor. The three headline
  footprints are pinned in the module with `#guard_msgs`, so a change fails the
  build rather than this audit.
* The `store8` kernel theorems are unchanged: `LlvmBridge/Store8.lean` is not
  modified, and its axiom lines above are the ones recorded in the section
  before this one.

## Separate toolchain pins

The bridge is built at the sibling's `leanprover/lean4:v4.35.0` pin. The
ownership repository pins `v4.35.0-rc3`; after this record's bridge run, the
pinned rc3 closure was copied to the worker and the changed `Cap` package was
built separately under that pin:

```
nix develop . -c bash -c 'cd .../ownership && lake build Cap'
```

with `scidonia-lean: Lean (version 4.35.0-rc3, Release)`. The build, capability
controls, axiom audit and 126-row docs census all passed. This rc3 result is
evidence about `Cap` only; the composed theorem in this directory remains a
4.35.0-release build. The two results are not treated as interchangeable, and
the bridge's `Cap` oleans are not claimed to be an rc3 artifact.

## Scope of the theorem

The theorem is about one allocation, one caller-supplied window (`off ↦ base +
off`) and one write. `llvm-bridge/README.md` states every remaining assumption:
the representation premise (`MemRep`), the window's bounds (`off < buf.length`,
derived; `off < 2 ^ 63` for the emitted `getelementptr`), the address map's
single-allocation scope (with `MemRep.frame_write` naming the disjointness a
second allocation owes), the IR projection, the capability route, and the
executable edge.

# Evidence: the finite multi-allocation relation

Recorded 2026-11-27.  Every compilation below ran on the worker; the local side
only copied files.  No clang ran: the emitted IR is unchanged, so its recorded
provenance above still applies.

## Inputs

| Input | Value |
| --- | --- |
| ownership base commit | `97e5afa`; this change's delta is under `llvm-bridge/` only |
| this change's bridge delta | `LlvmBridge/MultiAlloc.lean` (new), `LlvmBridge/Ownership.lean` (`MemRep.frame_write` takes an arbitrary `UInt8`), `LlvmBridge.lean`, `scripts/check-axioms.lean`, `README.md`, `EVIDENCE.md` |
| sibling LeanLLVM commit | `e88ee2d`; its working tree has 35 modified files outside the bridge's import closure, and the eight imported core modules plus `lean-toolchain`/`lakefile.toml` are clean |
| bridge toolchain | `leanprover/lean4:v4.35.0` |
| lake | `/nix/store/bkkg0bxfw5xl46icjwkd1ap9d0f19rd3-lean4-4.35.0/bin/lake`, `Lake version 5.0.0-src (Lean version 4.35.0)` |
| worker | `ownership-bridge-map2-01a1a0ae`, zone `europe-west4-b`, hostname `nixos`, Linux 6.18.63 x86_64 |

`sha256` of the Lean and script inputs the build compiled:

```
ac793dffefc83b330d948137bb9f522414e059382fd4c1aaecbca2cd74c2422a  llvm-bridge/LlvmBridge/MultiAlloc.lean
4c21bf75928b6fda00145a2a3ebb7b4d5493a69b97042096e7f1089e61e24ba6  llvm-bridge/LlvmBridge/Ownership.lean
5691f98c9c56d48e554e9e3ec0e65f301d8c77967d1018f908a4783babe9f353  llvm-bridge/LlvmBridge.lean
8d23227ab9a37a719658664986e8eec897a5d7190765fa71a410b7e3b83f7408  llvm-bridge/scripts/check-axioms.lean
adca11444b8e289967f3c04cb4992ec8b4b64d3760f4d14f7d1950e7f12c06fd  Cap/AddressMap.lean
f9433588d03ad77eecb0d59304701bd996839529954b96394b940a9ea961cd1d  Cap/Integrated.lean
4d4de55dd2588e459be070ca3fe04e6dc337799f4c418d942800eee6480d9075  Cap/Sealed.lean
```

The `Cap` hashes are the committed tree's: this change adds no `Cap` source.
The worker's copies of those three files were checked to be the same bytes.

## Worker layout

The bridge is at `~/ownership/llvm-bridge`, the sibling at `~/lean-llvm`, and
the ownership package at `~/ownership`, with `~/ownership/lean-llvm` a symlink
to `../lean-llvm` so the bridge's `path = "../lean-llvm"` resolves.  The pushed
sibling's package definition was replaced by
`scripts/worker-lean-llvm-lakefile.toml` — the projection `build-remote.sh`
installs — so the Mathlib-backed `ITree` and JSON targets are outside this
build.  The sibling's sources are otherwise unmodified.  The worker's copies of
the eight core modules the bridge imports and of `lean-toolchain` were checked to
be the same bytes as this checkout's.

## Command and transcript

```bash
cd ~/ownership/llvm-bridge
rm -rf .lake ~/ownership/.lake ~/lean-llvm/.lake
lake build
lake env lean scripts/check-axioms.lean
```

with `lake` and `lean` taken from the release store path above.  All three
`.lake` directories were removed first, so the transcript is a from-source build
of the pushed tree, not a replay:

```
Lake version 5.0.0-src (Lean version 4.35.0)
Lean (version 4.35.0, Release)
✔ [4/32] Built Cap.Id (304ms)
✔ [6/32] Built LeanLLVM.Basic (906ms)
⚠ [21/32] Built Cap.Reconstruction (4.4s)
⚠ [22/32] Built Cap.Integrated (1.4s)
⚠ [23/32] Built Cap.AddressMap (814ms)
✔ [24/32] Built Cap.Sealed (2.1s)
⚠ [25/32] Built LeanLLVM.Semantics (9.6s)
⚠ [26/32] Built LeanLLVM.Memory (6.4s)
✔ [27/32] Built LeanLLVM.Frames (326ms)
✔ [28/32] Built LlvmBridge.Store8 (612ms)
✔ [29/32] Built LlvmBridge.Ownership (418ms)
✔ [30/32] Built LlvmBridge.MultiAlloc (443ms)
✔ [31/32] Built LlvmBridge (214ms)
Build completed successfully (32 jobs).
```

The excerpt elides the intermediate `Cap` and `LeanLLVM` lines; the recorded log
is 32 jobs with `errors=0`, `sorry=0` and `bridge_warnings=0`.  The 276 warning
lines are `Cap`'s and `LeanLLVM`'s own under Lean 4.35.0 (deprecated
`if_pos`/`if_neg`/`dif_pos`/`dif_neg` spellings and unused simp arguments);
neither `LlvmBridge` module emits a warning.

## Axiom audit

```
'LlvmBridge.MemRepMap.write' depends on axioms: [propext, Quot.sound]
'LlvmBridge.MemRepMap.write_len' depends on axioms: [propext]
'LlvmBridge.sealed_store8_write_comp_map' depends on axioms: [propext, Classical.choice, Quot.sound]
'LlvmBridge.memRepMap_twoAlloc' depends on axioms: [propext, Quot.sound]
'LlvmBridge.example_write_model' depends on axioms: [propext, Quot.sound]
'LlvmBridge.example_out_of_window_refused' depends on axioms: [propext, Quot.sound]
'LlvmBridge.overlapping_window_refused' depends on axioms: [propext, Quot.sound]
```

The full audit also reprints every earlier theorem with its unchanged footprint
(`store8_exec_write_comp` and `sealed_store8_write_comp` remain on
`[propext, Classical.choice, Quot.sound]`, `write_authority` on `[propext]`).
The multi-allocation footprints are pinned inside `MultiAlloc.lean` with
`#guard_msgs`, so a change fails the build rather than this audit.  No footprint
contains `sorryAx`.

## What this record establishes

* `MemRepMap` and its write preservation are kernel-checked against the committed
  `Cap.AddressMap`, with no `sorry` and no axiom beyond the bridge's floor.
* The concrete two-allocation model is inhabited in a flat memory
  (`memRepMap_twoAlloc`), the same model accepts an in-window write
  (`twoAlloc_write0_accepted`, `example_write_model`), and the out-of-window and
  overlapping-window controls are refused, so the refusal controls are not
  vacuous.
* The one-window theorems are unchanged apart from `MemRep.frame_write` taking
  an arbitrary `UInt8`; their recorded footprints are the same.

## Scope of the relation

`Cap.AddressMap.Rel` is still caller-supplied: that the map is well formed,
bounded, and covers exactly the live allocations is a premise, and that a loader
assigns those windows — or that physical storage lives at them — is not proved.
The `off < 2 ^ 63` pointer-width premise and the IR projection are as recorded
for the one-window composition.  The executable edge (ABI, native execution, a
live handle, the physical allocation) remains the sealed boundary's stated
trust.

# Evidence: the bridge against the repaired ownership invariant

Recorded 2026-11-27.  Every compilation below ran on the worker; the local side
only copied files and computed hashes.  No clang ran: the emitted IR is
unchanged, so its recorded provenance above still applies.

## Inputs

| Input | Value |
| --- | --- |
| ownership repaired revision | `451dd30` (`Record the invariant repair revision`).  The worker's ownership package is that tree: its `Cap/` tree — 55 files, `Cap.lean` included — hashes file-for-file to `git archive 451dd30 Cap Cap.lean`, and revision `6e70b45` carries the same `Cap` tree (`git diff 451dd30 6e70b45 -- Cap Cap.lean` is empty).  The build therefore compiles the repaired `State.WriteGuard` (which now carries `c.alloc = s.alloc`) and the repaired `State.Inv` (whose component invariant now carries `Coherent` and `Scope`) |
| this change's bridge delta | `LlvmBridge/Ownership.lean` (the guard is consumed as `st.WriteGuard c off`, and `c.alloc = st.alloc` is carried through `component_write_parts`, `exec_write_parts` and `write_authority`; two `#guard_msgs` pins added), `LlvmBridge/MultiAlloc.lean` (destructuring only), `scripts/check-axioms.lean` (the two new prints), `README.md` (the authority row), `EVIDENCE.md` |
| sibling LeanLLVM commit | `e88ee2d`; the eight core modules the bridge imports and `lean-toolchain` in the pushed archive are byte-identical to `git cat-file blob e88ee2d:<path>`, and the sibling checkout's `git status --short` for them is empty |
| bridge toolchain | `leanprover/lean4:v4.35.0` |
| lake | `/nix/store/bkkg0bxfw5xl46icjwkd1ap9d0f19rd3-lean4-4.35.0/bin/lake`; `Lake version 5.0.0-src (Lean version 4.35.0)`, `Lean (version 4.35.0, Release)` |
| worker | `ownership-audit-p0-01a1a0ae`, zone `europe-west4-b`, hostname `nixos`, Linux 6.18.63 x86_64, NixOS `26.05 (Yarara)` |

`sha256` of the compiled inputs, each value equal on the local checkout, the
pushed archive and (for the `Cap` files) the revision's blob:

```
9ae44a556ba1cf4cd3135610a684925d1bc820dab3147ed6a288779cc6a96982  LlvmBridge/Ownership.lean
6b26aaac39e9230778ba848b1e52dae785c4f3cf9e43587b0f8a5e1833e05dd1  LlvmBridge/MultiAlloc.lean
ead507b596b1b68dcaffcd3328bdfdda93dc3a9cbd90f1e9d399ca667c79d67f  LlvmBridge/Store8.lean
5691f98c9c56d48e554e9e3ec0e65f301d8c77967d1018f908a4783babe9f353  LlvmBridge.lean
2d6fe746a9ec3d57ceeea2fec8b9b74247c757afd8ed7509e665f095989ec1ea  scripts/check-axioms.lean
bbf32ef6ec48702548339f278d6b0623a38537d694d7b725ab32b13696bc2e0c  scripts/worker-lean-llvm-lakefile.toml
b486e85859f3767a922d4fbe47e4e2c492cf241b3a889590aec5b95eca2875c2  Cap/Reconstruction.lean
6be706342100d362183ea66dcfeda9f7fc998788dc2f32e7db0766b5503d7bb6  Cap/Integrated.lean
adca11444b8e289967f3c04cb4992ec8b4b64d3760f4d14f7d1950e7f12c06fd  Cap/AddressMap.lean
4d4de55dd2588e459be070ca3fe04e6dc337799f4c418d942800eee6480d9075  Cap/Sealed.lean
f390cdc0ed02329ec1f14655ddf73427ac885c396c3f4f9d884f5890175472f5  Cap.lean
752fedf410bb9f3bf399d4dc663018e7a4da3c62920ceae92ae6c2168e2ba58b  lakefile.toml (the ownership package's committed definition)
b59e7702e31f80f5eb71cf47f7d2f7f37dbcd4e30a36c61300a700d215b9e1ce  the sibling archive the worker extracted
```

The `Cap` manifest was compared on both sides with

```bash
git archive 451dd30 Cap Cap.lean | tar -x -C <snapshot>
(cd <snapshot> && find Cap Cap.lean -type f | sort | xargs sha256sum | sort -k2)
# on the worker:
cd ~/final_p0b && find Cap Cap.lean -type f | sort | xargs sha256sum | sort -k2
```

and the two sorted manifests were identical (`diff` empty, 55 lines each).

## Worker layout

The bridge is at `~/final_p0b/llvm-bridge`, the sibling at `~/lean-llvm`, and the
ownership package at `~/final_p0b`, with `~/final_p0b/lean-llvm` a symlink to
`../lean-llvm`, so the bridge's `path = "../lean-llvm"` and `path = ".."`
requirements resolve.  The sibling's package definition was replaced by
`scripts/worker-lean-llvm-lakefile.toml` — the projection named above — so the
Mathlib-backed `ITree` and JSON targets are outside this build.  Unlike the
earlier records, the ownership package keeps its committed `lakefile.toml`: the
bridge imports `Cap.Sealed`, and the build's 32-job list contains only `Cap.*`
modules from that package, so its other libraries and the `capuf` executable are
never built.  The worker's package holds exactly the committed `Cap` files the
manifest above lists; the local checkout's untracked `Cap/Authority.lean` is not
present there and is not part of this build.

## The breakage the repair caused

Before the bridge was changed, the committed `LlvmBridge/Ownership.lean` failed
against the repaired `Cap`.  The old proof split the write's `if` on a
five-conjunct spelling of the guard; the guard is now `st.WriteGuard c off`, so
the split never fired and the goal kept its `dite`:

```
error: LlvmBridge/Ownership.lean:233:12: Tactic `subst` failed: invalid equality proof, it is not of the form (x = t) or (t = x)
error: LlvmBridge/Ownership.lean:236:6: unsolved goals
error: LlvmBridge/Ownership.lean:432:0: ❌️ Docstring on `#guard_msgs` does not match generated message:
- info: 'LlvmBridge.store8_exec_write_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
+ info: 'LlvmBridge.store8_exec_write_comp' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
error: LlvmBridge/Ownership.lean:438:0: ❌️ Docstring on `#guard_msgs` does not match generated message:
error: LlvmBridge/Ownership.lean:444:0: ❌️ Docstring on `#guard_msgs` does not match generated message:
error: build failed
```

`Cap` itself built in that run (including `Cap.Reconstruction`, `Cap.Integrated`,
`Cap.AddressMap` and `Cap.Sealed`); the only failing target was
`LlvmBridge.Ownership`, and the `sorryAx` entries were the failed proof's
consequence, refused by the pins.  `LlvmBridge/MultiAlloc.lean` had not been
reached.

The change is the one the guard requires, not a new hypothesis: the branch is on
`st.WriteGuard c off` and the guard's five value conjuncts plus its allocation
binding are read from the six-conjunct value.  `c.alloc = st.alloc` is added to
the conclusions of `component_write_parts`, `exec_write_parts` and
`write_authority` — a strengthening derived from the guard — and every consumer
carries the extra conjunct in its `obtain`.  No theorem gains a premise, and the
statements of `store8_exec_write_comp` and `sealed_store8_write_comp` are
unchanged.

## Command and transcript

```bash
cd ~/final_p0b/llvm-bridge
rm -rf .lake ~/final_p0b/.lake ~/lean-llvm/.lake
/nix/store/bkkg0bxfw5xl46icjwkd1ap9d0f19rd3-lean4-4.35.0/bin/lake build
/nix/store/bkkg0bxfw5xl46icjwkd1ap9d0f19rd3-lean4-4.35.0/bin/lake env lean scripts/check-axioms.lean
```

All three `.lake` directories were removed first, so the transcript is a
from-source build of the pushed tree, not a replay:

```
✔ [4/32] Built Cap.Id (367ms)
✔ [5/32] Built LeanLLVM.Basic (1.1s)
⚠ [6/32] Built Cap.Bytes (662ms)
✔ [7/32] Built Cap.Backend (363ms)
⚠ [8/32] Built Cap.Ledger (1.1s)
⚠ [9/32] Built Cap.Retag (1.3s)
⚠ [10/32] Built Cap.Loans (1.3s)
⚠ [11/32] Built Cap.Join (1.5s)
✔ [12/32] Built LeanLLVM.Syntax (2.6s)
⚠ [13/32] Built Cap.Context (426ms)
✔ [14/32] Built LeanLLVM.Printer (702ms)
⚠ [15/32] Built Cap.World (401ms)
⚠ [16/32] Built Cap.Invariant (1.0s)
⚠ [17/32] Built LeanLLVM.Binary64 (4.4s)
⚠ [18/32] Built Cap.History (379ms)
⚠ [19/32] Built Cap.WorldInvariant (934ms)
✔ [20/32] Built LeanLLVM.Parser (4.6s)
⚠ [21/32] Built Cap.Reconstruction (6.5s)
⚠ [22/32] Built Cap.Integrated (1.6s)
⚠ [23/32] Built Cap.AddressMap (945ms)
✔ [24/32] Built Cap.Sealed (2.4s)
⚠ [25/32] Built LeanLLVM.Semantics (11s)
⚠ [26/32] Built LeanLLVM.Memory (7.0s)
✔ [27/32] Built LeanLLVM.Frames (376ms)
✔ [28/32] Built LlvmBridge.Store8 (722ms)
✔ [29/32] Built LlvmBridge.Ownership (480ms)
✔ [30/32] Built LlvmBridge.MultiAlloc (526ms)
✔ [31/32] Built LlvmBridge (241ms)
Build completed successfully (32 jobs).
```

`⚠` marks a build that emitted warnings, not a failed module.  The transcript is
1374 lines: no line contains `error` and no line contains `sorry`, and the 288
warning lines are `Cap`'s and `LeanLLVM`'s own under Lean 4.35.0 (deprecated
`if_pos`/`if_neg`/`dif_pos`/`dif_neg` spellings and unused simp arguments);
`grep -c '^warning: LlvmBridge/'` is 0, so neither bridge module emits a warning.

## Axiom audit

```
'LlvmBridge.runFuel_store8IR_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'LlvmBridge.Beh_store8IR_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'LlvmBridge.store8IR_refines_model' depends on axioms: [propext, Classical.choice, Quot.sound]
'LlvmBridge.store8IR_completes' depends on axioms: [propext, Classical.choice, Quot.sound]
'LlvmBridge.store8IR_frame' depends on axioms: [propext]
'LlvmBridge.store8Model_replay_read' depends on axioms: [propext]
'LlvmBridge.Beh_store8Ref_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'LlvmBridge.store8IR_refines_store8Ref' depends on axioms: [propext, Classical.choice, Quot.sound]
'LlvmBridge.store8_exec_write_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'LlvmBridge.sealed_store8_write_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'LlvmBridge.write_authority' depends on axioms: [propext]
'LlvmBridge.component_write_parts' depends on axioms: [propext]
'LlvmBridge.exec_write_parts' depends on axioms: [propext]
'LlvmBridge.runFuel_store8_at_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'LlvmBridge.store8IR_refines_model_at_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'LlvmBridge.MemRepMap.write' depends on axioms: [propext, Quot.sound]
'LlvmBridge.MemRepMap.write_len' depends on axioms: [propext]
'LlvmBridge.sealed_store8_write_comp_map' depends on axioms: [propext, Classical.choice, Quot.sound]
'LlvmBridge.memRepMap_twoAlloc' depends on axioms: [propext, Quot.sound]
'LlvmBridge.example_write_model' depends on axioms: [propext, Quot.sound]
'LlvmBridge.example_out_of_window_refused' depends on axioms: [propext, Quot.sound]
'LlvmBridge.overlapping_window_refused' depends on axioms: [propext, Quot.sound]
```

The four footprints this record is about are unchanged by the repair:
`store8_exec_write_comp` and `sealed_store8_write_comp` on
`[propext, Classical.choice, Quot.sound]`, `MemRepMap.write` on
`[propext, Quot.sound]`, and `sealed_store8_write_comp_map` on
`[propext, Classical.choice, Quot.sound]`.  No footprint contains `sorryAx`.
The two declarations whose statements changed and that were not already pinned —
`component_write_parts` and `exec_write_parts` — are pinned in `Ownership.lean`
with the `[propext]` lines the audit prints, alongside the existing
`write_authority` pin, so a later footprint change fails the build rather than
this audit.

## What this record establishes

* The bridge compiles from source against the repaired ownership invariant: the
  `Cap` tree that the worker built is the repair commit's, byte for byte, and
  the composed statements are kernel-checked with no `sorry` and no axiom beyond
  the floor.
* The repair's only effect on the bridge is the guard shape.  The branch follows
  `st.WriteGuard`, the authority's allocation binding (`c.alloc = st.alloc`) is
  derived from that guard and carried to the theorems that expose the consumed
  fragment, and nothing is assumed to make the files compile.  The composed
  theorems' statements are untouched, and `MemRepMap.write`,
  `MemRepMap.write_len` and `sealed_store8_write_comp_map` are unchanged apart
  from the extra `obtain` conjunct.
* This is a `leanprover/lean4:v4.35.0` build, like the records above; it is not
  an rc3 artifact.

## Rebuild after the recoverability invariant

The recoverability repair (`1f3777f`) adds `lenders_not_retired`, `RestoreChain`,
`Forest.Recovers`/`WellRecovered` and `State.Recovers` to `Cap` without changing
the bridge source. A from-source release build on the repaired tree completed
successfully (32 jobs), including `Cap`, `LeanLLVM`, `LlvmBridge.Store8`,
`Ownership` and `MultiAlloc`; `scripts/check-axioms.lean` exited 0 with no
`sorryAx`. The composed store and `MemRepMap` footprints remain
`[propext, Classical.choice, Quot.sound]` and unchanged.
