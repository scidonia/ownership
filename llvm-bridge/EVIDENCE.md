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

## Toolchain limitation

`Cap`'s modules are elaborated here by the bridge's Lean (4.35.0). The ownership
repository pins `v4.35.0-rc3` in its own `lean-toolchain`, and the worker has no
rc3 toolchain (`/nix/store` shows the 4.35.0 release builds only), so the
repository's own pinned build of the changed `Cap/Integrated.lean` **was not
run**. The added declarations use only the module's existing vocabulary
(`unfold`, `split`, `cases`, `simp`, `rw`, `Subsingleton.elim`) and add no
import; the pinned build must still be run separately. Nothing in this record
is evidence about it.

## Scope of the theorem

The theorem is about one allocation, one caller-supplied window (`off ↦ base +
off`) and one write. `llvm-bridge/README.md` states every remaining assumption:
the representation premise (`MemRep`), the window's bounds (`off < buf.length`,
derived; `off < 2 ^ 63` for the emitted `getelementptr`), the address map's
single-allocation scope (with `MemRep.frame_write` naming the disjointness a
second allocation owes), the IR projection, the capability route, and the
executable edge.
