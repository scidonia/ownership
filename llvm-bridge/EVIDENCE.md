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

It does not establish any relation between that byte memory and the ownership
invariant; `llvm-bridge/README.md` states the three obligations that remain.
