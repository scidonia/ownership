# llvm-bridge — one compiled C kernel, refined through LeanLLVM

The smallest real compiled-C → LLVM refinement this repository can state: clang
compiles a one-byte store kernel, `LeanLLVM.Parser` reads the emitted IR, and a
kernel-checked theorem relates the emitted body's execution to a reference
store semantics.

It answers the first half of the review's F8 boundary requirement — *prove one
useful kernel refinement through that boundary* — and nothing else. The
ownership invariant is not related to this memory; the last section states
exactly what would remain.

## Files

| Path | Contents |
| --- | --- |
| `c/store8.c` | the kernel: `void store8(uint8_t *p, uint64_t i, uint8_t v) { p[i] = v; }` |
| `ir/store8.raw.ll` | clang's emission, verbatim |
| `ir/store8.ll` | the same emission projected onto the parser's accepted surface |
| `scripts/project-ir.sed` | the projection, rule by rule |
| `scripts/emit-ir.sh` | compiles `c/store8.c` **on the worker** and installs or checks `ir/` |
| `scripts/build-remote.sh` | pushes the sibling and this package to the worker and builds |
| `scripts/worker-lean-llvm-lakefile.toml` | the pushed copy's LeanLLVM package definition |
| `scripts/check-axioms.lean` | prints the theorem footprints for the build log |
| `LlvmBridge/Store8.lean` | the AST pin, the reference store, and every theorem |
| `EVIDENCE.md` | the recorded remote build and the provenance of the IR |

## Provenance of the IR

```
clang -std=c11 -S -emit-llvm -O1 -o store8.raw.ll store8.c
llvm-as store8.raw.ll -o /dev/null          # the emission is valid IR
sed -E -f project-ir.sed store8.raw.ll > store8.ll
```

`-O1` is deliberate: at `-O0` clang spills the three parameters to `alloca`s
and reloads them, which is a different (larger) body; the kernel boundary here
is the optimised one. `llvm-as` accepting the raw emission is part of the
provenance — the clang output is IR before any of this repository's processing.

The projection removes only surface the model does not represent: the
function's attribute group, the parameter attributes (`noundef`, `zeroext`,
`nocapture`, `captures(none)`, `writeonly`), `local_unnamed_addr`, the TBAA
metadata attachment, the `nuw` promise on the `getelementptr`, the module-level
`source_filename`/`target`/`attributes`/named-metadata lines, and the absent
first-block label (inserted as `entry:`). No modelled instruction is rewritten;
`scripts/project-ir.sed` states the reason for each rule. Two surviving tokens
are accepted-and-dropped by the parser: `inbounds` on the `getelementptr` and
`align 1` on the store — the model has no field for either.

The pin is a build gate, not a comment:

```lean
def store8Text : String := include_str "../ir/store8.ll"
#guard decide (firstFunction store8Text = some store8IR)
```

`#guard` rather than `rfl` because the parser runs on `String` primitives the
kernel does not reduce. A drift between `ir/store8.ll` and `store8IR` fails
`lake build`.

## Theorems

`B` is `LeanLLVM.Beh`; `A p x v` is `store8Args p x v = [.ptr p, .int 64 x, .int 8 v]`;
`S p x v` is `store8Model [] p x.toNat (byteOf v) = writeByte [] (p + x.toNat) (byteOf v)`;
`H` is `x.toNat < 2 ^ 63` (the `getelementptr` adding case).

| Theorem | Statement | Axioms |
| --- | --- | --- |
| `runFuel_store8IR_succ` | from any state binding the three parameters, one control step yields `some (.ret none (writeByte s.mem (p+x.toNat) (byteOf v)))` | `propext, Classical.choice, Quot.sound` |
| `runFuel_store8IR` | the same at `initState` for `A p x v` | same |
| `Beh_store8IR_iff` | `B noCalls store8IR (A p x v) out ↔ out = .ret none (S p x v)` — one outcome, no `ub` run, no divergent run | same |
| `store8IR_refines_model` | every behaviour is the model store's outcome | same |
| `store8IR_completes` | the model store's outcome is a behaviour | same |
| `store8IR_byte` | the byte at the computed address reads back as the argument byte | `propext` |
| `store8IR_frame` | outside `{p + off}` the memory agrees (`AgreesOutsideMem`) | `propext` |
| `store8Model_replay_read` | a repeated identical write is unobservable | `propext` |
| `Beh_store8Ref_iff` | the reference kernel's behaviour is the same single outcome | `propext, Classical.choice, Quot.sound` |
| `store8IR_refines_store8Ref` | every compiled behaviour is a reference-kernel behaviour, for **every** `p`, `x`, `v`: where `H` fails the reference is `ub` and so admits the compiled outcome | same |

The `ub` and divergence directions are discharged rather than assumed: there is
no `ub` prefix at the argument list (the block's only step returns), and the
outcome is produced at fuel one on every budget.

Why the last row is a refinement and not a restatement: the reference side is
an AST (`store8Ref`: `call void @store8.model(...)`) whose meaning is a `Calls`
environment (`store8Calls`) writing the model store's byte. The inclusion is
between the compiled body's behaviours (empty call environment) and that
kernel's — the shape `Refines` compares, at the target's whole argument shape.

## Build and run

The sibling must be a `lean-llvm` checkout at Lean `v4.35.0` (the bridge's
`lean-toolchain`); `EVIDENCE.md` records the commit its core modules were built
from. The ownership package is at `v4.35.0-rc3`, which is why this is a separate
package and why it cannot import `Cap`.

**On the worker** (the route this session used; nothing is built locally):

```bash
cd llvm-bridge
LLVM_BRIDGE_REMOTE=/path/to/gcloud-remote.ts scripts/build-remote.sh \
  --session <worker-session> \
  --lake /nix/store/<lean4-4.35.0>/bin/lake
```

A worker whose `lake` on `PATH` is a project wrapper injecting a package set
(the lean-llvm image's `lake` does exactly this and fails without its stamps
directory) needs `--lake` naming the plain binary. The script copies
`../lean-llvm` and this package to the worker, replaces the pushed copy's
`lakefile.toml` with `scripts/worker-lean-llvm-lakefile.toml` (no Mathlib
requirement; the core modules are the roots), builds, and prints the axiom
audit. The sibling checkout is never modified.

**In the flake** (the sibling tree's own shell, same Lean):

```bash
cd llvm-bridge
nix develop ../lean-llvm -c lake build
nix develop ../lean-llvm -c lake env lean scripts/check-axioms.lean
```

This session ran no local build; the recorded build is the worker's
(`EVIDENCE.md`).

**Reproduce the IR** (compiles on the worker, compares with `ir/`):

```bash
LLVM_BRIDGE_REMOTE=/path/to/gcloud-remote.ts scripts/emit-ir.sh \
  --session <worker-session> --check
```

## What is not claimed

The theorem is about LeanLLVM's byte memory. The ownership model's observable
that corresponds is `Cap.State.read?` (via `Cap.Heap.read?` / `Cap.Backend.read`)
at `(AllocId, offset)`; the byte update corresponds to `Cap.Backend.write`; the
access obligation corresponds to the `Writable` guard of `Cap.World.write?` and
the reachability state `Cap.World.Rel`; the frame corresponds to
`Cap.Footprint.View.Within` and `Cap.Heap.write_ne`; snapshots correspond to
`Cap.Heap.snapshot?` (unaffected by later writes, `Cap.Bytes.snapshot_independent`).

The exact remaining relation, none of it proved here:

1. an address map from `AllocId × Nat` into the flat memory, with a proof that a
   live allocation's bytes are its backend's buffer (the two ends are
   `LeanLLVM.Globals` and `Cap.AllocId`);
2. a call-site `Writable` guard discharged by an actual `Cap` run, including the
   length/within-bounds fact that `LeanLLVM` does not model (an absent cell is
   created by a write, so "in bounds" is an assumption here, not a theorem);
3. preservation of `Cap.State.Inv` / `FullInv` across the call, and the
   physical-aliasing, snapshot and replay policy for two `Cap` values reaching
   one mutable allocation.

The kernel allocates nothing (`alloca`-free; the reference environment returns
`next` unchanged) and frees nothing, so allocation failure and cleanup have no
path in this body. `store8Model_replay_read` is idempotence of the *model*
memory, not a statement about sealed-value copies.
