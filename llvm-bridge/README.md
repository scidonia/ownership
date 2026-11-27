# llvm-bridge — one compiled C kernel, refined through LeanLLVM

The smallest real compiled-C → LLVM refinement this repository can state: clang
compiles a one-byte store kernel, `LeanLLVM.Parser` reads the emitted IR, and a
kernel-checked theorem relates the emitted body's execution to a reference
store semantics.

It answers both halves of the review's F8 boundary requirement for one
authorized write: *prove one useful kernel refinement through that boundary*,
and *compose that refinement with an ownership state*. `LlvmBridge/Store8.lean`
proves the kernel half against LeanLLVM's byte memory. `LlvmBridge/Ownership.lean`
relates one `Cap.Integrated` allocation's heap bytes to that memory at an
explicit address map and proves the composed statement, and
`LlvmBridge/MultiAlloc.lean` extends that relation to a finite map: every live
allocation has a window, the memory holds each window's buffer, and an accepted
write preserves the relation while framing every other allocation. The last
sections state exactly what the composition assumes and what remains.

## Files

| Path | Contents |
| --- | --- |
| `c/store8.c` | the kernel: `void store8(uint8_t *p, uint64_t i, uint8_t v) { p[i] = v; }` |
| `ir/store8.raw.ll` | clang's emission, verbatim |
| `ir/store8.ll` | the same emission projected onto the parser's accepted surface |
| `scripts/project-ir.sed` | the projection, rule by rule |
| `scripts/emit-ir.sh` | compiles `c/store8.c` **on the worker** and installs or checks `ir/` |
| `scripts/build-remote.sh` | pushes the sibling, the ownership `Cap` projection and this package to the worker and builds |
| `scripts/worker-lean-llvm-lakefile.toml` | the pushed LeanLLVM copy's package definition |
| `scripts/worker-ownership-lakefile.toml` | the pushed `Cap` projection's package definition |
| `scripts/check-axioms.lean` | prints the theorem footprints for the build log |
| `LlvmBridge/Store8.lean` | the AST pin, the reference store, and the kernel theorems |
| `LlvmBridge/Ownership.lean` | the address map, the memory representation, and the composed ownership theorems |
| `LlvmBridge/MultiAlloc.lean` | the finite multi-allocation relation `MemRepMap`, its write preservation and sealed composition, and the two-allocation model with its refused controls |
| `EVIDENCE.md` | the recorded remote builds and the provenance of the IR |

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

## The composed ownership theorem

`LlvmBridge/Ownership.lean` relates one `Cap.Integrated` allocation's heap bytes
to `LeanLLVM`'s byte memory and composes that relation with the emitted body.

The address map is the one a single live allocation admits: offset `off` of an
allocation placed at `base` is the flat address `base + off` (`allocAddr`), and
`allocAddr_injective` records that the window is injective. `MemRep m buf base`
says the flat memory holds the allocation's buffer at that map. Nothing here
assigns `base`: the caller supplies the window and the representation premise,
and `MemRep.frame_write` states the disjointness a second allocation's window
needs before the frame can be read for it.

For one accepted integrated write — `Cap.Sealed.write`, which
`Cap.Integrated.Sealed.write_ok_iff` identifies with the underlying
`State.exec (.write …)` — the file proves:

| Theorem | Statement |
| --- | --- |
| `write_authority` | the write consumed a current (`findLeaf?`), active, whole-share (`c.q = st.D`), read--write (`c.ceiling = .readWrite`) fragment of the written allocation (`c.alloc = st.alloc`) covering the offset — derived from the command's guard, not assumed |
| `component_write_parts`, `heap_write_lookup` | the component write behind it is a `Cap.Heap.write?` at that offset, so the post-heap is `List.set` and the offset was in range |
| `runFuel_store8_at_mem` | from **any** flat memory the emitted body at `(base, off, bv)` completes at every positive budget with `writeByte` at `base + off` (the `getelementptr` adding case assumes `off < 2 ^ 63`) |
| `store8IR_refines_model_at_mem`, `store8IR_completes_at_mem` | the run-level refinement and completion at that memory: every outcome is the reference store's, and it has one |
| `store8_exec_write_comp` | the composition: completion, `MemRep` of the post-state's buffer at the same window, `AgreesOutsideMem` outside `base + off`, `s'.Inv`, the post-state's component holding `buf.set off (byteOf bv)`, the written byte on both sides, and every other allocation's state unchanged |
| `exec_write_read_frame` | every other offset of the same allocation reads as it did |
| `sealed_store8_write_comp` | the same conclusion at the sealed boundary, from an accepted `Cap.Sealed.write` |

The kernel half is this package's existing work, reused rather than re-proved:
`runFuel_store8IR_succ` for the step, `store8Model_read_at` for the byte and
`store8Model_frame` for the frame. The ownership half is `Cap`'s:
`State.exec_inv`, `State.find?_inv`/`find?_alloc`, `State.exec_frames_other` and
`Heap.write_ne`.

## The finite multi-allocation relation

`LlvmBridge/MultiAlloc.lean` replaces the single caller-supplied window with
`Cap.AddressMap`'s finite map.  The relation is

```lean
def MemRepMap (m : Mem) (map : Cap.AddressMap.Map) (s : Cap.Integrated.State) : Prop :=
  Cap.AddressMap.Rel map s ∧
    ∀ (a : Cap.AllocId) (w : Cap.AddressMap.Window),
      map.lookup? a = some w →
        ∃ (st : Cap.Reconstruction.State) (buf : List UInt8),
          s.find? a = some st ∧ st.heap.lookup? a = some buf ∧
            buf.length = w.len ∧ MemRep m buf w.base
```

so the map's own invariant (`Rel`: distinct keys, pairwise-disjoint bounded
windows, and coverage of exactly the live allocations with their recorded
lengths) comes with a representation of every window's buffer.  Nothing about
the map is assumed beyond `Rel`; the windows themselves are still supplied by
the caller.

For an accepted integrated write the file proves:

| Theorem | Statement |
| --- | --- |
| `MemRepMap.write_len` | an accepted write at a mapped allocation is inside that allocation's window: `off < w.len` is derived from acceptance and the relation (`heap_write_lookup`'s in-range offset and the relation's recorded length), not assumed |
| `MemRepMap.write` | given the window lookup `map.lookup? a = some w` and `off < w.len`, the accepted write preserves `MemRepMap` at the kernel's post-memory `writeByte m (w.addr off) v` and frames every other allocation (`s'.find? b = s.find? b`) |
| `sealed_store8_write_comp_map` | at the sealed boundary: the emitted body completes at every positive budget with `postMem m w.base off bv`, the post-memory satisfies the updated `MemRepMap`, and an unrelated allocation's component and snapshot are unchanged; the map is the same term, so its windows are unchanged |

The write frame is where the finite map pays off.  `WellFormed`'s
`NonOverlapping` gives two distinct live windows `wb` and `w` as `Disjoint`, and
`disjoint_addr_ne` turns disjointness into `wb.base + j ≠ w.base + off` for every
in-window `j` and `off`; that is exactly the avoidance `MemRep.frame_write`
needs to keep `b`'s buffer represented in the post-memory.  `MemRep.frame_write`
now takes an arbitrary `UInt8`, so the same lemma serves the kernel's
`byteOf bv` and the ownership model's own write; `MemRep.set` handles the
written allocation.

The concrete model is `memRepMap_twoAlloc`: the map's own `twoAllocMap` and
`twoAllocState` fixture (`⟨0⟩` at `[4096, 4160)`, `⟨3⟩` at `[8192, 8224)`) in a
flat memory of the two windows' zero bytes.  `example_write_model` runs an
accepted write at offset 5 of `⟨0⟩` — `twoAlloc_write0_accepted` is the
`decide`-checked affirmative control that the write is not refused — and keeps
the relation, `⟨3⟩`'s component and `⟨3⟩`'s snapshot.  `example_third_frame` is
the same fact at the flat-memory level: every byte of `⟨3⟩` reads back unchanged
after the write in `⟨0⟩`.

The refused controls are the other half:

* `MemRepMap.exec_write_eq_none_of_len_le` — a write at or past the mapped
  window's end is refused, with `example_out_of_window_refused` the fixture
  instance at offset 64 of `⟨0⟩`;
* `overlapping_window_refused` — the map refuses a window overlapping `⟨0⟩`'s,
  and `overlapping_window_shares_addr` shows the overlap is real (address 4128 is
  offset 32 of `⟨0⟩`'s window and offset 0 of the refused one), which is what
  would defeat the write frame;
* `example_window_addr_none` — the map produces no address outside a window, so
  there is no kernel call site past the end either.

## Build and run

The package requires two path dependencies: the sibling `lean-llvm` checkout at
Lean `v4.35.0` (the bridge's `lean-toolchain`, the same release the sibling is
pinned to), and the ownership package as `..` — this package lives inside it and
the composed theorems import `Cap`. `Cap`'s modules are therefore elaborated by
the bridge's Lean; the ownership repository's own pinned toolchain is a separate
build, and `EVIDENCE.md` records which toolchain verified what.

**On the worker** (the route this session used; nothing is built locally):

```bash
cd llvm-bridge
LLVM_BRIDGE_REMOTE=/path/to/gcloud-remote.ts scripts/build-remote.sh \
  --session <worker-session> \
  --lake /nix/store/<lean4-4.35.0>/bin/lake \
  --ownership /path/to/ownership-cap-snapshot
```

A worker whose `lake` on `PATH` is a project wrapper injecting a package set
(the lean-llvm image's `lake` does exactly this and fails without its stamps
directory) needs `--lake` naming the plain binary. The script copies
`../lean-llvm` and this package to the worker, replaces the pushed copy's
`lakefile.toml` with `scripts/worker-lean-llvm-lakefile.toml` (no Mathlib
requirement; the core modules are the roots), copies the ownership package's
`Cap/` and `Cap.lean` to the worker root with
`scripts/worker-ownership-lakefile.toml` as its package definition (only the
`Cap` library), builds, and prints the axiom audit. The worker layout is what
makes both path requirements resolve: the bridge is at the worker's
`llvm-bridge`, the sibling at `lean-llvm`, and the `Cap` projection at the
worker root, so `..` from the bridge is the `Cap` package. `--ownership`
(default: this package's parent) chooses the sources to push; a pinned snapshot
keeps a concurrent working-tree edit out of the record. Neither the sibling nor
the ownership package is modified.

**Local builds.** The paths above are the worker layout; a local build would
also need a `lean-llvm` checkout at `ownership/lean-llvm` beside this package.
No local build was run for this record.

**Reproduce the IR** (compiles on the worker, compares with `ir/`):

```bash
LLVM_BRIDGE_REMOTE=/path/to/gcloud-remote.ts scripts/emit-ir.sh \
  --session <worker-session> --check
```

## What the composition assumes, and what remains

Proved, for one accepted integrated write: the authorization
(`write_authority`), the component write and its in-range offset, completion and
the run-level refinement from any memory, the represented post-state, the frame,
the byte on both sides, other allocations unchanged, and the integrated
invariant (`store8_exec_write_comp`, `sealed_store8_write_comp`).  Over a finite
map, the same write preserves `MemRepMap`, derives its own in-window bound, and
frames every other allocation through the map's disjointness
(`MemRepMap.write`, `MemRepMap.write_len`, `sealed_store8_write_comp_map`).

Assumed, and stated rather than discharged:

1. **The representation premise.** `MemRep m buf base` — the flat memory already
   holds the window — and its finite-map form `MemRepMap m map s`, which also
   holds every other live allocation's window. `LeanLLVM` has no allocation
   bounds, so the C-level in-bounds guarantee is the ownership guard plus
   `off < buf.length` (derived from the accepted write), not a theorem about C.
   `off < 2 ^ 63` is the pointer-width assumption the emitted `getelementptr`
   needs.
2. **The address map.** The one-window theorem maps one allocation by
   `off ↦ base + off`; the multi-allocation relation takes `Cap.AddressMap`'s
   finite map, and assumes only its `Rel` — distinct keys, pairwise-disjoint
   bounded windows, and coverage of exactly the live allocations.  Disjointness
   is then what discharges `MemRep.frame_write`; that a *loader* assigns those
   windows, and that the physical allocation lives at them, is not proved.
3. **The projection.** The emitted IR is projected onto the parser's surface
   (`scripts/project-ir.sed`, above). Parser/AST agreement is a guard on the
   text, not a semantic justification of the abstraction; the projection is
   assumed, exactly as `LlvmBridge/Store8.lean` states.
4. **The capability route.** The write's authority is the integrated
   reconstruction guard. The `Cap.World` `Writable`/`Rel` route is not the path
   the sealed boundary runs, and nothing here relates the two.
5. **The executable edge.** ABI, execution of the verified body, native
   compilation, a live handle and the physical allocation remain trust or proof
   obligations (`Cap.Sealed`'s `boundaryClaims`).

Still not claimed: physical aliasing between two `Cap` values that reach one
mutable allocation, the snapshot policy at the destructive runtime boundary, and
replay of a copied live handle. `store8Model_replay_read` is idempotence of the
*model* memory, not a statement about sealed-value copies. The kernel allocates
and frees nothing (`alloca`-free; the reference environment returns `next`
unchanged), so allocation failure and cleanup have no path in this body.

## What is not claimed

The kernel refinement is about LeanLLVM's byte memory; the composition adds one
ownership state at an explicit window, and the finite map relates a whole state
to its windows (above). What neither proves:

1. an address assignment by a loader. The map is caller-supplied, and
   well-formedness and coverage (`Cap.AddressMap.Rel`) are inputs. Disjointness
   of two live windows is then a consequence of the map's `WellFormed`, not a
   per-theorem hypothesis, but that a loader chose those windows — and that the
   physical storage is there — is still assumed;
2. a call-site `Writable` guard discharged through the `Cap.World` capability
   path. The authority used is the integrated reconstruction guard; the two
   routes are not related here;
3. the physical boundary: two `Cap` values reaching one mutable allocation,
   snapshots at the destructive runtime boundary, and replay of a copied live
   handle.

The composed theorem does not restate `Cap.State.Inv`: it uses the sealed
value's carried invariant (`Sealed.state_inv`) and `State.exec_inv` for the
write, and it reads the post-state through `Sealed.state` — the read-only
accessor added for this composition, which leaves the constructor and the
invariant field private.
