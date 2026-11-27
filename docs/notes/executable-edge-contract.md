# Executable-edge contract for the compiled kernel

Scope: one clang-emitted `store8` body, a caller-supplied window or finite
address map, one accepted
`Cap.Sealed.write`. This record separates what is proved from what is assumed or
left to a runtime protocol. It does not claim a loader, ABI proof, native
installation or a physical ownership refinement.

## Status

| Edge | Status | Evidence / obligation |
| --- | --- | --- |
| Emitted body refines reference store | Proved | `store8IR_refines_store8Ref`, `Beh_store8IR_iff`; LeanLLVM byte memory |
| One ownership write composes with the body | Proved | `store8_exec_write_comp`, `sealed_store8_write_comp` |
| Write authority is the current whole read--write fragment | Proved | `write_authority`, derived from the accepted command |
| Post-heap, written byte and outside-window frame | Proved | `store8_exec_write_comp`, `exec_write_read_frame` |
| Other allocation's component/bytes unchanged | Proved | `WriteFrame.component`, `WriteFrame.rel_write` |
| Finite multi-allocation relation over the address map | Proved | `MemRepMap`, `MemRepMap.write`, `sealed_store8_write_comp_map` |
| Two-allocation concrete model and refused controls | Proved | `memRepMap_twoAlloc`, `example_write_model`, `example_out_of_window_refused`, `overlapping_window_refused` |
| IR projection is semantics-preserving | **Trusted** | `scripts/project-ir.sed`; parser/AST agreement is a textual guard, not a semantic proof |
| Supported LLVM definedness | Proved for this body | one step, no `ub` prefix, positive budgets; `off < 2^63` for the `getelementptr` |
| ABI and linkage to the exact body | **Trusted** | the C signature and emitted symbol are matched by inspection; no ABI/linker proof |
| Concrete allocation failure and cleanup | **Not modelled** | the kernel has no `alloca` and allocates/frees nothing; allocation policy lives in the runtime |
| Snapshot versus borrowed view | **Runtime protocol** | `Sealed.snapshot` copies bytes; no theorem makes a borrowed view stable across a write |
| Reentrancy and copied live handles | **Runtime protocol** | no theorem; repeated identical stores are idempotent only in the model memory |
| Loader address assignment / multi-allocation disjointness | **Trusted or supplied** | `Cap/AddressMap.lean` is a logical finite map; `LlvmBridge/MultiAlloc.lean` relates it to the byte memory (`MemRepMap`) and derives two live windows' disjointness from `WellFormed`; a loader's choice of windows, and physical storage, are not proved |

## Address map extension

`Cap.AddressMap` relates live `Integrated.State` allocations to finite
`(base, len)` windows:

- distinct live windows are disjoint and satisfy `base + len ≤ 2^64`;
- every live allocation has exactly one window of its recorded length;
- allocation adds a fresh disjoint window and free removes it;
- a write preserves every unrelated allocation's window, component and bytes.

`LlvmBridge/MultiAlloc.lean` connects the map to `LeanLLVM`'s byte memory:
`MemRepMap m map s` is `Cap.AddressMap.Rel map s` plus a `MemRep` at every
mapped window; `MemRepMap.write` preserves it across an accepted write, taking
the frame from the map's `WellFormed` disjointness, and
`sealed_store8_write_comp_map` states the composition at the sealed boundary.
The relation is inhabited at two allocations by `memRepMap_twoAlloc`, whose
concrete memory holds both windows' bytes, and `example_write_model` runs an
accepted write in one of them. What remains trusted is the loader's choice of
windows and the physical storage, not the disjointness of the map's own live
windows.

## Live-session protocol (specified, not proved)

The C boundary may copy a sealed value. The following is the contract a runtime
must implement; none of it is a theorem about physical memory.

1. A sealed value denotes a live session and one allocation. Copying the value
   does not copy the allocation.
2. A snapshot view is immutable bytes. A borrowed view is valid only while no
   write, split, reconstruct, return or free invalidates it.
3. Replaying a copied exclusive handle is not authorised by idempotence of the
   store. Mutation rights are held by the session, not by the copy.
4. Free invalidates all views and handles for that allocation; a retired
   capability name is never reissued.
5. Allocation failure returns no session and leaves no partially initialised
   handle visible.

## Remaining proof work

- A semantic parser/projection theorem or a translation-validation check.
- A loader theorem assigning each live allocation the physical window the map
  records; the concrete two-allocation memory model exists
  (`LlvmBridge.memRepMap_twoAlloc`), but the map is still caller-supplied.
- An ABI/linker contract for the exact emitted symbol.
- A runtime state machine for snapshots, borrowed views, reentrancy and copied
  handles, with failure and cleanup paths.
