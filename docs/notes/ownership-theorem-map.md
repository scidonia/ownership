# Ownership paper: declaration map

Supplementary artifact documentation for
`paper/ownership-skeleton.tex`. This file is not part of the paper's argument: it
records which declarations carry which claim, so that a reader of the artifact can
move from a statement in the paper to the Lean code that proves it. The paper
keeps only a short paper-to-code pointer.

The map is not exhaustive. It lists the declarations named in the paper, grouped
by the section that uses them. Every name here is a declaration in this
repository. Module paths are relative to the repository root.

The paper-to-code entry points are `Ownership/CompleteAccounting.lean`,
`Ownership/Preservation.lean`, `Ownership/CountedNested.lean`,
`OwnershipLcnf/CountedTrace.lean` and `OwnershipLcnf/Principal.lean`.

| Declarations | Role |
| --- | --- |
| `check_sound`; `checkN_sound_of_entryInv`; `Accounted` (`mult_eq`, `count_one_dichotomy`, `at_most_one_owner`, `countFidelity`); `initCtx`; `initCtx_accounted`; `OwnersAccounted`; `alias_not_accounted`; `aliasEntryInv`; `accountedNotEntryInv`; `Supported`; `supported_check`; `supported_run`; `supported_store_exclusive`; `storeSlots_init` | checker; accounting and independence; preservation with `Accounted` + `StoreSlots` |
| `project_sound`; `recognized_write_in_place`; `execAST_recognized`; `index_path_simulates_model`; `childContracts_of_path`; `childContract_of_path` | recognition and correspondence |
| `pair_accounting`; `pair_traffic_neutral`; `boundary_correspondence`; `no_free_components_not_exclusive`; `pairPhase_refused`; `counted_takeOut`; `CountedChildCall`; `counted_restore`; `counted_nested_chain`; `HeapCompat` | counted protocol; N10 |
| `putBack_exclusive_of_wellFormed`; `execCounted_protocol_boundary`; `checkExclusive_no_abort`; `setAt_inPlace_of_entryInv`; `prefix_abort_impossible`; `checkN_extraction_exclusive`; `checkN_extraction_exclusive_of_entryInv` | restoration; counted prefix; runtime model; store targets |
| `principal_write`; `Prefix.toModel_supported`; `principal_accounted`; `principal_supported_path`; `principal_instance`; `principal_counted_fragment`; `counted_fragment_instance`; `family_chain`; `family_chain_two` | flat and nested guarantees; instance and family |
| `retained_parent_copies`; `retained_parent_not_mutate`; `no_free_components_not_exclusive`; `pairPhase_refused`; `dupSupport_witness`; `omittedOwner_witness`; `unboundRoot_witness`; `persistent_check`; `persistent_setAt` | control witnesses: retained parent, omitted release, pair-live state, invalid owner support, persistent root |

## Where the groups live

| Group | Modules |
| --- | --- |
| checker, accounting, preservation | `Ownership/Soundness.lean`, `Ownership/Accounting.lean`, `Ownership/CompleteAccounting.lean`, `Ownership/Preservation.lean`, `Ownership/Entry.lean` |
| counted protocol and restoration | `Ownership/CountedPair.lean`, `Ownership/PutBack.lean`, `Ownership/CountedNested.lean` |
| recognition and correspondence | `OwnershipLcnf/Semantics.lean`, `OwnershipLcnf/Projection.lean`, `OwnershipLcnf/NestedProjection.lean`, `OwnershipLcnf/PairProjection.lean`, `OwnershipLcnf/PathRecursion.lean`, `OwnershipLcnf/CountedTrace.lean`, `OwnershipLcnf/Principal.lean` |
| runtime model | `OwnershipLcnf/RuntimeModel.lean`, `OwnershipLcnf/NoAbort.lean` |
| instances and controls | `OwnershipTest/Principal.lean`, `OwnershipTest/PrincipalCounted.lean`, `OwnershipTest/CountedFamily.lean`, `OwnershipTest/CountedNested.lean`, `OwnershipTest/PathRecursion.lean`, `OwnershipTest/PathConsolidation.lean`, `OwnershipTest/RuntimeModel.lean` |

## Claim boundaries

Three boundaries the map must not blur when it is used to check a claim:

- **Ordinary and counted child contracts.** `childContracts_of_path` derives the
  ordinary `ChildContract` at every level of a finite path from one supplied leaf.
  `CountedChildCall` adds the field `edges`, the call's effect on the caller's
  incoming edges, cursor and cell carrier; `accounted_of` derives the caller's
  complete accounting at the body's return from it and the caller's accounting at
  the call. No theorem derives that edge effect from the path induction; it is a
  premise of `principal_supported_path` and `principal_counted_fragment`, and
  `OwnershipTest/Principal.lean` supplies it as `B_edges`.
- **Accounting at boundaries, not inside the pair-live window.** `pairPhase_refused`
  is the kernel check that no support accounts the take-out state. `Accounted` is
  concluded at the entry, at the protocol boundary and at the restored state; it is
  not an invariant of the counted interpreter at every instruction.
- **Model correspondence, not runtime fidelity.** `HeapCompat` relates two model
  heaps and tolerates one cursor step; `Corr` relates two models and binds no
  physical C object or address. Primitive fidelity, replay-to-backend identity and
  reference identity remain assumptions or observations.

## Modelled instruction meanings

The recognised fragment is a list of `OwnershipLcnf.NestedOp` values
(`OwnershipLcnf/NestedProjection.lean`), and `execCounted`
(`OwnershipLcnf/CountedTrace.lean`) gives each a meaning. This table states which
meanings are defined by the development and which parts stand in for the compiler.

| Recognised operation | Meaning in `execCounted` | Status |
| --- | --- | --- |
| `projArray`, `projIndex`, `projPath` | bind the path's array, selected index and continuation; the heap is unchanged | defined; bookkeeping only |
| `incArray`, `incIndex`, `incPath` | no-op on the ownership heap | defined no-op: the emitted increments of the path projections are accounted at the counted boundary, not as heap effects |
| `incParent`, `incChild` | `Heap.inc q 1` on the bound handle | defined |
| `decNode`, `decIndex` | no-op | defined; bookkeeping only |
| `decPair` | `CountedPair.decRef` at the pair's name | defined (restricted non-cascading release) |
| `arraySize`, `decLt`, `boundsTrue`, `siteConst`, `stateDefault` | scalar bookkeeping, no heap effect | defined |
| `checkArray` | bind the array check's result | defined |
| `takeOut` | `CountedPair.takeOut`: allocate the pair, write the placeholder, record parent and child; fault `.noCell` when the cell is absent | defined on the model heap; the emitted `lean_array_fget`/`lean_array_fset` and the allocation are the supplied primitive meaning |
| `projParent`, `projChild` | read the pair record | defined |
| `checkChild` | exclusivity test; fault `.notExclusive` otherwise | defined |
| `recurse` | run the supplied `Ownership.Nested.NCode` body on the call's isolated environment, appending its writes | **supplied**: a model body, not the emitted recursive callee (N10) |
| `setArray` | `PutBack.putBack`: the restoration, with the disposition derived | defined; the emitted `lean_array_uset` is the supplied primitive meaning |
| `retVar` | return the put-back result | defined |

Three meanings therefore stand in for the compiler rather than being proved against
it: the array read, write and allocation primitives at the take-out and the
put-back, and the recursive callee, which enters as a body contract. Their
correspondence to the linked runtime is observed by the probe and the artifact
gate, not proved.
