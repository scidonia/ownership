# Ownership handoff: establish the runtime uniqueness connection

Date: 28 October 2026  
Repository: https://github.com/scidonia/ownership  
Review baseline: `aaae62a` — Name the checked prefix's abort-impossibility theorem  
Previous review baseline: `ffa8348`

## Goal

Strengthen the connection between the proved ownership protocol and the reference-count operations executed by the compiled program. Prioritise diagnosing the reported context-sensitive copying and discharging the temporary-pair and put-back contracts before expanding modeled coverage.

The target remains ordinary array updates, including nested arrays. Writable range splitting is a separate extension and is not required for this milestone.

This handoff is based on inspection of source and theorem statements. The reviewer did not reproduce builds or runtime measurements because the review environment lacked `nix` and `lake`. Re-establish the baseline in the supported environment before changing implementation or claims.

## Preserve the progress already made

| Addition since `ffa8348` | Evidence and boundary |
| --- | --- |
| Path-level agreement | `Ownership/Path.lean`: `agrees_of_path` derives intermediate agreement from structural, environment, leaf and child-confinement premises |
| Annotation reachability | `annotationsIn_of_path` derives extraction reachability through the path |
| Finite-path safety and confinement | `Ownership/PathSafety.lean`: `path_run_safe`, `path_run_confined`, `level_call_confined` compose existing checker results |
| Client retention | `client_retention` preserves separation from the entry footprint for the same client-root list |
| Nontrivial concrete evidence | `OwnershipTest/PathSafety.lean` supplies a depth-three certificate |
| Named abort-impossibility result | `OwnershipLcnf/NoAbort.lean`: `prefix_abort_impossible` derives absence of faults in the restricted prefix semantics |
| Reproducibility and runtime record | `scripts/check_artifacts.sh`, `docs/notes/OWNERSHIP_RUNTIME_EVIDENCE.md` |

These results reduce repetitive model-level obligations. They do not yet establish physical RC=1. In particular, the abort-impossibility theorem is a corollary of the existing conditional prefix result; it does not independently connect `exclusive?` to `lean_is_exclusive` in the linked executable.

## Priority 1 — Diagnose the context-sensitive copying

The runtime evidence note reports an in-place update in a separate function and copying in a larger `do` block. Treat this as an observed discrepancy requiring a committed explanation, not as a general conclusion that larger blocks necessarily retain aliases.

### Work

1. Commit a minimal compiled reproducer for both cases at the pinned sibling/toolchain revision. Use the same input construction, update and relevant observations in both.
2. Include exact-capacity and spare-capacity controls where applicable, so resizing/allocation capacity does not become an alternative explanation.
3. Inspect the actual compiled call sites and callee signatures. Record the ownership arguments, increments/decrements, retained bindings and inlining decisions that distinguish the cases.
4. Audit the instrumentation: address/count observations must not themselves create or retain the alias being measured. Keep observation operands and their lifetime explicit.
5. Repeat the relevant case through the sealed `Structured.runFresh` interface. Determine whether the behavior affects permitted client programs or only direct layout operations supplied with caller-owned state.
6. Run with the exclusivity check both enabled and disabled. Keep compiled execution distinct from interactive evaluation.

### Acceptance

- Both original observations are reproduced, or the earlier observation is explicitly corrected with the reason.
- The responsible reference/lifetime/borrow decision is identified in emitted code. Do not infer the cause from source syntax alone.
- A positive in-place case and a deliberately shared control form a regression fixture.
- The permitted API's behavior is documented separately from direct layout-helper behavior.
- Any implementation change preserves the functional result and explains why the compiled ownership improves.

## Priority 2 — Prove temporary-pair RC accounting

Contract N2 in `OwnershipLcnf/NestedSemantics.lean` currently makes parent/child increments and pair destruction neutral in the abstract ownership heap. The parent and child handles refer to the objects whose counts matter, so their combined neutrality needs a concrete count argument.

### Work

Introduce or reuse a small counted-object semantics sufficient for this path:

- A fresh temporary pair with two counted component references.
- Projection of its fields and creation of owned component handles.
- Increment of the parent and child component counts.
- Decrement of the pair, including release of its component edges when it is destroyed.
- The correspondence from this concrete state to the existing ownership model at the end of the extraction protocol.

Follow the captured `takeOut` implementation and its call sites. Establish whether each operation transfers, borrows, increments or releases ownership; do not assume that allocation of the pair creates two additional component owners if the helper transfers existing handles.

The intended argument is that each component may temporarily have two counted references, then returns to one after destruction of the unique pair. Prove the initial count, the pair's uniqueness, the relevant object identities and the absence of retained aliases. Include persistence and the supported decrement/free behavior, or state justified restrictions excluding them.

### Acceptance

- A theorem derives the parent/child counts at the protocol boundary from a well-formed concrete entry state.
- The child is live and exclusive before its update; the parent remains live while suspended.
- Omitting pair destruction or retaining a counted component alias invalidates the claimed uniqueness, with a corresponding negative control.
- The abstraction lemma replaces the relevant part of N2. Remaining scalar/path bookkeeping assumptions stay individually named.

This is a bounded runtime model, not a requirement to verify the entire Lean allocator or C backend immediately.

## Priority 3 — Derive put-back exclusivity rather than assume mutation

Contract N11 currently interprets put-back as an in-place store. Its documented runtime copy branch is not modeled on this path. Consequently, the current correspondence assumes the behavior that the no-copy claim ultimately needs to establish.

### Work

1. Give the concrete put-back operation both exclusive/mutate and shared/copy dispositions.
2. Use the temporary-pair accounting to establish the suspended parent's count.
3. State a child-call contract preserving the parent's relevant count and liveness, not only the abstract values of cells outside the child footprint.
4. Connect that contract to the admitted child body, then account for the actual emitted call boundary and any remaining handles.
5. Derive that the exclusive branch is selected at restoration and that the parent address is preserved.

### Acceptance

- Exclusive restoration is a theorem consequence under concrete entry/call facts.
- A shared-parent control reaches the copy disposition, or is excluded by a clearly stated supported-interface premise.
- No-copy is not obtained by defining restoration to have only an in-place branch.
- Functional restoration and reference-count preservation are stated separately enough to review independently.

## Priority 4 — Consolidate the remaining compositional premises

Do not widen the interpretation of the path theorems while the runtime work proceeds.

| Current premise/boundary | Required follow-up |
| --- | --- |
| `ChildConfined`, leaf agreement and checker acceptance | Derive these for supported constructed programs; identify precisely which leaf/callee contracts remain supplied |
| Finite list of path levels | Connect the built finite model to emitted recursive `setAt` execution; arbitrary runtime recursion is not established by finite syntax alone |
| Fixed client-root list in `client_retention` | Add a justified account of new results/observations and callbacks before claiming general non-escape |
| Post-state footprint containment | Derive it generically for the supported path operations; the current general theorem takes supporting heap facts separately |
| Runtime separation of node/continuation traffic | Establish it through the interface and representation relation rather than omission from the heap model |

Retain the depth-three certificate. It is a concrete use of the theorem architecture, not a substitute for discharging the general premises.

## Small fixes to include now

### Reject a dirty sibling in the artifact gate

`scripts/check_artifacts.sh` checks the sibling's HEAD but does not check its working tree. Add an explicit cleanliness check and document the handling of tracked modifications, untracked build inputs and submodules. Keep generated build outputs from causing irrelevant failures through appropriate ignore/scoping rules.

Acceptance: the clean pin passes; a relevant source modification at the same commit is rejected before artifact regeneration; the diagnostic explains the failure. This still does not bind the linked executable or prove replay-to-backend identity.

### Correct the borrow-inference table

The runtime evidence note describes `setAt`'s borrowed argument as “the state.” The captured signature is `x.1 @&x.2 x.3`: `x.1` is the path, `x.2` the replacement value and `x.3` the owned state. Verify this mapping against the pinned declaration and correct the table and any conclusions depending on it.

An owned parameter is a reference-management convention, not evidence of exclusivity; a borrowed replacement does not establish that the updated state is borrowed.

## Validation and completion report

Read and follow the current `AGENTS.md` and behavior-contract pages. At minimum run:

```sh
nix develop -c lake build Ownership
nix develop -c lake build OwnershipTest
nix develop -c lake build OwnershipLcnf
```

Run the pinned projection checks, nested checks and artifact gate, plus the sibling's documented build/IR/in-place harness checks. Execute the new context reproducer as a compiled binary. Retain positive controls beside negative controls and inspect the axiom dependencies of new headline theorems. Do not add `sorry`, `admit` or new axioms to close the milestone.

The completion report must distinguish:

1. Newly proved model or concrete-runtime statements.
2. Experimental observations and exact reproduction commands.
3. Removed, weakened or retained N2/N11 assumptions.
4. The exact artifact, compiler, sibling and runtime revisions involved.
5. Outstanding emitted-callee, source-interface, backend and linked-executable connections.

The next strong result is a counted extraction/call/restoration protocol whose RC=1 facts are derived and whose observed execution context is reproducible. This would strengthen the central no-copy claim more than extending the set of abstract paths.
