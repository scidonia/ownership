# Ownership: next steps toward a certified nested update

Date: 27 October 2026  
Repository: https://github.com/scidonia/ownership  
Reviewed main: `df22f73` — Connect the recognized execP prefix to the AST  
Reviewed development branch: `recursive-ownership-callat`, `9672c40` — Add a callable recursive ownership layer

## Objective

Compose the recursive ownership development with one captured, emitted nested-update path. Establish a bounded theorem about that path under explicit entry and primitive contracts, then strengthen the client and runtime connections.

Keep the existing architecture: a sealed client interface, a fixed executor, an explicit entry invariant, recognition of supported emitted code, and kernel-checked ownership evidence. This work does not require a general Lean compiler verification or a general C refinement framework.

This document is an implementation handoff based on source inspection. Builds and executable checks were not independently reproduced: the review environment had neither `nix` nor `lake`. Establish the baseline in the repository's supported environment before changing proofs.

## Current evidence and its boundary

| Component | Main at review | Development branch |
| --- | --- | --- |
| Scalar-array ownership checker and soundness | Present | Retained |
| Recognizer for the pinned scalar-array LCNF prefix | Exact supported operation order, operand identities, arities and branch constructors | Retained |
| Projection/boxing/write data flow | One environment supplies the actual modeled write operands | Retained |
| Prefix correspondence and in-place result | `project_sound`, `recognized_write_in_place`, arbitrary in-bounds index/replacement, nonzero value-changing corollary | Retained |
| Concrete recognition evidence | Kernel-checked reified transcription; executable comparison with replay; eleven mutation controls | Retained |
| Recursive mutable footprint and client reachability | Not yet merged | Present, with shared-grandchild and indirect-client countermodels |
| Heap-changing call body and confinement | Placeholder in main's nested model | Embedded body, isolated environment/context, return-identity and confinement results |
| Nested `TakeOutsOK` discharge | Supplied as a premise | Derived from invariant, acceptance and explicit heap/program agreement |
| Emitted nested/pair correspondence | Open | Open |
| Full executor/client and physical-runtime connection | Open | Open |

`execAST` recognizes an actual `Code .impure` value and executes its decoded fragment. Its meaning is the repository's restricted semantics under named contracts. It is not a simulation against an independently established general LCNF semantics. Preserve this distinction when reporting completion.

The reified transcription uses placeholder fields where the recognizer does not inspect types. It certifies the supported structural representation, not the complete well-formed compiler declaration. The operational replay comparison and the kernel artifact proof are separate pieces of evidence.

## Step 1 — Validate and integrate the recursive model

Review and integrate `recursive-ownership-callat` before extending emitted-code recognition. Preserve the scalar-prefix certificate and its negative controls.

Check the following in the branch:

- `MutableFootprint` and `ClientReachable` are transitive, and their boundaries for immutable observations are documented.
- `RootsComplete` states completeness of the checker's owned variables. Do not describe it as completeness of all physical runtime roots or client roots; those need separate representation facts.
- `callAt` executes the embedded body on its isolated environment and passes the resulting heap to the caller's continuation.
- Accepted bodies return the same reference that was handed to the call.
- `callAt_frame_confined` preserves cells outside the entry subtree under its stated annotation and heap premises.
- `CountFree` remains an explicit restriction: admitted call bodies exclude explicit model `inc`/`dec` operations. The embedded bodies are structurally finite syntax, not yet a semantics for arbitrary recursive runtime calls.

Run the required builds and contract fixtures from `AGENTS.md`. Preserve the unique three-level positive case, shared-grandchild rejection, indirect-client separation rejection, and suspended-parent access rejection.

Acceptance: all required checks pass after integration; main contains the recursive model results without widening their claims. Update the stale introductory status in `PLAN.md` and distinguish completed model results from remaining emitted-code and runtime work.

## Step 2 — Fix the next theorem boundary before implementing it

Target one pinned `setAt` `Path.index` path with a genuine heap-changing child update. Include extraction, the call boundary and restoration. A schematic target is:

```text
recognized nested prefix
and supported-state/operand agreement
and entry ownership/separation invariant
and in-bounds path
and a certified child-call contract
imply:
  execution reaches the restoration boundary without ownership faults;
  the child operation performs only exclusive designated writes;
  the extracted result is restored to the selected parent slot;
  the parent and supported child targets retain their references;
  suspended frames and unrelated cells are preserved;
  the returned state satisfies the invariant required by the caller.
```

Make heap modification observable in the theorem: use a nonzero replacement at a nontrivial child index, and show the changed leaf value. Also show another parent slot or sibling subtree is unchanged.

Initially the child-call contract may be a theorem about an admitted model body. State the connection to the emitted recursive callee as an outstanding obligation until it is proved. Do not call that intermediate result certification of the whole recursive executor.

Acceptance: the theorem's observation boundary, supported instructions, entry relation, callee contract and non-claims are written down before recognizer expansion.

## Step 3 — Certify the emitted nested protocol

Reuse the strict-recognizer approach, while keeping decoding, instruction meaning and model correspondence as distinct reviewable layers.

1. Capture the pinned nested alternative and the helper bodies it depends on. Record the source/sibling commit, compiler, options, runtime configuration and acquisition route.
2. Recognize the supported bounds test, array check, take-out helper, pair projections, reference traffic, child check/call and put-back in actual execution order.
3. Establish every relevant operand identity. In particular, put-back must use the parent array obtained from extraction, the selected index, and the child result returned by the call.
4. State semantic contracts for helpers. Review the temporary extraction pair: its projections, increments and disposal can affect the child's count. Do not discard those effects merely because the high-level protocol transfers one handle.
5. Execute the decoded prefix in the restricted semantics and prove its correspondence to the recursive model, including the heap-changing callee contract and frame restoration.
6. Kernel-check recognition and acceptance on a concrete represented artifact. Keep the replay comparison separate until the build-identity connection is stronger.

If code needed for this path uses joins, handle the required joins explicitly rather than flattening their bodies into a list. Unsupported control flow must reject. Do not add general joins, callbacks or an unrelated LCNF fragment just to enlarge coverage.

Required negative controls, each paired with acceptance of the original:

- Retain an extra child handle across the child update.
- Restore to a different parent or selected index.
- Restore the old extracted child instead of the call result.
- Swap the extraction pair's parent/child projections.
- Alter an ownership-relevant increment/decrement or its operand.
- Exchange bounds alternatives or bypass the checked target.
- Use a call body that accesses a suspended parent frame.

Use well-formed executable mutations where possible. Label malformed AST mutations as recognizer tests, not semantic counterexamples.

Acceptance: one emitted extraction/call/restoration prefix has a conditional model correspondence theorem, nontrivial update evidence and structural rejection controls. Every omitted RC effect has an explicit justification or named runtime obligation.

## Step 4 — Discharge program/heap agreement compositionally

The branch improves `TakeOutsOK` discharge, but `Agrees` still specifies the identities that annotations must name along execution, including after a body returns. This is a real obligation, not a consequence of exclusivity alone.

Build a representation relation between source layouts/paths, runtime operands, heap slots and model annotations. Derive annotation identities by following the path and selected slots. Prove that extraction, child execution and restoration preserve the relation needed by the remaining path.

Similarly, derive the `AnnotationsIn` facts needed for confinement from path interpretation and the structural invariant. Avoid requiring each client to supply a description of every intermediate heap manually.

Acceptance: a reusable path-level theorem establishes agreement and annotation reachability for supported inputs; example certificates invoke it instead of reproducing those premises step by step.

## Step 5 — Connect finite bodies to the fixed recursive executor

Keep the finite-body result. Add a call rule and proof principle that match how the real executor recurses: structural induction on supported paths when justified, or a finite-execution-prefix safety theorem when termination is not available.

The proof must connect the emitted recursive call to the already certified body contract. Checking a finite embedded expansion alone does not establish arbitrary recursion.

Prove separately that callbacks and permitted clients cannot retain references into the mutable footprint. This is especially important for model contract A2: treating node/continuation RC traffic as disjoint from the state is conditional on real separation, not simply on those objects being absent from the model heap.

Acceptance: every supported nested path is covered by the recursive theorem, and caller invariants are preserved across the call/return boundary. Unknown callbacks are rejected or require a justified uniform contract.

## Step 6 — Strengthen artifact and runtime identity

These are separate work items; neither is supplied by a clean axiom inventory.

| Connection | Required evidence |
| --- | --- |
| Represented prefix to replay | Auditable structural export/comparison of every field the certificate depends on; prefer automatic export over manual transcription |
| Replay to backend input | Capture the actual backend-input declaration if feasible; otherwise state and enforce replay assumptions, including specialization and inlining |
| Heap counts to runtime counts | Account for counted roots, heap edges with multiplicity, external handles, borrows and persistence |
| Abstract operations to runtime | Allocation freshness, boxing, array layout, update disposition, decrement and free/cascade contracts |
| Certified code to linked executable | Build gate binds the accepted artifact, toolchain, runtime and selected implementation |

Start with the operations needed for the certified paths. A full general LCNF or C semantics is not required for a bounded trusted-fragment result. If extending the claim to physical no-copy behavior, either prove the relevant runtime connections or explicitly retain them as assumptions and report measurements as supporting evidence rather than proofs.

## Validation and reporting

Run from the supported Nix environment:

```sh
nix develop -c lake build Ownership
nix develop -c lake build OwnershipTest
nix develop -c lake build OwnershipLcnf
```

Run the projection replay and behavior-contract commands exactly as documented in the current `AGENTS.md` and `tests/` pages, with the required pinned sibling checkout. Include the recursive-frame fixture after integration. Inspect `#print axioms` for headline theorems; retain the repository prohibition on new axioms, `sorry` and `admit`.

The completion report should identify:

1. The exact certified prefix and compiler/sibling revisions.
2. The principal theorem and its concrete instantiation.
3. The heap-changing positive example and rejection controls.
4. Checks actually run and their outcomes.
5. Remaining semantic, client, callee, artifact and runtime assumptions.

The next deliverable is a certified nested protocol under explicit contracts. Full-executor certification and physical RC=1 remain subsequent, separately assessable results.
