# Steering note: close the emitted-code ownership proof

Date: 24 October 2026  
Repository: https://github.com/scidonia/ownership  
Reviewed commit: `3ffa9c046f310b35192db906a8546bd671ccc579`

## Direction

Keep the existing architecture: a sealed client language, a fixed executor, an explicit entry invariant, and a checked ownership certificate for the generated code. No extension to Lean's kernel type system is required by this architecture.

The immediate priority is to connect one actual emitted array-update branch to the proved ownership semantics. Do this before substantially expanding the standalone models. The current development establishes useful facts about its models; the decisive next result is a theorem connecting those facts to the code being compiled.

This note steers implementation. It does not claim a new proof or supersede the repository's explicit non-claims.

## Preserve the existing results

The development already makes several necessary distinctions:

- An owned handle is not itself evidence that its object is exclusive.
- `check_sound` proves fault freedom, exclusive recorded writes, and invariant preservation for accepted straight-line `Code` programs.
- The nested checker tracks extraction frames and rejects stale access, incorrect restoration, and prohibited exits.
- The pair model distinguishes unique reuse from shared copying.
- The measurement script inspects replayed LCNF and rejects targeted mutations of branch structure.

Retain the negative examples and their positive controls. Keep the distinction between kernel theorems about models, executable AST checks, and backend/runtime assumptions visible in documentation and theorem names.

## Priority 1: connect emitted LCNF to the proved semantics

`check_sound` currently applies to `Ownership.Code`, not to Lean's emitted LCNF. Shape checks and digests help identify and inspect an artifact, but they do not prove that execution of the artifact has the semantics of the hand-built model.

Choose the smallest useful fragment containing the measured scalar-array update. Either interpret that LCNF fragment directly or define a partial projection into the existing model and prove its ownership-relevant semantic correspondence. Reject unsupported constructs explicitly.

The correspondence must cover argument identities, ownership transfer, increments/decrements, exclusivity checks, update disposition, and continuation/return behavior. Model primitive calls through explicit contracts. A projection that merely recognizes names and operation order is insufficient.

Acceptance criteria:

1. Capture the actual supported LCNF artifact and identify its compiler version and acquisition route.
2. Produce kernel-checked evidence that its represented form passes the checker.
3. Prove that the supported LCNF execution is represented by the model execution, including ownership faults and copy-versus-mutate behavior.
4. Derive fault freedom and absence of copying for the designated update from a concrete entry invariant.
5. State whether the captured artifact is the backend input or a replay, and list the assumptions connecting it to the backend input.

This milestone may still trust the C backend and runtime contracts. Name those assumptions; do not expand this task into verification of the entire compiler.

## Priority 2: make the entry condition recursive

In `Ownership/Entry.lean`, `footprint` contains the root and its immediate field references. `UniqueTree` therefore checks only one level of descendants. It can hold while a grandchild is shared. The current scalar-array initializer is compatible with this definition, but arbitrary nested updates require a stronger condition.

Introduce transitive reachability over the relevant mutable edges. Separate mutable cells from immutable observations, so harmless sharing does not unnecessarily invalidate the invariant. State client separation using reachable sets, rather than relying on a list whose completeness is implicit.

For a unique-tree sufficient condition, require exclusivity of every reachable mutable cell and the structural facts needed for extraction and restoration. Alternatively, support internal sharing with explicit per-write exclusivity obligations.

Acceptance criteria include a root-to-child-to-grandchild example where the root and child are unique but the grandchild has another incoming reference. The strengthened condition must reject that example for a write to the grandchild, while accepting an otherwise equivalent unique structure. Also test an external client root that reaches a mutable descendant indirectly.

## Priority 3: give recursive calls a real contract

In `Ownership/Nested.lean`, `callAt` checks exclusivity, records a write, and returns the same reference with an unchanged heap. This establishes the surrounding protocol for that modeled operation. It does not yet establish the protocol for recursive `setAt`, which may change the heap.

Replace or generalize this placeholder with a semantic call relation. Its contract must specify permitted heap changes, returned ownership, preservation of suspended parent frames, separation, and the exclusivity of designated writes. Preserve a root address only where the supported operation actually guarantees it.

Prove that the recursive implementation satisfies this contract. Then instantiate the surrounding frame theorem with it. `TakeOutsOK` should ultimately follow from structural entry facts and preservation lemmas, rather than remaining a separately supplied description of every intermediate state.

Do not require this larger recursive proof before closing the first emitted scalar-array branch. It is the next extension after that connection works.

## Runtime correspondence obligation

`Inv.rc_eq` equates the heap's stored count with the context's count. This is useful inside the model, but does not alone show that either count equals the number of incoming counted references in a runtime object graph.

The runtime bridge needs a well-formedness relation covering counted roots, heap edges with multiplicity, external references, borrows, persistence, and allocation freshness. It must also explain how the model's non-freeing, saturating decrement corresponds to runtime decrement and cascading destruction for the executions being certified.

This is a separate proof obligation, not a claim that the existing model theorems are false. Keep it explicit when transferring model-level RC=1 to physical in-place execution.

## Next milestone and completion statement

Target this bounded result:

> For the pinned emitted scalar-array update fragment, checker acceptance and the established entry invariant imply that execution avoids ownership faults and that the designated fixed-size replacement selects the in-place branch and preserves the target address, under explicitly listed primitive and backend/runtime contracts.

After completing it, extend the same connection to nested extraction, recursive calls, and pair reuse. Avoid describing the current model artifacts as full-executor certificates or describing the shallow footprint as a recursive ownership invariant.

Review basis: source inspection at the commit above. Builds and measurement commands were not independently reproduced because the review environment had neither `nix` nor `lake` installed. Implementation should run the repository's required build and behavior-contract checks before reporting the milestone complete.
