# Ownership core technical gaps and closure programme

Date: 2 November 2026  
Baseline: `scidonia/ownership`, commit `73c5775802358cb7b5e2a7e796aa447d4ba172c4`  
Audience: implementation and proof agent.

## Purpose

Close the gaps between an accepted ownership-model program, the actual counted execution of its supported compiler fragment, and the claim that the relevant array operations take their in-place branches. This document specifies the missing invariants, semantic connections, and completion criteria. It does not request a general verified Lean compiler or concurrent runtime.

The baseline has useful proved components: checker soundness over its models, flat-prefix correspondence, finite nested model results, counted extraction-pair accounting, derived suspended-parent preservation, restoration-disposition lemmas, and a separate runtime model. `initCtx_accounted` now establishes the environment-side accounting predicate for the fixed initializer context. The appendix exposes the full nested and restoration theorem types, and ordinary probe modes now assert their observations.

The core remaining problem is composition with adequate accounting. A stored count of one is meaningful as runtime uniqueness only when it accounts for the owning references that can exist at that point. A no-copy result for a nested protocol must cover extraction and restoration as well as its designated leaf writes, and must describe the instructions the emitted call actually executes.

This programme is based on source review at the baseline and earlier focused checks described in the review history. It does not claim a fresh build or a rerun of the sibling-dependent gates at `73c5775`.

## Choose the claimed boundary explicitly

| Boundary | Achievable claim | What must be connected |
| --- | --- | --- |
| Abstract ownership model | Accepted programs satisfy the model's count and update properties | Checker acceptance, state validity, preservation, and operation coverage |
| Counted supported compiler fragment | The recognised fragment's actual modeled RC traffic and stores take exclusive branches | Counted instruction execution, ownership accounting, call interpretation, and simulation |
| Pinned linked implementation under contracts | The counted-fragment theorem applies to the designated runtime implementation | A concrete representation and operational contracts tied to the pinned code |
| Arbitrary Lean source | A source discipline establishes the runtime property through compilation | Source non-escape and entry guarantees, lowering correspondence, and broader compiler coverage |

The recommended next theorem is at the counted supported-fragment boundary. Keep any unproved C-runtime fidelity explicit. The arbitrary-source claim is a later extension unless the paper actually relies on it.

## Gap 1: Complete ownership and reference-count accounting

### Current limitation

`Inv` equates `H.rc` with `Ctx.mult`, but does not independently establish that either counts the actual owning roots and incoming heap edges. `OwnersAccounted` improves the count-zero/count-one environment property; it is not a complete count representation for arbitrary multiplicities.

`CountFidelity` currently counts variables in an arbitrary list and heap fields in `List.range H.next`. The definitions do not require that the variable list is duplicate-free or complete, or that all live heap cells lie below `H.next`. Repeated variables can inflate the owner count, omitted owners can disappear from it, and out-of-range cells can hide incoming edges.

The already established initializer predicate is useful but only concerns that fixed context. It does not repair general entry-state validity or operation-by-operation count preservation.

### Required design

Define one coherent validity/accounting relation for the supported fragment, including:

- A finite set of owning roots, or a duplicate-free list with a completeness proof.
- The interpretation of each root as an actual counted ownership obligation. Distinguish owning references from borrowed pointers, administrative aliases, and stale values in dead variables.
- A complete finite heap domain, or a heap-range invariant proving that enumeration below the cursor includes every live cell.
- The incoming owning edges contributed by supported object fields, with object liveness and field validity conditions.
- A precise account of outstanding RC obligations that the current language does not represent as distinct owned variables.
- Explicit single-threaded, nonpersistent restrictions where the count equation relies on them.

For the supported single-threaded fragment, the intended equation is schematically:

```text
storedRC(r) = owningRootObligations(r) + incomingOwningEdges(r)
```

If an additional category of outstanding RC obligations is needed, give it a representation and transfer semantics. Its entries must correspond to real counted obligations in the instruction execution. Do not repair the equation with unconstrained ghost credits that merely restate the stored count.

### Why inc needs particular attention

The present `Code.inc x n` raises a count without introducing a distinct destination variable. A complete fidelity invariant that counts only variables tagged `owned` cannot automatically be preserved by that operation. Decide whether to model ownership credits associated with future owned uses, make handle creation explicit, or restrict the supported counted instruction language. The consuming operation must discharge the same obligation.

This is a modeling choice that must be settled before promising a general preservation theorem.

### Required results

1. The supported initializer establishes the complete validity relation.
2. Count one implies no competing counted owner or incoming owning edge beyond the one permitted owner.
3. Moving or borrowing a pointer does not manufacture an additional owning obligation.
4. The validity relation excludes duplicated support, omitted owning roots, and hidden out-of-range incoming edges.

Completion criterion: a theorem derives the intended uniqueness fact from complete accounting, rather than interpreting the raw integer count as uniqueness by definition.

## Gap 2: Preserve accounting through checker-accepted execution

### Current limitation

The new local preservation lemmas require additional side conditions: `bindOwned` needs no existing owner of the introduced reference, and `dec` needs the stated restriction on surviving owners. `check` and `checkNF` have not been strengthened to establish these conditions for general accepted programs.

`principal_write` takes accounting only at `Runner.initCtx`. It does not carry the missing per-operation obligations through arbitrary nested execution. Its `hacc` and `hcount` premises are unused by the proof.

### Required implementation choice

Use a stronger checker, derive the side conditions from the complete invariant, or define a precise program-indexed obligation that clients must establish. Whichever route is chosen, state who supplies each fact and prove it at the state where the operation executes.

Do not silently turn a desired preservation result into a hypothesis requiring the invariant after every step.

### Required operation cases

| Operation | Preservation obligation |
| --- | --- |
| Move/check alias | Transfer one owning obligation; invalidate the previous owned use without counting administrative pointer copies twice |
| Borrow/read | Establish lifetime and permitted use without assuming that every pointer occurrence increments RC |
| Increment/decrement | Create or discharge the represented counted obligation; handle count-one transitions and any supported release semantics |
| Extract child | Transfer the selected slot's ownership into the temporary protocol; establish the child's preconditions and suspend the parent's frame |
| Enter/return from call | Transfer parameter/result obligations while preserving suspended caller ownership |
| Restore child | Consume the returned child obligation into the slot and preserve the parent's exclusive ownership |
| Scalar replacement | Preserve appropriate counts and account for the overwritten value under the stated scalar-only restriction |

Use the existing frame and confinement results where applicable. Avoid requiring every owning name to be globally injective when several legitimate counted references are supported at higher counts; the invariant should capture count ownership, not impose an accidental whole-language ban on sharing.

### Target theorem

The intended statement is schematic:

```text
Accepted(c, program) and ValidState(initial, c)
imply that execution preserves validity at each reached program point,
and that each certified store is reached with its target exclusive.
```

The final-state version alone is insufficient to justify the count at intermediate writes. A big-step proof may establish the intermediate facts internally; a small-step formulation may state them directly.

Completion criterion: the main accepted-execution result preserves the strengthened accounting relation and uses it at certified stores. Merely adding unused premises to an existing theorem does not satisfy this criterion.

## Gap 3: Compose the counted pair protocol with nested execution

### Current limitation

The detailed counted-pair and restoration results exist, but the headline nested correspondence does not consume them. `execNested` treats the parent/child increments and pair decrement as no-ops. It models restoration by an unconditional field update. `Nested.runN` likewise updates the restored slot without choosing a copy or mutate disposition.

There are already useful boundary lemmas, including `protocol_cells`, relating counted extraction to the abstract take-out on session cells. Use those results. The missing connection is an execution simulation that justifies the abstraction and the exclusive restoration branch.

### Required semantics

Introduce or extend a counted execution for the supported operations. It must represent the temporary pair, its component edges, increments, restricted release, child-call boundary, and both restoration dispositions.

The central protocol should have the following actual state transitions:

1. Transfer the parent/child ownership into a fresh temporary pair under the helper's supported ownership convention.
2. Project the parent and child and establish the new counted obligations.
3. Release the unique pair and remove its two edges; derive the resulting component counts.
4. Run the supported child computation while preserving the suspended parent's cell and ownership.
5. Restore the actual returned child into the parent using a semantics that admits a copy branch.
6. Derive that the exclusive branch is selected from the preserved accounting facts.

Use `CountedPair` and `PutBack` results directly where their premises fit. Generalise them where the actual execution boundary differs. Do not redefine restoration as always mutating and then describe mutation as a derived disposition.

### Required representation relation

The counted execution and abstract nested model need not have identical heaps at every instruction. The temporary pair exists only in the more detailed state; allocation can also advance the cursor even when the pair is later freed.

Define a relation that identifies session objects, handles temporary objects and allocator progress, and preserves the facts needed at the next step. State whether reference names are identical or related by an injective mapping. An erased temporary pair must have no observable surviving owner or edge before it is hidden.

Completion criterion: a checked macro-step or instruction-step simulation connects the full counted extraction/call/restoration sequence to the abstract nested transition, and derives restoration's disposition. The final theorem uses this result in its proof dependency chain.

## Gap 4: Cover every operation included in the no-copy claim

### Current limitation

The nested `Write` trace records designated writes from the scalar program, but extraction and put-back change fields without producing events. An accepted extract/restore sequence can therefore have an empty trace. The statement that all recorded writes are exclusive does not certify these unrecorded stores.

### Required repair

Either extend the event trace to include the relevant extraction/restoration operations, or retain the designated-write trace and prove separate disposition results for every other store included in the claim. Both approaches are valid if the final theorem explicitly covers the complete claimed sequence.

If introducing richer events, useful fields include operation kind, target identity, selected index, observed pre-store ownership state, and actual disposition. The event must be derived from the branch the semantics takes; logging `inPlace = true` unconditionally would not repair the theorem.

Prove coverage as well as event properties:

```text
Every array store covered by the guarantee has a corresponding execution fact;
every such execution fact establishes the exclusive disposition.
```

Distinguish in-place array updates from allocation freedom. The temporary pair, boxed values, or call frames may allocate even when no covered array buffer is copied.

Completion criterion: a nontrivial nested certificate covers the leaf update, extraction placeholder stores, and parent restorations. A leaf-only trace cannot stand in for a whole-protocol certificate.

## Gap 5: Relate recursive calls to actual invocation-local code

### Current limitation

The `.recurse` interpretation executes a supplied `Nested.NCode` body. The finite-path induction derives contracts for constructed tail bodies, but does not identify them with actual emitted recursive invocations. N10 remains that connection.

The present model also exposes path and value as scalars. Deeper indices must come from those exposed scalars, whereas the emitted function re-projects the selected index from each invocation's own path node. This is an expressiveness mismatch in the state model, not simply a missing application of induction.

### Required extension for an emitted recursive guarantee

- Represent invocation-local environments or frames, so repeated static binder identities do not conflate different dynamic invocations.
- Represent the supported path data and its continuation sufficiently to interpret each invocation's index projection.
- Resolve the recursive target to the actual captured declaration and interpret the supported body, rather than supplying a replacement model body to the call rule.
- Specify actual parameter passing, returned values, suspended caller state, and continuation resumption.
- Relate the emitted return value to the model's return requirement. Do not force the original reference into the call result unless the admitted callee contract establishes that identity.
- Use a well-founded path measure or an appropriate recursive semantics for the intended executions. If bounded execution is used, state the bound and prove it adequate for the supported finite paths.

The recognised pair branches also need their own execution connection if they are included in the recursive theorem. Their recognisers alone do not establish the meaning of their reset/reuse operations.

Completion criterion: the simulation follows the actual supported declaration on nested paths with independently chosen per-level indices and preserves caller frames through return. The emitted body or its desired behaviour is not supplied as the conclusion in a call contract.

If this work is deferred, retain the current finite syntactic-path theorem with its explicit N10 boundary. Do not describe it as a certificate for arbitrary emitted recursion.

## Gap 6: Make the principal theorem transport the property across the chosen boundary

### Current limitation

`principal_write` conjoins the flat recognised-prefix and runtime-model results. That is a valid presentation of those results. Its unused accounting premises do not establish a new physical ownership conclusion, and both heaps in its conclusion remain formally defined models.

### Required theorem structure

Keep the model theorem with the assumptions it actually needs. Add an adequacy or transport theorem for the counted execution or concrete representation being claimed. The latter should consume the completed accounting, execution simulation, and operation-coverage results.

For the counted supported-fragment target, the principal claim should have this schematic content:

```text
Recognition(actualCode, supportedFragment)
and Acceptance(context, projectedProgram)
and CompleteValidEntry(countedState, context)
and the specified primitive/call contracts
imply that execution of supportedFragment
preserves ownership validity and takes the exclusive branch
at every covered array operation,
with the stated result and heap correspondence.
```

If extending to the linked implementation, introduce an actual concrete-state/representation relation and state the external runtime contracts that connect instruction transitions and RC observations to that state. Those contracts may remain trusted for a conditional submission. A second heap with the same count fields is not by itself a relation to physical memory.

Completion criterion: each layer contributes a theorem actually used by the principal proof, and the conclusion states the intended ownership/no-copy property at the advertised execution boundary. Retain an explicit list of residual implementation contracts.

## Evidence gate correction

This is supporting validation work rather than a replacement for the semantic gaps above.

The probe now returns `1` on ordinary observation mismatches. The runtime gate also expects `1` for the check-enabled `inline-exact` and `closed-case` abort controls. Consequently, an ordinary mismatch can be accepted as the expected exclusivity abort.

Give observation mismatches a distinct result, such as exit `2`, and require a specific abort outcome or diagnostic for the negative controls. Require that a normal return from a mode expected to abort is always a failure. Keep positive controls that establish the probe still executes successfully in the matching unarmed or exclusive case.

The differential corpus still compares observations with recorded expectations, rather than executing the Ownership model. Keep that distinction explicit. Every claimed measured configuration, including the row-specific armed cases, needs a corresponding executable mode and actual run evidence.

Completion criterion: wrong values, wrong dispositions, ordinary failures, and the intended exclusivity abort cannot be confused by the gate.

## Recommended implementation order

| Stage | Work | Evidence of completion |
| --- | --- | --- |
| 1 | Settle the complete ownership/RC state and supported operation scope | Validity definitions, adequate support/domain conditions, initializer proof, and rejected accounting countermodels |
| 2 | Establish accounting preservation for accepted operations | Checker-derived or explicit program-indexed obligations and an execution preservation theorem |
| 3 | Connect counted extraction and restoration | Counted macro-step simulation consuming the existing protocol and disposition proofs |
| 4 | Establish operation coverage | All stores included in the no-copy claim are covered, with derived dispositions |
| 5 | Extend invocation/path semantics where recursive emitted execution is claimed | Per-invocation indices, actual captured callee, and caller-preserving return simulation |
| 6 | Compose the principal guarantee | A theorem at the chosen boundary that uses the preceding results |
| Parallel small fix | Separate expected aborts from probe mismatches | Positive and negative gate results with distinct failure classification |

For the narrower paper route, stages involving actual emitted recursion or concrete C semantics can remain explicit limits. Accounting adequacy, faithful claims, and reliable evidence labels still need to be resolved for whatever boundary is chosen.

## Agent deliverables

Return the changed definitions and theorems, the principal result's complete type, a proof-dependency map, and meaningful regression cases for the previously admitted accounting configurations and omitted operations. Include one executable nested example with differing per-level indices if claiming emitted recursive coverage.

Run the repository's prescribed Lean builds and axiom audit. Run the sibling gates only when their pinned environment is available, and report actual outcomes separately from expected results. Document any remaining primitive or backend assumptions without marking them proved merely because they have been named.

Do not weaken existing results or introduce new axioms to make the completion criteria pass. If the supported fragment must narrow, state exactly what is excluded and why the remaining theorem still addresses the intended use case.

## Source map at the baseline

- [Accounting definitions and initializer lemmas](https://github.com/scidonia/ownership/blob/73c5775802358cb7b5e2a7e796aa447d4ba172c4/Ownership/Accounting.lean#L276)
- [Current principal theorem](https://github.com/scidonia/ownership/blob/73c5775802358cb7b5e2a7e796aa447d4ba172c4/OwnershipLcnf/Principal.lean#L29)
- [Nested model execution](https://github.com/scidonia/ownership/blob/73c5775802358cb7b5e2a7e796aa447d4ba172c4/Ownership/Nested.lean#L159)
- [Nested emitted-fragment interpretation](https://github.com/scidonia/ownership/blob/73c5775802358cb7b5e2a7e796aa447d4ba172c4/OwnershipLcnf/NestedSemantics.lean#L283)
- [Counted pair protocol](https://github.com/scidonia/ownership/blob/73c5775802358cb7b5e2a7e796aa447d4ba172c4/Ownership/CountedPair.lean#L422)
- [Protocol/session-cell bridge](https://github.com/scidonia/ownership/blob/73c5775802358cb7b5e2a7e796aa447d4ba172c4/Ownership/PathConsolidation.lean#L1422)
- [Derived parent preservation](https://github.com/scidonia/ownership/blob/73c5775802358cb7b5e2a7e796aa447d4ba172c4/Ownership/PutBack.lean#L432)
- [Restoration disposition theorem](https://github.com/scidonia/ownership/blob/73c5775802358cb7b5e2a7e796aa447d4ba172c4/Ownership/PutBack.lean#L703)
- [Finite-path/N10 and invocation-index boundary](https://github.com/scidonia/ownership/blob/73c5775802358cb7b5e2a7e796aa447d4ba172c4/OwnershipLcnf/PathRecursion.lean#L63)
- [Runtime-model correspondence](https://github.com/scidonia/ownership/blob/73c5775802358cb7b5e2a7e796aa447d4ba172c4/OwnershipLcnf/RuntimeModel.lean#L472)
- [Probe mismatch result](https://github.com/scidonia/ownership/blob/73c5775802358cb7b5e2a7e796aa447d4ba172c4/runtime-bridge/RuntimeBridge/Probe.lean#L166)
- [Expected-abort gate](https://github.com/scidonia/ownership/blob/73c5775802358cb7b5e2a7e796aa447d4ba172c4/scripts/check_runtime_binding.sh#L38)

## Stage 1 status (2 November 2026)

The counting layer Gap 1 asked for exists. `Ownership/CompleteAccounting.lean`
defines `Accounted support H env c` — the checker invariant, a duplicate-free,
sound, complete and reference-bound enumeration of the owning variables, the
live-cell domain, and the count equation over the two independently computed
counts — proves it at the initializer (`Accounted.initCtx`), derives the
count-one dichotomy and the retained predicates, preserves it through the context
operations and through the take-out, put-back and in-place store at the
interpreter's own post-states, and refutes the configurations the older
predicates admitted. The `inc` question is settled by narrowing the counted
fragment: `Ownership.Supported` admits no increment and exactly one decrement of
an owned handle, and carries the side conditions the checker does not supply. It
is the interface the preservation theorem will quantify over, not a checker.

Superseded here (both kept as the record at the stated baseline):

- The `principal_write` paragraph at line 78: the `hacc` and `hcount` premises
  are no longer in the theorem's signature, and `OwnershipLcnf.principal_accounted`
  consumes `Accounted` at the initializer, concluding what the removed premises
  asserted. The per-operation obligations are still not carried through arbitrary
  nested execution.
- The Gap 6 paragraph at line 195: the unused accounting premises are gone. Its
  second half stands — both heaps in the conclusion remain formally defined
  models, and no transport theorem is added.

Superseded in the dated audit `docs/notes/ownership-paper-contract-audit.md`
(kept as the record at its own revision): the sentence at line 180 that an
ordinary observation mismatch returns 2. This is false for the `sealed` mode,
whose mismatch returns 1 (`runtime-bridge/RuntimeBridge/Probe.lean`); the living
surfaces state the exception, and correcting the code is a separate change.

Still open: execution preservation over the accepted checker, with the facts it
does not supply named where they are consumed — the alias target's and the
scalar-`.let` target's freshness, `dec`'s single handle, and the extracted
child's no-second-edge premise (`Accounted.noOwnerOfSingleEdge` consumes it
without deriving it from the footprint); the counted pair/restoration
composition; the LCNF extraction/restoration stores and their trace events;
invocation-local recursion; and transport at the principal boundary. The heap
remains a named-cell model: nothing here relates it to physical counted
references.
