# Ownership subsystem: review and implementation handoff

Date: 15 November 2026  
Repository: [scidonia/ownership](https://github.com/scidonia/ownership)  
Reviewed revision: [`979729bdbdc31ee8a2f5475f372cde29279d1c12`](https://github.com/scidonia/ownership/tree/979729bdbdc31ee8a2f5475f372cde29279d1c12)  
Primary notes: `report/capability-report.tex` and the fractional-ownership design brief.

## Assessment

The capability subsystem has made substantial progress. The value-admission issue is repaired, the ledger has executable split and join operations, and the surface can produce kernel-checked certificates for closed permission programs. These are useful components of the intended discipline.

The next milestone is to connect the checker, ledger, loans and byte execution into one sound subsystem. At present, important properties are proved in separate models with different instruction languages and different invariants. Their coexistence does not establish that a certified surface program executes safely and cleans up its resources.

Prioritise that connection over additional examples, algorithm libraries, specialisation or performance work.

This is a source review. Lean, Lake and Nix were unavailable in the review environment. No independent build or kernel check of the proposed regression examples was performed. Findings about what a definition checks are grounded in the inspected source; proposed counterexamples should be elaborated in the pinned development environment.

## Improvements to retain

| Improvement | What it establishes |
| --- | --- |
| Canonical coded storage | `SafeType` now produces `El code`, rather than storing an arbitrary `T` on the strength of an isomorphism |
| Thunk regression | The code distinguishes logical encoding from confinement of a compiled value |
| Ledger transitions | Spatial/fractional split and sibling fractional join operations have budget-preservation proofs |
| Closed surface certificates | `#own_cert` emits a theorem of `Checked ...`, verified by the kernel |
| Byte model | Reads, writes, snapshots and concrete byte results have proofs |
| Backend model | A separate pure buffer state machine is related to the reference heap |
| Explicit scope boundaries | Module comments and the report acknowledge several missing integration theorems |

Do not discard these results when strengthening the invariant or unifying execution. Reuse them as lemmas beneath the final safety theorem.

## R1 — Connect certification to the operations that execute

**Priority: P0. Status: established missing connection.**

`Cap/Core.lean` defines a permission-command language containing `write`, `splitAt`, `splitFraction` and `nop`. `Cmd.write` carries a capability identifier and an index, but no byte value. Its checker verifies `Owner.Writable` and leaves the owner unchanged; it performs no heap operation.

`Cap/Exec.lean` defines a different language, `Instr`, containing `fill` and `snapshot`. Its interpreter runs buffer operations without consulting a `Checked` certificate, owner state, loan state or capability guard.

Consequently, the current certificate establishes permission-checker acceptance. `check_covered` establishes coverage preservation for that checker. Neither theorem connects accepted commands to the actual byte interpreter.

### Required change

Choose one of these architectures:

1. Prefer one object-language instruction set with a declarative typing judgement, an executable certificate-producing checker and an operational semantics over a complete world.
2. Alternatively, retain separate permission and executable languages, define their translation explicitly, and prove that execution of the translated program obeys the certified permission transitions.

In either architecture, writes need a value operand and an allocation/capability association. Reads, allocation, joins, loans, snapshots and disposal should enter the same semantics as they are added. Raw backend operations may remain internal implementation primitives, but they must not substitute for execution of the checked program.

### Target theorem

```text
WellFormedWorld initialWorld
and Typing initialContext program Result postcondition
and EnvironmentMatches initialWorld program
imply that every reachable execution prefix avoids ownership faults.

If execution returns value and finalWorld,
then WellFormedWorld finalWorld
and the final context satisfies postcondition(value).
```

State bounds faults, stale access, expired loans and invalid disposal explicitly. For bounded programs, prove termination separately. Allocation failure, if modeled, needs a resource-preserving failure result rather than being silently classified as ownership unsoundness.

### Acceptance criterion

A program written through the surface executes through this certified route and returns a byte snapshot. The safety theorem must apply to that same program and execution, not a second hand-written sequence of fills.

## R2 — Strengthen the invariant beyond byte coverage

**Priority: P0. Status: established invariant and freshness gaps.**

`Ctx.Realizes` currently requires that every owner is covered at denominator `D` and that allocation identifiers are distinct. `Session.Realizes` requires only owner coverage. These predicates do not yet express the full design invariant.

The split operations accept caller-supplied child capability IDs without checking that they are fresh or distinct. The checker calls those operations directly. Reusing a parent ID can make an old name designate a newly active child; repeating a child ID makes lookup ambiguous. Byte-budget preservation does not exclude either state.

`Ctx.alloc_ids_nodup` is useful, but a separate lemma with freshness hypotheses is not a preserved freshness invariant for all accepted commands.

### Required change

Define a complete invariant that includes:

- Positive denominator and valid positive shares.
- Unique active capability identities and valid allocation associations.
- Footprints bounded by their allocations.
- Correct split-node relationships, inherited access ceilings and reconstruction provenance.
- Freshness/history sufficient to prevent consumed identities from being reused.
- Exactly one disposal entitlement per live allocation.
- Loan-to-capability and lifetime relationships, including suspended obligations.
- Agreement between allocation metadata and actual heap storage.

Make every transition preserve that invariant, and make checker acceptance depend on the necessary transition conditions. Either issue fresh IDs internally or require checked freshness evidence.

**Resolve identifier roles before defining uniqueness.** The present tree constructors reuse a child capability ID as an internal split-node ID. `Tree.ids` includes internal and leaf IDs. A blanket `Tree.ids.Nodup` invariant would therefore fail even for an ordinary split. Separate node identities from access-capability identities, or define precisely which occurrences denote the same entity and which must be distinct.

### Regression targets

Starting from a normal initial owner, attempt:

```text
splitAt oldId oldId freshId midpoint
write oldId leftIndex
```

Under the design's stale-handle policy, the original capability must not become valid again merely because its number was reused for a child.

Also attempt:

```text
splitAt oldId sameChildId sameChildId midpoint
```

The transition must reject duplicate child authority identifiers. Add collisions with another live capability, a disposal entitlement where namespaces overlap, and a previously consumed ID.

These are regression specifications; this review did not independently run their Lean forms.

## R3 — Connect lifetimes to capabilities and implement actual reborrowing

**Priority: P0. Status: established missing relationships.**

`Policy.Writable` currently conjoins an owner write guard with liveness of a supplied lifetime. It does not prove that the capability belongs to that lifetime or that an applicable loan authorises it. An unrelated live lifetime satisfies its liveness conjunct.

`LoanCtx.BeginOK` does not establish all relationships between the inserted records, including equality between the new lifetime ID and the loan's lifetime field. `endLoan` checks the selected loan's lifetime but does not require descendant loans to have ended.

`Cap/Nested.lean` is explicitly a separate bookkeeping model. Its `nested_begin` theorem begins a second borrow after the first has ended. This demonstrates sequential restoration and borrowing again, rather than a borrower lending onward while its enclosing loan remains live. It does not update the owner tree or loan context.

### Required change

Integrate loan records with capability entries:

1. Each borrower records its applicable lifetime, footprint, ceiling and parent loan.
2. Beginning a loan validates its lender and binds the loan to the newly created lifetime.
3. Delegation suspends the appropriate lender authority in the ledger.
4. A reborrow delegates from a borrower whose enclosing lifetime remains live.
5. Ending a loan requires completed descendants and reconstruction or retirement of all delegated authority.
6. Restoration consumes or invalidates borrower capabilities before restoring lender access.

A write under a borrowed capability must check its own lifetime and dependencies. Choosing another live lifetime must not reauthorise it.

### Acceptance criterion

Run a genuinely nested example:

```text
begin outer mutable loan
  begin inner reborrow from outer borrower
    write through inner borrower
  end inner loan
  write through restored outer borrower
end outer loan
```

Reject writing through the suspended outer borrower during the inner loan, ending the outer loan first, and accessing the inner borrower after restoration.

## R4 — Give disposal one complete rule across the execution API

**Priority: P0. Status: established inconsistency between model interfaces.**

`Session.free?` refuses disposal when its loan list is nonempty, but otherwise does not demand root reconstruction or a supplied disposal entitlement.

`Ctx.freeWith?` checks the recorded disposal ID and removes the owner. `World.freeWith?` uses that operation. This route does not consult outstanding fragments or loans.

The session loan check therefore does not establish a uniform disposal discipline for the world. The current models are pure values; this observation is not a demonstrated physical use-after-free. It identifies missing conditions before a mutable runner can safely use these operations.

### Required change

Define one legal-disposal predicate and use it in the certified execution route. According to the present design it requires:

- The unique disposal entitlement.
- The prescribed reconstructed root authority.
- No outstanding delegated fragments or dependent loans.
- A live allocation with matching metadata and storage.
- Consumption of ownership and invalidation of all remaining names for that allocation.

Prove allocation removal and stale-handle rejection. Internal helper functions that simply erase a map entry should be described as helpers, not sufficient public disposal checks.

### Acceptance criterion

The same disposal command rejects missing entitlement, outstanding fractional/spatial fragments and live loans, then succeeds after legal reconstruction. Subsequent access fails through the same typed/executable route.

## R5 — Complete the acceptance example through the certified route

**Priority: P1. Status: the existing examples cover different parts of the intended trace.**

The current session's 64-byte example manually builds a spatially split owner, fills two halves, and snapshots the result. Fractional scans and other byte facts are demonstrated separately. The example does not execute the complete acceptance trace from the design.

Once R1–R4 are addressed, run one surface program that:

1. Allocates 64 zeroed bytes and records the root/disposal authority.
2. Begins a full mutable loan.
3. Spatially splits into `[0,32)` and `[32,64)`.
4. Fills the halves with `1` and `2` respectively.
5. Splits the right view fractionally into two readers.
6. Scans both readers, obtaining `64` from each.
7. Rejoins the readers and spatial slices.
8. Ends the loan and restores the root.
9. Takes an independent immutable snapshot.
10. Frees the allocation and terminates with no live resource or loan.

Prove the result and cleanup for the actual certified execution. Include stale aliases, wrong-allocation joins and illegal disposal as refused variants.

The union-find example is useful after this connection is established. Currently it demonstrates proof-guarded pure list updates and a concrete result. Its structure has only a length agreement between parent and rank lists; it is not an integrated client of the certified command interpreter. Do not count it as evidence that the full execution boundary is already enforced.

## Documentation and claim corrections

Update the report and module comments alongside the implementation:

| Current wording or implication | More precise description |
| --- | --- |
| The context is never a public value | The intended runner will encapsulate the execution state; current context/session/world structures are public pure model data |
| Deep checker soundness | Acceptance implies the particular guard/transition and coverage results currently proved; whole-program execution safety awaits R1 |
| Nested borrowing | Current standalone bookkeeping includes sequential end-and-borrow-again; integrated nested reborrowing remains open |
| 64-byte acceptance run | Current guarded fill/snapshot example; the complete split/borrow/join/free trace remains to be connected |
| Mutable backend | Pure buffer state-machine model, currently implemented with lists |
| Admission excludes closures | Canonical storage excludes arbitrary original values; the encoding relation alone does not establish confinement |

`Cap/Admission.lean` still has an old header asserting that no resource-hiding type can be bijective with a code. Remove it; it contradicts the corrected definitions and the retained thunk regression.

`Cap/Certify.lean` has an outdated header saying the surface emits no proof term. Update it to reflect `#own_cert`.

The report's open-items section already acknowledges the missing interpreter consuming certified commands against the world. Promote that to the principal next milestone so readers do not infer an integrated guarantee from the component inventory.

## Backend and performance boundary

`Backend` is a pure state machine over `List UInt8`. Its relation to the reference heap is meaningful, but it does not establish native mutation, RC=1, pointer uniqueness or absence of copying.

Keep permission soundness, mutable-backend refinement and runtime-representation guarantees separate. A certificate about full permission does not imply that two Lean array wrappers for disjoint slices avoid copy-on-write.

The current timing report is explicitly about interpreted pure models. Preserve that qualification. Measure a real mutable implementation only after its execution route is tied to the certified semantics; measure dispatch, ledger lookup, allocation, snapshot and copy costs separately.

## Recommended implementation sequence

| Order | Work | Completion evidence |
| --- | --- | --- |
| 1 | Define the complete world/ledger invariant and identifier roles | Satisfiable initial states; freshness, bounds, allocation, disposal and loan relationships stated |
| 2 | Strengthen split/join transitions | Full invariant preservation; duplicate/recycled IDs refused |
| 3 | Unify checked commands and execution, or prove their translation | A general execution-safety/preservation theorem for accepted programs |
| 4 | Integrate loans, capability lifetimes and disposal | Real nested reborrow and complete disposal controls |
| 5 | Run the complete 64-byte surface example | Snapshot, scan results, cleanup and safety proved for one execution |
| 6 | Add symbolic contracts and hidden-index elaboration | Modular programs produce certificates without supplying arbitrary closed owners |
| 7 | Implement/refine actual mutable storage | Primitive refinement and representation invariant for the chosen substrate |
| 8 | Specialise and expand algorithm examples | Correctness-preserving optimization and measurements of the resulting implementation |

Avoid adding more parallel miniature models to satisfy individual checklist items. Each new operation should be an extension of the same certified language, invariant and execution relation.

## Validation requirements

Use the repository's pinned Nix/Lake workflow and `AGENTS.md`. At minimum:

```bash
nix develop -c lake build Cap
nix develop -c lake build OwnershipTest
nix develop -c bash scripts/check_all.sh
```

Ensure intended positive and negative capability fixtures actually run in the relevant gate. The current full gate builds `Cap`, but the standalone `bench/` controls should not be assumed covered merely because their filenames appear in the report. Expected rejections need a harness that checks the intended diagnostic or failed proposition.

Audit exported safety theorems and closed certificates for the intended axiom policy. Do not treat a successful `by decide` certificate as stronger than its proposition: `Checked` currently means success of the current checker.

For every strengthened theorem, supply a closed positive instance discharging its premises. Keep the earlier isolated-accounting impossibility regression: conditional theorem acceptance alone does not demonstrate usable hypotheses.

## Source pointers

All links are pinned to the reviewed revision.

- [Implementation report](https://github.com/scidonia/ownership/blob/979729bdbdc31ee8a2f5475f372cde29279d1c12/report/capability-report.tex)
- [Core checker and certificate predicate](https://github.com/scidonia/ownership/blob/979729bdbdc31ee8a2f5475f372cde29279d1c12/Cap/Core.lean)
- [Byte interpreter](https://github.com/scidonia/ownership/blob/979729bdbdc31ee8a2f5475f372cde29279d1c12/Cap/Exec.lean)
- [Context invariant and disposal](https://github.com/scidonia/ownership/blob/979729bdbdc31ee8a2f5475f372cde29279d1c12/Cap/Context.lean)
- [Ledger and split operations](https://github.com/scidonia/ownership/blob/979729bdbdc31ee8a2f5475f372cde29279d1c12/Cap/Ledger.lean)
- [Sibling joins](https://github.com/scidonia/ownership/blob/979729bdbdc31ee8a2f5475f372cde29279d1c12/Cap/Join.lean)
- [Loan bookkeeping](https://github.com/scidonia/ownership/blob/979729bdbdc31ee8a2f5475f372cde29279d1c12/Cap/Loans.lean)
- [Lifetime policy](https://github.com/scidonia/ownership/blob/979729bdbdc31ee8a2f5475f372cde29279d1c12/Cap/Policy.lean)
- [Standalone borrow model](https://github.com/scidonia/ownership/blob/979729bdbdc31ee8a2f5475f372cde29279d1c12/Cap/Nested.lean)
- [Session and fill/snapshot example](https://github.com/scidonia/ownership/blob/979729bdbdc31ee8a2f5475f372cde29279d1c12/Cap/Session.lean)
- [World model](https://github.com/scidonia/ownership/blob/979729bdbdc31ee8a2f5475f372cde29279d1c12/Cap/World.lean)
- [Surface certificate generation](https://github.com/scidonia/ownership/blob/979729bdbdc31ee8a2f5475f372cde29279d1c12/Cap/Surface.lean)
- [Canonical storage admission](https://github.com/scidonia/ownership/blob/979729bdbdc31ee8a2f5475f372cde29279d1c12/Cap/Admission.lean)
- [Backend model](https://github.com/scidonia/ownership/blob/979729bdbdc31ee8a2f5475f372cde29279d1c12/Cap/Backend.lean)
- [Union-find example](https://github.com/scidonia/ownership/blob/979729bdbdc31ee8a2f5475f372cde29279d1c12/Cap/UnionFind.lean)
