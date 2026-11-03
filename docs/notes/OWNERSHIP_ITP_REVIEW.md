# Simulated ITP Review: Ownership for In-Place Unobservable Updates in Lean 4

**Subtitle:** Without Modifying the Compiler  
**Author:** Gavin Mendel-Gleason  
**Review date:** 3 November 2026  
**Reviewed revision:** [`04bbf39b06c616195f4c0c4b428df5f9d8120cdb`](https://github.com/scidonia/ownership/tree/04bbf39b06c616195f4c0c4b428df5f9d8120cdb)  
**Manuscript:** `paper/ownership-skeleton.pdf`, 16 pages  
**PDF SHA-256:** `3d27c5445b9ff67defaaf2d352301d41619aba462754b8741abf6b45ecc94a14`

## Recommendation

**Weak reject for the current full-paper submission; a credible candidate for acceptance after focused revision.** This is a simulated reviewer judgement, not a prediction of a programme committee decision.

The development contains a substantive mechanised result. In particular, the counted execution of the recognised extraction/call/restoration fragment is now composed with the abstract nested-update model, and the restoration's in-place disposition is derived at the child call's output state. This addresses a major weakness of earlier versions.

My remaining reservations concern the scientific positioning and the interpretation of the semantic boundary. The paper advertises a static guarantee over existing compiler IR, while the strongest proved execution is an interpretation of a recognised trace, with important operations specified by contracts and the recursive call replaced by a supplied model computation. This can support an ITP paper. It must be presented as that particular achievement, and its novelty must be justified at that boundary.

I found no demonstrated contradiction in the inspected theorem statements or proof scripts. The concerns below distinguish established scope limitations, manuscript discrepancies, and questions about the modelling choices. They should not be treated as reports of kernel-level unsoundness.

**Reviewer confidence: medium.** I read the manuscript, inspected the central definitions, proof compositions and instances, and checked selected primary related work. Lean, Lake and Nix are unavailable in this environment, so I did not independently elaborate the development or rerun the runtime experiments.

## Summary of the contribution

The paper studies when Lean's reference-counted arrays can be updated through the exclusive branch. It introduces an accounting relation between stored counts, incoming heap edges and owning variables; proves preservation for a restricted straight-line language; and verifies an extraction/call/restoration protocol that temporarily allocates a pair containing the parent and extracted child.

A structural recogniser reads a pinned compiler declaration and produces an operation trace. An abstract interpreter and a counted interpreter execute that trace. For one recognised nested-update level, the principal theorem relates the counted execution to the abstract model's execution under layout, entry, path and counted child-call hypotheses. Compatibility permits allocation-cursor slack while requiring identical cells. A parameterised one-level family and a separate closed instance on the captured declaration demonstrate that relevant premises can be discharged. Compiled probes provide supporting observations about the pinned implementation.

The strongest defensible contribution is:

> A mechanised, contract-based certification of a recognised reference-counting protocol, combining complete boundary accounting, derived in-place restoration and a correspondence between counted and abstract fragment semantics.

This is more specific than a general ownership system for Lean or a verified account of unobservable mutation in arbitrary compiled Lean programs.

## Strengths

1. **The principal counted theorem is genuinely composed.** `principal_counted_fragment` connects the recogniser's accepted trace, its counted execution, the abstract path run, accounting at the relevant boundaries, and restoration at the actual call-output heap. These are no longer merely adjacent lemmas.
2. **The ownership invariant addresses a real specification problem.** Equating a context multiplicity with a stored count does not establish that all owning roots are counted. `Accounted` explicitly includes a finite, duplicate-free, complete support of owning variables and a bounded live-cell domain.
3. **The restoration branch is derived.** The counted execution invokes a restoration operation with both dispositions available. The proof establishes that the relevant invocation selects mutation; it does not establish the result by defining restoration as mutation only.
4. **There are non-vacuous instances and useful controls.** The array-length/index/value family establishes more than a fixed computation. The retained-parent, omitted-release, invalid-support and persistent-object controls probe distinct mechanisms rather than treating every failure as checker rejection.
5. **The implementation documents its limits unusually explicitly.** The distinction between ordinary and counted child contracts, the missing emitted callee, model references versus physical addresses, and boundary versus instruction-by-instruction accounting can all be located in the source.
6. **The subject fits ITP.** The interesting questions concern invariant design, preservation, abstraction boundaries and proof composition. A complete verified C backend is not needed for a worthwhile contribution here.

## Major concerns

### M1. The compiler connection needs a more exact semantic description

**Assessment:** established limitation; the present framing gives it insufficient prominence.

In `OwnershipLcnf/CountedTrace.lean`, `execCountedAST` first calls `projectNested`, then executes the returned prefix's `fragment`. Its recognition lemma reduces by simplification after rewriting the recogniser result. This makes recognition load-bearing, but it establishes decoding consistency, not a separate adequacy theorem against independently defined LCNF execution.

The substantive execution theorem is between `execCounted` and `Nested.runN`. Those are meaningful, separately defined interpreters, and the correspondence between them is not erased by this observation. However, the route from the accepted LCNF syntax to the chosen operation meanings remains part of the semantic modelling and its external contracts.

For example, the counted interpreter makes path/node bookkeeping operations no-ops on the ownership heap. Its recursive-call clause directly executes the supplied `Nested.NCode` body; it does not look up and execute the emitted recursive declaration. The take-out helper's body is not independently executed by this interpreter either.

**Required revision:**

- State early that the proved correspondence relates an interpretation of the recognised fragment to the ownership model.
- Separate structural recognition, decoding consistency, interpreter correspondence and implementation fidelity in one diagram or table.
- Describe exactly which instruction meanings are defined, which omitted effects are justified by a separation contract, and which helper/callee meanings are supplied.
- Avoid allowing “the connection to the emitted fragment is checked” to imply that execution adequacy for the actual LCNF or C implementation has been proved.

**Possible technical strengthening:** define a semantics for the accepted LCNF subset independently of the recogniser and prove the decoding faithful to it, keeping primitive and call contracts explicit. This need not extend to all LCNF or C. If that proof is deferred, position the contribution as recognised-trace certification and justify its usefulness at that boundary.

### M2. The finite-path statement understates the deeper-index limitation

**Assessment:** a specific discrepancy between the manuscript's explanation and the implementation's documented scope.

Section 6.2 says that a deeper level which re-indexes by projecting a continuation is described by the path list rather than the flat environment. This reads as if the representation issue has been handled.

The header of `OwnershipLcnf/PathRecursion.lean` explicitly states a narrower result. The finite model requires a deeper level's index to come from one of the scalar values exposed by the isolated call. It excludes the case in which that index is obtained by re-projecting the actual continuation. The emitted function does perform such projections at successive invocations; its body is not captured by this theorem.

**Required revision:** replace the explanation with a direct limitation, for example:

> The finite model does not interpret successive path-node projections by the emitted recursive callee. The recognised outer fragment is related to a supplied model child computation; the emitted callee's frame and path projections remain outside the correspondence.

Do not present ordinary finite-path induction as a proof about arbitrary executions of the emitted recursive declaration. A narrow one-level result with a modular call contract is acceptable; ambiguity about the larger claim is not.

### M3. The counted child-call contract carries a substantial part of compositional correctness

**Assessment:** explicit and legitimate assumption, but its scientific weight is not sufficiently explained.

`CountedChildCall` contains `PutBack.ChildCall` and post-call `Accounted` for the caller's environment and context. Expanding `PutBack.ChildCall` reveals admission, checker acceptance, an isolated invariant, annotation and extraction facts, parent/child separation, a completed model run returning the child reference, and preservation of that reference's count and persistence.

The paper correctly says that ordinary finite-path induction does not construct the counted post-call accounting. This is important: the induction does not yet yield a general recursive counted certificate. The closed instance supplies the missing field for a particular child computation.

The contract is not simply an assumption that the desired parent mutation succeeds. Parent preservation and the restoration branch are derived from it, which is a real achievement. Nevertheless, a reader needs to see how much the child computation must already establish and how a user supplies those facts.

**Required revision:**

- Give a compact mathematical specification of the child contract next to the principal theorem, including the unchanged child count/persistence and caller accounting.
- Distinguish what the ordinary path induction derives from what the counted call contract supplies.
- Explain which facts are discharged automatically, by generic lemmas, and by instance-specific proof.
- State that the supplied computation is a model body and that the emitted recursive callee remains an implementation obligation.

**Most useful technical extension:** a counted composition lemma that reconstructs caller accounting from a verified child computation and a suspended-frame condition, demonstrated on two nested extraction levels. This would provide stronger evidence of reuse than another one-level example. It is an alternative way to strengthen the submission, not a demand to verify arbitrary runtime recursion.

### M4. The temporary-pair window needs a consistent account of live owners

**Assessment:** unresolved modelling/exposition question; not a counterexample to the boundary theorem.

The paper explains that handles transfer into the temporary pair, but also says that the caller's handle still owns the parent, producing a roots-plus-edges overcount. Table 2 calls the handles moved while reporting component owners during the same stage.

The inspected negative theorem, `pairPhase_refused`, is precise: it refutes accounting for the pair-live heap at a particular context in which parent and child have already been bound as owned variables. It does not show that every possible ownership interpretation of that concrete state fails. In particular, the pair itself is a live counted object, and a faithful intermediate accounting could potentially transfer ownership into a root for the pair and treat component projections as borrowed until their increments.

A boundary abstraction may be the right engineering choice. The paper must distinguish that choice from an inherent failure of reference-count accounting during a correct runtime protocol.

**Required revision:**

- Name the context and support interpretation used during the pair-live window.
- Show whether the owning component variables represent actual live LCNF owners at that point, projected aliases, or the abstract take-out's output context.
- Explain how the pair's own owning root is represented or deliberately abstracted away.
- Qualify the claim: this accounting relation at this chosen context is not maintained inside the window; entry, release and restoration are the certified boundaries.
- Explain why boundary simulation is preferable to refining the intermediate root/context model.

If the current component roots are ghost obligations from the abstract take-out, say so directly. The proof remains useful; its conceptual interpretation becomes much easier to trust.

### M5. The novelty argument should focus on preservation and semantic composition

**Assessment:** plausible contribution, insufficiently established by the current comparison.

The count-one dichotomy is elementary once the roots-plus-edges equation is assumed. The contribution must lie in maintaining that equation for the relevant operations, dealing with the counted protocol and establishing the recognised-fragment correspondence.

Huisinga's thesis is an appropriate close comparison: its Sections 6.2 and 6.6 and conclusion explicitly leave compiler integration and formal soundness to future work. This supports the distinction concerning a proved guarantee, but does not itself establish that all the present proof techniques are novel. Perceus already develops reference-count soundness through a linear resource calculus and supports reuse; Counting Immutable Beans studies the relevant reference-count and destructive-update machinery. The paper should compare the actual invariants, semantic assumptions and preservation arguments, not just whether one approach inserts counts and the other checks an existing fragment.

The subtitle's “without modifying the compiler” is an architectural constraint, not enough on its own to establish novelty. Likewise, the broad statement that Linear Haskell and Clean are not connected to emitted code should be replaced by a specific distinction about their source-level guarantees and this paper's certification target.

**Required revision:** add a compact comparison covering the certified object, invariant, proof status, caller obligations and compiler/runtime boundary. State one technical insight the reader can carry to another reference-counted compiler. The most promising candidate is the composition of boundary accounting with a recognised counted protocol, rather than the arithmetic consequence of count one.

### M6. The evidence does not yet demonstrate the full advertised workflow

**Assessment:** useful evidence, but several different scopes must remain separate.

The parameterised `OwnershipTest.CountedFamily.family_chain` applies the counted nested-chain theorem over lengths, valid indices and replacement values. The closed `OwnershipTest.counted_fragment_instance` applies the whole recognised-fragment theorem on the reified captured declaration. These are distinct pieces of evidence: the parameterised family is not itself a parameterised application of the recognition-to-counted-fragment theorem.

The runtime probe is also separate. Its differential mode compares observations with recorded expected booleans; it does not execute the formal Ownership model on the same input. The manuscript already acknowledges this, and should preserve that distinction.

The runtime-binding script checks pinned captures and IR shapes, searches generated C and runtime headers for named primitives, and checks selected probe results. This is supporting evidence, not a semantic proof or an exact certified connection to a linked binary.

**Required revision:** make the coverage explicit:

| Evidence | Scope established |
| --- | --- |
| Parameterised counted family | One model extraction/call/restoration level for arbitrary length, valid indices and scalar value |
| Closed recognised instance | Whole counted-fragment theorem at a concrete captured declaration and supplied model child body |
| Structural mutation controls | Rejection of specified malformed traces, not a universal rejection theorem |
| Linked probes | Observed exclusivity, address and result behaviour on the recorded corpus |
| Artifact gate | Pin, cleanliness and regenerated-capture checks, plus separate backend/probe checks |

A small worked user workflow would improve the paper: show a change to the source update, the regenerated recogniser result, the client obligations, and the certificate that succeeds or fails. A broad performance benchmark is less urgent because the paper does not establish a new compiler optimisation or an asymptotic speedup theorem.

## Additional technical observations

### The all-exclusive trace is not a record of every protocol store

`execCounted` appends the child's `runN` writes during `.recurse`. Its `.takeOut` and `.setArray` clauses update the heap without adding corresponding events to that write list. Extraction and restoration have separate exclusivity/disposition arguments.

Consequently, equality of traces plus an all-exclusive trace predicate should not be presented as sufficient by itself to certify every heap store in the protocol. This is not a missing restoration proof: the principal result has separate restoration conjuncts. Add an event-coverage sentence or table explaining that distinction.

### The flat and nested guarantees use different assumptions

`principal_write` takes the flat entry invariant and runtime-model correspondence; it does not take complete accounting. `principal_accounted` derives consequences of an accounting premise, and `Prefix.toModel_supported` connects the projected flat model to the supported fragment. The manuscript acknowledges that these results are adjacent rather than a single accounting-preservation theorem for every recognised prefix. Preserve that qualification in contribution summaries and diagrams.

### Supported certification is stronger than checker acceptance

`Supported` carries freshness conditions beyond the raw checker and excludes increments and multi-count decrements. `StoreSlots` supplies a heap-dependent fact about the stores reached by execution. `supported_run` is therefore a theorem about certified supported programs from accounted states with that slot predicate, not about every program accepted by `check`.

This is a reasonable theorem. Describe the certificate workflow rather than letting “static ownership checker” imply that the raw checker's success alone establishes complete accounting. Note also that the store restriction concerns the old selected slot as well as the scalar replacement; it excludes general reference-valued array updates from the flat preservation theorem.

### “Unobservable updates” needs an observation boundary

The new title is attractive but broader than the principal counted theorem. That theorem establishes model heap/outcome compatibility; it does not quantify over arbitrary Lean contexts or independently establish contextual equivalence of the emitted program with immutable source semantics. The source library has separate functional-update facts, and the ownership development has separate client-retention results, but they should not be silently folded into the headline theorem.

Either state that unobservability is the existing functional-semantics motivation, while this work certifies a restricted in-place condition, or give the exact client observations and connecting theorem being claimed. Address observations, costs and unsafe inspection must not be accidentally included in a blanket equivalence claim.

## Formalisation and artifact assessment

The following assessment is based on source inspection. “Proved” here describes what the checked-in declarations state and prove, not an independently reproduced kernel build in this review environment.

| Component | Inspected result | Boundary |
| --- | --- | --- |
| `CompleteAccounting` | Complete support/domain/count relation; uniqueness consequences; operation-level accounting lemmas | Named-cell model; no physical-address interpretation |
| `Preservation` | Checker acceptance and accounting along supported flat execution | `Supported`, entry accounting and `StoreSlots` supplied |
| `CountedPair` | Projection increments and restricted pair release restore component counts | Restricted non-cascading protocol model |
| `PutBack` / `CountedNested` | Parent preservation, derived mutate disposition and accounting after restoration | Ordinary and counted child-call contracts supplied |
| `PathRecursion` | Ordinary child contracts derived over finite model paths | No general counted caller-accounting induction; deeper emitted re-projection excluded |
| `CountedTrace` / `Principal` | Whole recognised trace interpretation related to abstract execution | Recognition/layout/agreement/path/accounting/call hypotheses; no emitted-callee execution |
| Closed and family instances | Premises inhabited at specified concrete/model data | Captured recognition instance and parameterised chain family are distinct |
| `RuntimeModel` | Independent definitions of modeled check/write operations and correspondence | No refinement theorem for the actual C primitives |

The repository records successful kernel builds and an axiom audit at its reproduction revision, including the principal counted theorem and family. The recorded footprint contains only standard Lean axioms, without `sorryAx` or `Lean.ofReduceBool`. I did not reproduce those results. A source scan found no `sorry` proof term or declared axiom in the inspected core, LCNF and test Lean files; that scan is not a substitute for elaboration or dependency auditing.

The pinned sibling source was inspected at `66e64334a1c968d829903b8aec8d22f7e3b9fd3f`. Its `takeOut` uses an owned array exchange and its `setAt` array branch has the extraction/check/recursive-update/restoration structure described in the paper. This supports the choice of example but does not discharge the emitted-code contracts.

For artifact evaluation, provide one clean-checkout entry command that provisions the pinned sibling and runs the existing build, axiom, claim, capture and runtime checks. Clearly distinguish the commands the reviewer can run without the sibling from those requiring it. An immutable release identifier would make the submission easier to evaluate.

## Presentation and minor corrections

- The LIPIcs layout is recognisable and legible. The two figures help explain the ownership traffic and the simulation boundaries.
- Keep the `NCode` declaration together. It currently starts on page 3 and resumes after the figure on page 4.
- Put a concise mathematical principal theorem before the long Lean signature. Ellipses should not hide the child-call or accounting obligations; long administrative binder lists need not dominate the main text.
- Explain “a count of one is not one owner” as a failure of the original model invariant to establish ownership accounting. In a faithful reference-count model, one counted owning obligation is precisely what count one is intended to mean.
- Replace “nothing in between is accounted” with the exact statement established for the chosen intermediate contexts. The table itself contains projection stages with different count/edge/root arithmetic.
- Define which uses of “runtime” refer to `Runtime.RHeap` and which refer to the linked Lean runtime. The second model is not independent empirical validation of the first.
- The current PDF has 16 pages. `paper/README.md` still describes a 17-page footprint and should be synchronised.
- Keep disclosure factual, but remove internal revision-process instructions from the submitted paper. This review does not assess compliance with a future conference's AI-assistance policy; verify the applicable policy separately.
- Do not invent proceedings metadata or assume the current page count meets an unverified future call's limit.

## Questions for the author

1. What semantic claim is intended between actual accepted LCNF and the decoded operation trace beyond the structural recognition result?
2. During the pair-live window, which variables are actual owning roots, and which are abstract obligations? Could ownership of the pair replace the duplicated component roots in a finer intermediate relation?
3. What generic condition would let a verified child computation re-establish the suspended caller's complete accounting?
4. Can two counted nested levels be composed without instance-specific reconstruction of every post-call accounting field?
5. Which theorem, if any, connects the title's unobservability claim to the counted-fragment result? If none is intended, can the introduction make that distinction explicit?
6. How much certificate construction is automated after a new source update is compiled, and what is the expected manual proof work?

## Revision priorities and what would change my recommendation

| Priority | Change | Completion criterion |
| --- | --- | --- |
| P0 | Correct the deeper-index explanation | Manuscript and `PathRecursion` state the same exclusion |
| P0 | Clarify the semantic connection | Recognised syntax, trace interpretation, model correspondence and implementation contracts are visibly separate |
| P0 | Expose the child contract | A reader can identify its substantive obligations without opening Lean code |
| P0 | Resolve the intermediate-root explanation | Transfer, live roots, pair ownership and boundary accounting are described consistently |
| P1 | Establish the technical novelty | Comparison with prior RC/uniqueness work explains a reusable proof insight |
| P1 | Strengthen the compositional demonstration | Prefer a counted two-level certificate or generic caller-accounting transport lemma; otherwise justify the one-level scope sharply |
| P1 | Show a usable certificate workflow | One source change is traced through recognition and discharged obligations |
| P2 | Compress and polish | Main theorem readable, datatype intact, documentation synchronised |

I would move toward weak accept if the paper made the semantic boundary unambiguous, gave a convincing account of why the boundary protocol is the interesting proof problem, and demonstrated that the counted reasoning is reusable rather than a one-off reconstruction of a fixed trace. A small counted composition result would be particularly persuasive.

I would not make a verified C runtime, a complete Lean compiler-correctness proof, arbitrary recursion, array splitting or a LeanIn-wide certificate prerequisites for this submission. Those would be different projects. The immediate task is to make this narrower result both scientifically compelling and impossible to misread.

## Evidence and source pointers

All ownership links below are pinned to the reviewed revision.

- [Manuscript](https://github.com/scidonia/ownership/blob/04bbf39b06c616195f4c0c4b428df5f9d8120cdb/paper/ownership-skeleton.pdf)
- [Complete accounting](https://github.com/scidonia/ownership/blob/04bbf39b06c616195f4c0c4b428df5f9d8120cdb/Ownership/CompleteAccounting.lean#L679) and [supported preservation](https://github.com/scidonia/ownership/blob/04bbf39b06c616195f4c0c4b428df5f9d8120cdb/Ownership/Preservation.lean#L198)
- [Counted child-call contract](https://github.com/scidonia/ownership/blob/04bbf39b06c616195f4c0c4b428df5f9d8120cdb/Ownership/CountedNested.lean#L434) and [ordinary child-call obligations](https://github.com/scidonia/ownership/blob/04bbf39b06c616195f4c0c4b428df5f9d8120cdb/Ownership/PutBack.lean#L359)
- [Counted trace execution](https://github.com/scidonia/ownership/blob/04bbf39b06c616195f4c0c4b428df5f9d8120cdb/OwnershipLcnf/CountedTrace.lean#L234) and [recogniser-based AST entry point](https://github.com/scidonia/ownership/blob/04bbf39b06c616195f4c0c4b428df5f9d8120cdb/OwnershipLcnf/CountedTrace.lean#L928)
- [Principal counted theorem](https://github.com/scidonia/ownership/blob/04bbf39b06c616195f4c0c4b428df5f9d8120cdb/OwnershipLcnf/Principal.lean#L422)
- [Finite-path limitations](https://github.com/scidonia/ownership/blob/04bbf39b06c616195f4c0c4b428df5f9d8120cdb/OwnershipLcnf/PathRecursion.lean#L70)
- [Pair-window refusal](https://github.com/scidonia/ownership/blob/04bbf39b06c616195f4c0c4b428df5f9d8120cdb/OwnershipTest/CountedNested.lean#L294)
- [Parameterised counted family](https://github.com/scidonia/ownership/blob/04bbf39b06c616195f4c0c4b428df5f9d8120cdb/OwnershipTest/CountedFamily.lean#L627) and [closed recognised-fragment instance](https://github.com/scidonia/ownership/blob/04bbf39b06c616195f4c0c4b428df5f9d8120cdb/OwnershipTest/PrincipalCounted.lean)
- [Runtime binding script](https://github.com/scidonia/ownership/blob/04bbf39b06c616195f4c0c4b428df5f9d8120cdb/scripts/check_runtime_binding.sh), [probe source](https://github.com/scidonia/ownership/blob/04bbf39b06c616195f4c0c4b428df5f9d8120cdb/runtime-bridge/RuntimeBridge/Probe.lean), and [recorded verification results](https://github.com/scidonia/ownership/blob/04bbf39b06c616195f4c0c4b428df5f9d8120cdb/docs/notes/artifacts/final-revision-check.txt)
- [Pinned source update implementation](https://github.com/scidonia/lean-examples/blob/66e64334a1c968d829903b8aec8d22f7e3b9fd3f/Scidonia/FracPerm/StateVar/Layout5.lean)

Selected primary related work consulted:

- Marc Huisinga, [Static Uniqueness Analysis for the Lean 4 Theorem Prover](https://pp.ipd.kit.edu/uploads/publikationen/huisinga23masterarbeit.pdf), 2023; especially Sections 6.2, 6.6 and the conclusion.
- Alex Reinking, Ningning Xie, Leonardo de Moura and Daan Leijen, [Perceus: Garbage Free Reference Counting with Reuse](https://xnning.github.io/papers/perceus.pdf), PLDI 2021; the soundness/resource-calculus and reuse contributions.
- Sebastian Ullrich and Leonardo de Moura, [Counting Immutable Beans: Reference Counting Optimized for Purely Functional Programming](https://pp.ipd.kit.edu/uploads/publikationen/ullrich19counting.pdf), IFL 2019 proceedings; owned/borrowed references and destructive-update machinery.
- Lean reference manual, [Reference Counting](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Reference-Counting/), consulted 3 November 2026 for background. This current manual is not a replacement for the pinned toolchain's semantics.
