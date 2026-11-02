# Ownership: ITP 2027 preparation and agent handoff

Prepared: 2 November 2026  
Target: ITP 2027, regular research paper  
Repository inspected: `scidonia/ownership`  
Baseline: `61a01439f4b313fb51f7240097b29cdff53131fb`  
Audience: Gavin and the implementation/proof/writing agent

## 1. Submission decision

Prepare a regular ITP paper about a mechanised ownership discipline for a precisely delimited array-update fragment. The preferred technical contribution is a sound count-accounting invariant composed with the counted extraction/call/restoration protocol and its recognised compiler fragment. The paper should teach that proof construction, rather than present a catalogue of separately proved components.

This is a preparation target, not a readiness verdict or a prediction of acceptance. The current repository has substantial proved components, but the counted nested composition remains open. A verified C runtime and arbitrary Lean-source verification are outside the proposed scope.

Working title, appropriate to the current boundary:

> **Mechanising Count-One Ownership for Array Updates in Lean 4**

A stronger title about certifying counted nested updates should wait for the corresponding theorem.

The existing Markdown gap programme remains a useful technical specification. This handoff turns it into a submission plan and updates its status: the model-level extraction/restoration exclusivity gap has now been addressed; the counted emitted-execution connection has not.

## 2. Venue facts and provisional requirements

The official ITP 2027 site places the conference at the University of Strathclyde, Glasgow. Its header gives 2–7 August 2027, while its welcome text still says the dates are being finalised. No submission CFP or deadlines were visible on that page when checked on 2 November 2026. Treat the event dates as provisional and the submission deadline as unknown. [S1]

Use the previous call only as a planning precedent: ITP 2026 allowed regular papers of 16 pages excluding references, in LIPIcs format, without appendices; short papers were six pages. It used lightweight double-blind review and requested anonymised verifiable supplementary material. None of these is yet a confirmed 2027 rule. [S2]

When the 2027 CFP appears, record its actual abstract/paper deadlines, time zone, categories, formatting, anonymity, supplementary-material rules, and AI policy. Replace this provisional requirements paragraph. Do not transfer 2026 dates to 2027 or use third-party deadline estimates.

## 3. The central argument

The problem is understandable without the implementation: an array update can copy when an extra counted reference survives. A compiler-generated temporary pair introduces exactly the sort of ownership traffic that a simple “one variable owns the array” explanation misses. A convincing static guarantee must connect the checker's permission to the counted execution at each update.

Organise the result around three questions:

1. **What does count one mean?** Relate the stored count to a complete representation of owning roots, heap edges, and any outstanding counted obligations.
2. **Why is it preserved?** Show that accepted operations transfer those obligations correctly, including temporary pair projections, release, and the suspended caller frame.
3. **What code does this certify?** Connect that proof to an explicitly supported recognised fragment, with an honest call and primitive boundary.

The preferred contribution sentence, to use only after the missing composition is proved, is:

> We mechanise a count-aware ownership checker and prove that accepted programs in a supported finite nested array-update fragment preserve ownership accounting and select exclusive update branches, with a correspondence to recognised LCNF under explicit primitive and call contracts.

Until then, describe checker soundness, flat correspondence, finite nested correspondence, and counted protocol lemmas as separate results. Do not call their coexistence a completed counted nested execution proof.

### Conservative abstract draft for the present baseline

This draft describes existing components and the remaining boundary. It is a starting point for author revision, not a submission-ready abstract:

> Reference-counted array updates can mutate their input when it is exclusive and otherwise require copying. We present a Lean formalisation of a static count-one ownership discipline for a restricted array-update language. The development proves checker soundness, recognises selected emitted LCNF fragments, and relates their interpreted outcomes to ownership models under explicit contracts. It also formalises the reference-count traffic of a temporary extraction pair and derives an exclusive restoration result from counted and child-call boundary conditions. A separate theorem establishes exclusivity of extraction and restoration targets in the abstract nested model. These results expose two distinct obligations: accounting for all counted ownership, and connecting that accounting to execution of the recognised fragment. The flat write has a composed model-level guarantee; composition of the counted nested protocol remains open. We delimit this boundary explicitly and provide structural rejection controls and pinned runtime evidence as supporting validation.

Once the preferred theorem is complete, rewrite the last four sentences around that theorem and its proof mechanism. Do not merely remove the sentence naming the open obligation.

## 4. Claim ledger at the inspected revision

Source paths below are relative to the repository root. “Proved” means the corresponding declaration exists at the inspected revision, with its stated hypotheses. This preparation pass inspected source; it did not perform a fresh Lean build or rerun the sibling-dependent runtime gates.

| Claim | Present evidence | Submission treatment |
| --- | --- | --- |
| Flat checker acceptance implies model write safety under its invariant | `Ownership/Soundness.lean`; `Ownership/Entry.lean` | Existing result. Explain what the invariant represents and what it does not establish about physical counts. |
| Recognised flat-prefix execution corresponds to the model | `OwnershipLcnf/Semantics.lean`; `recognized_write_in_place` | Existing conditional result for the designated prefix/write, not an arbitrary compiler theorem. |
| Extraction and restoration targets are exclusive in the abstract nested execution | `Ownership.Nested.ExtractionExclusive`; `checkN_extraction_exclusive`; `OwnershipTest/ExtractionExclusive.lean` | Existing recent progress. Combine its meaning with leaf-write soundness in the exposition. |
| The temporary pair's count traffic is neutral at the protocol boundary | `Ownership/CountedPair.lean` | Existing restricted protocol result; its release and persistence assumptions must remain visible. |
| Restoration takes the exclusive branch under the counted and child-call boundary facts | `Ownership/PutBack.lean`; `putBack_exclusive_of_wellFormed` | Existing derived result. The child count/persistence premises and execution boundary still matter. |
| A finite path has a model correspondence | `OwnershipLcnf/PathRecursion.lean`; `index_path_simulates_model` | Existing conditional result. N10 and the leaf contract do not verify the emitted recursive callee. |
| The initializer satisfies environment owner accounting | `Ownership/Accounting.lean`; `initCtx_accounted` | Existing fixed-initializer fact, not general accepted-execution preservation. |
| Current count fidelity accounts for every real owner and edge | `CountFidelity` definition | Not established. Arbitrary support lists and cursor-bounded enumeration lack the necessary validity conditions. |
| Accepted execution preserves complete accounting | Local accounting preservation lemmas | Open. `bindOwned` and `dec` require side conditions not established generally by the checker. |
| The counted nested protocol implements the recognised nested execution | `CountedPair`, `PutBack`, boundary lemmas, `NestedSemantics` | Open composition. The nested interpreter still erases relevant count traffic and uses an unconditional restoration update. |
| The principal theorem transports actual ownership accounting into a runtime guarantee | `OwnershipLcnf/Principal.lean`; `principal_write` | Too strong a reading. Its accounting hypotheses are unused; its conclusion combines results over models. |
| Linked runtime behaviour is proved for all supported inputs | Backend gate and probes | Not established. These are pinned observations and structural checks, not C-semantics verification. |

### Immediate manuscript corrections

- Qualify the introduction's “verified composition” wording: the counted nested composition is explicitly open elsewhere in the same manuscript.
- Present `principal_write` as the conjunction it currently proves. Remove unused accounting premises from the mathematical statement, or replace it with a result that actually consumes the strengthened relation. Adding premises does not extend the guarantee.
- Explain that `RuntimeModel` is another operational model. Its state correspondence does not itself bind physical C objects or addresses.
- Preserve the recent `ExtractionExclusive` progress. Do not continue reporting the old model-store coverage gap as wholly unresolved.
- Label empirical table entries as observed results or predictions. Every claimed measurement needs an actual command, mode, and captured outcome.
- Revisit the conclusion's “next step is a verified runtime model” wording: a runtime model already exists. The unresolved work is fidelity and composition at specified boundaries.

## 5. Proof work required for the preferred paper

Complete these gates in dependency order. The agent should report a theorem and its actual premises for each gate; a renamed definition or a new unconsumed hypothesis does not close one.

### Gate A — settle ownership accounting

Define a well-formed counted state for the supported fragment. It needs a duplicate-free, complete root support; a complete live-heap domain; valid incoming owning edges; and a distinction between owning obligations, borrowed pointers, and dead administrative names. State the single-threaded and nonpersistent restrictions wherever the equation relies on them.

The intended equation is conceptually:

```text
stored count = owning root obligations + incoming owning heap edges
```

If the language needs pending RC obligations, represent their creation, transfer, and consumption. The current `inc x n` raises the count without creating distinct owned variable names. Counting only names tagged `owned` will not automatically support preservation. Decide whether to model pending owned uses, make handle creation explicit, or restrict the counted language. Unconstrained ghost credits that merely equal the unexplained remainder are insufficient.

**Done when:** initialisation establishes the relation; count one yields the required absence of competing counted owners; duplicate support, omitted owners, and hidden out-of-range edges are excluded by checked validity conditions.

### Gate B — preserve accounting at intermediate states

Prove preservation through the operations the accepted fragment actually uses. Derive the `bindOwned` no-existing-owner and `dec` surviving-owner obligations from the strengthened state relation, strengthen the checker to enforce them, or expose a precise checkable certificate. Identify who supplies any additional certificate and demonstrate it on the captured fragment.

The proof must account for moves, borrows, increments/decrements, extraction, call entry/return, restoration, and replacement of the supported value kind. Do not expand scalar-only replacement to arbitrary reference-valued replacement without its edge-release obligations.

**Done when:** accepted execution preserves the relation at the states where stores occur. A final-state theorem alone cannot justify intermediate exclusive branches.

### Gate C — connect the counted protocol to execution

Use `CountedPair` and `PutBack` in a checked instruction-step or macro-step simulation of the recognised extraction/call/restoration sequence. Execute the temporary pair allocation, component projections/increments, pair release, child-call boundary, and restoration's copy/mutate alternatives. Derive selection of the exclusive branch from preserved state facts.

The relation to the abstract heap must tolerate temporary cells and allocator progress; freeing the pair does not necessarily restore the old cursor. Reuse existing boundary lemmas such as `protocol_cells` where applicable rather than requiring literal equality of every intermediate heap.

**Done when:** the main counted execution theorem depends on the protocol/restoration results, or on equivalent proved lemmas, and covers extraction, leaf replacement, and restoration within its stated scope. An unconditional `H.set` cannot serve as evidence that a modeled copy alternative is unreachable.

### Gate D — choose and state the call boundary

The preferred first paper can remain about finite supported paths. It need not verify arbitrary data-dependent recursion. However, it must not describe syntactic descent through a supplied finite model body as verification of emitted `setAt` recursion.

Choose one explicit boundary:

- Keep calls contractual. State the child-call relation in the main theorem, instantiate a useful leaf computation, and limit the claim to that conditional supported fragment.
- Capture and interpret the emitted callee with activation-local environments, actual path-field reprojection, and a return relation, then prove the recursive connection.

Choose the contractual boundary for the first submission unless the second is already tractable. The call contract must not assume exclusivity of the suspended parent if the paper claims to derive that preservation by confinement.

**Done when:** the title, abstract, example, theorem, artifact, and limits describe the same call boundary, with at least one nontrivial instantiation.

### Gate E — expose one principal theorem

The following is a specification, not an existing Lean declaration:

```text
Given:
  a recognised supported fragment and its operand/layout agreement;
  checker acceptance, plus any explicit checked certificate;
  an initially well-formed, completely accounted counted state;
  bounds, path/heap agreement, and stated primitive/call contracts;

prove:
  the counted execution simulates the abstract execution;
  accounting is preserved at each relevant boundary;
  each certified update selects its exclusive branch;
  the supported functional update and frame properties hold.
```

Quantify over supported indices and replacement values rather than proving only a constant fixture. If termination is contractual or outside scope, state a reached-store safety theorem or a conditional terminating-execution result; do not silently promise total execution.

For each main premise, say whether it is checked, derived, supplied by the caller, or trusted as a primitive contract. Show which proof step uses it. Retain explicit C/runtime fidelity assumptions; do not make physical pointer identity an implicit corollary.

**Done when:** a reviewer can follow an actual proof dependency path from recognition and acceptance to the counted-store conclusion. Mutating that path or violating a substantive premise has an explanatory negative control.

## 6. Paper rewrite: provisional 16-page budget

This budget follows the 2026 precedent pending the 2027 CFP. It includes the abstract and leaves one page of flexibility. References are outside the budget. Full theorem signatures belong in the supplementary theorem map if the no-appendix rule continues. [S2]

| Part | Pages | What the reader should learn |
| --- | ---: | --- |
| Abstract, motivation, contributions | 1.5 | The concrete copying failure, chosen boundary, and one central advance |
| Running example and execution model | 1.5 | A nested update, its temporary pair, and its counted obligations |
| Accounting invariant | 2.5 | Why the previous raw count invariant is insufficient; the repaired representation |
| Checker and preservation proof | 3.0 | The important rules, the hard preservation cases, and the soundness argument |
| Counted protocol and fragment correspondence | 3.0 | How temporary aliases disappear and restoration becomes exclusive |
| Case study and reproducible evidence | 1.0 | One general instantiation, informative negative cases, and artifact commands |
| Related work | 1.5 | The precise advance over the nearest ownership/RC analyses |
| Limits and conclusion | 1.0 | Contracts, excluded cases, and exactly what the theorem buys |
| Flexible space | 1.0 | Readability and the proof detail most needed by reviewers |

Replace the eight-step introduction and six-contribution inventory with a short argument and at most three contribution bullets. Use one running example through the invariant, checker, counted execution, and theorem. Put the important intermediate counts in a small table, with columns distinguishing root obligations from pair edges.

Show the proof's difficult cases in mathematical prose. A reader should understand why projection increments temporarily raise counts, why freeing the unique pair removes its edges, and why the suspended parent remains exclusive across the child call. Raw Lean signatures cannot replace those explanations.

### Author-led writing brief

Gavin should own the first-page argument, the novelty paragraph, the intuitive theorem explanation, and the limitations. The agent can assemble source-accurate statements, edit transitions, and maintain consistency. Rewriting every sentence manually is not a technical requirement; making the argument precise and readable is the goal.

For every major section, answer: what obstacle arose, why the obvious argument failed, what invariant or relation repaired it, and what remains assumed. Remove repeated assurance words such as “verified” where a more specific statement would help.

### Related-work task

Start with Marc Huisinga's 2023 thesis, which implements uniqueness analysis for a model of Lean IR and lists integration and soundness among future work. Compare the analyzed language, borrowing/escape treatment, proof status, count representation, and compiler connection. Do not claim to be the first static uniqueness analysis for Lean. [S4]

Then verify the relevant primary references already in the bibliography, including Counting Immutable Beans and Perceus. Explain their relationship to the counted protocol. Avoid a broad table that collapses type systems, program logics, compiler optimisations, and verified compilation into the same category. Every comparison needs a specific supported difference. Check the pinned Lean source for runtime claims rather than relying solely on moving API documentation.

## 7. Artifact preparation

Prepare two independently described layers: the self-contained Lean development, and the sibling-dependent compiler/runtime reproduction. A reviewer should be able to check the theorems even before running the latter.

### Required contents

- `README` with the paper's claim, supported fragment, prerequisites, commands, expected results, and approximate resource requirements measured on a named machine.
- Exact ownership commit, Lean toolchain, Nix inputs/lock, and sibling revision. The inspected toolchain is `leanprover/lean4:v4.35.0-rc3`. The currently documented sibling pin is `66e64334a1c968d829903b8aec8d22f7e3b9fd3f`; verify it again for the final artifact.
- A claim-to-declaration map: paper theorem, source declaration, full assumptions, and command checking it. Include the extraction/restoration theorem as well as leaf-write soundness.
- A compact trust ledger separating kernel-checked results, primitive/call contracts, representation/backend assumptions, and measurements.
- Fixtures for the changed leaf, restored slot, untouched sibling, and client/outside-footprint preservation. Include a nonzero index and a meaningful nested instance.
- Negative controls for retained ownership, persistence, omitted release, malformed recognition, invalid support/domain accounting, and invalid call/frame behaviour where supported. Keep a corresponding positive control.
- Runtime observations with exact probe mode, expected success/copy/abort, actual exit status, diagnostic or output, and toolchain pin. Do not describe hardcoded expected booleans as an executable model differential oracle.
- A clean archive prepared under the actual anonymity rules. Do not weaken citations or erase attribution in the public development to make the archive anonymous.

### Baseline check commands

These are the repository's documented commands, not claims that they were freshly run for this preparation:

```bash
nix develop -c lake build Ownership
nix develop -c lake build OwnershipTest
nix develop -c lake build OwnershipLcnf
nix develop -c lake env lean scripts/check_axioms.lean
nix develop -c bash scripts/check_artifacts.sh
nix develop -c bash scripts/check_runtime_binding.sh
```

The last two need the correctly pinned clean sibling checkout. Record its provisioning instructions from scratch. Verify the theorem checks separately from the backend checks, so failures are diagnosable.

The axiom audit should include every new headline theorem. Preserve the no-`sorry`/no-new-axiom discipline and report the actual axiom output. Arrange one clean-machine reproduction by someone who has not been maintaining the development.

The abort gate has already been strengthened to require the expected status and an exclusivity diagnostic. Preserve that distinction. Check the remaining `sealedCase` mismatch exit-code inconsistency when cleaning the probe, but do not prioritise it above proof composition.

## 8. AI use and authorship

Dagstuhl's current policy permits reviewed AI assistance, keeps responsibility with human authors, and requires disclosure beyond minor assisted proofreading. It asks for the purpose of use and the extent of human review; tool/version details are optional. Recheck both publisher and conference policy before submission. [S3]

Maintain a factual provenance note now: which tools assisted prose, proof/code development, or analysis; what they produced; and how the authors checked those outputs. Keep kernel checking distinct from human validation that the theorem states the intended result. Do not claim that a human manually checked every proof step unless that actually occurred.

Write the final disclosure from that record. Manual paraphrasing does not erase substantive AI involvement. There is no need to optimise the manuscript for an AI detector; optimise the mathematical argument, evidence, and author accountability.

## 9. Internal milestones and scope decisions

These dates are proposed internal targets, not ITP deadlines or estimates of proof effort. If a gate proves harder than expected, reduce scope deliberately and update the plan. An earlier official deadline would take precedence.

| Internal date | Deliverable | Decision enabled |
| --- | --- | --- |
| 9 November 2026 | Corrected claim ledger; chosen call boundary; one-page accounting design with `inc` interpretation | Can the proposed theorem be stated without circular assumptions? |
| 23 November | Initialisation and key accounting preservation results, or explicit counterexamples to the design | Continue this representation or revise it before writing around it |
| 7 December | Counted extraction/restoration macro-step and a representative instantiation | Is the preferred composition on a credible path? |
| 21 December | First complete readable manuscript; theorem map with every open item marked | Freeze the actual contribution and choose submission category/scope |
| 11 January 2027 | Clean artifact reproduction and revised manuscript | Remove evidence gaps and unsupported claims |
| 25 January | Independent adversarial reading and response-to-reviewer exercise | Submission-ready internal candidate, subject to the real CFP |

At the 21 December decision:

- **Preferred regular paper:** complete the accounting/preservation/counting connection for the stated fragment, with an informative mechanised case study.
- **Narrower regular paper:** possible if the strongest completed result has a clear standalone contribution. Rewrite around that result; do not imply that all originally planned gates were completed. Its merit needs a fresh novelty assessment.
- **Short-paper fallback:** consider only if the 2027 call offers it and the completed work fits its scope. Present ongoing work honestly. Shorter length is not a substitute for a sound theorem.

## 10. First task for the implementation agent

Start with Gate A and the immediate manuscript corrections. Do not expand the recogniser corpus, generalise to arbitrary recursion, or add more headline theorem wrappers before settling the accounting representation.

Return a reviewable change with:

1. The proposed `ValidCountedState` relation, including finite support/domain conditions and the operational meaning of increments.
2. An initializer theorem and at least the difficult preservation cases for the chosen supported language, or a precise report of the obstruction and a minimal counterexample.
3. A theorem signature for the counted protocol simulation, with every call/primitive premise identified and no assumed final in-place conclusion.
4. An updated claim ledger and paper wording that matches the completed proofs.
5. The exact revision and meaningful build/axiom results; distinguish checks actually run from checks still pending.

Keep implementation changes and paper-claim changes reviewable together. A closed gate is demonstrated by the proof dependency and its instantiation, not by prose saying that it is closed.

## 11. Final readiness questions

- Can an ITP reviewer explain the new proof insight after reading two pages?
- Does complete accounting give a substantive interpretation to count one, rather than define exclusivity by that integer alone?
- Does the proof consume the counted protocol at the execution boundary it claims to certify?
- Are all updates in the claimed scope covered, including extraction and restoration?
- Is finite contractual recursion clearly distinguished from the emitted callee?
- Does the abstract promise exactly what the main theorem establishes?
- Are all empirical claims reproducible and distinguished from theorem claims?
- Can a clean checkout check the proof and reproduce the supporting observations from documented pins?
- Has the author verified the novelty comparisons, references, AI disclosure, and actual 2027 rules?

## Sources and baseline links

- **[S1]** [Official ITP 2027 site](https://itp-conference-2027.github.io/), checked 2 November 2026. Location confirmed; dates internally inconsistent/provisional; no submission call visible.
- **[S2]** [Official ITP 2026 CFP](https://itp-conference-2026.github.io/cfp.html), checked 2 November 2026. Historical formatting/category precedent only.
- **[S3]** [Dagstuhl statement on GenAI](https://drops.dagstuhl.de/docs/gen-ai), checked 2 November 2026. Recheck for the submission's applicable policy.
- **[S4]** [Marc Huisinga, Static Uniqueness Analysis for the Lean 4 Theorem Prover, 2023](https://pp.ipd.kit.edu/uploads/publikationen/huisinga23masterarbeit.pdf), especially implementation and future-work sections.
- [Inspected ownership revision](https://github.com/scidonia/ownership/tree/61a01439f4b313fb51f7240097b29cdff53131fb).
- [Accounting definitions and local lemmas](https://github.com/scidonia/ownership/blob/61a01439f4b313fb51f7240097b29cdff53131fb/Ownership/Accounting.lean).
- [Current flat principal theorem](https://github.com/scidonia/ownership/blob/61a01439f4b313fb51f7240097b29cdff53131fb/OwnershipLcnf/Principal.lean).
- [Nested execution semantics and N-contracts](https://github.com/scidonia/ownership/blob/61a01439f4b313fb51f7240097b29cdff53131fb/OwnershipLcnf/NestedSemantics.lean).
- [Existing technical gap programme](https://github.com/scidonia/ownership/blob/61a01439f4b313fb51f7240097b29cdff53131fb/docs/notes/ownership-core-technical-gaps.md). Its extraction/restoration coverage discussion predates the newest exclusivity theorem; use the updated ledger above.

