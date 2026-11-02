# Ownership paper: revision map for an ITP submission

Date: 2 November 2026  
Author: Gavin Mendel-Gleason  
Audience: implementation, proof, and manuscript agent  
Inspected revision: `48a1ac016a8f0322067793f92541c752a823b857`  
Manuscript: `paper/ownership-skeleton.tex` and its accompanying PDF  
Purpose: produce both a substantive mechanisation paper and a recognisably professional ITP manuscript.

## 1. Editorial decision

Build the paper around **complete ownership accounting and a compositional proof of a counted array-update protocol**. The compiler-fragment connection demonstrates why the formalisation matters. The paper's unit of explanation should be a mathematical problem and its solution, not a repository declaration.

Keep the current title, **Mechanising Count-One Ownership for Array Updates in Lean 4**, unless the final theorem justifies something more specific. Do not broaden the title to suggest certified Lean compilation, arbitrary runtime recursion, or physical no-copy guarantees.

The work is no longer at the earlier stage where complete accounting and accepted-execution preservation were wholly missing. Preserve those completed results. The remaining technical priority is to connect the whole counted recognised fragment, through restoration and return, under the existing explicit child-call contract. This is a narrower task than verifying the emitted callee or C runtime.

This map sets an editorial and technical target. It does not guarantee acceptance, and its proposed new theorems are not existing results. The present pass inspected the source and manuscript; it did not freshly rerun the Lean build or backend gates.

### Definition of the desired result

A reader should leave able to explain:

1. Why a usage tag and an integer multiplicity alone do not account for ownership.
2. How a complete roots-and-edges relation gives that integer a meaning.
3. How temporary pair edges and projected handles are introduced and discharged.
4. What execution correspondence is proved, what the child-call contract supplies, and where the implementation trust boundary lies.

These explanations are the content that must earn the page space. Formatting should make them accessible.

## 2. Submission format: establish the real constraint first

The official ITP 2027 site currently has no submission CFP or deadline. Use the 2026 call as a **provisional planning precedent**, not a confirmed 2027 requirement: regular papers were at most 16 pages excluding references, in LIPIcs, without appendices, with lightweight double-blind review and anonymised verifiable supplementary material. Recheck the actual 2027 rules before submission. [V1, V2]

Move to the official LIPIcs class before editing to a page budget. The present PDF's 16 pages in an 11-point `article` class do not establish compliance. The publisher currently provides `lipics-v2021`, version 2021.1.3, with an example and author instructions. Use that supplied template and its bibliography/metadata conventions. [V3]

Do not infer a submission page allowance from the lengths of published proceedings papers; use the applicable CFP.

## 3. Priority map

The priorities below are recommendations for this manuscript, not additional conference rules.

| ID | Priority | Change | Evidence that it is complete |
| --- | --- | --- | --- |
| T1 | Main technical priority | Finish correspondence for the full counted recognised fragment under the explicit child-call contract | A theorem about execution of the entire fragment, through restoration and return, instantiated on the captured shape |
| T2 | Claim accuracy | Separate ordinary finite-path `ChildContract` derivation from the stronger supplied `CountedChildCall` | The theorem, abstract, example, and source comments name the same remaining obligation |
| T3 | Demonstration | Turn the closed example into a readable case study and, where feasible, a small parameterised family | Exact before/after state, accounting, and disposition facts, with the call contract discharged for that family |
| W1 | Manuscript essential | Write a short problem-led introduction and abstract | A reader understands the problem and contribution before encountering implementation identifiers |
| W2 | Manuscript essential | Present the main results as mathematical theorems with proof sketches | Definitions precede use; assumptions and conclusions are visible without opening Lean |
| W3 | Manuscript essential | Replace audit inventories with a proof narrative | Each retained declaration, table, and limitation explains a specific part of the argument |
| F1 | Format essential | Adopt LIPIcs and rebuild the page budget | Clean PDF using the supplied class and ordinary class typography |
| E1 | Evidence essential | Reproduce the final proof/artifact revision and report exact scope | Recorded commands, pins, axiom output, and a claim-to-artifact map |

If T1 cannot be completed in the available cycle, stop promising a whole counted-fragment guarantee. A paper about the completed accounting and boundary-protocol results remains a possible narrower submission, but needs its own novelty assessment. Do not disguise the missing execution connection with a larger conjunction.

## 4. Technical revision T1: make the counted execution the central connection

### Current state

`OwnershipLcnf/Principal.lean` composes useful results at the same entry:

- An abstract recognised execution corresponding to the finite path model.
- `counted_nested_chain`, connecting counted extraction/call/restoration boundaries and final accounting to the abstract run.
- `execCounted_protocol_boundary`, connecting the counted interpreter to the recognised prefix through pair release.

The last result covers the first nineteen operations. It does not prove execution correspondence for the whole `p.fragment`, including restoration and return. The paper explicitly acknowledges this. Completing it would turn the central account into a theorem about one counted execution rather than an assembly of related views.

### Requested implementation

1. Prove a structural decomposition of the recogniser's fragment into the protocol prefix and remaining suffix. Reuse the existing boundary theorem. The split should be justified by the recognised shape, rather than left as an unexplained numeric cutoff in the paper.
2. Continue `execCounted` from the post-release state through the remaining child-check, call, restoration, and return operations.
3. Consume the supplied `CountedChildCall` at the actual counted call-entry state. Derive restoration's mutate branch at the actual call-output state. Do not assume the final mutate disposition.
4. Relate the resulting counted heap to the abstract heap by `HeapCompat`. Preserve the cursor slack caused by allocation and release of the temporary pair; do not assert literal heap equality when the cursors differ.
5. State the result over the entire recognised trace. If a code-level wrapper is added, make successful recognition load-bearing in that wrapper/theorem, as it is for `execNestedAST`.
6. Instantiate the theorem using the existing reified declaration and a leaf that changes a scalar slot. Retain a control in which a retained parent prevents exclusive restoration.

Use a macro-step simulation at the temporary-pair window. `Accounted` and `HeapCompat` need not hold at every instruction while the pair is live. Their restoration at the boundary, together with proved internal count effects, is the argument to explain. Do not redesign all semantics merely to force a uniform invariant across that window.

### Intended theorem, stated schematically

This is a specification of the desired result, not a Lean declaration to paste into the paper:

```text
Recognition, operand/layout agreement, a well-formed accounted entry,
the supported path/slot facts, and the explicit counted child-call contract
imply:

  the full counted recognised fragment completes with the specified root result;
  its post-state corresponds to the abstract model's post-state;
  the counted protocol's final boundary satisfies complete accounting;
  the local extraction/restoration targets satisfy their exclusive-update facts;
  restoration selects mutate and restores the specified child slot;
  the child computation satisfies exactly the properties in its call contract.
```

Quantify indices and values to the extent supported by the semantics. If the claim is safety conditional on reaching a store, say that instead of adding an unsupported termination claim. Do not silently include every child store in a stronger counted guarantee than the child contract supplies.

**Completion test:** the proof talks about the final result of `execCounted` on the full fragment. Its dependency chain uses the counted protocol and the actual call-output/restoration state. An abstract completed run plus a counted prefix run is not the requested theorem.

## 5. Technical revision T2: distinguish the two call contracts

`OwnershipLcnf/PathRecursion.lean` derives `ChildContract` along finite model paths. `Ownership.CountedChildCall` additionally includes:

```lean
accounted : Accounted support Hout env ctx
```

That post-call accounting fact is supplied to the current nested principal theorem. In the closed instance it is established by `calledAccounted`. The existing ordinary path induction does not itself construct the stronger counted contract.

Required corrections:

- State that ordinary finite-path call properties are derived, while the stronger counted return accounting remains an explicit premise of the counted theorem.
- Correct the comment preceding `CountedChildCall` that says the added field is discharged by the same finite-path induction. It currently reads as a completed connection that the referenced module does not establish.
- Avoid unqualified phrases such as “only the leaf and N10 remain” when discussing a theorem that separately takes the stronger counted postcondition.
- Keep the emitted recursive callee outside the theorem unless it is actually captured and interpreted with activation-local environments and path reprojection.

There are two defensible endpoints:

1. **Recommended first-paper scope:** a complete local counted-fragment theorem under the stronger explicit call contract, with that contract discharged for a useful example/family.
2. **Broader finite-path result:** prove an induction that constructs `CountedChildCall` or an equivalent counted preservation result at each level. This is additional work; it is not obtained by renaming `ChildContract`.

A contractual child call is a legitimate modular boundary. The paper must explain what the contract requires and demonstrate that a useful child computation meets it.

## 6. Technical revision T3: turn the instance into evidence the reader can inspect

The existing closed instance has a real changed leaf and supplies all premises. Keep that achievement, but stop presenting it primarily as “a 25-conjunct existential”.

Present a small nested array before the update and after it. Show the selected outer slot, the child slot being changed, an untouched sibling, the temporary pair, and the restored reference. State which equality is functional correctness, which property is count accounting, and which fact selects the in-place branch.

Prefer a small parameterised family over several unrelated constant examples. Suitable parameters are array lengths, an in-bounds outer index, a supported child index, and scalar replacement values. Prove the counted child-call contract for the family. Do not imply support for arbitrary deeper per-invocation indices that the current flat environment cannot express.

Use a compact table:

| Scenario | Obligation varied | Expected result to establish |
| --- | --- | --- |
| Unique nested update | All stated premises hold | Changed leaf, restored slot, exclusive restoration, accounted final boundary |
| Retained parent | Parent has an additional counted owner | Copy disposition or exclusion from the certified case |
| Pair not released | Temporary pair edges survive | Component counts stay elevated; exclusivity fails |
| Invalid owner support | Duplicate or omitted owner | Complete accounting is refused |
| Persistent object | Nonpersistence condition fails | Outside the certified fragment; separate runtime behaviour if measured |

Keep formal counterexamples separate from linked runtime observations. “Refused by the relation”, “rejected by the checker”, and “copies in the executable” are different outcomes.

No new benchmark campaign is required merely to make this a mechanisation paper. If runtime performance becomes a contribution, measure it properly; otherwise report reproduction cost and supporting observations without claiming speedups.

## 7. Replace the contribution list

The existing list contains many declaration names. Replace it with three substantive statements, revised to match the final proof status:

1. **A complete accounting relation for counted ownership.** Explain the roots-and-edges equation, finite support/domain requirements, and the uniqueness consequence. Explain why the weaker raw invariant admits an ownership mismatch.
2. **Preservation and temporary-alias accounting.** Prove preservation for the precisely restricted flat fragment and justify the temporary-pair protocol at its boundaries. Explain the distinct proof techniques and restrictions.
3. **A checked connection to a recognised compiler fragment.** State the exact execution correspondence, explicit call boundary, and nontrivial instantiation. Describe full counted-fragment correspondence only after T1 is complete.

Name the key declaration once, beside the relevant theorem or in a footnote/artifact link. There is no need to rename established Lean declarations to achieve this.

## 8. Section-by-section replacement map

The locations below refer to section titles at the inspected revision, not unstable line ranges.

| Current location | Action | Replacement and completion criterion |
| --- | --- | --- |
| Title and italic disclaimer above abstract | Keep the restrained title; remove the disclaimer from the opening | Put the notation/source-excerpt convention near the first Lean listing or in the artifact note |
| Abstract | Rewrite completely | Problem, approach, strongest completed result, proof insight, scope, evidence; no `hacc`, `hcall`, or catalogue of predicates |
| Introduction | Rebuild around the running problem | Explain observable array copying, why naive ownership counting fails, the repair, the proof challenge, and the exact contribution |
| “Three contributions” | Replace declaration inventory | Use the three content statements above; no multi-line list of theorem identifiers |
| “Setting and the running example” | Move the example earlier and simplify | Show source-style pseudocode and a heap picture before introducing both complete syntax datatypes |
| “Model programs” | Shorten and distinguish languages | Give the grammar needed by the proof. Clearly distinguish the general checker language from its accounted `Supported` subset |
| “The accounting invariant” | Keep as the mathematical foundation | State a definition, prove/explain the count-one consequence, then motivate the representation fields with counterexamples |
| “The judgement and its rules” | Compress the prose and reduce the rule table | Define the judgement once. Show the important rules as inference rules; move the exhaustive operational rule inventory to supplementary documentation |
| “Preservation through the supported fragment” | Add the actual proof sketch | Explain induction on supported syntax and the hard flat cases: fresh binding, decrement, and edge-neutral scalar store |
| “Three hard cases” under preservation | Move and rewrite | Its current pair projection/free/call argument belongs in the counted-protocol section. It is not a proof sketch for the flat `supported_run` theorem |
| “Counted protocol and fragment correspondence” | Split into focused sections | First explain counted boundary simulation and restoration; then connect the recognised full fragment, using T1 if complete |
| “The runtime model” | Condense or demote | Explain its purpose and distinct state representation; keep only the detail needed for a stated result, without treating a second model as C verification |
| “The composed guarantee” | Replace the abbreviated four-group presentation | Give a self-contained mathematical theorem with defined assumptions and a short proof decomposition; put the full Lean type in the supplement |
| “The instance and its controls” | Replace tuple inventory with the worked case | Show concrete before/after behaviour and how the call contract is met |
| “Evidence” | Keep compact, regenerate at final revision | Separate proof checks, recogniser controls, and runtime observations; every observation has a mode, pin, and actual outcome |
| “Theorem map” | Move to supplementary artifact documentation | Retain at most a small paper-to-code mapping if useful; no page of declaration names in place of explanation |
| “Related work” | Rewrite as specific comparisons | Identify the closest predecessor, exact difference, and significance; avoid category labels masquerading as comparisons |
| “Limits and conclusion” | Split and shorten | One compact scope/trust discussion, then a conclusion stating the completed scientific result |
| “AI assistance” | Replace process commentary with a factual disclosure | Describe actual assistance and author verification; keep provenance limitations honest and move submission-policy reminders into project notes |

## 9. Target outline and page budget

Use the following as a planning budget in actual LIPIcs output, subject to the 2027 CFP. Aim for 15.5 pages including front matter and acknowledgements, leaving half a page of flexibility before a provisional 16-page ceiling. References are additional under the 2026 precedent. [V2]

| Section | Pages | Required content |
| --- | ---: | --- |
| Abstract and introduction | 1.75 | Concrete failure mode, contribution, strongest theorem in words, scope |
| Running example and semantic setting | 1.50 | Supported operations, heaps, entry facts, example |
| Complete ownership accounting | 2.00 | Count equation, support/domain validity, uniqueness consequence, countermodel |
| Checker and flat preservation | 2.25 | Judgement, supported restrictions, preservation theorem and proof sketch |
| Counted protocol and boundary simulation | 2.50 | Pair traffic, call boundary, restoration, compatibility relation |
| Recognised-fragment correspondence | 2.00 | Recognition, counted execution connection, main theorem, trust boundary |
| Case study, mechanisation, and artifact | 1.50 | Contract discharge, controls, engineering lessons, reproducibility |
| Related work | 1.00 | Closest comparisons and exact novelty |
| Limitations, conclusion, disclosure | 1.00 | Concise residual boundary and factual assistance statement |
| **Planned total** | **15.50** | **0.50 page flexibility; remeasure after every structural revision** |

If space runs short, cut inventories, repeated restrictions, and broad background first. Do not shrink fonts, hide assumptions, or remove the proof argument.

## 10. The first two pages

### Abstract recipe

Aim for roughly 150–190 words as an editorial target, not a venue requirement. Use five or six sentences:

1. The concrete problem: reference-counted array updates may copy because ownership traffic is difficult to track.
2. The approach: a mechanised count-aware discipline for a specified fragment.
3. The accounting result: roots and incoming edges, with preservation under stated restrictions.
4. The protocol/correspondence result: temporary aliases, restoration, and the exact completed compiler-fragment boundary.
5. The insight: boundary simulation handles temporary count traffic without pretending the simple invariant holds inside the pair-live phase.
6. The scope/evidence: an explicit child-call contract and a checked instantiation; C-runtime fidelity remains outside the proof.

No raw hypothesis names. Do not repeat the full limitations list. Do not imply absence of allocation: the protocol allocates a temporary pair even when the certified array update does not copy the array.

### Introduction sequence

**Paragraph 1: problem.** Start with a small array update and the practical difference between mutation and copying. Identify the guarantee sought.

**Paragraph 2: obstruction.** A local owning name is insufficient when heap edges and temporary handles also contribute to the count. Use the temporary-pair example, not a declaration list.

**Paragraph 3: proof idea.** State the accounting equation and explain why the protocol needs boundary reasoning. Describe the child-call boundary in ordinary language.

**Paragraph 4: result and novelty.** Name the strongest completed theorem in words and compare the exact advance over the closest existing analysis. Do not claim first static uniqueness analysis for Lean.

**End: contributions and organisation.** Three short contribution bullets and, if useful, a short section roadmap.

The first two pages should let a programming-languages reader unfamiliar with the repository answer: what is certified, what is assumed, why the proof is difficult, and what is new.

## 11. Mathematical presentation and proof explanations

### Establish compact notation

Use a short notation table for heap, environment, checker context, owner support, and the counted/abstract state relation. In prose, distinguish:

- **Checker acceptance** in the general object language.
- **Supported certification**, which includes extra restrictions/certificates.
- **State validity/accounting**, which is not produced solely by the checker.
- **Child-call specification**, which supplies properties across a modular boundary.

Do not suggest `check c s = some c'` alone gives complete accounting preservation. The result additionally needs the supported fragment, initial accounting, and store-slot fact. Explain why `Supported` excludes general increments and restricts decrements, while the separate protocol models selected emitted increments explicitly.

### Present definitions as definitions

The current “Claim 1” is an invariant definition, and “Claim 2” is a structure definition. Use Definition, Lemma, Theorem, Example, and Proof environments according to their role. Use the class's ordinary theorem styling.

The main theorem must not have `∃ …, … -- four groups below` as its only formal content. Define short named assumptions and a meaningful outcome relation, then state the result without hidden essential premises. A structured result record may improve the Lean API, but the paper still needs to explain every component it presents.

### Supply three distinct proof sketches

1. **Flat preservation:** induction on supported syntax; a move transfers an owner rather than adding one; freshness prevents losing an existing owning obligation; a single decrement removes one corresponding root obligation; a scalar-for-scalar store leaves incoming reference edges unchanged.
2. **Counted protocol:** transfer into the temporary pair; projection increments; release removes the pair edges; confinement protects the suspended parent; post-call accounting supports restoration; compatibility tolerates the advanced allocation cursor.
3. **Execution correspondence:** recognition fixes operand identities and operation order; the counted prefix matches the protocol boundary; the suffix consumes the call specification and restoration result; the final state relates to the abstract execution.

Explain the relevant induction measure or decomposition. “The theorem follows from named lemmas” is insufficient when those lemmas contain the paper's insight.

### Show the useful uniqueness corollary

For an accounted state with a known owning root at reference `r`, multiplicity one and the count equation force one owning root and no incoming owning edge. Present that derived consequence after the general count-one dichotomy. Do not identify it with a claim about physical pointers unless a representation theorem is supplied.

## 12. Visual and typesetting changes

### Adopt the actual proceedings template

- Replace `article`, manual `geometry`, hand-set body fonts, and custom theorem styling with the official LIPIcs example as the starting point.
- Follow the publisher's current compiler/package guidance; the current instructions specify pdfLaTeX. Remove the `fontspec`/custom-font dependency rather than carrying an incompatible preamble forward. [V3]
- Use the template's metadata and bibliography conventions, including `plainurl`. Fill real author metadata in the author version and apply the required anonymous mode for submission if the 2027 rules require it. Do not invent proceedings identifiers, article numbers, or a DOI.
- Keep one canonical manuscript source and one documented build command. If renaming `ownership-skeleton.tex`, update the build instructions and references rather than maintaining divergent paper copies.
- Prefer a small, reproducible listing setup over a shell-escape dependency when feasible. Preserve Lean syntax and readable mathematical symbols; handle Unicode explicitly rather than letting glyphs disappear.

These are implementation directions for the revision agent, not a request to change the manuscript in this handoff.

### Figure 1: ownership traffic

Draw the example as a vector figure with labelled parent, child, temporary pair, and owning roots. Use three panels: entry; projected handles while the pair is live; pair released and child ready for the call. Label the root/edge contributions and counts. Mark the pair-live panel as outside the boundary invariant.

Add a restoration panel only if it remains legible. Clearly distinguish array mutation from temporary allocation. Reuse the same reference names and indices in the theorem explanation and case study.

### Figure 2: simulation boundaries

Draw counted and abstract execution rows. Connect them at entry, after pair release, and after restoration where the relation is actually proved. In a current-status diagram, show the missing full-fragment connection honestly; in the final paper, draw only edges supported by the final theorems. Do not draw a vertical invariant edge at every pair-live instruction.

Generate exact diagrams in TikZ/SVG/PDF or equivalent deterministic vector tools, not image generation. Any conceptual diagram in development notes must be redrawn consistently for the paper.

### Tables and listings

- Keep the protocol count table, but define explicitly that each root/edge pair is ordered parent/child. Separate the boundary assertions from the per-stage count calculations.
- Replace the large checker-rule table with selected inference rules or two smaller tables aligned with the two fragments.
- Remove the multi-row theorem-name census from the main text.
- Use at most a few purposeful source listings: a motivating update, the invariant's essential shape, and a small executable/certificate excerpt if it helps. A long theorem signature belongs in the artifact.
- Keep captions self-contained. Avoid `scriptsize` tables as the solution to an overfull layout.

### PDF inspection

Render the final PDF and inspect every page at normal reading size. Require legible table cells, no clipped rules/listings, no missing glyphs, no overfull lines, no unresolved citations, and no stranded headings. Check that the first page resembles the official template, not a custom title sheet. Judge page density in the final class, not the old article layout.

## 13. Repair specific claim inconsistencies

| Current wording/problem | Required replacement |
| --- | --- |
| “The composed statements do not transport accounting” | Restrict that observation to the flat theorem where appropriate. The nested theorem does conclude final counted-boundary accounting; transport to physical runtime objects is unproved |
| “The child contract is derived at every level” without qualification | Specify ordinary `ChildContract`; state the separate counted post-call accounting obligation |
| Pair-live state treated as an accounting failure | Explain intentional boundary abstraction and its internal count argument, rather than suggesting the whole protocol is unaccounted |
| Omitted extraction/restoration trace events listed like an absent safety theorem | Explain the separate target-exclusivity predicate; distinguish event representation from missing full counted-execution correspondence |
| “The checker guarantees …” used for the stronger preservation result | Name the additional supported certification, entry relation, and store-slot premise |
| “In place” suggesting no allocations | State that the certified array operation does not copy under the modeled contracts; the temporary pair still allocates |
| A second runtime model described as the physical implementation | State the relation between formal models and the residual runtime/backend fidelity assumptions |
| Relative observation age such as “two commits behind” | Give the exact revision and check date; relative ages become false as the repository changes |

Use one compact trust table to distinguish checked syntax, proved model facts, supplied client/call facts, and implementation assumptions. Avoid enumerating A1–A12/N1–N12 repeatedly before their meanings are explained.

## 14. Related work and the ITP-specific contribution

Lead with the closest predecessor, Huisinga's static uniqueness analysis for a Lean IR model. Compare analyzed language, ownership/count representation, proof status, and compiler connection. The difference must be supported and significant; “ours is kernel-checked” is not a complete explanation of the advance.

Verify the primary sources for Perceus and Counting Immutable Beans and explain whether each comparison concerns a count-insertion transformation, reuse optimization, semantic correctness, or static uniqueness guarantee. Do not collapse all those properties into “ownership pass correctness”.

Explain what formalisation taught:

- Which tempting invariant was too weak, and what exact countermodel exposed it?
- Why are complete owner support and live-domain coverage necessary?
- Why can the simple accounted relation fail inside a correct temporary-alias protocol?
- What does boundary simulation recover, and why does allocator progress prevent plain equality?
- Which restrictions follow from the chosen representation, and which are merely unimplemented features?

Answering those questions makes the paper useful to someone building another mechanised analysis. An internal countermodel alone is not a research contribution; its general lesson and the repaired construction are what matter.

Two accepted ITP papers offer useful presentation references, not templates to imitate mechanically: *Verifying Datalog Reasoning with Lean* develops semantic definitions, theorem statements, proof arguments, and evaluation; *A Mechanized First-Order Theory of Algebraic Data Types with Pattern Matching* foregrounds a concrete verification gap, correctness results, and broader lessons. Study their exposition and theorem presentation, not their final page counts or scientific claims. [P1, P2]

## 15. Artifact, verification, and disclosure

For the final revision, supply a compact reproducibility section and a separate detailed artifact README. Record the ownership and sibling commits, toolchain/lock files, commands, expected results, and which checks need the sibling repository.

Use the repository's existing checks, expanded to cover new headline theorems:

```bash
nix develop -c lake build Ownership
nix develop -c lake build OwnershipTest
nix develop -c lake build OwnershipLcnf
nix develop -c lake env lean scripts/check_axioms.lean
nix develop -c bash scripts/check_artifacts.sh
nix develop -c bash scripts/check_runtime_binding.sh
```

Do not report these as freshly run until they have actually succeeded at the recorded revision. Keep proof checks, structural recogniser controls, and linked runtime probes in separate result categories. A declaration-name census is useful housekeeping, not validation of theorem meaning.

Disclose AI assistance accurately under the applicable policy. Do not manufacture missing historical model/version records or an unperformed human review. Replace the manuscript's submission-policy reminders with a short factual account of assistance, verification, and author responsibility; preserve material provenance limitations. Recheck publisher/conference policy at submission. [V4]

Gavin should personally review the definitions, main theorem statements, interpretation of the evidence, novelty claims, and citations. Kernel checking does not establish that a theorem answers the intended research question. Line-by-line manual checking of generated proof terms is not the task to substitute for that review.

## 16. Ordered implementation plan

Make changes in reviewable units. The following are suggested change groups, not instructions to publish or push anything.

1. **Freeze the claim and repair contract wording.** Correct T2 and the inconsistencies in Section 13. Write the intended main theorem in mathematical prose and identify each premise's provider.
2. **Convert to LIPIcs.** Keep this largely a formatting/build change. Establish the actual page footprint before attempting compression.
3. **Complete the counted-fragment bridge.** Implement T1, reuse the existing boundary/protocol results, adapt the principal theorem and positive/negative instances, and audit the new theorem's axioms.
4. **Strengthen the case study.** Implement the most useful supported parameterisation for T3, or clearly retain a constant example with its limited role. Do not expand into arbitrary recursion as a prerequisite.
5. **Rewrite the scientific narrative.** Apply the section map, add proof sketches and exact figures, replace theorem inventories, and write the abstract last.
6. **Reproduce and inspect.** Run the final proof/artifact checks, inspect every PDF page, reconcile every claim surface, and obtain a fresh reader's assessment.

For each group, return the changed files, the exact resulting claims, checks actually run, and any remaining gap. If T1 fails because an assumption is insufficient, provide the minimal obstruction; do not make the desired conclusion a new premise and call it completion.

## 17. Final acceptance checklist for the revision agent

### Technical content

- [ ] The strongest claim has a theorem about the execution boundary advertised in the abstract.
- [ ] A whole counted-fragment claim is backed by T1; otherwise the paper explicitly remains a boundary-protocol paper.
- [ ] Ordinary and counted child contracts are distinguished, with a nontrivial contract discharge shown.
- [ ] Complete accounting is meaningful independently of raw multiplicity, and its preservation restrictions are explicit.
- [ ] Extraction/restoration and leaf-write guarantees are scoped accurately.
- [ ] The main result does not imply physical pointer identity, zero allocation, or arbitrary Lean-source verification.

### Scientific exposition

- [ ] The first two pages explain the problem, insight, result, and novelty without a declaration catalogue.
- [ ] Mathematical theorem statements expose assumptions and outcomes without essential ellipses.
- [ ] Flat preservation, counted protocol, and correspondence each have the correct proof sketch beside them.
- [ ] The running example is reused consistently through the proof and evaluation.
- [ ] The reader can identify at least one reusable mechanisation insight beyond the specific fixture.
- [ ] Related-work comparisons and empirical claims have been checked against primary evidence.

### Appearance and delivery

- [ ] The paper builds in the supplied proceedings style with ordinary typography and a compliant page budget.
- [ ] Definitions, theorems, proof sketches, and examples use conventional environments.
- [ ] Vector figures and tables are legible at normal size; the PDF has no clipped content or unresolved references.
- [ ] Full theorem types and the exhaustive declaration map are in supplementary documentation, not substituted for the paper's argument.
- [ ] Final revision pins, checks, anonymity requirements, AI disclosure, and actual 2027 rules have been reconciled.

## Sources and stable baseline references

Venue and publisher sources checked 2 November 2026:

- **[V1]** [Official ITP 2027 site](https://itp-conference-2027.github.io/).
- **[V2]** [Official ITP 2026 CFP](https://itp-conference-2026.github.io/cfp.html): historical formatting and submission precedent only.
- **[V3]** [Official LIPIcs author instructions and template downloads](https://submission.dagstuhl.de/series/details/LIPIcs).
- **[V4]** [Dagstuhl statement on generative AI](https://drops.dagstuhl.de/docs/gen-ai).
- **[P1]** [Verifying Datalog Reasoning with Lean, ITP 2025](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2025.36).
- **[P2]** [A Mechanized First-Order Theory of Algebraic Data Types with Pattern Matching, ITP 2025](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2025.5).

Repository evidence for this map:

- [Inspected manuscript](https://github.com/scidonia/ownership/blob/48a1ac016a8f0322067793f92541c752a823b857/paper/ownership-skeleton.tex).
- [Complete accounting and supported fragment](https://github.com/scidonia/ownership/blob/48a1ac016a8f0322067793f92541c752a823b857/Ownership/CompleteAccounting.lean).
- [Flat preservation and store-slot predicate](https://github.com/scidonia/ownership/blob/48a1ac016a8f0322067793f92541c752a823b857/Ownership/Preservation.lean).
- [Counted protocol and stronger child-call contract](https://github.com/scidonia/ownership/blob/48a1ac016a8f0322067793f92541c752a823b857/Ownership/CountedNested.lean).
- [Counted interpreter and prefix boundary theorem](https://github.com/scidonia/ownership/blob/48a1ac016a8f0322067793f92541c752a823b857/OwnershipLcnf/CountedTrace.lean).
- [Ordinary finite-path contract derivation](https://github.com/scidonia/ownership/blob/48a1ac016a8f0322067793f92541c752a823b857/OwnershipLcnf/PathRecursion.lean).
- [Current principal theorems](https://github.com/scidonia/ownership/blob/48a1ac016a8f0322067793f92541c752a823b857/OwnershipLcnf/Principal.lean).
- [Closed principal instance](https://github.com/scidonia/ownership/blob/48a1ac016a8f0322067793f92541c752a823b857/OwnershipTest/Principal.lean).

