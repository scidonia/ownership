# Ownership paper submission handoff

Date: 1 November 2026  
Manuscript reviewed: *Static Count-One Ownership for In-Place Array Updates in Lean 4*, Gavin Mendel-Gleason, dated 30 October 2026 (`ownership-skeleton.pdf`, 15 pages).

## Objective and assessment

Revise the manuscript and, where necessary, its supporting formalisation into a defensible research submission. Treat the present review as an adversarial specification for the revision.

The current manuscript would receive a rejection recommendation as a full research paper. It describes potentially useful verified components, but does not make the novelty, assumptions, or composition of its central guarantee sufficiently assessable. The strongest candidate contribution is verified reference-count accounting for an extraction, child-update, and restoration protocol, connected to recognised compiler output. Build the revised paper around the strongest result the artifact actually supports.

This handoff is based on the PDF and the accompanying literature checks. The formalisation was not independently built or audited. A question about an omitted definition or abbreviated theorem is not an established bug in the repository. Inspect the implementation before deciding whether the repair requires a proof, a stronger invariant, or clearer exposition.

Do not turn this into a project to verify all of Lean or its C runtime. A complete conditional result at a precisely chosen semantic boundary can be a satisfactory submission. The immediate goal is to make that boundary and the achievement within it unambiguous.

## Working rules

- Preserve correct existing results. Do not weaken a theorem merely to remove a review concern without documenting what guarantee has changed.
- Do not introduce an axiom, `sorry`, or a renamed hypothesis that simply assumes the desired exclusivity or recursive correspondence.
- Distinguish global axioms, theorem hypotheses, proved interface contracts, and empirical observations.
- Expand every semantically significant hidden premise when assessing a theorem. Administrative parameters may remain abbreviated in the main text.
- Describe an unresolved audit question as unresolved until the relevant definitions and proofs have been inspected.
- Keep all reported results tied to an exact revision and toolchain. Do not manufacture timings, corpus outcomes, supported examples, or acceptance rates.
- Use the repository's existing instructions and meaningful checks. Add tests where they address a real semantic or integration risk.

## Priority and dependency order

| Priority | Work package | Required outcome |
| --- | --- | --- |
| P0 | WP1: Establish novelty | Direct comparison with the closest prior work; a supportable contribution statement |
| P0 | WP2: Audit assumptions | Complete contract inventory and full types of headline theorems |
| P0 | WP3: Compose the principal guarantee | One theorem at a named execution boundary with explicit premises |
| P0 | WP4: Resolve alias and count accounting | Explain why the relevant model states represent valid runtime ownership |
| P0 | WP5: Resolve recursive-call scope | Prove invocation correspondence or state the finite-path result narrowly |
| P1 | WP6: Connect the extraction protocol | Visible count derivation and its connection to recognised instructions |
| P1 | WP7: Audit recognition and observations | Precisely specified accepted fragment and property-preserving observations |
| P1 | WP8: Demonstrate practical use | One complete source-to-certificate example and informative experiments |
| P1 | WP9: Make the artifact reproducible | Pinned build, proof audit, gate, and experimental commands |
| P2 | WP10: Rewrite and correct | Coherent paper, proof explanations, repaired claims and references |

WP2 and WP4 should inform WP3. Resolve WP5-WP7 before finalising the theorem's scope. Rewrite the abstract and introduction after the technical audit, so they describe the final result.

## WP1: Establish the actual novelty

### Problem

The paper treats an external ownership checker without changes to Lean's kernel as a principal distinction. That is insufficient. Marc Huisinga's 2023 thesis, *Static Uniqueness Analysis for the Lean 4 Theorem Prover*, targets a model of Lean's IR and implements a uniqueness checker in Lean; formal soundness and compiler integration remain future work there [S1].

The likely distinction to investigate is a stronger verified guarantee and its connection to emitted code, obtained for a narrower fragment. Do not assert this distinction until the artifact audit confirms it.

### Tasks

1. Read the closest prior work and compare the semantic guarantee, supported fragment, verification status, and compiler connection.
2. Explain which contribution is new: exact count accounting, checker soundness, recognised-output correspondence, or their verified composition.
3. Discuss Lean's existing `Array.markLinear`: it can first copy an array to establish uniqueness and, with `LEAN_ABORT_ON_NONLINEAR` enabled, panic on later nonlinear use [S2]. Distinguish that dynamic facility from the static guarantee being claimed.
4. Position the recognised-output strategy relative to translation validation [S3]. State exactly which property is validated; do not imply validation of arbitrary compiler transformations.
5. Revise Table 1 to compare actual guarantees and integration boundaries, rather than suggesting that alternative approaches necessarily require pervasive host-language changes.

### Acceptance criteria

- The introduction identifies the closest predecessor and a concrete technical advance over it.
- Novelty does not rest on being the first static uniqueness analysis for Lean, or on the general possibility of implementing a checker without kernel changes.
- Existing runtime diagnostics are acknowledged and distinguished from the proposed guarantee.

## WP2: Expose and audit the assumptions

### Problem

Pages 9-12 invoke A1-A12, N1-N12, agreement, layout, leaf contracts, child-call boundaries, and returned-handle accounting without defining enough of them. A reviewer cannot tell how much of the claimed result is contained in these premises.

### Tasks

1. Locate the exact declarations for all contracts, including contracts introduced through section variables, implicit binders, and typeclasses.
2. Expand the full types and dependencies of at least:
   - `check_sound`
   - `checkN_sound_of_entryInv`
   - `project_sound`
   - `recognized_write_in_place`
   - `index_path_simulates_model`
   - `pair_accounting`
   - `putBack_exclusive_of_wellFormed`
   - `checkExclusive_no_abort`
   - `setAt_inPlace_of_entryInv`
   - `prefix_abort_impossible`
3. Create a contract table with the proposition, consumer, provider, status, and remaining obligation for each assumption.
4. Audit N10, returned-handle accounting, and A6/A8 particularly carefully. Determine whether they specify primitive behaviour, require a substantial callee invariant, or already require a conclusion close to the headline result.
5. Explain what evidence supports each implementation assumption. Tests may support alignment but do not discharge a universal semantic contract.

### Required classification

| Category | Meaning |
| --- | --- |
| Proved lemma | Derived in the formal development from stated premises |
| Client obligation | A precondition or interface fact callers must establish |
| Implementation assumption | A proposition about backend or runtime behaviour that remains unproved |
| Global axiom | An axiom in the proof dependency closure |
| Empirical evidence | A measured observation on a specified implementation and input |

Do not collapse these into a single label such as “proved under contracts”.

### Acceptance criteria

- A reader can assess the central theorem's remaining obligations without opening the repository.
- The appendix contains complete types for the principal results.
- No exclusivity or recursive-correctness obligation is concealed by calling it an implicit parameter.

## WP3: State one composed principal theorem

### Problem

The manuscript presents a chain across `Ownership.run`/`runN`, `execAST`/`execNestedAST`, a separate runtime model, and linked experimental code. Individual results across these semantics do not automatically compose for one program and execution.

### Tasks

1. Choose and name the strongest execution boundary actually supported by the proofs.
2. State one principal theorem identifying the recognised code, checker acceptance, entry conditions, semantic contracts, and relevant write events.
3. Show how the supporting results discharge this theorem's premises. If a connection remains an assumption, place it in the theorem and the contract table.
4. Explain how many writes are covered and how they correspond to the execution. Avoid a guarantee that can be satisfied merely because the observed write list is empty.
5. Separate the proved theorem from an engineering corollary about the pinned implementation under backend/runtime assumptions.

The intended shape, expressed schematically rather than as an asserted existing result, is:

```text
recognised(code, model)
and accepted(context, model)
and validEntry(initialState, context)
and the listed semantic contracts
imply that execution at the stated boundary
performs each covered update through the exclusive branch.
```

If functional correctness, termination, or absence of other faults are also claimed, state and justify them separately. If only completed executions are covered, say so. Prefix safety, total correctness, and final-state agreement are different results.

### Acceptance criteria

- The reader can point to one statement answering “what exactly has been proved?”
- Every transition in the opening argument map is either discharged or explicitly assumed.
- The abstract and conclusion do not imply compiled-program guarantees beyond this boundary.

## WP4: Audit physical uniqueness and the ownership invariant

### Concrete challenge

Claim 1 on page 8 displays an `Inv` that relates context multiplicity to heap counts but does not visibly require all owning references to be counted. Consider distinct variables `x` and `y` with:

```text
us x = us y = owned
refOf x = refOf y = some r
env x = env y = some (ref r)
mult r = H.rc r = 1
```

With an appropriate live, nonpersistent cell, the displayed invariant fields do not exclude this configuration. If both variables denote independently owning runtime handles, the physical count cannot be one.

This is a challenge to the interpretation of the displayed invariant, not a demonstrated counterexample to `check_sound`. The missing exclusion may already follow from `RootsComplete`, another invariant, or a different interpretation of environments.

### Tasks

1. Inspect `Inv`, `EntryInv`, `RootsComplete`, `UniqueTree`, `ClientSeparated`, and the environment semantics.
2. Determine exactly which predicate excludes the configuration above or why its variable bindings do not denote independent owners.
3. Explain the accounting of owning roots, incoming heap edges, temporary handles, and runtime counts. Where counts are deliberately abstract, state that interpretation.
4. Explain borrowed aliases separately: they need not increment RC, but their liveness and allowed uses need justification.
5. Audit the connection between the whole-heap condition `rc_eq : ∀ r, H.rc r = c.mult r` and local ownership. Explain how unrelated client heaps or suspended state are represented and preserved.
6. Clarify whether `Ctx.refOf` contains abstract object names or concrete model references, and how those names are interpreted across runtime executions.
7. Explain how a context is obtained statically, which annotations are supplied, and who discharges the entry invariant. Do not equate fixture-specific acceptance with analysis of arbitrary runtime inputs.

### Acceptance criteria

- The paper explains why model count one corresponds to the required runtime uniqueness fact under its stated assumptions.
- The alias challenge is resolved by a cited definition and consequence, or by a documented strengthening of the invariant.
- Context construction and entry obligations are part of the user-facing method.

## WP5: Resolve finite paths versus emitted recursion

### Problem

The argument map describes correspondence without a callee hypothesis. The later text retains N10, excludes the emitted callee and continuation, and says the flat environment cannot express per-invocation indices. A finite nested model and the compiled recursive function are not automatically the same execution.

### Tasks

1. Identify precisely what the induction in `index_path_simulates_model` discharges.
2. Expand N10 and distinguish the model-level tail obligation from the semantics of an emitted call.
3. Explain the role of invocation-local variables, indices, returns, and continuations.
4. Choose a repair supported by the implementation:
   - Prove the invocation correspondence using suitable environments and a call semantics; or
   - State the result as a finite-path model correspondence under an emitted-call contract.
5. Present `calls_build` and `callBody_build` as supporting syntactic lemmas, not as evidence by themselves that the compiled recursive function follows the model.

The narrower second repair is acceptable if the overall contribution remains substantial. Do not undertake a full recursive compiler semantics solely to preserve an overbroad sentence.

### Acceptance criteria

- The reader can distinguish the verified finite structure from the supplied recursive-call meaning.
- “Without a callee hypothesis” appears only if its precise interpretation is justified.
- The claimed execution guarantee matches the environment and continuation model.

## WP6: Make extraction and restoration accounting explicit

### Problem

Claim 8 may contain the central technical mechanism, but the paper does not show enough of the protocol or its connection to emitted code. Claim 9 abbreviates relationships among `H`, `Hin`, and `Hout`, leaving the restoration boundary difficult to assess.

### Tasks

1. Add a protocol table tracing parent, child, and pair counts, ownership-bearing roots and edges, and pair lifetime at each stage.
2. Derive the count effects of moving handles into the pair, projecting components, releasing the unique pair, invoking the child body, and restoring the parent.
3. Connect `protocol` to the recognised instructions. A proof about a hand-written protocol function needs an explicit bridge to the emitted extraction.
4. Print the full restoration theorem and explain the equations or relations connecting `H`, `Hin`, and `Hout`.
5. Separate four facts: parent exclusivity before restoration, returned-child ownership, the restoration disposition, and preservation of unrelated state.
6. Explain the scope of restricted free. Distinguish the modeled release of this pair from general deallocation and cascading release, which the manuscript excludes.
7. Keep the no-free and retained-alias controls, but explain what each establishes and whether it is a theorem or an experiment.

### Acceptance criteria

- The count derivation is understandable without reading the proof script.
- The pair theorem and put-back theorem compose at an explicitly identified state.
- Returned-handle accounting is either derived or plainly recorded as a substantive remaining obligation.

## WP7: Audit recognition, execution semantics, and observations

### Problem

The paper claims rejection of “any token-preserving near miss” without defining that class or stating a general rejection result. Also, `execAST` reportedly requires successful decoding. If the recogniser and executor share model-oriented definitions, their equality may establish less about independent instruction semantics than the prose suggests.

This is an audit question, not a finding of circularity.

### Tasks

1. Specify the accepted grammar, including operand identities, arities, instruction order, constructors, branches, joins, and continuation boundaries.
2. Identify whether execution is defined independently on LCNF instructions or through the recognised representation. Explain what adequacy result relates it to the intended instruction semantics.
3. Audit `PrefixOutcome.ofExec`, `PrefixOutcome.ofModel`, and their nested counterparts. List preserved and discarded observations.
4. Show that observations preserve the property of interest: every covered write's exclusive/copy disposition, not just final functional contents.
5. Explain how traces account for writes, faults, and early exits. State any limits on unrecognised suffixes or continuations.
6. Replace universal near-miss language with a proved, precisely scoped claim or a description of the mutation corpus actually tested.
7. Retain useful negative cases for operand substitution, reordering, extra increments, omitted release, branch changes, and continuation changes where those cases address actual recognition obligations.

### Acceptance criteria

- The accepted fragment has an explicit structural definition.
- Recognition constrains the execution being discussed rather than only a shared decoder's output.
- Outcome projection cannot erase a violation of the stated update guarantee without an explicit limitation being acknowledged.

## WP8: Add a running example and informative evaluation

### Running example

Use one actual Lean source program with a meaningful array update. Prefer a small nested update that exercises the main protocol, with a simpler flat write as an introduction.

Show the source, relevant emitted instructions, recogniser result, generated model, context construction, entry obligations, checker result, and theorem application. State what the programmer supplies manually and what the tool computes. Include a nearby rejected variant and explain its diagnostic.

### Experimental improvements

Replace the five “agree” rows with informative observations. For each case, record checker status where applicable, exclusive/copy disposition, array-buffer copying or allocation, functional result, and relevant configuration.

Retain or add cases for unique arrays, observably live aliases, released aliases, persistent/closed values, closure-held arrays, and nested extraction/restoration. Show the closed-pure-array case explicitly rather than leaving its relationship to the table implicit.

Make an alias observably live after the update when testing sharing. A source binding alone is insufficient because the compiler may release it before the write. Explain how measurement avoids introducing additional owning references or changing their lifetimes.

Separate array copying from other allocation. A temporary pair may allocate even when all certified array writes are in place. Do not describe no-copy certification as an allocation-free execution theorem.

### Cost claim

Give a concrete program for the opening linear-versus-quadratic motivation. One initial alias need not force a copy on every iteration; after the first copy, subsequent updates may operate on a unique array. Demonstrate the pattern that sustains sharing, or state the asymptotic effect as a possible consequence under specified usage.

Use a cost argument or scaling experiment appropriate to the claim. Report timing methodology and uncertainty only where performance measurements are actually used.

### Acceptance criteria

- A reader can reproduce certification of a real source example.
- The experiments demonstrate the central nested protocol as well as isolated primitives.
- The reported observations distinguish copying, allocation, correctness, and static acceptance.
- No speedup or asymptotic conclusion exceeds the evidence.

## WP9: Produce a reproducible artifact and proof audit

### Tasks

1. Supply a repository or archival artifact link and exact revision.
2. Pin the Lean toolchain, relevant sibling/runtime revisions, dependencies, compiler flags, and platform details.
3. Provide commands for building the proofs, running recognition/gate checks, reproducing negative controls, and running the differential corpus.
4. Audit the headline theorems' axiom dependencies using facilities supported by the pinned toolchain, including `#print axioms` where appropriate.
5. Record full theorem hypotheses as well as global axioms. An axiom audit alone does not reveal a strong theorem parameter.
6. Explain what the artifact/IR/C gate checks: identity, hashes, structural shapes, runtime headers, or other properties. Distinguish reproducible identity checks from semantic preservation claims.
7. Explain replay-to-backend identity and address identity assumptions, including how experiments observe the relevant object or buffer identity.
8. Run the documented procedure from a clean environment and preserve the actual results.

### Acceptance criteria

- The artifact can be built and its reported experiments repeated from the supplied instructions.
- The proof and implementation trust boundaries are explicit.
- “Pinned” is accompanied by concrete identifiers, not merely a statement that pinning exists.

## WP10: Rewrite the manuscript around the result

### Proposed structure

1. Problem, running example, closest prior work, and precise contribution.
2. Execution boundary, supported fragment, and principal theorem in readable mathematical form.
3. Ownership judgement, context construction, heap invariant, and checker soundness.
4. Extraction, child-call isolation, and restoration accounting, with proof sketches.
5. Recognised-code correspondence and explicitly stated contracts.
6. Source-to-certificate demonstration and empirical alignment.
7. Comparison with prior work and specific limitations.
8. Conclusion matching the theorem's exact scope.
9. Appendices containing full theorem types, contract inventory, and artifact instructions.

Cut repeated argument maps and chains. Use that space for definitions, the running example, and explanations of why the proofs work. Promote checker soundness, protocol accounting, and the composed recognised-code guarantee. Move routine structural facts to the appendix.

### Conceptual and wording repairs

- Describe `Code` and `NCode`, which are explicit syntax interpreted by `run`, as a deep embedding. Ordinary Lean definitions do not make the object language shallowly embedded.
- Remove the claim that a linear discipline necessarily requires changes to the kernel, unification, and every library.
- Define usage linearity, uniqueness, and exact reference counts separately.
- Explain “static” in terms of the analysis inputs and quantification over executions.
- State the single-threaded runtime restriction explicitly. Count one and non-persistence should not be presented as a universal characterisation of all Lean runtime modes.
- Separate absence of exclusivity-check aborts from absence of all faults and from successful performance of an update.
- Replace unexplained internal labels such as “M7” with their substantive obligations.
- Replace a catalogue of related systems with concrete comparisons of guarantees and boundaries.
- Remove the claim that the discipline is “complete” unless the sense is defined. Soundness for an accepted fragment is not completeness of analysis.
- Check consistency between the opening argument map, numbered claims, and conclusion.
- Review the long italic passages and large code boxes for readability. Layout changes follow technical corrections.

### Bibliography corrections

- Resolve all visible “Verify ...” placeholders.
- Reference [14]: the cited MSCS article is by Erik Barendsen and Sjaak Smetsers, volume 6, issue 6, pages 579-612, 1996 [S4].
- Reference [7]: the original Iris author list includes Derek Dreyer [S5].
- Reference [9]: verify the entry against the publisher or paper. Its current listed authors agree with the inspected paper; remove the verification note once checked [S6].
- Preserve appropriate capitalisation for Lean, Rust, Haskell, CakeML, and C.

## Completion checklist

- [ ] The novelty statement survives direct comparison with the closest prior work.
- [ ] Every important contract is defined and classified.
- [ ] The paper contains one composed principal theorem at a named semantic boundary.
- [ ] The ownership/count interpretation resolves the alias challenge.
- [ ] Recursive-call claims match the proved invocation semantics.
- [ ] Pair accounting and restoration are connected to recognised code and compose explicitly.
- [ ] The observed trace preserves the update property and identifies the covered writes.
- [ ] One nontrivial source-to-certificate example is reproducible.
- [ ] Empirical rows contain actual observations, including the nested protocol and relevant negative controls.
- [ ] Cost and allocation claims match the evidence.
- [ ] Exact revisions, build commands, and a proof dependency audit are supplied.
- [ ] The abstract, introduction, theorem statements, limitations, and conclusion describe the same guarantee.
- [ ] No unresolved question is presented as a discovered bug or a completed repair.

## Expected agent deliverables

Return the revised manuscript source and rendered PDF, any necessary formalisation changes, the contract/dependency inventory, reproduction instructions and results, and a concise resolution table mapping each work package to the changed declarations or manuscript sections. List remaining obligations explicitly.

If the audit shows that the existing development only supports a narrower result, revise the paper to that result and explain the change. A modest theorem with a clear boundary is more defensible than an apparently stronger theorem whose difficult content remains hidden in contracts.

## Sources checked for the review

- [S1] Marc Huisinga, *Static Uniqueness Analysis for the Lean 4 Theorem Prover*, master's thesis, KIT, April 2023. See especially the implementation and future-work discussion: https://pp.ipd.kit.edu/uploads/publikationen/huisinga23masterarbeit.pdf
- [S2] Official Lean API documentation for `Array.markLinear`: https://lean-lang.org/doc/api/Init/Data/Array/Basic.html#Array.markLinear ; release context: https://lean-lang.org/doc/reference/latest/releases/v4.35.0/
- [S3] George C. Necula, *Translation Validation for an Optimizing Compiler*, PLDI 2000: https://people.eecs.berkeley.edu/~necula/Papers/tv_pldi00.pdf
- [S4] Publisher record for Barendsen and Smetsers, *Uniqueness typing for functional languages with graph rewriting semantics*: https://doi.org/10.1017/S0960129500070109
- [S5] Iris project publication list, including the original POPL 2015 paper: https://iris-project.org/
- [S6] Andrea Lattuada et al., *Verus: Verifying Rust Programs using Linear Ghost Types*, OOPSLA 2023: https://www.andrew.cmu.edu/user/bparno/papers/verus-ghost.pdf
- [S7] Official Lean reference-counting documentation: https://lean-lang.org/doc/reference/latest/Run-Time-Code/Reference-Counting/
- [S8] Official explicit-RC pass documentation: https://lean-lang.org/doc/api/Lean/Compiler/LCNF/ExplicitRC.html

Use the artifact's pinned Lean revision for implementation claims. Current documentation supplies context, not proof that an older or modified runtime has the same behaviour.
