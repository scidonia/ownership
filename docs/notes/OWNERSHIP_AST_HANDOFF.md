# Ownership handoff: certify the recognized LCNF write prefix

Date: 26 October 2026  
Repository: https://github.com/scidonia/ownership  
Review baseline: `34865f21edcd48d17a7dc4c8d6d06a63be6dc6df`  
Scope: finish the semantic connection for the scalar-array `execP` write prefix before extending the recursive models.

## Goal

Preserve the existing architecture: a sealed client language, fixed executor, explicit entry invariant, ownership checker, and certificate for the generated artifact. No change to Lean's kernel type system is required.

The next result should establish:

> For the pinned, represented LCNF scalar-array update prefix, successful recognition, LCNF well-formedness, and an entry relation imply that execution of the actual recognized instructions simulates the ownership model. On the in-bounds path, the designated write avoids ownership faults, selects the in-place branch, and preserves the target address, under explicitly stated primitive and backend/runtime contracts.

This is a bounded artifact result. It need not verify the entire compiler, continuation, recursive executor, or C backend.

## What has improved

The four commits after `3ffa9c0` add the captured LCNF, a structural projection, executable projection checks, and a fragment semantics with model-level in-place results.

| Component | Current evidence | Preserve |
| --- | --- | --- |
| Artifact provenance | `docs/notes/artifacts/execP.lcnf.txt` records toolchain, sibling revision, acquisition route and hashes | Keep the distinction between replay and backend input |
| Structural recognizer | `OwnershipLcnf/Projection.lean` walks projections, increments/decrement, bounds computation and check/box/set sequence | Reject unsupported instructions and unexpected interleavings |
| Negative controls | `scripts/check_projection.lean` rejects seven mutations while accepting the original declaration | Retain positive controls |
| Model correspondence | `toCode_fragment`, `exec_eq_run`, `project_sound` | Retain as lower-level lemmas where useful |
| Entry-based update result | `projected_check`, `designated_write_in_place`, initializer and fragment theorems | Derive exclusivity from entry facts rather than relying on the assertion to establish it |
| Primitive boundaries | A1–A10 in `OwnershipLcnf/Semantics.lean` | Keep assumptions and non-claims explicit |

These are useful results. The issue below concerns the strength of their connection to the input AST, not the validity of their proofs about the defined models.

## Finding 1: recognition is not yet linked to execution of the AST

`project_sound` relates execution of `p.fragment` to execution of `p.toModel`. Both are constructed from the same `Prefix`. The theorem does not interpret `Lean.Compiler.LCNF.Code` and establish that the recognized input code executes as that fragment.

The headline theorems take `_hproj : projectPrefix code = some p`, but their proofs do not use it. Their conclusions concern the reconstructed fragment or model. An unused hypothesis is not by itself a proof error; here it exposes the missing semantic link.

The executable replay check establishes recognition and checker acceptance operationally. It does not yet construct kernel evidence for those facts on a concrete represented compiler artifact.

### Required change

Choose one of these bounded routes:

1. Define execution directly over the supported actual LCNF nodes, stopping immediately after the designated `Array.set!` result is bound.
2. Decode a supported AST prefix into an instruction trace, prove successful decoding faithfully represents the AST's execution, then prove trace execution simulates the ownership model.

Either route is acceptable. The second can reuse the current `Op` machinery, but the trace must be justified by inspecting the input AST rather than solely synthesized from `Prefix` metadata.

Make the recognition hypothesis substantively establish the supported path, instruction operands, and correspondence. Unsupported syntax must fail explicitly.

## Finding 2: the semantics bypasses part of the emitted data flow

`Machine` has both `locals` and `env`. Constructor projections and boxing update `locals`, while `setBang` reads its array, index and replacement through `env`. Thus those preceding local computations do not generally supply the write operands in the current interpreter.

In addition, the emitted `Array.set!` uses `p.boxedValue`, but `Prefix.fragment` constructs:

```lean
.setBang p.setResult p.checkResult p.index p.value
```

The scalar source and boxed operand are intentionally identified in the ownership abstraction. That identification needs a representation lemma connecting the actual local operand to the model value.

### Required change

Use the emitted operands in the low-level semantics. Introduce a relation between low-level locals, node fields, heap and model environment. Establish that:

- The node's index and replacement fields supply the projected locals.
- The bounds computation reads those same values and the target array's length.
- Boxing represents the same scalar without introducing a reference into the mutable footprint.
- The exclusivity check returns the same target reference.
- The write reads the actual checked-array, index and boxed-value binders.
- The result binder denotes the returned target reference on the exclusive branch.

Prove instruction preservation of this relation. Reusing a pre-populated model environment is fine if the relation proves its agreement with actual locals; independent initialization of matching values is insufficient for a general correspondence theorem.

Use arbitrary supported indices and scalar replacements in the general theorem. Keep the existing zero-index/zero-replacement initializer case as a corollary or regression case. Include at least one nonzero, value-changing example.

## Finding 3: branch identification relies on position

`recognizeSet` currently uses:

```lean
let trueAlt ← match pre.cases.alts with
  | #[_, second] => some second.getCode
  | _ => findAlt `Bool.true (.cases pre.cases)
```

The common two-alternative case does not verify that the selected alternative denotes `Bool.true`. This matches the captured ordering but does not independently establish the documented branch identity.

### Required change

Check constructor identity where the representation supplies it. If this compiler phase encodes selection by position, validate the discriminant representation and establish or explicitly assume the relevant ordering invariant. Do not silently identify “second” with “true.”

Check exact supported primitive arities and operand forms, and handle specialized versus unspecialized call signatures explicitly. Apply only the well-formedness checks needed for the bounded semantic claim; record any facts inherited from compiler well-formedness.

Add a fixture that moves the write body onto the false branch, or otherwise changes branch association while preserving its instruction tokens. The recognizer must reject it, or the semantic theorem must correctly account for the changed selection.

## Prefix boundary and primitive contracts

The emitted code continues after `Array.set!`. The model inserts a return of the checked handle. Treat this as an observation boundary, not as a literal return instruction in the original AST.

Define a prefix outcome containing the heap, local result binder, target reference and write disposition. Prove its relation to the model's returned handle. Explicitly exclude the subsequent index decrement, continuation invocation and recursive `execP` call unless they are actually included in the semantics.

Continue to permit trusted primitive and backend/runtime contracts. In particular:

- The runtime meaning of an exclusive array update can remain a stated contract for this milestone.
- Constructor layout and boxing contracts must justify the operand relation used by the proof.
- Treating node/continuation reference-count traffic as irrelevant requires a separation or noninterference premise: those operations must not change counts in the target mutable footprint. A continuation may capture references; do not infer separation merely because its handle is omitted from the model heap.
- The model's stored count of one still needs a separate connection to physical counted references before claiming physical no-copy execution.
- Replay-to-backend identity remains a named trust step until established independently.

An A1–A10 prose list is valuable, but distinguish assumptions encoded in definitions, explicit theorem premises, and external implementation contracts. An axiom inventory alone does not establish runtime correspondence.

## Implementation sequence

1. Tighten branch selection and supported primitive signatures; add focused negative fixtures.
2. Define the actual-AST prefix execution or a faithful AST-to-trace decoding relation.
3. Define low-level/model state agreement, including node projections, boxing and result binders.
4. Prove the recognized prefix simulates `Ownership.run`, using the recognition hypothesis.
5. Derive the designated write result from `EntryInv`, an in-bounds premise and the primitive contracts. Include arbitrary supported scalar replacements.
6. Represent the pinned captured artifact in Lean and produce kernel-checked recognition/checker evidence. The compiler or capture generator may be untrusted; the resulting represented artifact and certificate must be checked.
7. Preserve capture provenance and explain the remaining replay-to-backend trust step.
8. Update README and PLAN around the final proved statement. The README currently describes only a model certificate and survey; avoid either understating the new result or describing it as a full compiler proof.

The theorem names below are illustrative, not required API changes:

```text
recognize_sound:
  recognition + AST well-formedness
  -> supported AST prefix faithfully decodes

prefix_simulates_model:
  recognized AST + related initial states + primitive contracts
  -> related prefix outcomes

recognized_write_in_place:
  preceding results + EntryInv + in-bounds
  -> no ownership fault + exclusive write + target address preserved
```

## Acceptance criteria

- The correspondence theorem refers to execution of the input AST, or to an independently justified decoding of it.
- Recognition evidence is used to establish the supported path and operands.
- The write obtains its replacement through the emitted projection/box chain, with a proved abstraction relation.
- True-branch identification is checked or supported by an explicit representation invariant.
- The theorem observes the actual write result binder at a clearly stated prefix boundary.
- A concrete represented captured artifact has kernel-checked acceptance evidence.
- A nonzero index and nonzero, value-changing replacement are covered by a general theorem and/or useful concrete corollaries.
- Shared-target and intervening-increment examples remain rejected or receive the expected modeled fault/copy outcome; they must not acquire a no-copy certificate.
- Primitive semantics, backend identity and physical runtime assumptions remain explicit.
- No `sorry`, `admit`, or new unreported axioms are introduced.

## Verification

Follow `AGENTS.md` and run:

```sh
nix develop -c lake build Ownership
nix develop -c lake build OwnershipTest
nix develop -c lake build OwnershipLcnf
```

Then provision the pinned sibling checkout as specified by the repository and run the replay/projection check:

```sh
cd ../lean-examples
nix develop -c lake env bash -c \
  'export LEAN_PATH="../ownership/.lake/build/lib/lean:$LEAN_PATH"; lean ../ownership/scripts/check_projection.lean'
```

Retain the seven existing mutation checks and add branch-association and operand-flow cases. Inspect `#print axioms` for the new headline theorems. Report model proof builds, concrete artifact certification, executable replay checks and runtime measurements separately.

This review was based on source and captured-artifact inspection at the stated commit. Builds were not independently reproduced because the review environment had neither `nix` nor `lake` installed.

## Subsequent milestone: recursive ownership

After the scalar-array AST connection is complete:

1. Replace the one-level `footprint` with transitive mutable reachability, distinguishing immutable observations where needed.
2. State client separation over reachable client state, with a clear completeness condition on roots.
3. Add a root → child → shared-grandchild counterexample and its unique positive control, plus indirect external-client reachability.
4. Give `callAt` a heap-changing semantic contract preserving suspended parent frames and returned ownership; prove the recursive implementation satisfies it.
5. Derive intermediate `TakeOutsOK` obligations from entry facts and preservation.
6. Extend artifact correspondence to nested extraction/restoration and pair reuse.

Keep the physical runtime bridge separate: counted roots, heap edges with multiplicity, external references, persistence, allocation freshness, and decrement/free/cascade behavior must be related to the model before transferring model-level RC=1 to physical memory behavior.

## Completion report

Report the resulting theorem, concrete artifact identity, checks run, and remaining assumptions. A suitable bounded claim is:

> The pinned scalar-array write prefix has a kernel-checked artifact certificate and a semantic connection to the ownership model. Under the stated entry and primitive/backend contracts, its in-bounds designated update is fault-free and selects in-place mutation at the original target address.

Use that claim only after the AST execution and concrete certification criteria above are met. Until then, describe the new results as fragment/model correspondence with an executable recognizer for the captured replay.
