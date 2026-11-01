# Ownership paper contract audit

Base revision: `fcab2f39e9bf086cbb5817c947dadc1f68c8c605`  
Toolchain: `leanprover/lean4:v4.35.0-rc3`  
Manuscript: `paper/ownership-skeleton.pdf`, 15 pages.  
Revision specification: `docs/notes/ownership-paper-submission-handoff.md`.

The inventory below is taken from the declarations, not from the manuscript's
short labels. The `#check` and `#print axioms` commands were run with
`nix develop -c lake env lean` against the base revision. Every headline theorem
reports only `propext`, `Classical.choice` and `Quot.sound`.

## Headline declarations

| Manuscript label | Actual declaration | Boundary and premises | Classification |
| --- | --- | --- | --- |
| `check_sound` | `Ownership.check_sound` | `check ctx c = some ctx'`, `Inv H env ctx`; returns a completed run, every recorded write exclusive, and `Inv` at the output context | proved lemma, model |
| `checkN_sound_of_entryInv` | `Ownership.Entry.checkN_sound_of_entryInv` | `EntryInv H env c root client`, `Agrees H env code`, `checkN c code = some ctx'`; returns a completed `runN`, every recorded write exclusive, and `Inv` at the output context | proved lemma, model |
| `project_sound` | `OwnershipLcnf.project_sound` | `projectPrefix`, `Layout`, `Machine`, `Agrees`, cell and bounds facts; equality of the executed and model `PrefixOutcome` | proved lemma, LCNF |
| `recognized_write_in_place` | `OwnershipLcnf.recognized_write_in_place` | the same recogniser/layout/agreement facts, with `EntryInv H env (Runner.initCtx root) root client`; both outcomes are `inPlaceOutcome root i v o H` | proved lemma, LCNF |
| `index_path_simulates_model` | `OwnershipLcnf.index_path_simulates_model` | `projectNested`, `NestedLayout`, `LevelMatch`, `NestedAgrees`, and **`PathContract path value body tip l rest H mEnv c cb y`**; returns the nested outcome equality and a completed nested run whose writes are exclusive | proved lemma, LCNF, **child contract supplied** |
| `pair_accounting` | `Ownership.CountedPair.pair_accounting` | `WellFormedEntry H p c i`; the protocol result has parent and child at count one, live and exclusive, with counts equal to the entry heap | proved lemma, counted pair |
| `putBack_exclusive_of_wellFormed` | `Ownership.PutBack.putBack_exclusive_of_wellFormed` | `WellFormedEntry H p c i` and `ChildCall ...`; the put-back selects the mutate branch and leaves parent and child at count one and exclusive | proved lemma, restoration, child-call boundary supplied |
| `checkExclusive_no_abort` | `OwnershipLcnf.Runtime.checkExclusive_no_abort` | `Corr H R` and `H.Exclusive r`; the runtime check is not an abort | proved lemma, runtime model |
| `setAt_inPlace_of_entryInv` | `OwnershipLcnf.Runtime.setAt_inPlace_of_entryInv` | `EntryInv H env (Runner.initCtx root) root client`, `Corr H R`, cell and bounds facts; `setAt` returns `inPlace`, preserves `Corr`, and writes the field | proved lemma, runtime model |
| `prefix_abort_impossible` | `OwnershipLcnf.prefix_abort_impossible` | the recogniser, layout, `EntryInv H env (Runner.initCtx root) root client`, `Agrees`, cell and bounds facts; no `PrefixAborts` | proved lemma, emitted semantics |

Consequences for the manuscript:

- The labels in the appendix must carry their namespaces. The bare names in the
  current appendix do not resolve.
- `check_sound` and `checkN_sound_of_entryInv` are model theorems. The LCNF
  theorems are separate and have their own recognition/agreement premises.
- `index_path_simulates_model` does **not** prove the emitted recursive callee.
  It takes `PathContract` as a hypothesis. The finite-path discharge lives in
  `OwnershipLcnf/PathRecursion.lean`: the tail contract is the induction
  hypothesis and the leaf contract remains. The sentence "without a callee
  hypothesis" must be removed or restated.

## Alias and count-accounting gap

The displayed `Inv` (`Ownership/Code.lean:290-297`) has:

- `rc_eq : ∀ r, H.rc r = c.mult r`;
- `owned : ∀ x r, c.us x = .owned → c.refOf x = some r → env x = some (.ref r) ∧ 1 ≤ c.mult r`;
- `borrow`, `scalar`, `nonPersistent`.

`Ownership/Code.lean:219-241` defines `bindOwned` and proves
`bindOwned_mult : (c.bindOwned x r).mult = c.mult` by `rfl`.
`Ownership/Soundness.lean:251-255` proves
`Inv H (env.set x (.ref e)) (c.bindOwned x e)` from `Inv H env c` and
`c.mult e = 1`.

`EntryInv` (`Ownership/Entry.lean:121-125`) adds `UniqueTree`,
`ClientSeparated` and `RootsComplete`. `UniqueTree` (`:97`) says every cell in
the mutable footprint has `rc = 1`; `ClientSeparated` (`:110`) excludes client
reachability from the footprint; `RootsComplete` (`:116`) says every owned
variable's reference is in the footprint. `LiveIn` (`Ownership/Entry.lean:657`)
says owned and borrowed variables are in the footprint. None of these counts
owning variables.

Therefore the configuration

```text
us x = us y = owned
refOf x = refOf y = some r
env x = env y = some (.ref r)
mult r = H.rc r = 1
```

satisfies the displayed `Inv` and `EntryInv` when `r` is a live,
non-persistent cell in the root's footprint. `bindOwned` reaches it from a
one-owner state without changing `mult`, because it is a context operation, not
a heap operation. This is the handoff's alias challenge. A kernel-checked countermodel
(`AliasAudit.alias_admitted`, compiled from `/tmp/alias_countermodel.lean`
against this revision) constructs it: `Runner.initInv n` supplies the
one-owner `Inv`, and `Inv.bindOwned` adds the second owned variable without
changing `mult`. The countermodel is about `Inv`, the premise `check_sound`
uses, so the model's exclusive-write conclusion holds for a state with two
owning environment handles.

Consequence: `check_sound`'s "every recorded write is exclusive" is a theorem
about the model's `H.rc`. The manuscript's move from "count one" to "the runtime
has one owning handle" still needs an accounting premise:

1. `c.mult r` is the total handle count, not merely a context-local estimate;
2. every owning variable's handle is counted in it;
3. `H.rc` is the runtime count and incoming heap edges are accounted.

The first two are environment-side and can be strengthened in the model. The
third is a heap/runtime fidelity premise and should be named as such unless a
heap-well-formedness theorem is added.

## Resolution boundary

The selected direction is both:

- strengthen the environment-side accounting with a context support and owner
  count, add the take-out precondition that the extracted reference has no
  existing owner (`ownerCount c e = 0`, or the corresponding bound), and prove
  preservation through `setUs`, `move`, `bindOwned`, `inc` and `dec`;
- record the heap incoming-edge/runtime-count fidelity as an implementation
  assumption in the contract table and the principal theorem, rather than
  hiding it in `Inv`.

The alias countermodel is the regression test for the first part: the raw
`Inv`/`EntryInv` must no longer be presented as sufficient for the physical
reading, and the strengthened statement must reject the two-owner configuration
or carry the accounting explicitly.

### Implemented environment-side accounting

`Ownership/Accounting.lean` adds `OwnersAccounted c`:

- `c.mult r = 0` implies no owning variable refers to `r`;
- `c.mult r = 1` implies at most one owning variable refers to `r`.

The module proves preservation under `setUs` (non-owning use), `inc`, and
`bindOwned`/`dec` **with explicit preconditions**:

- `bindOwned` requires no existing owner of the target (`hno`);
- `dec` requires at most one owner other than the consumed variable
  (`hother`) and `n < c.mult r`.

`alias_not_accounted` is the kernel countermodel: the state produced by
`initCtx` plus `bindOwned 1 r` violates `OwnersAccounted` even though `Inv` is
preserved. `lake build Ownership` passes; the new lemmas use only `propext` and
`Quot.sound`.

The checker's take-out and `dec` rules do not yet enforce `hno`/`hother`. They
are therefore client obligations in the principal theorem, not silently
available facts. The heap incoming-edge/runtime-count half remains the named
implementation assumption.

## Other manuscript corrections established by the audit

- `Code` and `NCode` are explicit syntax interpreted by `run`: a deep embedding,
  not a shallow embedding.
- The claim that linearity necessarily requires changes to Lean's kernel,
  unification and every library is not supported by this development and must be
  removed.
- The novelty must be stated against Huisinga's 2023 uniqueness analysis and
  Lean's `Array.markLinear`; "no kernel changes" is not the distinction.
- The single-threaded runtime restriction must be explicit; count one and
  non-persistence are not a universal characterisation of all Lean modes.
- Absence of the exclusivity-check abort is not absence of all faults, and it is
  not by itself a successful update.
- "Complete" for the recognised fragment must be defined or removed; soundness
  of an accepted fragment is not completeness of an analysis.
- The appendix needs full names and types, not bare labels.

## Resolution status

The revision addresses the review's work areas in the manuscript and the
artifact. The remaining items are named obligations, not unresolved audit
questions.

| Review area | Disposition | Evidence |
| --- | --- | --- |
| Novelty | addressed | `Closest prior work` in the introduction; Table 1; related work. Huisinga, `Array.markLinear` and translation validation are compared; "no kernel change" is no longer the distinction. |
| Assumptions | addressed | Table 3 classifies entry/agreement, A/N contracts, accounting, `PathContract`, `Corr`, linked runtime and source correspondence; the appendix gives full principal type, names and status. |
| Principal theorem | addressed | `OwnershipLcnf.principal_write` composes the flat LCNF and runtime-model claims; its full type is in Appendix A.2. |
| Alias/accounting | addressed with named preconditions | `Ownership.OwnersAccounted`, `CountFidelity`, `alias_not_accounted`; Section 3.3; the checker's take-out/`dec` preconditions are client obligations, not hidden. |
| Recursive scope | addressed | `index_path_simulates_model` displays `PathContract`; `PathRecursion` discharges the finite tail; leaf and N10 are stated. |
| Extraction/restoration | addressed with a named composition gap | Protocol count table; `pair_accounting`/`putBack_exclusive_of_wellFormed`; `PairProjection` model term. The nested interpreter abstracts the pair traffic and unconditional restoration; its closure does not contain the counted-pair/put-back declarations, so the counted nested execution composition is outstanding. |
| Recognition/observations | addressed with a trace scope | Accepted grammar and mutation-corpus scope; `PrefixOutcome` preservation paragraph; shared decoder/adequacy boundary. The nested trace records designated scalar writes, not extraction/restoration stores. |
| Example/evaluation | addressed | Running `Layout5.setAt` source example; flat probe table with checker/runtime/buffer/result/config; nested C/IR gate; cost/allocation qualification. |
| Reproducibility | addressed with a gate scope | Appendix A.3 commands; test and gate results; `scripts/check_axioms.lean`; pinned sibling `66e64334...`; toolchain. The probe's modes assert their observations and the gate checks the status; the differential mode compares recorded expectations rather than executing the model. |
| Manuscript consistency | addressed | Abstract/introduction/principal/limits/conclusion describe the same conditional guarantee; deep embedding, single-threaded restriction and "complete" are corrected. |

Remaining named obligations:

- the C semantics of `lean_is_exclusive`/`lean_array_uset`, replay-to-backend
  identity, address identity and free/cascade;
- the emitted recursive callee and continuation (N10) and the leaf contract;
- the checker's take-out/`dec` accounting preconditions (`hno`/`hother`);
- `CountFidelity` for arbitrary entry heaps, and the runtime's count fidelity;
- the counted protocol's integration into the nested execution simulation;
- extraction/restoration disposition events for a full nested no-copy claim;
- a model-driven differential and a linked differential for the nested protocol
  (the current flat differential compares recorded expectations; the nested
  evidence is the model/LCNF and the generated-C/IR gate);
- the Lean-source-to-LCNF correspondence.

A second implementation audit (`docs/notes/ownership-implementation-audit.md`)
confirms the alias witness and the nested-composition/trace findings above. Its
positive points are retained: the flat `recognized_write_in_place` specifies the
single `(root, true)` write, `ChildCall.parent` derives parent preservation, and
the counted-pair accounting has explicit increments and controls. The paper now
presents the flat `principal_write` as the composed result and the nested path as
a separate finite model with the counted composition outstanding.

