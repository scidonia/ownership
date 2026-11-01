# Ownership implementation audit and revised agent handoff

Date: 1 November 2026  
Repository: https://github.com/scidonia/ownership  
Audited commit: `fcab2f39e9bf086cbb5817c947dadc1f68c8c605`  
Toolchain: Lean `4.35.0-rc3`, upstream release commit `470d5ce1400764999581fd26d5d72b00d990b0f4`.

## Assessment

This addendum refines the manuscript-only review using the actual implementation. The formal development is more substantial and explicit than the paper communicates. Checker soundness, call confinement, counted-pair accounting, restoration properties, and the flat-prefix correspondence are real checked results. Several earlier questions can therefore be closed or narrowed.

The principal submission risk is the composition and interpretation of these results. The headline nested correspondence does not use the counted-pair or put-back declarations; its interpreter abstracts their traffic and unconditionally performs restoration. Its write trace omits extraction and restoration stores. The physical meaning of model reference counts also remains an external obligation. These are limits on the claimed guarantee, not evidence that Lean has accepted a false theorem.

The supplied PDF is byte-identical to `paper/ownership-skeleton.pdf` at the audited commit. Its SHA-256 is `cc288241ba1771603910fa7b45064dcd1dae790f5e0098e26b355f05dc925385`. Differences between its quoted signatures and the implementation are therefore present at this revision, rather than explained by reviewing a different PDF.

## Verification performed

- Built `Ownership`, `OwnershipTest`, and `OwnershipLcnf` successfully: 45 jobs.
- Re-ran axiom audits for seven central declarations. The reported dependencies were subsets of `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or new axiom appeared in those results.
- Kernel-checked a witness showing that `EntryInv` admits two owned variable names for one count-one object.
- Kernel-checked that a take-out/put-back example is accepted by `checkN` and nevertheless has an empty `Write` trace.
- Traversed the full constant dependencies of the types and proof terms of three headline theorems, including opaque values. None depends on declarations in `Ownership.CountedPair` or `Ownership.PutBack`.
- Read the recognisers, semantic interpreters, entry invariant, path-recursion boundary, protocol and restoration modules, and runtime-gate/probe sources.

The build used the official binary release matching the pinned Lean version, not the Nix derivation. This environment lacks Nix and needed an executable-path compatibility shim for libuv's `uv_exepath`; the shim supplied the toolchain's application path and did not change proof definitions or Lean's kernel. The Nix artifact gate and sibling-dependent linked runtime experiments were not rerun. The repository source was not modified.

The proof witnesses and dependency-audit source are included below for reproduction in the ordinary pinned development shell, without the compatibility shim.

## How this changes the first review

| Earlier review question | Source-grounded disposition |
| --- | --- |
| Do the outcome projections preserve the important observations? | The flat `PrefixOutcome` preserves the heap, two result binders, target, disposition, fault, and write list. The flat theorem specifies exactly one successful write. Do not accuse this result of silently projecting away the copy disposition. |
| Is parent preservation merely assumed? | `ChildCall.parent` is derived through confinement and separation. Returned-child count/persistence remain explicit fields of `ChildCall`. |
| Does the repository supply actual pair accounting? | Yes. It models component increments and restricted pair destruction, with negative controls. The remaining issue is integration into the headline nested execution theorem. |
| Are the contracts undisclosed throughout the development? | No. Detailed A1-A12 and N1-N12 explanations exist in module headers. They are inadequately exposed in the manuscript, and many specify the interpretation by definition rather than appearing as Lean theorem parameters. |
| Is there any composed recognised-code theorem? | Yes: `recognized_write_in_place` is a useful composed result for the flat, bounded prefix under the stated model interpretation and entry conditions. Its scope should not be confused with a full recursive runtime certificate. |
| Does `RootsComplete` exclude duplicate owning aliases? | No. Its definition only places each owned reference inside the root footprint. A kernel-checked witness below confirms the stronger ambiguity remains even for `EntryInv`. |
| Is recursion connected to the actual callee? | No. The module expressly documents that the supplied model body and deeper scalar-index abstraction do not capture emitted invocation-local path re-projection. |

## Finding 1: Entry completeness does not account for physical owners

Priority: P0 for any interpretation as a physical uniqueness theorem.

Evidence: [Inv](https://github.com/scidonia/ownership/blob/fcab2f39e9bf086cbb5817c947dadc1f68c8c605/Ownership/Code.lean#L290), [RootsComplete and EntryInv](https://github.com/scidonia/ownership/blob/fcab2f39e9bf086cbb5817c947dadc1f68c8c605/Ownership/Entry.lean#L113).

`RootsComplete` states that every owned variable points into the mutable footprint. It neither distinguishes independent owners from several names for one owner nor relates the count to the number of roots and incoming owning edges. `UniqueTree` constrains the stored RC of footprint cells; it does not independently validate that count against the graph's ownership edges.

The checked witness constructs `EntryInv H env ctx 0 []` while variables 0 and 4 are both owned and both denote reference 0, whose count is one. The witness uses only the library's definitions and standard axioms.

This does not refute the model's `Inv.exclusive` theorem: the model defines exclusivity from its stored count and persistence flag. It refutes an interpretation of `EntryInv` alone as establishing a faithful count of independently owning runtime handles.

Agent action:

1. State precisely whether environment bindings are independent owners, borrowed names, or administrative aliases.
2. If physical count fidelity is claimed, introduce a representation invariant accounting for owning roots, incoming edges, and permitted administrative/borrowed names; show how the supported operations preserve it.
3. If that connection remains outside the paper, state the theorem over the abstract counted heap and list physical ownership accounting as a residual obligation.
4. Do not repair this by indiscriminately counting every environment binding: moved/dead variables can retain administrative values, and borrowing need not increment RC.

Acceptance: the paper cannot use the name `RootsComplete` as a substitute for an actual owner-accounting theorem.

## Finding 2: The headline nested proof does not consume the detailed protocol proofs

Priority: P0 for the proposed composed nested-update guarantee.

Evidence: [nested interpreter](https://github.com/scidonia/ownership/blob/fcab2f39e9bf086cbb5817c947dadc1f68c8c605/OwnershipLcnf/NestedSemantics.lean#L340), [put-back theorem](https://github.com/scidonia/ownership/blob/fcab2f39e9bf086cbb5817c947dadc1f68c8c605/Ownership/PutBack.lean#L703), [existing protocol boundary bridge](https://github.com/scidonia/ownership/blob/fcab2f39e9bf086cbb5817c947dadc1f68c8c605/Ownership/PathConsolidation.lean#L1391).

`execNested` interprets `.incParent`, `.incChild`, and `.decPair` as no-ops. Its `.setArray` operation unconditionally updates the modeled parent cell, without selecting between copy and mutate dispositions. `Nested.runN` similarly gives `putBack` an unconditional update semantics.

The module headers cite the counted-pair and restoration results as justifying these abstractions. However, a transitive declaration-dependency audit produced:

```text
OwnershipLcnf.index_path_simulates_model:
  CountedPair declarations in closure = []
  PutBack declarations in closure = []

OwnershipLcnf.index_prefix_simulates_model:
  CountedPair declarations in closure = []
  PutBack declarations in closure = []

OwnershipLcnf.recognized_write_in_place:
  CountedPair declarations in closure = []
  PutBack declarations in closure = []
```

The flat theorem's lack of dependence is expected: it does not execute the nested pair protocol. The nested results show the substantive missing composition.

There is useful partial bridging already: `protocol_parent_cell`, `protocol_child_cell`, and `protocol_cells` relate the counted protocol's session cells to the abstract take-out. Do not report that no bridge lemmas exist. The missing result is their integration into an execution simulation, including the actual restoration disposition.

Agent action:

1. Define a counted instruction execution or macro-step interpretation that performs the pair increments/free and both restoration dispositions.
2. Use the existing boundary bridge to relate its protocol boundary to the abstract nested interpreter. Account for the temporary pair and allocator cursor rather than demanding unjustified whole-state equality.
3. Derive the restoration branch from the relevant boundary invariant, using or appropriately generalising the existing `PutBack` results.
4. Prove the composed correspondence from this counted execution to the nested model.
5. If this is deferred, present the abstract correspondence and counted protocol results as separate results, with their composition explicitly outstanding.

Acceptance: the claimed combined nested certificate must actually depend on the protocol accounting and disposition argument, or on a replacement proof establishing those same facts.

## Finding 3: The nested write trace excludes extraction and restoration stores

Priority: P0 for any claim that all nested array writes are certified exclusive.

Evidence: [runN takeOut and putBack](https://github.com/scidonia/ownership/blob/fcab2f39e9bf086cbb5817c947dadc1f68c8c605/Ownership/Nested.lean#L159), [emitted interpretation of restoration](https://github.com/scidonia/ownership/blob/fcab2f39e9bf086cbb5817c947dadc1f68c8c605/OwnershipLcnf/NestedSemantics.lean#L369).

Both operations change fields but append no `Write`. The nested interpreter's `.setArray` also changes fields without adding an event. Thus `∀ w ∈ ws, w.2 = true` covers the recorded writes, not all field stores performed during a nested update.

The checked example below is accepted by `checkN`; its take-out followed by put-back produces `ws = []`. Consequently the all-recorded-writes predicate holds without saying anything about the dispositions of these two stores.

This does not invalidate the result for the trace as defined. It does invalidate describing that predicate alone as a proof about every nested array update.

Agent action:

- Either instrument extraction and restoration with suitable disposition events and establish coverage of the claimed operations, or explicitly restrict the trace claim to designated scalar writes and prove extraction/restoration exclusivity separately.
- Ensure the principal combined theorem states the latter facts as well if the paper claims the entire protocol avoids copying.

Acceptance: every operation included in a no-copy claim is covered by an event or a named disposition theorem actually used in the final result.

## Finding 4: The finite-path theorem remains an abstract call theorem

Priority: P0 for an emitted recursive-function claim; otherwise an explicit scope limitation.

Evidence: [documented residual N10 and index mismatch](https://github.com/scidonia/ownership/blob/fcab2f39e9bf086cbb5817c947dadc1f68c8c605/OwnershipLcnf/PathRecursion.lean#L63), [recurse implementation](https://github.com/scidonia/ownership/blob/fcab2f39e9bf086cbb5817c947dadc1f68c8c605/OwnershipLcnf/NestedSemantics.lean#L358).

The `.recurse` rule invokes `Ownership.Nested.runN body`, where the model body is supplied externally. The finite-path theorem derives contracts for the constructed tail bodies; that is real progress over an arbitrary supplied `ChildContract`. It does not establish that the emitted recursive declaration executes those bodies.

The module also explains that deeper model indices must come from exposed scalar arguments, whereas emitted invocations re-project the selected index from their own path node. This is a concrete expressiveness mismatch, not simply an omitted induction proof.

Agent action: retain the theorem as a finite syntactic-path result under N10, or extend the semantics with actual invocation frames/path data and prove the emitted callee correspondence. Do not call the latter completed merely because the arbitrary model-body contract has been eliminated.

## Finding 5: Two printed theorem excerpts are materially inaccurate

Priority: P0 manuscript repair.

Evidence: [printed nested theorem](https://github.com/scidonia/ownership/blob/fcab2f39e9bf086cbb5817c947dadc1f68c8c605/paper/ownership-skeleton.tex#L594), [actual nested theorem](https://github.com/scidonia/ownership/blob/fcab2f39e9bf086cbb5817c947dadc1f68c8c605/OwnershipLcnf/PathRecursion.lean#L506), [printed put-back theorem](https://github.com/scidonia/ownership/blob/fcab2f39e9bf086cbb5817c947dadc1f68c8c605/paper/ownership-skeleton.tex#L657), [actual put-back theorem](https://github.com/scidonia/ownership/blob/fcab2f39e9bf086cbb5817c947dadc1f68c8c605/Ownership/PutBack.lean#L703).

Claim 6 omits the `some` around `NestedOutcome.ofModel`, despite the left side being optional. It also replaces the actual head/tail construction and its supplied tail body with a simplified list/body presentation. This is more than hiding implicit binders.

Claim 9 prints a child call on unrelated `Hin`/`Hout` and then a put-back on `H`. The actual theorem takes the child call from `(CountedPair.protocol H p c i).2` to `Hc`, and performs put-back on `Hc`. These heap relationships are exactly what the claimed composition needs; the excerpt must preserve them.

Agent action: regenerate faithful excerpts from checked declarations, or label a separately written mathematical summary as such. Include complete types in the appendix. Add a check for excerpt fidelity if the paper continues to present Lean declarations as quotations.

Acceptance: no printed “quoted” theorem silently changes an outcome type, heap boundary, or recursive body.

## Finding 6: The runtime gate checks weaker properties than its summary suggests

Priority: P1 evidence repair.

Evidence: [runtime binding gate](https://github.com/scidonia/ownership/blob/fcab2f39e9bf086cbb5817c947dadc1f68c8c605/scripts/check_runtime_binding.sh#L20), [probe observations and return codes](https://github.com/scidonia/ownership/blob/fcab2f39e9bf086cbb5817c947dadc1f68c8c605/runtime-bridge/RuntimeBridge/Probe.lean#L135).

The generated-C/header checks search whole files for symbol names; they do not by themselves establish call-site identity or ordering. A separate sibling IR-shape gate may establish additional structure, but those obligations should not be attributed to the symbol-presence checks.

The gate's `expect` function checks exit status only. Most ordinary probe modes print observations and return zero regardless of the observed booleans. A check-off run that printed an unexpected copy or incorrect value could therefore satisfy that part of the gate. Check-enabled runs and the `differential` mode provide stronger controls, but they do not make every printed observation an asserted result.

The `differential` mode compares runtime observations against hard-coded expected booleans rather than importing and executing the Ownership model. This is a useful expectation corpus; describe it accordingly or compute predictions from an executable model interface.

The live-alias corpus does use the retained alias after the write. That earlier methodological concern is addressed in this source example. Do not repeat it as a discovered defect.

Agent action: make positive and negative modes return failure when the claimed address, disposition, functional value, or sealed-program result differs. Scope backend checks to the relevant declaration/instruction relation, and report which checks were actually rerun.

## Verified strengths to retain

1. The flat `recognized_write_in_place` theorem specifies a concrete `inPlaceOutcome`, including `writes = [(root, true)]`. This is a stronger and clearer result than a potentially empty trace predicate.
2. `ChildCall.parent` derives suspended-parent preservation from confinement and separation. Preserve this proof structure.
3. Counted-pair accounting includes explicit component increments and restricted destruction, rather than just asserting neutral traffic.
4. The repository already documents model/runtime boundaries, exact toolchain and sibling pins, negative controls, and standard axiom inventories. Much of this needs promotion into the paper, not reinvention.
5. The finite-path derivation genuinely removes an arbitrary model-body contract for its supported finite syntax, while openly documenting the emitted-call gap.

## Revised implementation priorities

| Order | Task | Completion evidence |
| --- | --- | --- |
| 1 | Correct the quoted signatures and state the semantic boundary | Faithful excerpts; abstract/introduction/conclusion match the checked result |
| 2 | Define operation coverage | Extraction, restoration, and designated writes explicitly covered by the claimed guarantee |
| 3 | Compose counted protocol and disposition proofs | A checked execution theorem using the required accounting and restoration argument |
| 4 | Resolve physical-owner interpretation | A representation invariant, or a clear residual obligation with narrower claims |
| 5 | Decide whether to extend call frames | Actual invocation/path semantics, or an explicitly finite model theorem |
| 6 | Strengthen empirical assertions | Wrong observations fail the relevant probe mode and gate |
| 7 | Complete novelty comparison and rewrite | Existing manuscript-review tasks, now informed by the audited scope |

Do not undertake a verified compiler/runtime as a prerequisite to a narrower submission. If choosing the narrow route, present the flat-prefix result as the established compiler-shape connection and the nested protocol as separately verified abstract/counting components whose full execution composition remains open.

## Reproduction of the focused checks

The repository's normal setup is sufficient:

```sh
nix develop -c lake build Ownership OwnershipTest OwnershipLcnf
nix develop -c lake env lean /path/to/ownership-counterexamples.lean
nix develop -c lake env lean /path/to/ownership-dependency-audit.lean
```

Run from the audited repository root. Save the following two code blocks to the filenames used above. No repository source changes are required.

### ownership-counterexamples.lean

```lean
import Ownership.Entry
import OwnershipLcnf.NestedSemantics

open Ownership Ownership.Entry

namespace ImplementationAudit

def H : Heap := (Runner.initHeap 1).2
def env : Env := fun _ => some (.ref 0)
def ctx : Ctx :=
  { us := fun x => if x = 0 ∨ x = 4 then .owned else .dead
    refOf := fun _ => some 0
    mult := fun r => if r = 0 then 1 else 0 }

theorem inv : Inv H env ctx := by
  constructor
  · intro r
    by_cases hr : r = 0 <;> simp [H, Runner.initHeap, Heap.rc, ctx, hr]
  · intro x r _ hr
    have h : r = 0 := by simpa [ctx] using hr.symm
    subst r
    exact ⟨rfl, by decide⟩
  · intro x r hu _
    simp only [ctx] at hu
    split at hu <;> contradiction
  · intro x hu
    simp only [ctx] at hu
    split at hu <;> contradiction
  · intro r o hc
    by_cases hr : r = 0
    · subst r
      have ho : o = ⟨#[.scalar 0], 1, false⟩ := by
        simpa [H, Runner.initHeap] using hc.symm
      simp [ho]
    · simp [H, Runner.initHeap, hr] at hc

theorem entry : EntryInv H env ctx 0 [] := by
  refine ⟨inv, ?_, ?_, ?_⟩
  · exact (initEntryInv 1).uniqueTree
  · exact (initEntryInv 1).separated
  · intro x r _ hr
    have h : r = 0 := by simpa [ctx] using hr.symm
    subst r
    exact MutableFootprint.root (o := ⟨#[.scalar 0], 1, false⟩)
      (by simp [H, Runner.initHeap]) rfl

theorem entry_allows_two_owned_names_for_count_one :
    EntryInv H env ctx 0 [] ∧
    ctx.us 0 = .owned ∧ ctx.us 4 = .owned ∧
    ctx.refOf 0 = some 0 ∧ ctx.refOf 4 = some 0 ∧
    env 0 = some (.ref 0) ∧ env 4 = some (.ref 0) ∧ H.rc 0 = 1 := by
  refine ⟨entry, ?_⟩
  simp [ctx, env, H, Runner.initHeap, Heap.rc]

-- Two heap stores, neither of which appears in the existing Write trace.
def nestedHeap : Heap :=
  { cells := fun r =>
      if r = 0 then some ⟨#[.ref 1], 1, false⟩
      else if r = 1 then some ⟨#[.scalar 7], 1, false⟩
      else none
    next := 2 }

def nestedEnv : Env :=
  fun x => if x = 0 then some (.ref 0)
           else if x = 1 then some (.scalar 0)
           else none

def extractRestore : Nested.NCode :=
  .takeOut 0 1 2 3 1 (.putBack 2 3 1 4 (.ret 4))

def nestedCtx : Ctx :=
  { us := fun x => if x = 0 then .owned else if x = 1 then .scalar else .dead
    refOf := fun x => if x = 0 then some 0 else none
    mult := fun r => if r = 0 ∨ r = 1 then 1 else 0 }

theorem extraction_and_restoration_are_accepted :
    (Nested.checkN nestedCtx extractRestore).isSome = true := by
  decide

theorem extraction_and_restoration_have_empty_write_trace :
    (Nested.runN extractRestore nestedEnv nestedHeap).writes = [] := by
  decide

#print axioms entry_allows_two_owned_names_for_count_one
#print axioms extraction_and_restoration_are_accepted
#print axioms extraction_and_restoration_have_empty_write_trace

end ImplementationAudit
```

### ownership-dependency-audit.lean

```lean
import Ownership
import OwnershipLcnf
import Lean.Util.FoldConsts

open Lean

def dependencies (env : Environment) (root : Name) : NameSet := Id.run do
  let mut todo := #[root]
  let mut seen : NameSet := {}
  while let some n := todo.back? do
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      todo := todo ++ ci.type.getUsedConstants
      if let some v := ci.value? (allowOpaque := true) then
        todo := todo ++ v.getUsedConstants
  return seen

set_option maxHeartbeats 0 in
run_meta do
  let env ← getEnv
  for root in [``OwnershipLcnf.index_path_simulates_model,
      ``OwnershipLcnf.index_prefix_simulates_model,
      ``OwnershipLcnf.recognized_write_in_place] do
    let ds := dependencies env root
    let counted := ds.toList.filter (fun n => (`Ownership.CountedPair).isPrefixOf n)
    let putback := ds.toList.filter (fun n => (`Ownership.PutBack).isPrefixOf n)
    logInfo m!"{root}: CountedPair declarations in closure = {counted}; PutBack declarations = {putback}"

#print axioms Ownership.check_sound
#print axioms Ownership.Entry.checkN_sound_of_entryInv
#print axioms OwnershipLcnf.recognized_write_in_place
#print axioms OwnershipLcnf.index_path_simulates_model
#print axioms Ownership.CountedPair.pair_accounting
#print axioms Ownership.PutBack.putBack_exclusive_of_wellFormed
#print axioms OwnershipLcnf.Runtime.checkExclusive_no_abort
```
