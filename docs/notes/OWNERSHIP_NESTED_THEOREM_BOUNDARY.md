# Nested update: the next theorem boundary

Date: 27 October 2026
Repository: `scidonia/ownership`, main at `15f07b3`
Pinned sibling: `lean-examples` at `66e64334a1c968d829903b8aec8d22f7e3b9fd3f`
Toolchain: Lean `4.35.0-rc3` from the repository flake

This note fixes the boundary of the next theorem before recognizer expansion.
It is a design statement, not a proof: no theorem below is claimed to hold yet,
and the emitted nested callee correspondence is an explicit outstanding
obligation.

## 1. Target

One pinned `setAt` `Path.index` path, from the root array through one child
array to a leaf, with a genuine heap-changing child update:

1. the root's selected slot is checked and the child array is extracted;
2. the child update is called with an in-bounds index and a nonzero replacement;
3. the child's designated leaf slot is written;
4. the extraction is restored, and the returned child reference is put back into
   the root's selected slot.

The model instance is the shape `OwnershipTest/RecursiveProof.lean` already
replays: `takeOut`, `callAt` with an embedded body, `putBack`, and a `setArr`
inside the body. The theorem's concrete instance extends that fixture with a
second root slot holding a scalar sibling, so the preservation half observes a
cell that is neither extracted nor restored.

The LCNF `setAt` `Path.index` alternative is the one `scripts/dump_executor.lean`
prints (size 81, digest `17644656787385327013`): bounds test, exclusive-array
assertion, `takeOut`, the two projection increments, the child `assertExclusive`,
the recursive `setAt` call, and `Array.set` for the restore. The nested
alternative and the helper bodies it calls are captured in
`docs/notes/artifacts/setAt-nested.lcnf.txt`, with provenance in
`docs/notes/OWNERSHIP_NESTED_CAPTURE.md`; the recognizer and its model
correspondence are the remaining tasks of the emitted-protocol step.

## 2. Observation boundary

The theorem observes, at the return of the top-level model run under the
restricted semantics:

- no ownership fault is reached and every write in the trace selects the
  exclusive branch;
- the designated leaf cell holds the replacement, at a nontrivial child index
  and with a nonzero replacement value;
- the child's restored slot holds the original extracted element;
- the root's sibling slot and any subtree under it are unchanged;
- the parent and the child references are retained by their respective
  variables;
- cells outside `MutableFootprint H root` are unchanged;
- the returned heap, environment and context satisfy `EntryInv` for the
  caller's root and client list.

The theorem does **not** observe or claim the LCNF replay correspondence, the
index's own `inc`/`dec` effects in the emitted code, or any physical runtime
counter.

## 3. Supported instructions

Model level: `takeOut`, `callAt`, `putBack`, `ret`, and inside the body `base`
with `let`, `checkAlias` and `setArr`. Bodies are `CountFree`: no explicit
`inc` or `dec`, so the caller's multiplicities still describe the heap the body
leaves.

Emitted level, once captured: the bounds `Array.size`/`Nat.decLt` test, the
array exclusivity assertion, `takeOut`, the pair projections, the child
exclusivity assertion, the recursive `setAt` call, and `Array.set` for the
restore. Joins and callbacks are out of scope; unsupported control flow must be
rejected rather than flattened.

## 4. Entry relation

`EntryInv H env c root client` supplies the handle/count invariant, the unique
tree, client separation and root completeness. The call site additionally
requires the checker's operand facts for the call (`state` owned with
multiplicity one, `path` and `x` scalar, `result` dead), the state-indexed heap
premise `TakeOutsOK H env code`, the heap/program agreement `Agrees H env code`,
and, for the confinement half, the extraction annotation premise
`AnnotationsIn H child body`.

`RootsComplete` is the checker's completeness condition on owned variables. It
is not completeness of physical runtime roots or of the client's own roots;
those need separate representation facts.

## 5. Callee contract

For the admitted model body, `Ownership.Entry.callAt_frame_confined` already
supplies fault-freedom, exclusive writes, exit through the reference handed to
the call, and preservation of every cell outside that reference's mutable
footprint, given `AnnotationsIn`, the body's check, the return-variable fact,
`Inv` at the isolated context and `TakeOutsOK`.

The child-call contract adds what the frame contract deliberately does not name:
the child's own designated write (its index and replacement operands bound by
the child's environment), the child's required `EntryInv`, and the child's
returned state as the input to the caller's continuation. In the first theorem
this contract is a hypothesis about an admitted model body. The connection to
the emitted recursive callee is an outstanding obligation, and the theorem must
not be described as certification of the recursive executor until that link is
proved.

## 6. Schematic statement

```lean
theorem nested_index_update
    (hcheck : checkN c code = some c')
    (hentry : EntryInv H env c root client)
    (hok : TakeOutsOK H env code)
    (hag : Agrees H env code)
    (hann : AnnotationsIn H child body)
    (hinBounds : …)            -- both path indices in bounds
    (hchild : ChildUpdateContract child ctx body leaf idx repl …) :
    ∃ H' env' v ws,
      runN code env H = .done H' env' v ws ∧
      (∀ w ∈ ws, w.2 = true) ∧
      -- the designated leaf write landed
      H'.cells leaf = some (leafObj.setSlot idx (.scalar repl)) ∧
      -- the extracted element was restored to the child's slot
      H'.cells child = some (childObj.setSlot selected (.ref leaf)) ∧
      -- the sibling slot and its subtree are untouched
      H'.cells root = some (rootObj.setSlot siblingSlot siblingValue) ∧
      -- outside the root's mutable footprint nothing moved
      (∀ q, ¬ MutableFootprint H root q → H'.cells q = H.cells q) ∧
      -- the caller's entry condition is re-established
      EntryInv H' env' c' root client
```

The exact field names and the `setSlot` helper are illustrative; the boundary
they state is what the implementation must fix.

## 7. Non-claims

- No general recursion, executor or compiler certification.
- The LCNF correspondence is conditional: the recognized prefix's execution is
  related to the model term, and the emitted recursive callee's body is not
  captured.
- No joins, callbacks or general LCNF fragment.
- No physical runtime reference-count claim; the model's counts are the
  restricted semantics' counts.
- `RootsComplete` is not a statement about all physical roots.
- The index's own `inc`/`dec` pair in the emitted prefix is not yet modelled.

## 8. Boundary acceptance

- The observation boundary, supported instructions, entry relation, callee
  contract and non-claims are stated above.
- The concrete instance is fixed with a sibling root slot, a nontrivial child
  index and a nonzero replacement.
- The pinned `setAt` digest and the sibling revision are recorded.
- Every premise is named as supplied by `EntryInv`, by the checker, or assumed
  (`Agrees`, `AnnotationsIn`, the child contract).

## 9. Obligations before certification

1. Capture the pinned nested alternative and its helper bodies with the
   source/sibling commit, compiler and options.
2. State and prove the emitted recursive callee contract, including the
   take-out pair's increments and disposal.
3. Discharge `Agrees` and `AnnotationsIn` compositionally from path
   interpretation and the structural invariant.
4. Add the recursive call rule connecting finite bodies to the fixed executor.
5. Connect the represented prefix, the replay, the heap counts and the runtime.

Status (27 October 2026): obligations 1 and 3 are done.
`OwnershipLcnf/NestedSemantics.lean` proves the conditional prefix
correspondence (`index_prefix_simulates_model`, consuming `projectNested`, over
the N1–N12 contracts in its header), and `OwnershipTest/NestedEmitted.lean`
instantiates it with the boundary's observations: the changed leaf, the restored
child slot, the untouched sibling, outside-footprint preservation and a
re-established `EntryInv`. `Ownership/Path.lean` proves the reachability
transitivity lemmas and derives `Agrees` and `AnnotationsIn` from a level chain;
`OwnershipTest/PathAgreement.lean` is the certificate that obtains both from
those theorems and feeds them to `takeOutsOK_of_entryInv` and
`callAt_frame_confined`. The emitted machine-level `NestedAgrees` still needs the
recognizer's operand identities and the reified machine fields (the model-field
part is derived in the certificate). The child-call contract is a hypothesis in
both. Obligations 2, 4 and 5 remain.
