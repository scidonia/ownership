# Handoff: fractional ownership and borrowing in Lean

Date: 14 November 2026  
Reviewed repository: [scidonia/ownership](https://github.com/scidonia/ownership)  
Reviewed revision: [`c0a2e31dd95ecfdb410eebeeb9a16316e63ed132`](https://github.com/scidonia/ownership/tree/c0a2e31dd95ecfdb410eebeeb9a16316e63ed132)

## Recommendation

Proceed with the new capability-ledger architecture. It is a better foundation for a reusable Lean ownership subsystem than concentrating solely on reference-count certificates for individual update protocols.

The design directly addresses fractional readers, disjoint writable slices, lexical borrowing, reborrowing and disposal. Its most important decision is that ordinary Lean values carry inert names, while the checked context carries authority. Duplicating a name therefore does not duplicate permission.

Before implementing the ledger on top of the current value-admission mechanism, repair its interpretation: a bijection to a first-order value type does not establish that the original Lean value contains no closures or retains no protected storage.

Prioritise a byte-array core, its invariant and primitive-preservation proofs. Treat generic value admission as a separate extension. Retain the older counted-heap work for a later backend connection where physical reference counts matter.

## Evidence and present status

This assessment is based on the checked-in design, brief and implementation. Lean, Lake and Nix were unavailable in the review environment; the example below was not independently elaborated. Its mathematical construction is explicit and should become a checked regression immediately.

| Component | Status at the reviewed revision |
| --- | --- |
| Distinct allocation/capability/loan/lifetime identifier types | Implemented in `Cap/Id.lean` |
| Exact shares using a context-wide denominator | Implemented with arithmetic lemmas in `Cap/Share.lean` |
| Bounded intervals, views and splitting facts | Implemented in `Cap/Footprint.lean` |
| Closed first-order code universe | Implemented in `Cap/Code.lean` |
| Bijection certificate and admission command | Implemented in `Cap/Admission.lean`; warrants a weaker interpretation than the current comments claim |
| Reflective one-transfer usage check | Prototype in `bench/OwnedStatic.lean`; not the proposed subsystem's soundness foundation |
| Context ledger and decomposition/loan invariants | Proposed |
| Typed core, operational semantics and execution-safety theorem | Proposed |
| Hidden-index elaborator, interpreter and backend refinement | Proposed |

The earlier suspended-root issue has been acknowledged and proved as an impossibility result in `OwnershipTest/IsolatedAccounting.lean`. Do not advertise the old two-level theorem as a usable composition result. The proposed ledger offers a route to repairing the underlying representation, but that repair is not implemented yet.

## Design decisions to preserve

| Decision | Required consequence |
| --- | --- |
| Handles are identifiers, not storage wrappers | Copying a host handle never creates a second capability entry |
| Current-context authority | Every access is justified against the context at that program point |
| Fractional sharing | Overlapping readers share one conserved access budget |
| Spatial splitting | Disjoint slices may each have full write access over their own footprints |
| Separate disposal entitlement | A full borrowed view cannot free the allocation |
| Explicit lender suspension | A delegated parent cannot authorise conflicting access |
| Recorded decomposition and loan ancestry | Rejoining checks provenance and removes descendants before restoration |
| Indexed program composition | Each instruction's output context supplies the next instruction's input context |
| Fresh closed executions | Replaying an immutable program creates a fresh arena |
| Independent semantics and backend | Interpreter correctness and physical uniqueness have separate proof obligations |

A suspended parent is bookkeeping, not an additional active share. Conversely, the obligations represented by a suspended frame must remain in global accounting even when the callee cannot name that frame.

Keep the distinction between the access environment and the ownership ledger explicit. Isolating executable names must not erase outstanding ownership or disposal obligations.

## P0: correct value admission before relying on it for confinement

### The current inference is too strong

The code universe contains first-order constructors, and `SafeValue T` contains a bijection `T ≃ El code`. The comments infer that a type hiding a live resource cannot have such a code.

That inference is false for closures. Extensional equality of functions does not describe their compiled environments.

There is a constructive bijection:

```text
(Unit → Nat) ≃ Nat

encode(f) = f()
decode(n) = fun () => n
```

Every function on `Unit` is extensionally equal to the constant function with its value at `()`. The inverse laws require no non-standard axiom.

Add the following regression, adjusted only as needed to match the project's syntax:

```lean
import Cap.Admission

open Cap

abbrev NatThunk := Unit → Nat

def thunkBij : Bij NatThunk (El .nat) where
  toFun f := f ()
  invFun n := fun _ => n
  left_inv f := by
    funext u
    cases u
    rfl
  right_inv n := rfl

#print axioms thunkBij
#admit_type NatThunk thunkBij
```

Under the inspected rule, this has the required certificate type and a proof using the permitted foundations. Confirm the command's actual result in the pinned environment.

A value of the admitted type can retain an array:

```lean
def retainBuffer (bytes : Array UInt8) : NatThunk :=
  fun () => bytes.size
```

In particular, the present `SafeType.new : Array UInt8 → T` admits an initializer of that shape when `T = NatThunk`. The bijection does not prove that the result drops its captured buffer. Whether the compiler retains or optimises away a particular capture is a backend fact, not a consequence of the bijection.

This challenges the admission rationale. It is not a demonstrated exploit of a completed mutable subsystem, because that subsystem has not yet been implemented.

### Recommended repair

For the initial core, store bytes and expose scalar reads, writes and independent snapshots. This is already sufficient for the design's principal example.

For later generic values:

1. Store only the canonical coded representation `El code` internally. Do not store arbitrary `T` merely because a bijection to `El code` exists.
2. Use user-supplied conversion proofs to establish logical representation properties, such as round trips. Do not interpret them as physical no-capture proofs.
3. Keep the actual arena storage out of arbitrary user initializers, converters and callbacks. Inputs must be detached data or controlled object-language values.
4. Specify conversion, export and snapshot behaviour at the execution boundary. A value leaving the subsystem must not retain an executable route to protected storage.
5. Preserve the existing axiom audit, but describe its purpose accurately: it checks proof dependencies; it does not establish representation confinement or absence of closure capture.

A schematic storage entry for a later coded-value backend would carry a code and `value : El code`, rather than a hidden arbitrary type `T` and `value : T`. This is a design direction, not an assertion that changing that field alone proves the backend safe.

If arbitrary `T` storage is retained instead, it needs a substantially stronger operational representation/confinement contract. Do not rename the bijection as that contract.

### Documentation changes

Update `Cap/Admission.lean`, `Cap/Code.lean` where relevant, and the printable brief:

- Distinguish the absence of function constructors in `Code` from the types that can be isomorphic to its denotations.
- Remove the claim that no resource-retaining type can be bijective with a coded type.
- State whether admission means logical encodability, canonical storage eligibility, or an operational confinement theorem.
- Label initializer and allocation examples as sketches until their controlled semantics exists.

Explicit certificates remain useful. The necessary correction is what they establish; this does not require switching to automatic deriving or typeclass-based admission.

## P1: implement the ledger and prove primitive preservation

Define the ledger before expanding the frontend. It should contain allocation metadata, unique disposal entitlements, capability states, decomposition provenance, lifetimes and loan dependencies.

For each byte of a live initialized allocation, terminal budget holders must sum to one. Active and deliberately retired terminal claims contribute; suspended ancestors do not contribute again. Access also requires the appropriate state, lifetime and ceiling.

The invariant must establish more than a numeric sum:

- Every capability has a valid allocation, bounded footprint and unique provenance.
- Split edges conserve shares or partition footprints as appropriate.
- Write authority requires a full share and a read-write ceiling.
- Restoration disables all delegated descendants before reactivating a lender.
- Every allocation has exactly one disposal entitlement.
- Outstanding loans prevent disposal.
- Fresh identities cannot reactivate stale handles.
- Suspended obligations remain represented across calls and scopes.

Use a declarative transition judgement and an executable checker that produces a proof of that judgement. The reflective occurrence counter can remain a diagnostic, but should not be the authority for the new subsystem.

The main proof target is:

```text
Typing Γ program Result Q
and Realizes heap Γ
and the environment matches Γ
imply ownership safety of every reachable execution prefix.

If execution returns value in heap',
then Realizes heap' (Q value).
```

Prove bounded-program termination separately. Give ownership faults an explicit semantic representation so that an illegal operation cannot disappear from the safety statement.

Do not base the theorem on module privacy or identifier secrecy. The checked program and controlled runner must enforce legal transitions even when host values or program descriptions are duplicated.

## P1 acceptance example: split, read, reconstruct and dispose

Implement the design's 64-byte program first:

1. Allocate a zeroed 64-byte buffer with one root owner and disposal entitlement.
2. Begin a full mutable loan and suspend the lender.
3. Split the loan into `[0,32)` and `[32,64)` full writable views.
4. Fill the left view with `1` and the right with `2`.
5. Split the right view into two half-share readers and scan both.
6. Rejoin the readers and then the two spatial views.
7. End the loan and restore root ownership through the prescribed transition.
8. Export an independent immutable snapshot.
9. Free the allocation and return the snapshot and scalar results.

Expected results: the snapshot contains 32 ones followed by 32 twos; both scans of the right half return `64`; successful termination leaves no live allocation or unresolved loan.

The same definitions must support negative controls:

| Attempt | Required outcome |
| --- | --- |
| Join two aliases of one capability identifier | Refuse duplicate consumption |
| Write through a half-share reader | Refuse insufficient authority |
| Reconstruct a read-only loan to a full share and write | Refuse the access ceiling |
| Use a parent after spatial splitting | Refuse suspended/consumed authority |
| Use a reader alias after its join | Refuse the consumed identifier |
| Free while a loan or fragment remains | Refuse outstanding dependencies |
| Join different allocations or mismatched intervals | Refuse identity/footprint/provenance mismatch |
| End an outer loan while a reborrow remains live | Refuse lifetime dependency violation |
| Replay a saved close operation in the same session | No valid composition from the post-close context |
| Run a closed program twice | Two independent fresh executions |
| Retain the original backing storage through initialization/export | Prevent by construction or discharge an explicit confinement contract |

Exercise invalid cases through direct core-certificate construction as well as the frontend. A surface rejection is insufficient if another public path can construct the forbidden execution.

## P2: add scope composition, then the programmer-facing surface

After basic splits and joins work, implement nested lexical reborrowing. Distinguish the callee's accessible names from the complete global ledger. Prove a frame rule that preserves suspended ownership and disposal obligations while a callee works on its authorized footprint.

Require a closed nested example with different indices/footprints and every hypothesis discharged. Kernel acceptance of a conditional theorem is insufficient evidence that its intended entry states exist; retain the isolated-accounting impossibility regression.

The elaborator should infer names, shares, lifetime relationships and post-contexts while emitting kernel-checked derivations. Hide indices after they have been threaded through composition. Do not existentially discard the matching intermediate contexts needed by bind.

Begin with explicit permission return and reconstruction. Automatic retirement, non-lexical lifetimes, escaping borrowed results and resource-bearing closures can follow after their semantics and confinement proofs exist.

## P3: connect a mutable backend and measure its costs

Keep three theorem families separate:

| Family | Guarantee |
| --- | --- |
| Permission soundness | Only authorized accesses execute; loans, joins and disposal preserve the ledger invariant |
| Backend refinement | Mutable execution implements the reference program and its observations |
| Runtime representation | Actual storage and compiler behaviour satisfy a specified exclusivity/no-copy property |

Logical full permission does not automatically imply Lean runtime RC=1. In particular, spatial splitting must not create two owning Lean `Array` wrappers and then assume both writes avoid copying. Keep one backing allocation owner with checked slice access, or use a dedicated mutable-buffer representation with an explicit contract.

The older reference-count development may support the runtime-representation proof. It remains useful, but should not be confused with the new permission algebra.

Measure dispatch, ledger lookup, allocations, copies and snapshot costs separately. Erasure of proof fields does not imply that an AST, ledger or capability lookup disappears. Specialization is a later semantics-preserving optimization.

## Immediate implementation order

| Priority | Task | Acceptance gate |
| --- | --- | --- |
| P0 | Add the `NatThunk` admission regression and correct the rationale | The project acknowledges the extensional/representation distinction |
| P0 | Fix the initial storage/initializer boundary | Arbitrary admitted host values cannot retain the protected backing storage |
| P1 | Define ledger, full invariant and primitive transitions | Each transition has a preservation proof |
| P1 | Implement reference byte-array execution | The 64-byte example returns the specified result and closes all resources |
| P1 | Add adversarial core and surface controls | Invalid aliases, joins, writes and disposal cannot receive legal certificates |
| P2 | Prove nested borrow/frame composition | A closed nested example retains suspended obligations and discharges every premise |
| P2 | Add hidden-index elaboration | Accepted surface programs produce checked core derivations |
| P3 | Implement and refine the mutable backend | Every primitive preserves the representation relation |
| P3 | Specialize and evaluate | Performance claims are tied to the actual generated implementation |

This plan establishes a controlled borrowing subsystem inside Lean. It does not claim to retrofit affine typing onto arbitrary Lean code or to cover Rust's full language. Its prospective value is the combination of a usable permission discipline, functional specifications and separately justified implementation guarantees.

## Source entry points

- [Detailed design](https://github.com/scidonia/ownership/blob/c0a2e31dd95ecfdb410eebeeb9a16316e63ed132/docs/lean-fractional-ownership-design.md)
- [Printable brief source](https://github.com/scidonia/ownership/blob/c0a2e31dd95ecfdb410eebeeb9a16316e63ed132/brief/ownership-subsystem-brief.tex)
- [Admission rule](https://github.com/scidonia/ownership/blob/c0a2e31dd95ecfdb410eebeeb9a16316e63ed132/Cap/Admission.lean)
- [Value-code universe](https://github.com/scidonia/ownership/blob/c0a2e31dd95ecfdb410eebeeb9a16316e63ed132/Cap/Code.lean)
- [Share arithmetic](https://github.com/scidonia/ownership/blob/c0a2e31dd95ecfdb410eebeeb9a16316e63ed132/Cap/Share.lean)
- [Footprints](https://github.com/scidonia/ownership/blob/c0a2e31dd95ecfdb410eebeeb9a16316e63ed132/Cap/Footprint.lean)
- [Isolated-accounting impossibility regression](https://github.com/scidonia/ownership/blob/c0a2e31dd95ecfdb410eebeeb9a16316e63ed132/OwnershipTest/IsolatedAccounting.lean)
