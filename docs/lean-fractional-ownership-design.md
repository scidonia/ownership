# Lean Ownership and Borrowing with Fractional Uniqueness

Build a Lean library and embedded programming language for safe mutable byte arrays, with fractional permissions, disjoint mutable slices, lexical borrowing and reborrowing. Users write a small ownership-aware programming surface; Lean checks an indexed representation whose permission contexts are inferred and hidden from ordinary source code.

The central decision is to combine a fractional-uniqueness resource algebra with a checked context-transition calculus. Ordinary Lean handles remain duplicable. Access authority lives in the current checked context, and no handle can perform memory operations outside the controlled interpreter.

The first implementation uses explicit return and join of permissions. An optional scoped layer can recover unused borrows automatically only after proving that all affected capabilities are inaccessible. This separates a tractable core from the stronger lifetime mechanism needed for Rust-like ergonomics.

This is a proposed implementation design. Lean snippets describe interfaces and theorem shapes; they are not a compiled library. The intended guarantees concern the defined subsystem and its interpreter, rather than arbitrary Lean programs or the complete Rust language.

## Goals and initial scope

The subsystem should provide the following capabilities.

| Capability | Required behaviour |
| --- | --- |
| Unique ownership | A root owner controls one allocation and its disposal authority |
| Full borrowed access | A borrower may update its footprint but cannot dispose of its allocation |
| Fractional access | Multiple compatible readers can share one footprint |
| Spatial splitting | Disjoint footprints can each retain full write permission |
| Lifetime scoping | A loan temporarily restricts lender access and restores it at a checked boundary |
| Reborrowing | A borrower may delegate a smaller footprint or a shorter-lived capability |
| Hidden accounting | Contexts, fractions and proof terms are inferred where practical |
| Static rejection | Invalid access transitions cannot receive an accepted typing certificate |
| Executable semantics | A reference interpreter gives the calculus an explicit operational meaning |
| Mutable backend | A later implementation refines that semantics while keeping raw storage internal |

Start with initialized byte arrays and half-open interval footprints. Include scalar reads and writes, allocation, freeing, splitting, joining, explicit borrowing, conditionals, bounded loops and immutable snapshot export.

Defer general recursive object graphs, references stored in mutable cells, arbitrary higher-order callbacks, lifetime polymorphism across stored closures, non-lexical lifetime inference, interior mutability, atomics and concurrent execution. These introduce distinct proof obligations and must not enter through an unrestricted lifting operation.

The first release should offer unrestricted reuse of ordinary immutable scalar data, explicit linear accounting of resource claims, and scoped temporary access. It need not implement a general semiring of usage grades for all Lean values.

A successful first example should allocate an array, split it into disjoint writable slices, update both, fractionally split one slice into readers, rejoin those readers, restore the array, export a snapshot and free the allocation. A corresponding invalid example should fail after an attempted write through a consumed reader handle.

## Relationship to fractional uniqueness

[Functional Ownership through Fractional Uniqueness, Marshall and Orchard, OOPSLA 2024](https://doi.org/10.1145/3649848) supplies the conceptual foundation: a distinct uniqueness grade, identity-indexed resources, fractional borrowed grades, explicit split and join, continuation-based borrowing, and distribution of borrowing over products. Its core uses lexical borrowing; array-slice distribution and the lifetime machinery below are extensions rather than claims about the paper.

The proposed Lean design uses a context ledger to enforce these ideas inside an unrestricted host language. It adds explicit disposal authority, interval footprints, loan dependencies, checked program certificates and a controlled execution boundary.

| Design choice | Purpose |
| --- | --- |
| Separate unique and borrowed states | Full access does not by itself confer ownership |
| Exact fractional arithmetic | Permission cannot be manufactured by rounding |
| Allocation identity on every view | Claims for different arrays cannot be joined |
| Distribution over disjoint footprints | Generalize partial views to array slices |
| Explicit restoration in the core | Make permission conservation locally checkable |
| Optional scope recovery | Support unused borrower handles without losing authority |
| Indexed elaboration | Hide bookkeeping while preserving its dependencies |

[From Linearity to Borrowing](https://doi.org/10.1145/3764117) is a complementary reference for scoped borrowing and the distinction between resource permissions and structural permissions. [RustBelt](https://doi.org/10.1145/3158154) informs the separation between live-loan access and later restoration. Neither is assumed as an imported theorem: this subsystem requires its own definitions and proofs.

## Architecture and the execution boundary

Use four layers.

1. A resource algebra defines identity, footprints, fractions and decomposition.
2. A typed core defines legal transitions and structured control flow.
3. An elaborator produces core programs and kernel-checked certificates.
4. An interpreter executes certified closed programs; a mutable backend is subsequently related to the reference interpreter.

The elaborator may be complex, heuristic or incomplete. A successful elaboration must always produce a proof accepted by the kernel. The elaborator is not itself the authority for memory safety.

The internal representation should be a first-order object-language program with explicit bindings. This prevents arbitrary Lean closures from silently retaining executable resource access. Scalar Lean computations may be imported through a separately specified pure interface; resource-capturing functions are not ordinary host functions in the initial core.

Lean-side handles may contain an arena marker and capability identifier:

```lean
-- Interface shape only.
structure Handle (ρ : Type) where
  id : CapId
```

The runtime buffer is not a field of this handle. A handle is a name, not a resource token that becomes linear by being placed in a structure.

Every primitive needs an authorisation derivation for the current context. Duplicating a handle duplicates its name, while the context still contains only one claim. A consumed identifier has no authorisation even if a host-level value mentioning it survives.

Constructors may be hidden for ergonomics. Safety must follow from the checked judgement and runner contract, not from private names, module visibility, an inability to guess identifiers, or the opacity of a definition.

Do not export a runner that executes a program against an arbitrary existing arena and merely assumes its starting context. In particular, a saved action that frees an allocation must not be replayable against the same mutable heap with its original precondition.

The closed runner creates a fresh arena for every execution. Reusing an immutable program description is allowed; each execution starts with new storage and a fresh identity namespace.

## Resource identities and exact shares

Maintain distinct identifier types for allocations, capabilities, loans and lifetimes. Use monotonically fresh names within an arena, or names with generations. A consumed capability identifier must never be recycled in a way that makes an old handle valid again.

An allocation entry records its length, initialized extent, storage type and disposal status. Initially all allocated bytes are initialized. Adding uninitialized memory later requires a separate initialization predicate.

Represent a footprint as an allocation identity and a bounded half-open interval.

```lean
-- Schematic mathematical data.
structure Interval where
  lo : Nat
  hi : Nat
  ordered : lo ≤ hi

structure View where
  alloc : AllocId
  range : Interval
```

Require the interval to lie within the named allocation. Natural-number offsets in the reference model are not machine pointers; lowering must separately establish that offsets and lengths fit the backend address arithmetic.

Use exact shares satisfying 0 < q ≤ 1. A proof model can use rational numbers; an executable representation can use normalized positive numerator and denominator fields with decidable equality and order. Halving is sufficient for the earliest frontend, but the algebra should not assume every later join is a halving inverse.

Zero is an accounting value, not an issued usable capability. Empty intervals require no byte-access budget; they cannot manufacture disposal authority or prove exclusive ownership of a nonempty allocation.

Distinguish the uniqueness marker from the rational fraction 1. In the mathematical interface, use U(a,F) for owned authority over a footprint and B(κ,a,F,q) for a borrowed view. The root allocation also has a separate, nonduplicable disposal entitlement. A full borrowed view B(κ,a,F,1) may write but may not free the allocation.

For the first implementation, owned parts are fragments of one root allocation owner. They are not independently disposable allocations. Returning a part to the owner requires a certified reconstruction, not merely an interval calculation.

## Context ledger and conservation invariant

A context consists of allocation metadata, a finite capability map, a decomposition forest, a lifetime forest and loan records. Capability keys are unique. A claim contains its allocation, footprint, share, access ceiling, lifetime and provenance.

The access ceiling is either read-only or read-write. It is useful for a read-only loan with fraction 1: collecting all readers must not turn an explicitly read-only loan into a writer. Write access requires both q = 1 and a read-write ceiling. Splits inherit the ceiling, and joins cannot increase it.

Track the following capability states.

| State | Meaning |
| --- | --- |
| Active | The claim may authorise operations |
| Suspended | Its budget has been delegated to descendants |
| Retired | Its budget is held for reconstruction but grants no access |
| Consumed | Its identifier no longer denotes a live claim |

The decomposition forest records fractional splits, spatial splits and loan delegation. A suspended parent is bookkeeping, not an additional active copy of its budget.

For each allocated byte x, sum the shares at the terminal budget holders whose footprints contain x. Terminal holders include active leaves and any deliberately retired leaves. Exclude suspended ancestors and consumed nodes.

$$
\mathrm{Budget}_{\Gamma}(a,x)
=
\sum_{\substack{c\in \mathrm{Frontier}(\Gamma)\\c.a=a,\;x\in c.F}}c.q
$$

Before disposal, require this budget to equal 1 at every byte of a root-owned initialized allocation. A spatial split preserves the equation because each byte belongs to exactly one child. A fractional split preserves it because child shares sum to the parent share. Retiring a claim preserves its contribution but removes its access authority.

The equation is necessary but not sufficient. The invariant must additionally establish:

- Each issued capability has exactly one provenance and a valid allocation.
- Decomposition edges satisfy their footprint, share and ceiling equations.
- Every usable claim belongs to a live lifetime or to current owned access.
- A suspended lender grants no conflicting access through an alias.
- Restoring a parent removes or disables every descendant budget holder.
- Disposal authority occurs once per live allocation and cannot be inferred from shares.
- Capability names remain fresh across allocation, branch execution and restoration.
- Subtasks, if later introduced, have disjoint accounting domains.

This prevents a superficial proof that counts claims but overlooks reactivation of an ancestor or a second disposal entitlement.

## Primitive transition rules

Every transition has a precise effect on the ledger and, where applicable, the logical heap. The resource predicates below are propositions about the current context; they are not reusable evidence that an IO operation remains valid forever.

### Allocation and disposal

alloc(n) creates a fresh allocation a, a root capability c over [0,n) with full access, and the unique disposal entitlement. It initializes the bytes to zero. Its result determines the post-context.

free(a,c) requires the root-owned view, the disposal entitlement, no outstanding decomposition fragments, and no loans depending on the allocation. It consumes the claims and removes the allocation. Full permission over a borrowed footprint is insufficient.

Initially require explicit free at successful termination. A later lexical allocation combinator may insert free only after its typing derivation establishes the same conditions.

### Reading and writing

readByte(c,i) requires an active claim, a live applicable lifetime, positive share, and an index within its footprint. It returns an immutable byte without changing permissions.

writeByte(c,i,v) requires the same validity conditions plus share 1 and a read-write ceiling. It changes the byte and preserves the access ledger. Do not attach a value equality to an ownership assertion and then pretend a write preserves it; memory-content refinements are a separate layer.

The first interface reads and writes UInt8. A generic read of arbitrary Lean values would need Copyable, move or borrow rules. It must not duplicate nested ownership-bearing values by returning an unrestricted result.

### Fractional splitting

splitFraction(c,q1,q2) consumes active c = (a,F,q), requires positive q1 and q2 with q1 + q2 = q, and creates fresh c1 = (a,F,q1) and c2 = (a,F,q2). Both inherit lifetime, ceiling and allocation identity.

joinFraction(c1,c2) consumes two distinct active claims of the same allocation, footprint, lifetime and compatible provenance. The output share is q1 + q2 and must be at most 1. A read-only ceiling remains read-only.

The initial implementation permits joins of certified sibling fragments. This is a deliberate restriction relative to an unrestricted same-resource fractional join. A later normalizer can support arbitrary compatible recombination after proving that it reconstructs the same conserved authority.

Never accept joinFraction(c,c), even if two Lean variables contain the same identifier.

### Spatial splitting

splitAt(c,k) requires an in-bounds split point and replaces [lo,hi) by [lo,k) and [k,hi), both at the original share. Each child receives fresh identity and decomposition evidence.

joinSpatial requires the appropriate two descendants, the same allocation, matching shares and ceilings, exact adjacency and coverage, and no outstanding subloans. Overlapping, reversed or merely same-length slices do not establish reconstruction.

For owned access, the two parts remain fragments of one root owner. Neither child acquires a second disposal entitlement.

### View restriction

A convenient subview operation must account for the complement. It can return the selected interval together with a residual view, or suspend the enclosing view through a scoped loan. It must not return an independent writable child while leaving the original full-footprint writer active.

## Lifetimes and explicit borrowing

Start with nested lexical lifetimes. A lifetime is a fresh node in a forest, with state live or ended. An outlives relation follows ancestry. Lifetime names are not user-supplied reusable tokens.

beginBorrow(c) suspends an active owned or borrowed claim and introduces a loan node with a fresh lifetime κ. It issues a borrowed child covering the delegated footprint and records the exact parent authority to restore. Delegation preserves the share; it does not reset a fractional parent to share 1.

A whole-array mutable loan of unique owned access therefore creates a borrowed claim at share 1 with a read-write ceiling. A whole-array read-only loan creates a borrowed claim with a read-only ceiling. The lender cannot use its suspended claim during either loan.

Partial lending is derived by spatially splitting first and lending only the selected fragment. The other fragments remain available.

Reborrowing an existing borrower creates a nested loan. The child lifetime λ must be within the parent lifetime κ. During the nested loan the delegated parent fragment is suspended. Ending λ restores that parent fragment, rather than jumping directly to root ownership.

The explicit core ends a loan only when its borrowed authority has been reconstructed to the expected returned footprint, share and ceiling and all nested loans have ended. It consumes the returned borrower, marks the lifetime ended, and restores a fresh lender capability. The original lender identifier remains stale.

Fresh restoration handles make the lifetime transition visible in certificates and prevent accidental resurrection of an old name. A surface binding may be rebound to the fresh handle automatically.

The restoration postcondition states ownership of the updated data. It does not assert that the bytes are unchanged. Spatially unrelated data is unchanged under the corresponding frame theorem.

This design admits full mutable reborrowing as a loan-delegation operation in addition to repeated fractional read splitting. The two operations have different bookkeeping and must not be conflated.

## Scoped recovery and discarded borrowers

The explicit core is linear in its accounting: every issued fragment must be returned, joined, retired under a defined rule, or consumed by a legal operation. Ignoring a handle in a Lean expression does not erase its ledger entry.

To offer affine borrower syntax, add a derived scoped interface rather than allowing arbitrary weakening of the permission ledger.

A controlled retire operation changes an active borrowed fragment to retired. It removes access but preserves its budget and its parent reconstruction information. A retired fragment cannot be used for a read, write or new loan. The frontend may insert retirement for an unused local borrower.

For the first affine extension, scoped closure may reconstruct a loan subtree when:

1. Execution is sequential and all nested borrowed scopes have ended.
2. No remaining external context refers to active descendants of the scope.
3. The result contains only permitted scalar or immutable exported data.
4. No continuation, stored computation or task retains runnable access to scope descendants.
5. All descendant budgets can be collected exactly, including retired leaves.
6. The closing transition invalidates every descendant identifier before issuing restored authority.

These conditions form a scope-closing certificate. They are not inferred solely from the fraction sum or the fact that the callback returned.

A particularly simple initial scope combinator returns only pure data and restores the lent resource automatically. A more expressive callback can return updated owned resources only after the core explicitly reconstructs them. Do not start by permitting an arbitrary dependent pair or host closure as a scope result.

This extension needs its own preservation and scope-confinement proof. Its intended effect is automatic return at a sealed boundary, not automatic reactivation whenever the programmer stops mentioning a handle.

Exceptional exits need analogous cleanup certificates. Until those exist, reject effectful exceptions in borrowed scopes instead of treating a failed callback as proof that loans have ended.

## Indexed computation type

Use a judgement with a result-dependent post-context.

```text
Γ ⊢ p : α ▹ Q
```

Here Q maps the returned value to its resulting permission context. This is needed when allocation or splitting returns fresh capability identifiers.

A schematic Lean interface is:

```lean
-- Q : α → Ctx ρ
OwnM : (ρ : Type) → Ctx ρ → {α : Type} → (α → Ctx ρ) → Type

ret :
  (x : α) →
  OwnM ρ Γ (fun _ : α => Γ)

bind :
  OwnM ρ Γ Q →
  ((x : α) → OwnM ρ (Q x) R) →
  OwnM ρ Γ R
```

In bind, R is a result-context function for the continuation result type. When the final context must also retain information depending on x, package that information in the continuation result or use a more general dependent judgement.

These are mathematical signatures. The concrete implementation should distinguish object-language value types from arbitrary Lean Type, and make arena and universe parameters explicit as required.

A fixed-output-context abbreviation remains useful for scalar operations:

```text
Ix ρ Γ Δ α := OwnM ρ Γ (fun _ : α => Δ)
```

Do not define the implementation merely as a publicly executable function from mutable State Γ to State Δ. Lean can copy ordinary state values. The preferred foundation is RawProgram together with a checked typing judgement, interpreted only by the controlled runner.

One representation is a syntax tree plus a proof:

```lean
-- Schematic representation, omitting object-language environments.
structure Checked (ρ : Type) (Γ : Ctx ρ) (α : ValueType)
    (Q : Value α → Ctx ρ) where
  code : RawProgram
  typed : Typing Γ code α Q
```

A typed inductive syntax is an alternative. In either case, mutation is an effect of interpreting the complete certified program, not of constructing or duplicating a proof object.

## Hidden indices and the ownership frontend

Provide an ownership programming block whose elaborator maintains a symbolic context. The programmer names arrays and views, while the elaborator tracks capability identifiers, decomposition witnesses, lifetimes and permission equations.

For each statement, the elaborator resolves names, selects the relevant transition, generates its side conditions, and threads its post-context into the next statement. It emits a core term plus proofs, not an unchecked executable that assumes the analysis was correct.

A source alias can either be disallowed for resource bindings or elaborated to the same inert capability name. If permitted, all aliases lose authorisation together when the capability is consumed. Never create a second ledger entry merely because a handle receives another source-level name.

Simple side conditions should be discharged by reduction, simplification and arithmetic proof procedures. More complex footprint facts may be supplied explicitly. Proof automation failure should report an unresolved obligation, rather than invent a conservative runtime meaning that differs from the stated type.

Diagnostics should name the conflicting operation and the relevant loan or split.

```text
Cannot write through rightReader.
Current share is 1/2; writing requires share 1.
The complementary share is held by otherReader.
Join the compatible readers before writing.
```

```text
Cannot free buffer.
A borrowed fragment covering [32,64) remains live in scope scan.
End that scope and reconstruct the root owner first.
```

The context indices are hidden by elaboration, not discarded before composition. A package of the form Sigma Γin, Sigma Γout, Program Γin Γout α cannot supply a generally valid bind unless the matching intermediate contexts are established.

After the full program has been checked, its internal contexts can be hidden behind a closed program type. The public interface need not expose them.

This architecture permits a convenient monadic surface without claiming that ordinary Lean arrows have become affine or that the ordinary Monad class tracks changing resource states.

## Functions and modular contracts

Resource-using functions should expose permission transformations, rather than arbitrary host functions accepting a raw reference. Begin with signatures over a named formal footprint and a parametric frame.

A read-only scan preserves a positive fractional view. A fill preserves a full writable view. A split consumes one view and produces a certified pair. A withMut helper restores its lent owned view after its callback returns the required borrowed authority.

```text
sumBytes :
  B(κ,a,F,q) → Nat × B(κ,a,F,q)
  requires q > 0

fill :
  B(κ,a,F,1) → UInt8 → B(κ,a,F,1)
  requires a read-write ceiling

withMut :
  U(a,F) →
  checked callback returning the complete borrowed footprint →
  U(a,F)
```

These signatures describe logical authority flow. The frontend may hide returned unchanged capabilities while its internal term records their preservation.

Support module calls by instantiating a checked resource contract against the caller context. The callee does not get the caller's entire heap or permission context. A frame rule preserves the unaffected part, provided framing respects the resource algebra and any loan dependencies.

A function returning a slice that borrows caller-owned storage needs an explicit lifetime relationship in its contract. This is a later extension beyond callbacks whose borrows end on return. An ordinary function returning an existentially hidden raw handle is not a substitute for such a contract.

For the initial core, pure scalar functions may be supplied as total Lean functions from scalars to scalars. Passing a host function does not grant it resource operations. General resource-bearing closures require an object-language closure type with a checked captured environment.

Do not store ownership-bearing values inside unrestricted generic containers without defining how their permissions are represented and transferred. Restrict initial snapshots to immutable bytes and scalar products.

## Control flow and loops

At a conditional, verify each branch from the same incoming context. The branches may access the same capability because only one branch executes. Their outputs must satisfy a common postcondition, possibly after certified renaming or reconstruction.

Do not add the permission budgets of mutually exclusive branches. Conversely, do not allow a later operation to assume authority that only one branch returns.

For example, a function that frees a buffer in one branch and retains it in the other must return an explicit sum describing those alternatives, or normalize both branches to a common state. It cannot return an unconditional active owner.

Fresh identifiers created independently in branches need alpha-renaming or existential postconditions. Matching source-level names is not sufficient. Dynamic allocation uses execution freshness; static certificates describe that freshness symbolically.

Start with bounded loops preserving a fixed resource shape. A loop over a slice can retain its full writable claim while its scalar index changes. The invariant states bounds, allocation validity, and the preserved permission context.

A loop that changes the decomposition structure needs a parameterized invariant describing its remaining and processed portions. A practical second example is walking a mutable iterator by splitting off one cell and carrying the residual slice. Each yielded writable cell must be disjoint from the remainder and every previously yielded cell.

General recursive divide-and-conquer functions require a footprint-indexed resource contract and a termination argument for the reference evaluator. Add these after bounded loops, rather than representing arbitrary unbounded execution as a total function without an explicit semantics.

For later nonterminating programs, use a small-step or partial semantics and state safety over all finite execution prefixes. Do not infer termination or eventual resource return from permission preservation.

## Closed execution and backend refinement

Define the reference heap using immutable mathematical byte arrays indexed by allocation identity. Reads and writes are pure state transformations, with explicit error states for allocation failure or program faults as appropriate.

Use first-order object-language result types and a restricted export relation. Results may include scalars, scalar products and immutable snapshots. They must not include raw handles, runnable borrowed actions, tasks or host closures carrying access to the arena.

A possible public shape is:

```lean
-- Schematic. ExportTy denotes an ownership-free result language.
runReference : ClosedProgram τ → ExportValue τ

runMutable : ClosedProgram τ → IO (ExportValue τ)
```

The reference version must either have bounded terminating programs or expose a fuel/partial result. Do not assign the first signature to a language with unbounded general recursion.

An abstract arena parameter can additionally prevent accidental cross-arena mixing. Lean's ST interface is a useful execution substrate, but ST references permit aliases; the stronger access rules come from this layer, not from ST itself. See the [Lean reference on mutable references](https://lean-lang.org/doc/reference/latest/IO/Mutable-References/).

The mutable interpreter owns its arena table, buffers and pointers. It may use ST-backed buffers or a narrowly specified low-level interface. No user-facing primitive returns those storage objects.

A snapshot operation must produce independently immutable exported data. If the backend returns an alias to storage that can later mutate, it violates the snapshot contract even if the permission ledger is well formed. Copying is a valid first implementation.

Executing a closed program twice creates two arenas. Saving the AST is harmless. Saving an already-authorized mutable action and rerunning it on the same arena must not be exposed as a separate operation.

Do not provide arbitrary liftIO, mutable state projections, foreign pointer extraction or a cast from a claimed Ctx to a realized runtime state. Each new external resource integration requires a typed primitive and a semantics/refinement contract.

For logical proofs, proof fields in Prop are erased by Lean's compiler. That does not establish that the entire ledger, AST, identifiers or footprint values disappear from executable code. An interpreter can retain all of them. Treat static specialization and erasure as a separate optimization with a correctness argument.

Define a simulation between reference heap states and mutable backend states. Prove that each mutable primitive implements its reference transition and preserves the representation relation. If the implementation relies on ST/FFI semantics or unchecked runtime replacements, identify those as part of the implementation assumptions until a lower-level proof is available.

## Example program and ledger trace

The proposed surface below demonstrates the intended programmer experience. It is pseudocode for the ownership elaborator, not currently available Lean syntax.

```lean
def example : ClosedProgram Snapshot :=
  ownership do
    let buffer ← allocBytes 64

    let buffer ← withMut buffer fun whole => ownership do
      let (left, right) ← splitAt whole 32

      fill left 1
      fill right 2

      let (reader1, reader2) ← splitFraction right half half
      let sum1 ← sumBytes reader1
      let sum2 ← sumBytes reader2
      -- Both sums are ordinary scalar values.
      let right ← joinFraction reader1 reader2

      let whole ← joinSpatial left right
      return whole

    let answer ← snapshot buffer
    free buffer
    return answer
```

The returned snapshot contains 32 bytes of value 1 followed by 32 bytes of value 2. Both scans return 64. The scalar results can be duplicated or discarded without changing the resource context.

| Step | Usable authority |
| --- | --- |
| Allocate | Owned root over [0,64) and its disposal entitlement |
| Begin mutable scope | Borrowed full writer over [0,64); lender suspended |
| Spatial split | Full writers over [0,32) and [32,64) |
| Fractional split of right | Left writer; two half-share readers over [32,64) |
| Rejoin readers | Left writer; restored full right writer |
| Rejoin slices | Full borrowed writer over [0,64) |
| End mutable scope | Restored owned root and disposal entitlement |
| Snapshot | Same owned root; independent immutable bytes |
| Free | No allocation or access authority remains |

If the programmer retains an alias oldReader = reader1, it still names the consumed capability after joinFraction. A subsequent read through oldReader is rejected.

A nested reborrow example should borrow only the left slice inside a shorter scope, restore that slice, then continue writing through it. A shared-scope example should permit several reads but reject writes even when those reads are reconstructed to a read-only claim of share 1.

## Algebraic laws and normalization

Prove the laws used by frontend normalization before making them elaborator rewrite rules.

Fraction conservation follows the exact rational equations. Spatial conservation follows a partition equation on footprints. Delegation conservation follows replacement of an active parent by its borrowed frontier without counting the suspended parent again.

For fractional reconstruction, splitting a claim into q1 and q2 and joining the resulting claims restores an observationally equivalent claim. Handle names may differ. Conversely, joining and splitting restores the original pair only when the split requests the original q1 and q2; an arbitrary halving split does not invert an unequal join.

For spatial reconstruction, split followed by a matching join restores the original view modulo fresh identifiers. Prove matching for allocation, endpoint order, share, ceiling and loan ancestry.

Identity and reassociation of nested scoped transformations should preserve observable results and final authority when intermediate footprints and contracts match. They should not equate programs with different allocation, disposal or externally visible effects.

Fractional and spatial splitting should commute at the level of permissions: either order yields four views with the corresponding footprints and shares. The initial sibling-only reconstruction tree may distinguish the resulting representations. Do not claim arbitrary operational interchangeability until a normalizer with a proven denotation-preservation theorem exists.

The first normal form can use a tree recording the actual sequence of splits. Later, interval refinement can produce a common partition, with compatible fraction vectors per segment and explicit reconstruction witnesses.

Arithmetic equality is not enough for context equality. Normalization must preserve the association between claims, loans, disposal authority and the physical allocation.

The resource algebra is a partial composition structure, not a claim that ownership, footprints and loans form one unrestricted numeric semiring. Fractions compose only for matching resources and compatible access. Spatial composition uses disjointness. Lifetimes introduce directed dependencies. Keep those operations separate in the definitions.

## Formal semantics and theorem obligations

Define a small-step relation over program, environment, heap and permission state. A distinguished Fault result records bounds, stale access, permission, lifetime and disposal failures. Fault is part of the specification so that safety cannot be proved merely by omitting illegal transitions.

Realizes(H,Γ) combines heap validity and the context invariant. It establishes that every claim refers to an existing initialized footprint and that the accounting forest describes the heap's access authority consistently.

The target theorem has two parts: all reachable prefixes avoid ownership faults, and successful execution realizes the promised post-context.

```text
Typing Γ p α Q
∧ Realizes H Γ
∧ initial environment matches Γ
⇒
  every reachable execution prefix is ownership-safe

and, if execution returns v in heap H',
  Realizes H' (Q v)
```

Give the statements below separate names and dependency order.

| Theorem | Required content |
| --- | --- |
| Share arithmetic correctness | Executable share operations agree with rational arithmetic |
| Context well-formedness | Names, footprints, roots, ceilings and lifetimes satisfy all invariants |
| Primitive preservation | Each legal primitive preserves Realizes with its specified post-context |
| Bounds safety | Every executed byte access is in its allocation and footprint |
| Access exclusion | A writable byte has no competing readable or writable budget outside the permitted access path |
| Lifetime validity | Usable borrowed claims belong to live loans whose dependencies remain valid |
| Reconstruction correctness | Joining or ending a loan removes descendants before restoring parent access |
| Disposal safety | Free consumes the unique disposal entitlement and has no live dependent access |
| Frame preservation | Operations preserve unaffected heap observations and authority |
| Typed execution safety | A certified program cannot reach an ownership Fault |
| Scope confinement | Scoped borrowed authority cannot remain executable outside its closing boundary |
| Normal-termination cleanup | A closed successful program leaves no live owned allocation or unresolved loan |
| Checker soundness | A successful checker result produces the declarative Typing judgement |
| Elaboration correctness | The generated core and certificate correspond to the accepted source program |
| Backend refinement | Mutable execution simulates the reference transitions and observations |

Progress must distinguish modeled environmental failure from an ownership fault. If allocation can fail, that failure is not permission unsoundness, but its returned resource state must still be specified.

For bounded programs, prove termination separately. For unbounded programs, safety concerns finite prefixes and does not promise that borrowed resources will eventually return.

State all theorems for permitted primitive and result languages. Do not quantify over arbitrary Lean IO computations or arbitrary externally supplied heaps without realization hypotheses.

A whole-world ledger is sufficient for the sequential proof. Do not require a full Iris implementation before validating the byte-array subsystem. A richer separation logic may become useful for recursive heaps, higher-order state or concurrent libraries, but that is a separate expansion.

## Runtime uniqueness and performance claims

Logical exclusive access means that only the currently authorized path can perform the relevant operation. It does not mean that the Lean runtime stores exactly one pointer or that its reference counter equals 1.

Inert handles, AST nodes, arena entries and implementation temporaries may all exist. To obtain predictable mutation, keep actual storage in the arena and expose only checked access primitives. Prove that user-visible snapshots and values do not retain mutable aliases to that storage.

For the first backend, correctness takes priority over eliminating all ledger overhead. Measure interpreter dispatch, capability lookup, arithmetic checks, allocation costs and snapshot copying separately.

A later specialization pass can remove ghost transitions, resolve capability identifiers to storage slots and emit ordinary loops over buffers. Its proof obligation is preservation of the reference semantics and access discipline. Erasing a join certificate is safe only if the generated code still respects the aliasing assumptions justified by that join.

Three claims must remain distinct:

1. The checked program obeys the logical ownership discipline.
2. The mutable backend implements that program correctly.
3. A chosen compiler/runtime representation guarantees a particular uniqueness or reference-count property.

The first does not imply the other two. If the goal is RC = 1 at a native array update, define an explicit runtime representation relation and prove the relevant update-site invariant. If the backend uses a dedicated mutable buffer with a specified aliasing discipline instead, its proof can target that discipline without making claims about Lean array reference counts.

An initial performance demonstration should compare a pure Lean reference implementation, the certified interpreter and a specialized backend on the same array transforms. Report allocations, copies and throughput alongside result agreement.

## Validation and adversarial examples

Use tests for the executable checker and interpreter, and proofs for the invariant. A passing test suite is not a replacement for preservation.

Every invalid case should be checked both through surface syntax and through a direct attempt to construct a core certificate. This catches a frontend that rejects an operation while the supposedly safe primitive interface still admits it.

| Attempt | Required rejection or behaviour |
| --- | --- |
| Duplicate one handle, then join the aliases | Reject because both names designate the same consumed ledger entry |
| Join fractions from distinct allocations | Reject allocation-identity mismatch |
| Join equal-length but different intervals | Reject footprint mismatch |
| Write through a half-share reader | Reject insufficient write authority |
| Rejoin a read-only loan to share 1, then write | Reject read-only ceiling |
| Spatially split a writer, then use its old parent | Reject suspended or consumed authority |
| Borrow a slice, then free the parent array | Reject outstanding loan |
| End an outer lifetime before an inner loan | Reject dependency violation |
| Reuse an old handle after free and reallocation | Reject stale identity or generation |
| Capture a borrower in a returned closure | Reject unsupported resource-bearing result |
| Return an existential package containing runnable access | Reject by the export and execution-boundary rules |
| Discard a reader in the linear core | Require explicit return or retirement |
| Retire a reader, then access it | Reject retired claim |
| Duplicate a saved close action inside one session | Cannot compose it from the post-close context |
| Run a closed allocation program twice | Succeed in independent fresh arenas |
| Free an empty slice | Reject missing root disposal authority |
| Overflow machine pointer arithmetic | Reject or prove bounds in the backend lowering contract |
| Lose a capability in one conditional branch | Require an explicit sum or common post-context |
| Throw while a borrow is live | Reject until the cleanup transition is specified |
| Lift arbitrary IO into a borrowed scope | No such general lifting operation |

Property tests should generate well-formed decomposition trees, apply legal transitions, and check pointwise conservation on small finite allocations. Separately generate malformed operations and confirm that the executable validator refuses them.

Include traces mixing spatial and fractional splitting, nested delegation, retirement and restoration. Check that mutable and reference interpreters return equal immutable snapshots.

For the proof build, check the intended axiom policy for exported safety theorems and reject placeholder proofs in the verified core. Keep any runtime replacement assumptions explicit at the backend boundary. Pin Lean and dependency versions so proof and executable behaviour can be reproduced.

## Suggested module structure

Use a small dependency graph, with executable arithmetic and invariant definitions below syntax and elaboration.

```text
Ownership/
  Id.lean
  Share.lean
  Footprint.lean
  Context.lean
  ContextInvariant.lean
  Transition.lean
  TransitionSoundness.lean
  Syntax.lean
  Typing.lean
  Semantics.lean
  Safety.lean
  Scope.lean
  ScopeSoundness.lean
  Checker.lean
  CheckerSoundness.lean
  Frontend.lean
  Runner.lean
  Backend/
    Representation.lean
    Mutable.lean
    Refinement.lean
  Examples/
    SplitFill.lean
    FractionalScan.lean
    NestedBorrow.lean
    InvalidPrograms.lean
```

Share and Footprint should have executable operations with proven arithmetic specifications. Context should use a representation with efficient lookup while exposing a mathematical finite-map view to proofs.

Keep Typing declarative and independent of frontend syntax. The checker can return either an error with a structured explanation or a core certificate. Its success theorem relates the executable procedure to Typing.

Keep first-order instruction semantics separate from the mutable backend. A direct mutable implementation must not become the only definition of the language's meaning.

Add a thin test harness for accepted and rejected programs and interpreter traces. Avoid building a large general-purpose resource framework before the array examples and primitive-preservation proofs work.

## Irreversible sharing and unrestricted host values

Do not expose a primitive that simply casts U(a,F) to an unrestricted Lean value while retaining the same disposal contract. Once arbitrary host aliases to mutable storage exist, the ownership subsystem can no longer justify exclusive access merely by rejoining its own claims.

For the initial array interface, sharing with ordinary Lean code means exporting an immutable snapshot. The original allocation remains owned internally until it is freed. A consuming export may combine snapshot creation and disposal.

A future zero-copy immutable export can transfer the entire allocation into a separately specified immutable or reference-counted representation. That transition consumes root ownership and disposal authority in this subsystem; it is not a temporary borrow whose uniqueness can later be recovered without a new import proof.

Likewise, an ordinary usage grade for a scalar or immutable host value is different from a fraction of resource access. Reusing the same scalar twice does not consume twice the array permission that was used to read it. Reusing a handle name twice does not create a second positive share. The resource ledger and any future general usage-grade system must interact through explicit rules rather than by multiplying their numeric indices indiscriminately.

## Implementation sequence and acceptance gates

Implement in proof dependency order. Do not postpone the invariant until after the convenient API is built.

| Stage | Deliverable | Acceptance gate |
| --- | --- | --- |
| 1 | Exact shares, allocation identities and bounded intervals | Arithmetic and disjointness specifications proved |
| 2 | Context ledger, decomposition forest and primitive transitions | Every split and join preserves the full invariant |
| 3 | Byte-array semantics and explicit ownership | Allocate, read, write, snapshot and free have sound transitions |
| 4 | Fractional and spatial views | Positive scans and disjoint fills work; adversarial joins fail |
| 5 | Explicit loans and nested reborrowing | Restoration and lifetime-dependency proofs completed |
| 6 | Typed programs, closed runner and bounded control flow | Closed reference programs are safe and clean on normal termination |
| 7 | Hidden-index elaborator and modular contracts | User examples elaborate to kernel-checked terms |
| 8 | Optional retirement and scope recovery | Scope-closing and no-escape obligations proved |
| 9 | Mutable interpreter | Simulation covers every implemented primitive |
| 10 | Specialization and broader integrations | Each optimization or integration has a corresponding correctness contract |

A useful first milestone ends at stage 4 with a manually constructed indexed API. It already validates the algebraic design. A useful programmer-facing milestone ends at stage 7, with explicit permission return but hidden bookkeeping. Automatic borrower retirement should not block those milestones.

The first end-to-end acceptance example is the 64-byte program above. Add variants that perform the same computation using nested reborrowing, then confirm rejection when a consumed child is reused.

Before supporting allocation inside loops, settle symbolic freshness and generation handling in the loop invariant. Initial fixed-shape loops can avoid this issue by allocating outside the loop.

Before accepting arbitrary same-resource fractional joins, prove the common-partition normalizer. Sibling-only joins are sufficient for the first examples and make conservation easier to audit.

## Extensions and integration policy

Non-lexical lifetime inference should be a frontend analysis that generates the same explicit lifetime transitions and certificates. It must not introduce a second, unchecked notion of permission validity. Start with conservative lexical scopes and explicit end points.

For concurrency, a fork must distribute capability authority and any required loan dependencies into child contexts. The combined child budget must respect the pointwise bound. Child capture is limited to certified environments; writable overlapping captures cannot be smuggled through host closures. A join collects child post-contexts before the parent continues. Detached borrowers are excluded until their lifetime and ownership semantics are defined.

Sequential permission safety is not by itself a proof of concurrent backend race freedom. That claim needs a concurrency semantics, a separation/compatibility theorem and backend assumptions about memory operations.

For asynchronous runtimes, keep ownership transitions on typed tasks. Suspension preserves the task's current claims; cancellation is a typed exit with specified cleanup. Do not attach borrowing safety to a task handle while leaving the captured execution frame unchecked.

For generic arrays, define Copyable, Movable and borrowable resource representations. Reading a non-copyable cell must move its authority or create a checked borrow; overwriting an occupied cell must account for its previous contents. Initialization and destruction then become part of the state.

For external buffers, specify an import primitive with a concrete representation contract. An external pointer plus a user assertion of uniqueness does not constitute a proved import. Root ownership must include whichever allocator and deallocator obligations the backend requires.

For existing Lean code, expose a bounded API or a source-to-core translation with a preservation theorem. The library does not retroactively impose linearity on all host code.

The design can begin as an independent array subsystem and later serve an asynchronous runtime or verified low-level backend. Integration should use the proved transition contracts rather than replacing them with runtime assumptions about apparent uniqueness.

## Design decisions to preserve

Keep the following decisions stable through the first implementation.

- Fractional uniqueness is the resource foundation; the host Lean type system remains unrestricted.
- User-visible handles are inert names. The current checked context provides access authority.
- Unique ownership, full borrowed access and disposal authority remain distinct.
- Fractions are exact, spatial partitions are certified, and reconstruction tracks provenance.
- Explicit return and join form the core; scoped automatic recovery is an additional proved feature.
- Indices are hidden by elaboration and abstraction after composition, not existentially discarded before it.
- Closed runs start with fresh arenas and export only ownership-free data.
- Permission soundness, backend refinement and runtime uniqueness are separate theorem families.
- Rust compatibility and a full generalization of graded types are later research goals, not initial acceptance criteria.

The most consequential implementation choice is to build and prove the context-transition core before the frontend. That core makes a hidden-index interface enforceable without requiring native affine arrows in Lean.

## References

1. Daniel Marshall and Dominic Orchard. Functional Ownership through Fractional Uniqueness. Proceedings of the ACM on Programming Languages 8, OOPSLA1, Article 131, 2024. [DOI](https://doi.org/10.1145/3649848). [Open access paper](https://kar.kent.ac.uk/105880/1/D.%20Orchard%20-%20Functional%20ownership%20through%20fractional%20uniqueness%20-%20PPDF.pdf). Relevant background: uniqueness and identity in section 4; fractional borrowing and resource interfaces in section 5; partial views in section 5.2; operational safety in section 6.3; further lifetime work in section 8.
2. Andrew Wagner, Olek Gierczak, Brianna Marshall, John M. Li and Amal Ahmed. From Linearity to Borrowing. Proceedings of the ACM on Programming Languages 9, OOPSLA2, Article 415, 2025. [DOI](https://doi.org/10.1145/3764117). [Author paper](https://johnm.li/from-linearity-to-borrowing.pdf).
3. Ralf Jung, Jacques-Henri Jourdan, Robbert Krebbers and Derek Dreyer. RustBelt: Securing the Foundations of the Rust Programming Language. Proceedings of the ACM on Programming Languages 2, POPL, Article 66, 2018. [DOI](https://doi.org/10.1145/3158154). [Author paper](https://plv.mpi-sws.org/rustbelt/popl18/paper.pdf). Lifetime logic is developed in section 5.
4. The Lean Language Reference. [Mutable references and ST](https://lean-lang.org/doc/reference/latest/IO/Mutable-References/). This documents the execution substrate rather than the proposed ownership layer.
5. The Lean Language Reference. [Logical model of IO](https://lean-lang.org/doc/reference/latest/IO/Logical-Model/). Relevant to the distinction between descriptions of effects and their execution.
6. The Rustonomicon. [Splitting borrows](https://doc.rust-lang.org/nomicon/borrow-splitting.html). A practical comparison for disjoint mutable views.

The calculus, ledger, frontend, theorem programme and implementation stages specified here are proposed work. The cited papers motivate the design but do not establish its soundness.
