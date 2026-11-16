# Sealed ownership in Lean: paper and C backend handoff

Date: 16 November 2026

## Decision and scope

Develop the paper around an executable, compositional borrowing discipline embedded in ordinary Lean, with a sealed runner and a refinement path to direct allocation and mutation in **C**. C is the intended backend for integration with Lean's compilation path.

The first implementation should retain algorithm control flow in Lean and use a small C primitive interface. Independently lowering the entire algorithm to C or another IR is a later option. Neither recursion nor ownership safety inherently requires a LeanIn-sized macro system.

Suggested title: **Borrowing Without Linear Types: A Sealed Ownership Discipline in Lean**.

This is a design and paper handoff based on source inspection at [`ab9ed32`](https://github.com/scidonia/ownership/tree/ab9ed32) and the preceding ownership handoff. It is not a complete review of every updated module. No independent build was performed. All new signatures and program examples below are schematic, not compiled Lean or C.

## 1. Claims the paper should make

| Claim | Precise formulation | Required evidence |
| --- | --- | --- |
| Borrowing can be encoded in ordinary dependent type theory | A specified calculus of exclusive access, fractional reads, spatial splitting, loans and disposal is represented in Lean | Definitions and preservation/safety theorems |
| A sealed machine enforces the discipline without linear host types | Freely copyable handles can only be exercised through operations authorised by the current execution context | Compositional program interface, execution theorem and confinement argument |
| Direct mutation can preserve functional behaviour | Concrete C operations implement reference transitions without invalid access and with equivalent permitted observations | Representation relation, primitive refinement, composition and boundary conditions |
| The fragment can be efficient | The chosen implementation avoids specified copies and has measured performance on real algorithms | Representation/cost evidence, compiled-code inspection and benchmarks |

Representing borrowing rules alone is not the strongest contribution. The contribution is connecting those rules to usable, compositional execution in a nonlinear host language.

Do not conflate logical full permission with RC=1. A C-owned buffer can have one authoritative owner without being represented as a uniquely referenced Lean array. In that design, absence of external aliases and legal pointer use are the relevant representation properties.

Mutation is intentionally observable inside the fragment: a read following a write sees the new value. The external guarantee is agreement with the functional specification, together with the absence of escaped aliases that expose unintended mutation. For an effectful public interface, specify its observations directly; for a pure interface, prove confinement sufficient to justify purity.

## 2. Current evidence and remaining connection

The inspected updates support the proposed direction:

- `Runner.Prog` packages a command list with a proof of its `checkWorld` result. `Prog.seq` composes certificates through the actual intermediate world.
- `ClosedProgram` establishes acceptance from the canonical empty world. It does not yet require the final resource context to be discharged.
- `Indexed.Ix` explicitly acknowledges that its field does not establish the claimed post-world for arbitrary inhabitants. It remains a specification experiment, not the general sound execution interface.
- `UFRun.union` follows parent links and sends writes through `World.writeChecked`. Reads remain observations of public pure worlds.
- `UFCompress` supplies functional bounded search and one-step compression lemmas. It is not integrated full path compression.
- `BackendArr` relates ByteArray operations to the list reference model and explicitly does not establish physical in-place execution.

Public pure worlds are useful for reasoning. They do not establish the sealing of actual mutable storage. Some `Runner.lean` comments describing worlds as unexported should be aligned with the public definitions.

The next integration milestone is a result-returning program interface with checked reads, data-dependent control flow, and one sound execution semantics. A fixed list of writes does not express a parent read followed by a decision about which node to visit next.

## 3. Core types: separate permissions from heap contents

Use a permission context `Γ` to describe allocation identities, footprints, shares, capabilities, loans and disposal rights. Use a separate model heap for stored values.

```lean
Prog (Γ : Ctx) (α : Type) (Q : α → Ctx) : Type
```

A program starts with context `Γ`, returns `a : α`, and ends with permissions `Q a`. Heap contents can change without changing the permission context.

```lean
bind : Prog Γ α Q →
       ((a : α) → Prog (Q a) β R) →
       Prog Γ β R
```

Bind enforces matching contexts statically. The evaluator must also pass the actual resulting world to the continuation. A post-context written in a type is insufficient unless execution is proved to realise it.

Build `Prog` as certified syntax or syntax packaged with a typing derivation. Do not permit a constructor wrapping an arbitrary client-supplied function on the concrete mutable world.

Define the context-preserving fragment:

```lean
Owned Γ α := Prog Γ α (fun _ => Γ)
```

It supports ordinary monadic sequencing in shape:

```lean
pure : α → Owned Γ α
bind : Owned Γ α → (α → Owned Γ β) → Owned Γ β
```

This fragment should carry most algorithm code. The indexed layer handles allocation, splitting, loans, reconstruction and disposal. A small elaborator can hide intermediate contexts; the core rules and proofs should exist independently of that syntax.

## 4. Sealing and execution

Expose model definitions, certified programs and safe combinators. Keep concrete mutable buffers, the authoritative runtime state and the raw evaluator behind the implementation boundary.

The public runner initially has the shape:

```text
runFresh : ClosedProgram SafeResult -> IO SafeResult
```

A closed program starts with no managed allocations and finishes with no outstanding resources or loans. Its final metadata may retain fresh-ID history. Safe results initially comprise scalar data and independent immutable snapshots.

Duplicating a handle copies a name, not authority. Each operation must match the current context. A stale proof about an earlier context cannot authorise live mutation. Duplicating a complete program is safe because each execution obtains independent resources; a fresh ledger over the same externally aliased buffer would not suffice.

The pure reference evaluator should have a result shape equivalent to:

```lean
eval (p : Prog Γ α Q) (w : ModelWorld) (h : Realizes w Γ) :
  Σ a : α, { w' : ModelWorld // Realizes w' (Q a) }
```

For bind:

```text
(a, w1, evidence1) := eval first w evidence
eval (continuation a) w1 evidence1
```

This is a total idealised signature. Model allocation failure, explicit algorithm errors and nontermination separately rather than silently assuming they cannot occur. Failure outcomes need a resource-preserving state or guaranteed cleanup.

Module encapsulation is an API boundary for safe clients. The paper must state its assumptions about unsafe code, FFI access, runtime integrity and compiler correctness. Do not claim that a private constructor protects against arbitrary foreign code accessing memory.

## 5. Recursion and loops

Recursion does not automatically create a new loan. A recursive call can sequentially use the existing exclusive capability while its caller is suspended on the call stack.

For union-find, reads and writes preserve ownership context. A fuel-bounded find can therefore use ordinary recursive control flow within `Owned Γ`:

```text
findCompress(uf, fuel, x):
  if fuel == 0:
    return Error.exhausted
  parent := readParent(uf, x)
  if parent == x:
    return Ok(x)
  result := findCompress(uf, fuel - 1, parent)
  match result:
    Error e => return Error e
    Ok root =>
      writeParent(uf, x, root)
      return Ok(root)
```

Its illustrative result type is `Owned Γ (Except FindError Vertex)`. All reads and writes use the current execution state. Bounds and parent validity are checked or established from representation invariants.

For valid forests, prove sufficient fuel or use well-founded recursion. Keep the proofs separate:

1. Ownership safety: every access is permitted and resource invariants are preserved.
2. Functional correctness: traversal finds the appropriate root; compression preserves the partition and forest validity.
3. Termination: the traversal reaches a root under the forest invariant.

A general loop may be represented by an explicit iteration construct or a semantic recursion mechanism. For possibly nonterminating programs, prove safety for every finite execution prefix. Termination is an additional theorem. Do not claim a total evaluator for unrestricted recursion.

Loops often have a fixed permission invariant and a changing data invariant. For filling an array, ownership of the full range remains constant while the functional invariant records the written prefix. This is why indexing by permissions is more practical than indexing every operation by exact byte contents.

## 6. Scoped borrowing and context-changing control flow

A scoped combinator can suspend a lender, invoke a certified body, and restore the lender after the body reconstructs its authority:

```text
withMutBorrow lender (fun borrower => body)
```

The body must finish with no outstanding descendants and the required borrowed authority available for return. The combinator invalidates borrower names before restoring the lender. A nested borrow has the following progression:

```text
owner active
owner suspended; outer active
owner suspended; outer suspended; inner active
owner suspended; outer restored; inner consumed
owner restored; outer consumed; inner consumed
```

Branches must produce a common post-context or return a tagged result whose context depends on the tag. One branch cannot dispose a resource while another retains it and then silently merge as though the permissions were identical.

Start union-find with sequential whole-object authority. Add scoped reborrowing as a separately proved combinator rather than making it a prerequisite for every recursive call.

## 7. Union-find case study

Implement an arbitrary-sized array of parent/rank records, or two explicitly owned arrays. Choose a concrete C representation and prove its connection to the functional model. The current four-node byte example is an integration seed, not the final general interface; larger indices need a representation with appropriate range and overflow conditions.

The closed example should:

```text
runFresh {
  uf := allocateUnionFind(4)
  initialiseSingletons(uf)
  union(uf, 0, 1)
  union(uf, 2, 3)
  union(uf, 0, 2)
  roots := findCompressAll(uf)
  result := immutableCopy(roots)
  dispose(uf)
  return result
}
```

For a specified tie-breaking policy, the parent trace can be `[0,1,2,3]`, `[0,0,2,3]`, `[0,0,2,2]`, `[0,0,0,2]`, and finally `[0,0,0,0]` after compression. State representative choices explicitly; preservation/merging of components is the general correctness property.

Prove `UFRep` separately from ownership: parent bounds, valid forest, length/layout agreement and the represented partition. Ownership permits a write; it does not prove that the written parent is a valid vertex or that the write preserves the forest.

Fractional readers support non-compressing finds. Path compression requires full writable authority. Spatially splitting storage does not automatically split the algorithm: parent traversal may leave the slice. Use split-array fill/map as the clean spatial example, and union-find as the data-dependent recursive example.

## 8. C backend and its proof boundary

Initially retain Lean recursion, branching and sequencing. Supply a narrow C interface for arena/buffer allocation, validated reads, writes, snapshots and disposal. Do not expose unrestricted raw pointers as ordinary client values.

An illustrative internal interface is:

```c
/* Design sketch, not a Lean FFI declaration. */
status buffer_alloc(arena *, size_t count, buffer_id *out);
status buffer_read(arena *, buffer_id, size_t index, word *out);
status buffer_write(arena *, buffer_id, size_t index, word value);
status buffer_free(arena *, buffer_id);
```

The actual interface needs the pinned Lean runtime's calling conventions, value representation and ownership conventions. Determine these during implementation rather than treating this sketch as drop-in FFI code.

Define `BackendRel concrete model`. For each primitive prove that permitted model execution is implemented by the concrete step and the relation is preserved. The relation and contracts must account for:

- Allocation extent, layout, alignment, index arithmetic and overflow.
- Live allocation identity, generation/freshness and pointer validity.
- Initialised reads and permitted writes.
- No access after disposal and no double disposal.
- Input/output confinement and independent immutable snapshots.
- Allocation failure, error cleanup and interaction with runtime finalisation.
- The sequential execution assumption, including callbacks and reentrancy.

Choose one allocation owner. Explicit disposal and a runtime finaliser must not independently free the same allocation. If a finaliser provides fallback cleanup, disposal must invalidate its ownership consistently.

Separate three levels of evidence:

| Level | What it proves |
| --- | --- |
| Abstract backend model | The intended primitives preserve ownership and observations |
| Implemented C primitives | The actual C code satisfies those contracts under a chosen semantics or explicitly trusted assumptions |
| Compiled execution | The compiler/runtime/ABI preserve the established behaviour, either proved or named as trusted |

A Lean theorem about an abstract external operation does not verify the C body. State whether the C implementation is verified, translation-validated, or trusted. Tests support engineering confidence but do not replace that distinction.

Keep runtime validation initially. Check erasure is a subsequent optimisation with a proof that reachable calls already satisfy the removed checks. Direct allocation alone does not establish speed; measure boundary overhead, checks, allocation, copying and snapshot costs.

## 9. Lowering to IR: two implementation routes

**Route A — Lean control flow with C primitives.** Compile the Lean algorithm through its normal pipeline and call the sealed backend. Prove program/primitive composition, and state the ordinary compiler and runtime trust assumptions. This is the recommended first complete implementation.

**Route B — custom lowering of the fragment.** Reify or otherwise inspect the algorithm, lower its operations and control flow into a selected IR, and prove a simulation or suitable refinement for that lowering. This route can remove interpretation, ledger and FFI overhead or enable bulk optimisations, but it is additional compiler work.

A program representation with Lean continuation functions is convenient for execution; those functions are not automatically inspectable syntax. Whole-program specialised lowering may require defunctionalisation or compiler integration. That requirement comes from the compilation objective, not from the basic ability to express recursion safely.

The paper should not imply that a proof about source contexts automatically proves emitted IR safe. Conversely, it need not verify every Lean compiler pass before demonstrating a useful sealed interface: an honest theorem can be conditional on the standard compilation/runtime boundary.

## 10. Surface syntax and macrology

Implement the semantic core first. Provide an ordinary monadic interface for context-preserving algorithm bodies and an indexed interface for resource transitions. Add a small `ownership do` elaborator to infer contexts, insert transition evidence and report failures in source terms.

Do not begin with a full bespoke control-flow compiler. The initial surface needs allocation scopes, borrow scopes, primitive calls and ordinary function composition. Extend it only when an actual example requires a new permission transition or a chosen lowering route needs explicit control-flow syntax.

The acceptance test is an author-written recursive union-find function using the safe API, not a precomputed list of writes. Its type and execution theorem must govern the same computation, including its reads and branches.

## 11. Paper structure and delivery priorities

Suggested paper structure:

1. The problem: verified functional specifications and controlled low-level mutation in Lean.
2. Borrowing calculus and permission-context invariant.
3. Certified computations, composition, recursion and scopes.
4. Sealed execution, observations and the safety theorem.
5. C representation and refinement boundary.
6. Spatial array processing and recursive union-find case studies.
7. Evaluation, limitations, related work and trust assumptions.

Prioritise these deliverables:

| Order | Deliverable | Completion evidence |
| --- | --- | --- |
| 1 | General result-returning program interface | Reads and dependent control flow compose soundly |
| 2 | Context-preserving monad and indexed transitions | Bind threads actual states; stale operations cannot compose |
| 3 | Closed-run lifecycle | Allocation through cleanup, with safe results and explicit failure behaviour |
| 4 | General union-find client | Recursive compression, functional specification and legal accesses in one route |
| 5 | Small C backend | Explicit representation/ABI contracts and stated verification status |
| 6 | Performance evidence | Compiled benchmarks and copy/allocation observations |
| 7 | Optional custom lowering | Refinement for the selected IR and justified check removal |

Negative tests should cover stale capability use, read through an expired loan, compression through a fractional reader, early disposal, double disposal, cross-run handle replay and out-of-footprint traversal. Positive tests should cover repeated exclusive writes, true nested reborrowing, fractional read-only finds and recursive compression followed by cleanup.

The paper can be valuable with a proved embedded discipline and a clearly delimited trusted C backend. A verified backend strengthens the result, but the manuscript must distinguish completed proofs from backend assumptions and planned lowering work.
