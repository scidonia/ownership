# Review note: proving RC=1 for the compiled ownership executor

Date: 24 October 2026

Scope: review of the supplied `PLAN.md`. This note assesses the proposed proof architecture, not the repository implementation. The reported compiler observations and existing sibling-library results have not been independently reproduced here.

## Recommendation

Keep the central architecture: a sealed client language, a fixed executor, and a verified checker over the executor's emitted post-RC LCNF. This can establish the narrow result that designated writes execute with RC=1 without first verifying the whole Lean compiler.

The immediate proof target should be a conditional theorem about the checked artifact and a concrete entry heap invariant. Establish separately that the runner and permitted initializers produce that invariant.

This result certifies an operational property of the generated code. Transporting the original functional specification requires a further source-to-target correspondence theorem. These obligations can be developed independently and composed later.

## 1. Separate owned handles from exclusive objects

Section 5.2 currently requires every variable classified as owned to denote a distinct object with RC=1. That conflates an obligation to consume a counted reference with a claim about the total number of references to its object.

Two owned handles can denote the same object. An owned parameter can therefore arrive shared. Borrow annotations describe reference-management obligations; they do not by themselves establish uniqueness.

The analysis should distinguish:

| Fact | Meaning |
| --- | --- |
| Owned handle | The code controls one counted reference and must consume or release it |
| Object identity | Which variables and heap slots may denote the same object |
| Count information | The contributions from handles and heap slots |
| Exclusive target | The object is nonpersistent and its total count is one |
| Borrow | An uncounted reference whose validity depends on a live owner |

A conservative analysis may reject any shape for which it cannot prove exclusivity. It must not infer exclusivity solely from an owned parameter annotation.

Constructor allocation establishes freshness of the outer object, not uniqueness of its children. The invariant also needs a rule preventing a surviving borrow from being used after its owner is released or its supporting path is invalidated.

## 2. Specify the initializer's heap postcondition

Runtime allocation alone does not establish uniqueness throughout a nested state. Consider the schematic initializer:

```lean
let child := makeChild ...
let state := #[child, child]
```

The outer array may be unique while both slots reference the same child. Removing one slot leaves the other counted reference. An initializer can also retain objects supplied by the client.

Introduce an explicit entry condition describing:

1. A well-formed, live heap with accurate counts.
2. A session root with the required ownership.
3. The sharing restrictions on the mutable footprint.
4. Separation of that footprint from client-reachable objects.
5. The required correspondence between executor variables and heap roots.

A unique mutable tree is a convenient sufficient condition, but need not be the final abstraction. Internal sharing is admissible if the protocol proves exclusivity of the actual target before every write.

The allowed `Init d` implementations must either establish this condition or be checked against a contract that establishes it. A source-level mathematical description of a tree alone does not specify its physical sharing.

## 3. Strengthen non-escape to separation of the mutable footprint

The absence of a state parameter in `PTree` is useful, but it does not alone imply physical disjointness. A client need not possess the session root to share a descendant installed by initialization.

Likewise, an observation with no explicit location constructor may still have a heap representation. Strings, arrays and inductive values can contain references. Sharing an immutable observation can be harmless; the proof should distinguish those objects from cells whose uniqueness is required for mutation.

Use a reachability condition of the form:

```text
client-reachable objects ∩ mutable footprint = ∅
```

Preserve that condition across initialization, observation, continuation invocation and writes. Allocation after receipt of the client tree helps establish freshness of newly allocated cells; it does not establish freshness of objects retained from initializer inputs.

Avoid claiming that state-typed subterms are impossible merely because the client language has no state parameter. The important property is access to the particular session's mutable objects, not the ability to construct some independent value of the same Lean type.

## 4. Prove absence of invalid writes

The proposed semantics makes exclusivity a prerequisite for field-write steps. In that presentation, preservation alone could show only that every write which takes a valid step is exclusive. It must also exclude reaching a write whose prerequisite fails.

Either introduce explicit ownership faults or prove progress for accepted configurations. The result should establish both:

- No ownership fault is reachable from a valid entry configuration.
- Every reached designated write has a nonpersistent target with RC=1.

For `Array.set` operations, model both the mutate and copy branches. Prove that designated state writes always select the mutate branch. This makes absence of copying a conclusion of the proof rather than a restriction built into execution.

Keep allocation and capacity assumptions explicit. The proposed fixed-size replacement fragment is a useful way to keep the address-preservation result focused.

## 5. State exactly what the checker certifies

An ownership checker can accept code that performs the wrong updates while maintaining perfect uniqueness. Therefore distinguish these claims:

| Claim | Required evidence |
| --- | --- |
| Generated executor writes at RC=1 | Checked ownership certificate and entry invariant |
| Generated executor implements the source interpreter | Semantic correspondence between source and generated code |
| Source interpreter satisfies the functional contract | Source-level correctness theorem |
| Executable has the stated physical behaviour | Backend and runtime correspondence, proved or explicitly trusted |

The first claim is the appropriate initial milestone. Call it an ownership or artifact certificate; use “translation validation” with a clear statement of which correspondence or property is being validated.

## 6. Make extraction, calls and build identity explicit

Three links need to appear in the formal statement or trust ledger:

**LCNF to `CodeF`.** If the theorem is about a projected fragment, prove that projection preserves the ownership-relevant semantics of accepted LCNF. Rejecting unsupported constructors is necessary but does not prove semantic preservation of the supported ones.

**Calls and callbacks.** Every call summary needs a semantic contract covering aliasing, ownership transfer, retention, allocation and writes. Borrow annotations alone are insufficient. Unknown client continuations must be covered by a uniform contract or relation; opaque callbacks are not automatically safe because the executor is fixed.

**Checked artifact to backend input.** A separate compiler invocation and a pinned digest provide useful build evidence. Explain how they identify the declaration actually passed to the backend. Prefer capturing the backend's input artifact directly; otherwise record the assumptions required for faithful replay, including configuration and dependencies. Specialization or inlining of the executor into client code must be prevented or the resulting instances must also be checked.

The Boolean gate must ultimately yield kernel-checked evidence of acceptance for the represented artifact, or be named as an additional trusted step. A successful external script alone is not a Lean proof of `check artifact = true`.

## 7. Revised first theorem

Use the following mathematical shape; names are schematic, not existing Lean declarations:

```text
check(d) = true
∧ EntryInv(H₀, ρ₀)
∧ CallContracts(Σ)
⇒ every execution of d from (H₀, ρ₀):
    • avoids ownership faults;
    • reaches every designated state write with an exclusive target;
    • preserves the target address at each such fixed-size update.
```

The semantics must cover the relevant control flow and calls, including nonterminating executions: the write property is a property of every finite execution prefix.

Then establish a separate runner theorem:

```text
admissible client + admissible initialization
⇒ EntryInv at executor entry
```

Compose these to obtain the uniform result for accepted clients. Keep the C backend and runtime assumptions visible at the boundary where the modeled result is transferred to execution.

## 8. Connection to conditional lower-level refinement

For the original specification-gluing goal, retain an abstract-to-concrete relation `R` and a source precondition `P`. A natural concrete entry predicate is:

```text
P_low(t) := ∃ s, P(s) ∧ R(s, t)
```

Prove that `P_low` supplies the entry invariant needed by the artifact theorem. At an internal optimization point, establish the corresponding invariant over states reachable from admissible entry states.

This exposes the exact glue: the original precondition is interpreted as concrete heap and execution facts. A lower-level transformation can then be proved correct only under those facts. Functional preservation and RC=1 remain separate properties, connected through the same representation relation where appropriate.

## 9. Suggested implementation order

1. Complete M1: inspect the actual executor, initializer and callback shapes before fixing the analysis domain.
2. Define the entry invariant and separate owned handles from exclusive targets.
3. Prove the small artifact theorem for one array write, including its shared-target rejection case.
4. Add nested-state tests: repeated child, client-retained child, held extraction pair, and detached immutable observation.
5. Extend to joins, reset/reuse and recursive calls using checked summaries.
6. Prove runner initialization and client separation.
7. Connect the checked artifact to the backend input and produce acceptance evidence.
8. Add source functional correspondence when pursuing the broader refinement result.

The architecture remains viable. The main adjustment is to put the concrete entry invariant at the centre of the development: that is the assumption under which the desired lower-level guarantee actually holds.
