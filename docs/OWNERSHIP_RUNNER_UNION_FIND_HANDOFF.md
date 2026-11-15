# Runner-owned ownership in Lean: implementation handoff

Date: 15 November 2026

## Decision

Proceed with a sealed runner that owns the authoritative ledger and managed storage. Handles may be copied in ordinary Lean; every use must be authorised against the current execution state. This is a viable architecture for an embedded ownership discipline without a linear host language.

The guarantee depends on invariant-preserving transitions and confinement of the actual resources. Hiding constructors alone does not establish either. A public pure model is useful and should remain available for reasoning.

This handoff develops the supplied `ownership-encapsulation-argument.md` and the earlier review at `979729b`. The union-find walkthrough below is based on direct source inspection of `Cap/UnionFind.lean` at `979729bdbdc31ee8a2f5475f372cde29279d1c12`. The newer `Unified` and `Indexed` modules are described by the supplied argument; they have not been independently inspected or built for this handoff. All proposed syntax is pseudocode, not compiling Lean. No independent Lean build was performed.

## 1. State the guarantee precisely

Recommended claim:

> A sealed runner can enforce ownership over its managed resources in ordinary Lean, despite freely duplicable handles, by validating each operation against one authoritative evolving ledger. Soundness requires invariant-preserving transitions and a resource boundary that prevents external aliases.

There are three distinct obligations:

1. **Model soundness:** legal transitions preserve ownership, bounds, lifetime and disposal invariants.
2. **Execution refinement:** the actual runner implements those transitions on actual storage.
3. **Boundary confinement:** clients cannot obtain raw mutable access, fork the authoritative state, import aliased resources as exclusive, or replay stale authority.

Neither model soundness nor module privacy alone establishes all three. RC=1 and absence of copying require an additional representation argument.

## 2. Duplication examples

### Copying a handle is allowed

```text
h := allocate(64)
alias := h
(left, right) := splitAt(h, 32)
write(alias, 0, 7)                -- reject: original authority was consumed
write(left, 0, 7)                 -- accept
```

Both `h` and `alias` name the same capability entry. Splitting consumes that identity and issues fresh children. It must not reuse `h` as a child identity: otherwise an old alias could regain authority accidentally. Freshness must cover retired identities, not just currently live ones; generations are one possible implementation.

Repeated writes through a still-active full capability are legal. Affine transfer does not mean that a writable handle can be used only once; it means that delegation or disposal changes which future uses are legal.

### Copying a pure model is allowed

```text
w1 := modelWrite(w0, cap, 0, 1)
w2 := modelWrite(w0, cap, 0, 2)
```

This creates two functional model branches. It is safe when each branch is ordinary immutable data. It becomes a problem if both purported worlds authorise mutation of the same underlying live buffer. The runtime must not expose such a fork operation.

### Proof replay must not control live mutation

```text
p : Writable(oldWorld, cap, index)
newWorld := split(oldWorld, cap)
writeActualBuffer(cap, index, value, p)   -- invalid API design
```

The proof is still true of `oldWorld`. It says nothing about the authoritative current state. The runner must either check current permission or execute a certified program whose state transitions enforce that correspondence. Proof duplication is harmless when proofs are used only within that properly connected execution route.

## 3. Recommended public boundary

Expose program construction, safe result values, and a controlled execution entry point. Keep raw mutable storage and authority-bearing execution state inaccessible to clients.

```text
buildProgram : ... -> Program Result
runFresh     : Program SafeResult -> SafeResult
```

These signatures express the intended shape, not a completed type design. A real effectful runner may return in `IO`; a pure runner requires the stronger confinement argument that justifies its externally pure semantics.

Keep the reference `World`, transition functions and predicates public for proofs. Immutable ledger diagnostics are also acceptable if they cannot authorise operations against a live runtime world.

For repeated program execution, fresh ledgers must correspond to independent managed allocations. A closure capturing one mutable buffer cannot be run twice with two fresh exclusive claims. Initially support allocation inside the runner and copied immutable inputs. Treat zero-copy imports, callbacks and cross-run resource transfer as separate interfaces with explicit contracts.

Returned results must not expose mutable aliases. Copying a snapshot is a simple initial policy. A zero-copy frozen result needs a proof that all mutable authority has been permanently revoked. Numeric handles escaping a run must never become valid in another run; scope handles by arena identity or prevent their escape through the result interface.

## 4. What the unified execution route must establish

The supplied argument describes `World.writeChecked` and `checkWorld`, connecting write permission checks to backend updates. This addresses the write-specific portion of the earlier checker/execution gap. According to that same argument, its command language currently contains writes and no-ops only.

Extend this same route with allocation, reads, spatial and fractional split/join, loans, restoration, snapshot and disposal. Preserve a complete invariant that includes:

- Unique capability identities, allocation association, valid bounds and shares.
- Split provenance and reconstruction conditions.
- Capability-to-lifetime associations and suspended lender obligations.
- Disposal entitlement and absence of outstanding dependent authority.
- Agreement between allocation metadata and storage.

Prove preservation for every successful step and ownership-safe failure for rejected steps. If runtime checks remain, state that invalid programs may be rejected at runtime. For statically certified programs, additionally prove that certified operations cannot encounter ownership rejection, under their explicit execution assumptions.

An indexed computation is useful only to the extent that its execution is tied to its stated post-world. A type containing `run : (w : World) -> w = pre -> Option α` does not, by that field alone, establish a post-state relation. Inspect the constructors and soundness theorem before claiming that arbitrary inhabitants satisfy a Hoare-style contract.

## 5. Union-find: what the inspected example does

The existing `UF` structure contains an owner, parent and rank lists, a proof that their lengths agree, and a denominator. `UF.writeParent` takes an `Owner.Writable` proof and applies `List.set`. `findRoot` follows parent links with bounded fuel.

The example uses denominator 4 and a full-share capability covering indices `[0,4)`. Its concrete execution is:

| Step | Parent list | Represented components |
| --- | --- | --- |
| Initialise | `[0,1,2,3]` | `{0}`, `{1}`, `{2}`, `{3}` |
| Write parent[1] := 0 | `[0,0,2,3]` | `{0,1}`, `{2}`, `{3}` |
| Write parent[3] := 2 | `[0,0,2,2]` | `{0,1}`, `{2,3}` |
| Write parent[2] := 0 | `[0,0,0,2]` | `{0,1,2,3}` |

The final lookup for 3 follows `3 -> 2 -> 0`; all four lookups return 0. The repository proves the concrete final list, lookup results and lengths using `decide`.

This establishes useful concrete facts. It does not yet implement general union-by-rank or path compression: the three parent writes are selected manually and rank is unused. The state is public pure data, so branching it is permitted. The proof argument of `writeParent` is not a sealed mutable execution interface.

The general structure also needs a stronger representation invariant: equality of parent/rank lengths does not establish equality with the owner's extent. A permitted index according to the owner need not be in the actual list for an arbitrary `UF`. Nor does ownership require a written parent value to be a valid vertex or preserve an acyclic forest.

## 6. Put union-find through the runner

Start with one exclusive capability for the entire union-find object. Use a representation whose permission coordinates are explicit. Two reasonable choices are a single array of `{parent, rank}` records, or two separately owned arrays. The current pair of lists plus one four-index owner does not itself specify a physical layout over both arrays.

For a first implementation, use records and define field updates as operations on an owned record index. Then expose an algorithm API whose internal operations use the same checked runner:

```text
runFresh {
  uf := makeUnionFind(4)
  union(uf, 0, 1)
  union(uf, 2, 3)
  union(uf, 0, 2)
  roots := map(findCompress(uf), [0,1,2,3])
  answer := immutableCopy(roots)
  dispose(uf)
  return answer
}
```

Specify tie-breaking if the test expects representative 0. Component membership is the general semantic property; representative identity is an implementation choice.

### Find with path compression

```text
findCompress(uf, x):
  p := readParent(uf, x)
  if p == x: return x
  r := findCompress(uf, p)
  writeParent(uf, x, r)
  return r
```

Each read/write uses the current capability. A simple implementation threads the whole exclusive capability sequentially; recursion need not introduce loans. If the API uses lexical reborrowing, the recursive call receives a reborrow and returns it before the enclosing frame writes.

At the inspected final state, compression of 3 changes `[0,0,0,2]` to `[0,0,0,0]`. Ownership proves the update is authorised. A separate algorithm proof shows that redirecting 3 to its existing root preserves the represented partition.

### Union by rank

```text
union(uf, x, y):
  rx := findCompress(uf, x)
  ry := findCompress(uf, y)
  if rx == ry: return
  compare rank[rx] and rank[ry]
  attach the lower-rank root under the higher-rank root
  on equal rank, choose one root and increment its rank
```

First prove parent bounds, forest validity, find termination/correctness, and partition semantics for union and compression. Rank invariants support the algorithm and later complexity analysis; they are distinct from ownership. Avoid claiming amortised complexity until its additional argument is supplied.

## 7. Splitting and borrowing in union-find

Fractional splitting is useful for simultaneous **read-only, non-compressing** finds:

```text
(readerA, readerB) := splitFraction(whole, 1/2, 1/2)
a := findReadOnly(readerA, 3)
b := findReadOnly(readerB, 1)
whole := join(readerA, readerB)
findCompress(whole, 3)
```

`findCompress(readerA, 3)` must be rejected: path compression writes. The join must establish compatible provenance and consume both children. Concurrent scheduling would require additional execution and synchronisation reasoning; fractional permissions alone do not supply a scheduler.

Spatial splitting does **not** automatically permit general independent union-find operations. In `[0,0,0,2]`, a view of indices `[2,4)` cannot complete `find(3)` entirely inside that footprint: the traversal reaches 0. Spatial splitting works for initialisation and for separately maintained components whose parent edges stay within their regions. A union across regions requires sufficient authority over the relevant regions and a suitable protocol, or reconstruction of whole-object authority.

Use a split-array fill or map as the first divide-and-conquer demonstration. Use union-find to demonstrate data-dependent traversal, whole-object exclusive mutation and fractional read-only access.

## 8. Acceptance tests and delivery order

| Priority | Deliverable | Acceptance evidence |
| --- | --- | --- |
| P0 | One complete world invariant | Initial world satisfies it; every supported transition preserves it |
| P0 | Unified checked execution | Writes, splits, loans, joins and disposal share one authoritative state |
| P0 | Sealed resource boundary | No raw mutable alias or stale model proof can authorise mutation |
| P1 | Complete array example | Allocate, split, fill, fractional reads, rejoin, restore, snapshot, free |
| P1 | Union-find through runner | Concrete trace above executes through the same checked operations |
| P1 | General union-find correctness | Forest and partition proofs for find, compression and union |
| P2 | Mutable backend refinement | Concrete storage implements model steps and preserves confinement |
| P2 | Specialisation/performance | Eliminate justified checks and measure actual copying and allocation |

Required negative examples: stale parent after split; duplicate child IDs; expired borrower; enclosing loan ended before child; free with outstanding claims; stale access after free; handle replay across runs; compression under fractional read permission; parent traversal outside a spatial view.

Required positive examples: repeated writes through a live full capability; true nested reborrow followed by restoration; two fractional read-only finds followed by reconstruction; path compression preserving components; independent repeated runs of the same closed program.

Every safety theorem should have a nontrivial closed instance satisfying its premises. Record build commands, revision and actual validation results. Keep logical permission, algorithm correctness and physical no-copy guarantees explicit in the report.

## 9. Concrete type discipline and world threading

This section is the implementation specification for the architecture above. Signatures are Lean-like design sketches; they have not been elaborated. In particular, the dependent interpreter and syntax instances need implementation work. Do not present these sketches as existing repository definitions.

### 9.1 Separate permission indices from runtime contents

Use three layers:

```lean
-- Public mathematical descriptions; freely copyable.
structure Ctx where
  arena       : ArenaId
  allocations : AllocationTable
  capabilities : CapabilityTable
  loans       : LoanTable
  nextId      : Nat

structure ModelWorld where
  ctx  : Ctx
  heap : ModelHeap

def WellFormed (Γ : Ctx) : Prop := ...
def Realizes (w : ModelWorld) (Γ : Ctx) : Prop :=
  w.ctx = Γ ∧ WellFormed Γ ∧ StorageMatches w.heap Γ
```

The runtime backend has a separate private representation. Do not put the entire byte contents in every computation's type merely to track ownership. Permission indices describe which operations are legal; functional specifications describe values and algorithm results. Keeping those roles separate makes symbolic programming practical.

`Ctx` is ghost state: making a copy does not copy an allocation or confer authority over a running instance. The only route from a context-indexed program to actual mutation is the sealed interpreter.

### 9.2 Handles name entries; judgements grant permission

```lean
structure Handle (ρ : ArenaId) where
  alloc : AllocId
  cap   : CapId
  generation : Nat

def CanRead  (Γ : Ctx) (h : Handle Γ.arena) (i : Nat) : Prop := ...
def CanWrite (Γ : Ctx) (h : Handle Γ.arena) (i : Nat) : Prop := ...
```

The index connects a name to an arena. The predicates check live allocation, matching generation, bounds, current capability status, applicable lifetime, and sufficient permission. A write requires the full share and a read-write ceiling. A read requires a positive share and permission to observe that footprint.

For the certified AST, even publicly constructible handles are logically safe: inventing a name does not produce a proof of `CanWrite`. Opaque handles can improve the API, but the soundness theorem must rely on the judgement and execution correspondence, not on the inability to spell an integer. Runtime imports must still validate identity and cannot trust a phantom arena parameter alone.

### 9.3 A result-indexed computation

Use the following mathematical interface:

```lean
Prog (Γ : Ctx) (α : Type) (Q : α → Ctx) : Type
```

It denotes a program starting with permissions `Γ`, returning `a : α`, and finishing with permissions `Q a`. `Q` may depend on a returned fresh handle or on a branch result. This is an indexed monad; it is not an ordinary `StateM Ctx` exposed to clients.

The essential rules are:

```lean
pure : (a : α) → Prog Γ α (fun _ => Γ)

bind : Prog Γ α Q →
       ((a : α) → Prog (Q a) β R) →
       Prog Γ β R
```

Here `R : β → Ctx` is the common final context family. A continuation whose final context also depends on `a` can return `⟨a, b⟩` in a dependent pair, allowing the final context to depend on both. A simpler implementation can begin with fixed-postcondition `Ix Γ Δ α`, then add dependent results when allocation and branching require them.

Bind's type requires the second computation to start from exactly the permissions produced by the first. The interpreter must implement the same rule on runtime state. A type annotation naming `Q` without a semantic relation to execution is insufficient.

### 9.4 Make programs certified syntax, not arbitrary state functions

Define an indexed instruction family `Op Γ α Q`, with a constructor for every supported primitive and its evidence. Define programs from `pure`, primitive instructions and sequencing:

```lean
-- Schematic indexed inductive family.
inductive Prog : (Γ : Ctx) → (α : Type) → (α → Ctx) → Type where
  | pure ...
  | prim : Op Γ α Q → Prog Γ α Q
  | bind : Prog Γ α Q →
           ((a : α) → Prog (Q a) β R) → Prog Γ β R
```

This is a proposed deeply embedded effect language, allowing host-language continuations for pure control flow. Its constructors may be public if they enforce their premises and there is no constructor for arbitrary backend access. The trusted evaluator pattern-matches on this syntax; it never calls a client-supplied function of type `RuntimeWorld → IO RuntimeWorld`.

Lean positivity/universe details must be resolved in the implementation. For the first total fragment, structurally recursive folds over finite data are sufficient. Unbounded recursion needs an explicit semantics and partial-correctness/termination story; it must not enter through an unchecked general-purpose effect constructor.

An alternative representation is raw syntax packaged with a typing derivation. That is equally acceptable if the interpreter executes exactly the packaged syntax and the proof is tied to it. Do not maintain an independent permission program and an unrelated executable program.

### 9.5 Primitive transitions

Write down declarative transition relations first, with executable checkers proved sound against them:

```text
WriteOK Γ h i                       -- preserves ownership context
SplitSpatial Γ h k left right Γ'
SplitFraction Γ h q₁ q₂ r₁ r₂ Γ'
Join Γ left right restored Γ'
BeginLoan Γ lender borrower λ Γ'
EndLoan Γ borrower λ restored Γ'
Dispose Γ owner Γ'
```

Corresponding primitive types have this shape:

```lean
read  (h) (i) (p : CanRead Γ h i) : Prog Γ UInt8 (fun _ => Γ)
write (h) (i) (v) (p : CanWrite Γ h i) : Prog Γ Unit (fun _ => Γ)

splitAt (h) (k) (p : SplitSpatial Γ h k l r Γ') :
  Prog Γ Unit (fun _ => Γ')

endLoan (p : EndLoan Γ borrower λ restored Γ') :
  Prog Γ Unit (fun _ => Γ')
```

For deterministic fresh-ID allocation, `l` and `r` are computed from `Γ.nextId` and made available by the surface elaborator; returning unit avoids pretending the IDs are unpredictable runtime data. A dependent-result variant can return the handles and index its post-context by that result. Choose one convention consistently.

Each transition must preserve `WellFormed`. A spatial split retires the source identity, produces distinct fresh children, and records reconstruction provenance. A loan suspends the applicable lender authority. Ending it requires discharged descendants and consumes borrower authority before restoration. Disposal requires the entitlement, reconstructed authority and absence of outstanding dependent claims.

The concrete runtime operation and its ghost update form one semantic step. For example, a split may change only ledger metadata while retaining one buffer; it must not accidentally create two independently owned buffers or two unchecked mutable aliases.

### 9.6 How bind prevents stale use

```text
Γ0: h active over [0,64)
Γ1: h retired; left active [0,32); right active [32,64)

splitAt h 32 : Prog Γ0 Unit (const Γ1)
write h 0 7  : requires CanWrite Γ1 h 0 in the continuation
```

The old proof `CanWrite Γ0 h 0` has the wrong index. Bind does not accept an action requiring `Γ0` after the split. Replacing a context by a propositionally equal context is legitimate transport; a well-formed split should give no proof that `Γ0 = Γ1`.

The host can copy an entire `Prog Γ0 ...` value. It cannot execute that value against an arbitrary live world because that execution entry point is not exported. Inside a program, sequencing two copies is accepted only if the first post-context meets the second pre-context. Repeated ordinary writes are accepted because writes preserve permissions; repeating a consuming split is rejected.

### 9.7 Symbolic branches and loops

Both branches must produce a common final context, or return a tagged result whose post-context records which branch occurred. Scope combinators should restore their borrowed resources before returning so callers do not inherit unnecessary context differences.

```text
if condition then
  write h i a
else
  write h j b
-- both branches preserve Γ
```

A branch that disposes `h` cannot silently merge with one that retains it. Require explicit cleanup in both branches, or return a sum with different post-contexts.

For a loop, use a context invariant and a separate value invariant. An array fill usually preserves its ownership context throughout; its functional invariant records the prefix already written. Bounds evidence may be carried as `Fin n`, proved from a loop invariant, or generated by a checked bounds test. Hidden indices do not remove those obligations.

## 10. Operational threading and sealing

### 10.1 Reference interpreter

For the total, ideal-allocation fragment, the semantic interpreter should have a result shape equivalent to:

```lean
eval (p : Prog Γ α Q) (w : ModelWorld) (h : Realizes w Γ) :
  Σ a : α, { w' : ModelWorld // Realizes w' (Q a) }
```

The bind case explicitly threads the returned world:

```text
eval (bind p k) w h =
  let (a, w1, h1) := eval p w h
  eval (k a) w1 h1
```

It never evaluates the continuation against the original `w`. This is the dynamic counterpart of bind's static context matching.

This signature expresses permission preservation only. Add a denotation or execution relation relating input heap, program, returned value and output heap to establish functional behaviour. Preserve that relation in the real-backend refinement proof.

Real allocation may fail. Either restrict the first runner to preallocated storage, or use an outcome type whose failure case specifies the remaining owned state and cleanup. A bare exception escaping halfway through a loan does not establish resource safety.

### 10.2 Concrete runner

Implement a private backend machine with storage and authoritative resource metadata. Relate it to the model:

```text
BackendRel concrete model
```

For each primitive, show that its concrete execution simulates the model transition and preserves this relation. The runner sequences concrete state exactly as the reference interpreter sequences model state. It may retain runtime ledger checks initially. Erasing checks requires a theorem that the certificate, current state and backend representation guarantee the same legal transition.

The safe public module exports program builders and a fresh-run operation. It does not export the raw backend evaluator, mutable pointers, a world injection function, or an operation interpreting an arbitrary model snapshot as the current runtime world. In particular:

```text
runFresh : ClosedProgram SafeResult -> IO SafeResult
```

is an appropriate first executable interface. `ClosedProgram` requires an empty initial resource context and a discharged final resource context. The final context may retain fresh-ID history; it need not literally equal the initial context. `SafeResult` initially means scalar data and independently owned immutable snapshots.

For a purely functional public runner, separately prove that all effects are confined and the observable result agrees with the pure semantics. Returning in `IO` initially avoids claiming that additional property prematurely.

### 10.3 What is sealed

| Entity | Public? | Reason |
| --- | --- | --- |
| Model contexts/worlds and predicates | Yes | Clients need them for proofs; copying them has no runtime authority |
| Certified program syntax and safe combinators | Yes | Constructors enforce permitted transitions |
| Handle names | May be | Current-context validity, not secrecy, grants authority |
| Concrete mutable storage and evaluator state | No | Prevent alias extraction and authority forks |
| Raw primitive mutation functions | No safe public access | All mutation must pass through certified execution |
| Debug snapshots | Yes, immutable | They must have no route back into live authority |
| Fresh runner | Yes | Creates and cleans up its own managed resources |

Specify the trusted boundary explicitly: safe clients using the exported API are covered; arbitrary `unsafe` code, unchecked FFI mutation and illicit access to implementation internals are outside that claim. Module privacy is an API boundary, not a proof against an attacker who can replace the runtime or bypass the language's safety restrictions.

Host callbacks initially remain pure functions over safe data. Do not add `liftIO` or arbitrary callbacks receiving buffer aliases to the certified language. Reentrancy and concurrency require extending the semantics and authority protocol.

## 11. Hidden indices and authoring syntax

The core types carry contexts explicitly. A custom elaborator can hide them by constructing an indexed program and its evidence:

```text
ownership do
  h ← allocBytes 64
  (left, right) ← splitAt h 32
  fill left 1
  fill right 2
  h' ← join left right
  result ← snapshot h'
  free h'
  return result
```

At each statement the elaborator maintains the symbolic current context, resolves source variable names to capability identities, synthesises a transition, discharges decidable side conditions, and updates the context for the continuation. The generated kernel term contains the indexed program and required evidence. The elaborator itself need not be trusted if all certificates are kernel checked.

For symbolic bounds and contracts, generate proof obligations rather than guessing. Function interfaces must expose enough context transformation information for modular composition. A user-defined function cannot be treated as safe merely because its body happened to pass a closed example.

Do not promise ordinary Lean `do` integration before implementing the indexed bind syntax. A dedicated `ownership do` surface is sufficient initially. The internal contexts can be implicit parameters and inferred metavariables; they do not have to be erased from the mathematical interface.

## 12. Union-find expressed in this discipline

Begin with a single capability for an array of parent/rank records. Define `UFRep heap h partition` separately from ownership. It states storage length, parent bounds, forest validity and the represented partition. The owner gives legal access; `UFRep` gives the data its algorithmic meaning.

### 12.1 Permission signature

An initial find-with-compression interface can preserve the context:

```text
findCompress(h, x, wholeWritable, forestEvidence)
  : Prog Γ Vertex (const Γ)
```

Its functional specification says that the returned vertex is the original root, the final heap is a valid forest, and the represented partition is unchanged. Its implementation reads parents and performs authorised writes. It must use a well-founded measure or justified fuel; fuel exhaustion is an explicit result unless proved impossible for valid inputs.

Union similarly preserves the ownership context while changing the partition specification. Thus sequencing union-find operations does not require allocating a fresh permission context at every write. Heap values change even when permission indices remain the same.

### 12.2 Scoped borrow interface

For modular lending, provide a combinator whose implementation creates a loan, invokes a certified body in the borrowed context, verifies reconstruction, and ends the loan:

```text
withMutBorrow lender (fun borrower => body)
```

The body must have a post-context satisfying `Returnable loan`: no live descendants, required authority reconstructed, and no unaccounted delegated fragments. The combinator then consumes borrower identities and restores lender access. It does not accept an arbitrary host callback with raw access to the buffer.

For recursive reborrowing the context evolution is:

```text
Γ0: owner active
Γ1: owner suspended; outer borrower active
Γ2: owner suspended; outer suspended; inner borrower active
Γ3: owner suspended; outer restored; inner consumed
Γ4: owner restored; outer consumed; inner consumed
```

A recursive `findCompress` may run under the inner borrower. Its return must reach `Γ3` before the outer frame writes its compressed parent. Ending the outer loan in `Γ2` is ill-typed because its returnability condition fails.

Initially, sequentially threading the whole capability is simpler than recursive reborrowing and sufficient for union-find. Implement the scoped borrow separately and test genuine nesting before using it to make the algorithm interface more modular.

### 12.3 Returning values and avoiding escape

A returned vertex number is ordinary data and carries no authority. A snapshot must have an independent immutable representation. A captured borrower handle in a closure must never grant access after its loan ends: later operations require the current context where it is consumed.

For the first runner, restrict results to explicitly supported safe data. General higher-order results require a carefully specified escape policy. An arena type parameter by itself is not a complete escape proof in dependent Lean: existential packages can hide indices. Safety must still follow from the absence of a live execution entry point that accepts escaped authority.

### 12.4 Implementation acceptance criterion

Deliver one source program that allocates the four-element union-find, performs the three unions, compresses paths, returns the representatives, and disposes the allocation. Its generated type must begin with an empty resource context and end with a discharged one. Prove its model result and connect the same program to backend execution.

Add compile-time refusal examples for a stale handle after split, an outer borrower used during an inner loan, and path compression through a fractional reader. If any condition is intentionally dynamic, label the test as runtime rejection instead. This distinction must be reflected in the paper's description of the type discipline.

## Sources

- Supplied `ownership-encapsulation-argument.md`: architectural argument and reported newer `Unified`/`Indexed` implementation.
- Supplied `CAP_OWNERSHIP_REVIEW_HANDOFF_979729b.md`: earlier findings and acceptance targets.
- [Inspected union-find implementation](https://github.com/scidonia/ownership/blob/979729bdbdc31ee8a2f5475f372cde29279d1c12/Cap/UnionFind.lean).

The immediate goal is a single execution story: a program receives authority, performs authorised algorithm operations, restores delegated authority, and disposes its resources, with proofs attached to that same execution.
