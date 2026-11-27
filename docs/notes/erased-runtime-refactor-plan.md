# Erased-runtime refactor plan

Status: Phases 1–3 are green; Phase 4 (byte/write/alloc refinement) is next.

- `CapRuntime` exists as a separate library with no ghost imports.
- Raw `ByteArray` union-find and the runtime control compile and run.
- On a 256-node chain the raw runtime is ~1,700 ns versus ~3,750 ns for native Lean `Array Nat`; the ghost interpreter was ~752,000 ns.
- Runtime performance is not yet certified performance; the refinement relation is pending.
- Phase 3 now has `CapCertified.CertifiedProgram` with a proof-only `sound` field and an `erase` projection; the runtime import boundary rejects certificate/ghost imports. The current `Cap.Sealed`/`UFGeneric` interpreter is a
proof-facing model. It is not the runtime.

## 1. Contract

The refactor must establish all of the following:

1. **Certification is not execution.** A proof/certificate value has no role in
   the running program. Proof-only fields are erased or projection-only.
2. **Runtime carries no ghost state.** No `Forest`, `Restore`, `issued`,
   `retired`, `Coherent`, `Recovers`, `State.Inv` or list-model heap is read by
   runtime code.
3. **Runtime uses raw storage.** Parent/byte state is `ByteArray`/`Array` based,
   with indexed reads and constant-time updates on a uniquely referenced buffer.
4. **Correctness is a refinement theorem.** The runtime state relates to the
   ghost model by an explicit representation relation; execution refines the
   ghost semantics under stated checks.
5. **Existing proofs remain the specification.** Do not delete or weaken the
   reconstruction/ownership theorems. They move to the specification side.
6. **Performance is measured only on the runtime path.** Ghost-interpreter
   timings are labelled model cost and never presented as runtime performance.

## 2. Target architecture

```
                    proof / compile-time side
     ┌──────────────────────────────────────────────────┐
     │ Ghost model: Reconstruction.State, Forest,       │
     │ Restore, Accounts, Coherent, Scope, Inv          │
     │ CertifiedProgram: runtime program + proof fields │
     └───────────────────────┬──────────────────────────┘
                             │ erase / compile (proof only)
                             ▼
     ┌──────────────────────────────────────────────────┐
     │ Runtime.Program: commands, handles, lengths      │
     │ Runtime.State: allocation table, ByteArray bytes │
     │ Runtime.Exec: in-place reads/writes, no ghost    │
     └──────────────────────────────────────────────────┘
                             │
                             ▼
                  native Lean arrays / C backend later
```

The refinement theorem lives on the left and relates the two. It is not called
by `Runtime.exec`.

## 3. Module plan

New modules, all under `Cap/` and imported by `Cap.lean` only after their gates
pass:

| Module | Contents |
| --- | --- |
| `Cap/Runtime/Types.lean` | `Runtime.AllocId`, `Handle`, `Allocation`, `State`; no proof fields; live/retired generation bookkeeping that is genuinely runtime data |
| `Cap/Runtime/Bytes.lean` | `ByteArray` access/update, allocation table lookup, bounds checks, optional `ST`/unique-buffer API |
| `Cap/Runtime/Cmd.lean` | runtime command type: alloc, write, borrow, split, reconstruct, return, free; no ghost proofs |
| `Cap/Runtime/Exec.lean` | raw interpreter over `Runtime.State`; refusal/error outcomes; no model call |
| `Cap/Runtime/UF.lean` | `ByteArray` parent array, path chase/compression, union if/when specified; in-place update path |
| `Cap/Certified/Spec.lean` | ghost pre/post specifications and the accepted-run predicate |
| `Cap/Certified/Program.lean` | `CertifiedProgram` with `program : Runtime.Program` and proof fields; `Certified.view` projection |
| `Cap/Certified/Erase.lean` | `erase : CertifiedProgram → Runtime.Program`; proof that erased runtime commands are the source commands |
| `Cap/Certified/Refines.lean` | `Rep` between runtime and ghost state; execution/refinement theorems |
| `Cap/Recovery.lean` | ghost-interpreter completion strategy: recursive normalization of a designated obligation to accepted return/reconstruction commands, termination measure and framing |
| `Cap/Runtime/Refinement.lean` | optional re-export/layer for clients; no ghost fields in runtime structures |

Existing modules keep their names and proofs:

- `Cap/Reconstruction.lean`, `Cap/Integrated.lean`, `Cap/Sealed.lean`,
  `Cap/UFGeneric.lean`, `Cap/UFIntegrated.lean`, `Cap/UFReuseRunner.lean`,
  `Cap/Counted*` remain the specification/proof side.
- Their executable `Option`/`Except` interpreters become **spec interpreters**.
  The paper and docs must not call them the runtime.

## 4. Runtime data model

```lean
namespace Cap.Runtime

structure Allocation where
  bytes : ByteArray
  len   : Nat
  live  : Bool
  generation : Nat
  -- optional: base address / storage class, no ghost fields

structure State where
  allocations : Array Allocation
  nextGeneration : Nat
  -- no Forest, Restore, Accounts, Inv

structure Handle where
  alloc : Nat
  generation : Nat
  offset : Nat
  -- authority bits if runtime checks are retained
```

Rules:

- `Handle` validity is runtime: live allocation, matching generation, in bounds.
- If the certificate erases capability checks, the runtime command is only
  constructible through an erased certified program; direct runtime entry keeps
  the cheap checks.
- `Retired`/history needed for stale-handle refusal is runtime generation data,
  not the ghost `issued`/`retired` lists.
- No `List UInt8` in the runtime allocation; `ByteArray` is the storage.
- No proof object is stored in `Allocation` or `State`.

## 5. Certificate and erasure

```lean
structure CertifiedProgram where
  program : Runtime.Program
  spec    : Ghost.Spec
  accepts : Ghost.Accepts spec program
  refines : Ghost.Refines spec program
```

- `program` is the only runtime-read field.
- `accepts` and `refines` are proof-only; they must not be matched by runtime
  code.
- `erase (p) := p.program`.
- Runtime entry points take `Runtime.Program`, never `CertifiedProgram`.
- Add a structural guard/test that `Runtime.Exec` does not import/call the ghost
  modules or inspect certificate fields. A source-level import check is part of
  the architecture test.

If Lean's erasure is not sufficient for a field, restructure it so the proof is a
separate `Prop` argument to a compile-time lemma, not a runtime structure field.

## 6. Refinement relation

Define `Rep : Runtime.State → Ghost.State → Prop`:

- every live runtime allocation maps to one ghost component with equal length;
- `ByteArray` bytes equal the ghost heap buffer;
- runtime handles map to ghost capabilities (allocation, interval, share);
- generation validity corresponds to ghost non-reissuance;
- no ghost forest/restoration state is stored on the runtime side.

Define command refinement for each runtime command:
- allocation creates matching runtime/ghost allocation;
- write updates the same byte in both, preserving all other bytes;
- borrow/split/reconstruct/return correspond to the ghost operations' accepted
  traces and runtime handle updates;
- free removes both and retires the runtime generation.

Required theorems:

```lean
theorem erase_program (p) : (erase p).cmds = p.program.cmds
theorem runtime_exec_refines ... : Rep s g → Runtime.Exec s p = .ok s' →
  ∃ g', Ghost.Run g p spec = .ok g' ∧ Rep s' g'
theorem runtime_no_ghost ... : Runtime.Exec does not read Ghost.State
theorem certified_compiles ... : CertifiedProgram → Runtime.Program
```

The last is a structural/projection fact; the actual semantic result is
`runtime_exec_refines`.

## 7. Union-find runtime

`Cap/Runtime/UF.lean`:

- parent bytes in one `ByteArray` (8-bit node limit for the current domain, or a
  wider cell type if the interface is generalized);
- chase and path compression over `Nat` offsets with direct `ByteArray.get`/`set`;
- no `UF.Arr = List Nat`, no `Sealed.read?`/`write` in the timed path;
- refusal on out-of-range/exhausted chase is runtime-visible;
- a separate `Runtime.UF.Rep` proof layer, not a runtime field.

Performance experiment uses the same chain, query and repetitions as
`bench/CapUFPerformance.lean`, but times `Runtime.UF.find` only. The ghost model
timing is retained as a separate labelled diagnostic.

## 8. Migration sequence

### Phase 0 — freeze and label
- Add `docs/notes/erased-runtime-design.md` (done) and mark all current
  `Sealed`/`UFGeneric` timings as model cost.
- Do not add new performance claims from the ghost interpreter.

### Phase 1 — runtime types and bytes
- Add `Runtime.Types`, `Runtime.Bytes`, `Runtime.Cmd`, `Runtime.Exec`.
- Unit/architecture controls: no ghost imports from runtime; no proof fields in
  runtime structures; ByteArray bounds/refusal cases.
- No certified refinement yet; the runtime is executable but explicitly
  unverified.

### Phase 2 — raw UF runtime
- Implement `Runtime.UF.find`/compression; inhabit a 256-node chain.
- Add benchmark `capufruntime` with the same harness.
- Gate: runtime is O(n) on a path, near native Lean within a measured constant
  factor; no O(n²) list copies.

### Phase 3 — certificate skeleton
- Add `CertifiedProgram`, `erase`, `erase_program`; runtime entry takes only
  `Runtime.Program`.
- Add structural test/AST check that runtime modules do not import ghost modules
  and do not inspect certificate fields.
- Gate: compile/erasure is independent of `Reconstruction`, `Integrated` and
  `Sealed`.

### Phase 4 — refinement for bytes/write/alloc
- Define `Rep`; prove allocation and write refinement with frames.
- Migrate one simple client proof.
- Gate: byte equality, bounds, allocation identity, unaffected allocations.

### Phase 5 — borrowing/reconstruction runtime
- Add runtime handle updates for borrow, split, reconstruct, return, free.
- Prove each refines the corresponding ghost operation under the certificate.
- Preserve generation/non-reissuance and runtime framing.
- Gate: existing nested lifecycle and split/return examples produce the same
  observations through runtime.

### Phase 5b — constructive completion theorem
- Define a recursive completion strategy over the maintained ghost invariant and
  a designated obligation. It returns an actual `List Cmd`, not an assumed trace.
- Prove: `State.run` accepts it; subordinate obligations are discharged; the
  lender is restored; bytes are preserved; unrelated authority is framed.
- Expose the termination measure over combined suspension/loan dependencies and
  the next-step condition; add constraints to the discipline if the proof exposes
  an obstruction.
- This result precedes and anchors the erased runtime client. Its command list is
  then the source for runtime UF/the array client, rather than a second model.

### Phase 6 — UF certified client
- Erase `findRanked`/compression and the completion strategy into runtime
  commands; prove root, exact
  post-array, partition preservation and successor precondition at the runtime
  level.
- Add the parametric split/recurse/reconstruct array client required by the new
  review.
- Gate: a caller needs only functional data/rank/range facts; no ghost state in
  its runtime values.

### Phase 7 — sealed API and LLVM boundary
- Make the sealed API take erased programs; old `Sealed` remains specification.
- Relate runtime `ByteArray` to `LeanLLVM.Mem`/`MemRepMap`; preserve the
  multi-allocation `MemRepMap` composition.
- Keep loader/ABI/native installation as explicit trust contracts.

### Phase 8 — client/test migration
- Port `bench/CapUFIntegrated`, lifecycle and general-find clients to runtime.
- Keep proof-facing models and their tests; they are specification tests.
- Remove duplicate runtime calls in benchmark paths.
- Full suite, controls, axiom audit, docs census and PDFs.

## 9. Gates and evidence

Each phase must run remotely under the pinned rc3 toolchain:

```bash
lake build Cap
lake build CapRuntime          # or the runtime libraries as introduced
bash scripts/check_cap_controls.sh
lake env lean scripts/check_cap_axioms.lean
bash scripts/check_cap_docs.sh --rev WORKTREE
```

Add separate runtime benchmarks:

```bash
lake build capufruntime
./.lake/build/bin/capufruntime
```

and keep the ghost model benchmark labelled `model-only`.

Acceptance for the refactor:

- runtime imports no ghost module;
- no ghost structure occurs in runtime state/values;
- certificate projection/erasure test passes;
- every runtime transition refines its ghost counterpart;
- runtime UF is measured separately and does not use `List.set`/`sealedFind`;
- existing specification theorems, clients and bridge remain green;
- loader/ABI/native limits remain explicit.

## 10. Risks and non-goals

Risks:

- Lean `ByteArray` is still a managed value; in-place behavior depends on
  uniqueness/COW. A C/FFI backend remains a separate runtime contract.
- Proof erasure is not assumed by convention; the structural/projection design
  must enforce it.
- Handle checks may need to remain runtime checks even when proofs erase; this is
  runtime data, not ghost state.
- The ghost model is intentionally retained; it is the specification and is
  never presented as the implementation.

Non-goals for this refactor:

- proving a full C compiler or arbitrary native memory;
- parallel/concurrent ownership;
- amortized complexity of union-find;
- claiming native performance from the ghost interpreter;
- removing the existing reconstruction proofs.
