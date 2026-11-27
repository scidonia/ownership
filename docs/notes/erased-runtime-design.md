# Erased certification and runtime execution

The current sealed machine is a proof-facing model. It is not a runtime
representation:

- `Cap.Integrated.Sealed` carries `Reconstruction.State` values: `Forest`,
  `Restore` obligations, `issued`/`retired` histories and a list-backed `Heap`.
- `sealedFind` reads and writes those structures while it runs.
- The 256-node benchmark therefore measured a persistent list interpreter with
  capability checks, not an ownership-aware native backend.

## Required separation

### Ghost / certification side

- `State` and `Forest` remain the specification and proof state.
- A certificate is a type inhabited only by evidence: command/index parameters,
  resource and identity facts, and an accepted-run proof.
- Certificate fields that exist only for proof are in `Prop` or are used solely
  by the proof checker. They must not be read by runtime code.
- `CertifiedProgram` erases to a runtime program. The erasure relation is a
  theorem, not an executable dependency.

### Runtime side

The executing state contains only data needed to run:

- allocation table keyed by a runtime allocation id;
- `ByteArray` / `Array UInt8` storage per allocation;
- runtime handles/capability ids, lengths and offsets;
- the union-find parent bytes and any auxiliary bytes;
- no `Forest`, `Restore`, `CapId` proofs, issued/retired ghost histories or
  list-model heap.

The raw union-find operation performs indexed reads and in-place byte writes.
Capability checks may remain as cheap runtime checks, or be erased when the
certificate proves them; either way they consume runtime fields, not ghost data.

## Interface sketch

```lean
-- Proof side, erased from the executable path.
structure Certified (pre : Ghost.State) (α : Type) (post : Ghost.State → α → Prop) where
  program : Runtime.Program
  accepted : Checked pre program ...
  refinement : Runtime.Executes program ... post

-- Runtime side: no ghost state in any field.
structure Runtime.State where
  allocations : Array Runtime.Allocation
  ...

def Runtime.exec (s : Runtime.State) (p : Runtime.Program) : Runtime.State
```

`Certified` may contain `program` because that is the code to run; its proof
fields must never be inspected by `Runtime.exec`. A compile/erase function
returns only the runtime program and any runtime constants.

## Correctness statement

For every certificate `c`:

- `Runtime.exec (erase c) init = eraseState (Ghost.run c)`;
- runtime observations equal the certified model's observations;
- the runtime operation does not read ghost fields.

The refinement theorem is the bridge; it is not an interpreter over the proof
state.

## Performance acceptance

Benchmark only the runtime path. Report separately:

1. raw `ByteArray`/`Array` union-find baseline;
2. runtime backend with ownership checks;
3. ghost certificate-checking cost (compile-time, excluded from execution).

No performance claim should be derived from `Cap.Sealed` or `UF.Arr` again.
The existing `bench/CapUFPerformance.lean` results are model-cost evidence, not
runtime evidence.
