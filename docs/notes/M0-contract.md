# M0 contract: first certified transform kernel

Status: contract draft, not an implemented certified theorem.

## Supported fragment

Sequential byte-array transformation over one allocation and one borrowed
interval, recursively subdivided into two disjoint halves.

Excluded initially: concurrent mutation, escaping mutable views, arbitrary host
`IO` inside a borrow, callbacks that retain handles, and ordinary Lean functions
outside the supported surface.

## First kernel

For one live allocation `a` of length `n`, an interval `[lo, hi)` with
`0 ≤ lo ≤ hi ≤ n`, and input bytes `xs`:

```text
transform a lo hi f
```

where `f : Nat → UInt8 → UInt8` is a pure element transformation. The operation:

1. borrows the interval from `a`;
2. recursively splits `[lo, hi)` at a midpoint when `hi - lo > 1`;
3. recursively transforms both disjoint halves;
4. joins/reconstructs the parent;
5. returns the lender and the allocation to whole authority.

Zero-length and one-length intervals are explicit base cases. Nonempty
subintervals of a nonempty allocation are required; the current discipline refuses
empty children inside a nonempty parent.

## Required postcondition

For every `i < n`:

```text
result[i] = if lo ≤ i ∧ i < hi then f i xs[i] else xs[i]
```

The allocation length is unchanged, the allocation remains the same allocation,
the whole share is restored, and no live loan or restoration obligation remains.

The returned authority is usable by a second operation without reconstructing the
ledger by hand: the second operation starts from the first operation's successor
context.

## Runtime and evidence

The executed definition:

- reads and writes direct `ByteArray` storage;
- has no per-element `Forest`, `Restore`, share-arithmetic, or command dispatch
  in the hot loop;
- may retain a bounds check at a region boundary;
- performs no backing-buffer copy for a unique-input mutation after entry;
- does not read certificate/proof fields.

The certificate/refinement theorem must be tied to the exact generated definition,
not to a separate command interpreter.

## Benchmark rules

- Construction and input allocation are outside the timed region for every
  implementation.
- Compare identical algorithms, layout, input contents, and operation counts.
- Report unique-input and retained-snapshot workloads separately.
- Report best and median, dispersion, and allocation/copy behavior; not only a
  best-of-run number.
- Report direct Lean and C baselines; C remains a separate trust boundary.
- Do not count `Owned`/`SealedOwned` microbenchmarks as certified performance.

## Existing runtime inventory

- `CapRuntime.Owned`: private `ByteArray`, managed value; `write`/`fillRange`
  return a new wrapper; no release primitive.
- `CapRuntime.SealedOwned`: managed `ByteArray` plus a shared `used` flag;
  `take` refuses consumed/copied handles; no physical free.
- `CapRuntime.State.free?`: marks an allocation not live; storage is reclaimed by
  Lean GC, not by a runtime free.
- `CapRuntime.View.fill?`: one allocation lookup plus a direct `ByteArray` loop;
  no view/session extraction protocol yet.
- `CapCertified.Fractional`: compile-time share proof and runtime view; duplicate
  token use is not statically rejected yet.

## Gate

This contract is satisfied only when:

1. the typed core/checker accepts the transform and rejects the adversarial
   aliasing corpus;
2. generated code is related to the core by a proved refinement;
3. the generated code has the required postcondition and authority restoration;
4. benchmarks follow the rules above;
5. dynamic `SealedOwned` remains an explicitly labelled baseline, not the
   certified surface.
