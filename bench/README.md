# Union-find on the array write path

This directory is a benchmark, not part of the proof development. The union-find
program is hand-written Lean: it is not generated from the ownership discipline,
and no rule in the development checks it. What it exercises is the same runtime
mechanism the discipline models — Lean's copy-on-write array update — on code
outside the certified fragment.

Two variants run the same algorithm (path halving, union by size over two
`Array Nat`s):

- **unique** — the loop carries the only reference to the parent array;
- **shared** — a snapshot of the current parent array is taken each iteration and
  read after the update, so the array is still shared at the write.

```
cd bench
nix develop -c lake build
./.lake/build/bin/unionfind
```

## Measured: per outer iteration

`m` is the number of outer union-find iterations. Each iteration performs two
finds, and a union store only on the branches that take one, so the printed
`best / m` is **nanoseconds per iteration**, not per `Array.set!` call. The two
variants are compared at equal `n` and `m`.

| mode | n | m | ns/iteration |
| --- | ---: | ---: | ---: |
| unique | 2 000 | 8 000 | ~66–75 |
| unique | 16 000 | 64 000 | ~66–75 |
| shared | 2 000 | 8 000 | 559 |
| shared | 4 000 | 16 000 | 1 142 |
| shared | 8 000 | 32 000 | 2 174 |
| shared | 16 000 | 64 000 | 5 288 |

The union-find state checksums agree between the two variants at equal `n` and
`m`: sharing changes the cost, not the result. Over the measured range the
unshared workload stays roughly flat while the shared one grows with the array
size. The shared numbers are whole-iteration costs that include the copying
update; they are not a per-store coefficient and do not measure copy bandwidth.

These are single-machine, three-repetition minima, at one input size per point;
run-to-run variation is around ten to twenty percent. They are a workload-level
observation, not a cost theorem.

## The generated program family

`scripts/emit_program.lean` defines programs in the model language
(`Ownership.Code`), has the discipline's checker accept them, and emits them as
Lean into `bench/Generated.lean`, which the bench package's `generated` target
builds. Because the checker requires multiplicity one at every write, every
emitted program is a certified in-place path; there is no certified shared variant.

```
nix develop -c lake env lean scripts/emit_program.lean
cd bench && nix develop -c lake build generated
./.lake/build/bin/generated
```

Observed, with a fresh input array built per trial outside the timed region:

| writes | ms | ns/write |
| ---: | ---: | ---: |
| 200 | 1 | 6 062 |
| 1 000 | 1 | 1 253 |
| 4 000 | 1 | 318 |

The total is flat at about 1.2 ms across a twentyfold change in the number of
writes, so the per-write figure mostly amortises a fixed cost. **What that fixed
cost is has not been established**, and the harness does not verify the consuming
write's disposition; it therefore does not demonstrate an in-place timing result.
Establishing either needs instrumentation of the write path.

## A static alias/linearity check (experimental)

`bench/Alias.lean` provides `#alias_check term`, an elaboration-time check over
Lean terms. It tracks array-typed `fun`/`let` binders by de Bruijn index, allows
any number of borrowed reads (`size`, `getD`, `uget`, `back?`), allows at most one
move per path (writes, other calls, returns, rebinds), takes the maximum over `if`
branches, and refuses a capture under a lambda past the parameter spine.

| File | Shape | Result |
| --- | --- | --- |
| `AliasOk.lean` | transfer and a `foldl` loop | accepted |
| `AliasUfThread.lean` | union-find's `find`: borrow, borrow, move, return | accepted |
| `AliasBad.lean` | duplicated handle | rejected |
| `AliasBadCapture.lean` | closure capture | rejected |
| `AliasBadShared.lean` | retained alias at the write | rejected |

It is **experimental and not sound as a usage checker**. It tracks binders, not
owners, does not record that a particular owner has been consumed, ignores moves in
`if` conditions, and treats two reads of a container as two independent owners.
`AliasKnownGaps.lean` records three programs the current checker accepts though
they violate the intended discipline:

- reading the old array after the consuming write;
- consuming the array in a condition whose branches then use it;
- two binders obtained from the same element read, each later written.

Closing these needs an ordered ownership-state analysis (availability, condition
before branches, branch-state merge, ownership effects for calls and projections)
and a refusal to treat a read of an array-valued element as a fresh exclusive
owner. Until then the check is a demonstration of the analysis shape, not a
discharge of the model's multiplicity-one premise; `Ownership.Accounted` remains
the semantic half.

## What this does and does not show

The union-find comparison shows the runtime disposition qualitatively: the same
algorithm and results, a workload that is flat in the array size when the array is
unshared and grows with it when each write shares it. That is an observation about
this binary and this machine.

Nothing here certifies the union-find program, proves a cost model, or verifies
that the emitted C takes the in-place branch for the generated family. The
certified path inside the fragment is the emitted program and its agreement with
the model interpreter; the writes' runtime disposition remains observed, not
proved.

## Union-find performance probe: native Lean vs the ownership models

`bench/CapUFPerformance.lean` (`lake exe capufbench`) compares one full-path
find from the deepest node of an identical parent chain in three representations:

- **lean-array**: native Lean `Array Nat`, find plus full path compression;
- **uf-list**: the functional `Cap.UF` model (`findRootF` + `compressAll`);
- **sealed**: the `Cap.Sealed` byte-encoded machine, with every parent read and
  compression write crossing the checked sealed boundary.

Construction is outside each timed region. The executable and toolchain are the
same for all three rows (Lean 4.35.0-rc3, compiled executable on the worker).
The sealed row includes capability checks and list-backed byte storage; it is
**not** a native ownership backend and these are not amortized or
union-by-size results.

Observed on two runs of the same worker; values are nanoseconds per
find-and-compress, 200 repetitions, minimum (mean in parentheses):

| n | lean-array | uf-list | sealed | sealed / lean-array |
| ---: | ---: | ---: | ---: | ---: |
| 32 | 359 (375) | 12 052 (14 083) | 19 050 (20 412) | ~53× |
| 128 | 1 774 (1 826) | 161 949 (181 624) | 199 776 (216 704) | ~113× |
| 256 | 3 670 (3 877) | 628 291 (673 230) | 751 866 (799 577) | ~205× |

The second run differed by a few percent. The sealed byte model is roughly two
orders of magnitude slower than native Lean `Array` at the 256-node limit, and
the pure functional list model accounts for most of that gap; the sealed checks
add roughly 20% at 256. This is a model-vs-native comparison on one machine, not
a claim about a specialized mutable implementation or asymptotic complexity.

## Erased runtime union-find (Phase 1/2)

`CapRuntime` is a separate library with no ghost imports. `bench/CapRuntimeUF.lean`
(`lake exe capruntimeuf`) measures a raw `ByteArray` parent array with full-path
compression against native Lean `Array Nat`, on the same chain and with
construction outside the timed region. Runtime correctness control:
`CapRuntimeTest.lean`; boundary check: `scripts/check_runtime_imports.sh`.

Observed on two runs, compiled rc3 executable, 200 repetitions, best ns/mean ns:

| n | native `Array Nat` | runtime `ByteArray` |
| ---: | ---: | ---: |
| 32 | 337–347 / 360–371 | 221–224 / 236–237 |
| 128 | 1,827–1,828 / 1,862–1,871 | 846–875 / 935–964 |
| 256 | 3,727–3,773 / 3,824–3,916 | 1,638–1,715 / 1,835–1,863 |

The runtime is ~1.5× faster at 32 and ~2.2× faster at 256 than the native
`Array Nat` path in this microbenchmark. Both are Lean-managed values; this is not
a C/FFI comparison. The important result is the separation: the ghost interpreter
at 256 was ~752,000 ns, while the erased raw runtime is ~1,700 ns. `CapRuntime`
is not yet connected to a certificate/refinement theorem, so this is runtime
performance, not certified-runtime performance.
