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

| n | native `Array Nat` | direct Lean `ByteArray` | `CapRuntime` `ByteArray` |
| ---: | ---: | ---: | ---: |
| 32 | 295 / 301–543 | 183–186 / 202–219 | 187–189 / 202–204 |
| 128 | 1,558–1,563 / 1,596–1,598 | 726–736 / 780–785 | 731–733 / 764–789 |
| 256 | 3,221–3,223 / 3,295–3,348 | 1,387–1,390 / 1,504–1,622 | 1,467–1,605 / 1,565–1,772 |

The direct `ByteArray` implementation and the `CapRuntime` wrapper are
indistinguishable at 32 and 128. At 256 the wrapper is 5–15% slower in this
sample, within the observed run variance; the representation, not the wrapper
structure, is the dominant factor. Direct `ByteArray` and `CapRuntime` are both
about 2.2× faster than native `Array Nat` at 256, and the ghost interpreter was
~752,000 ns. Both Lean paths are managed values; this is not a C/FFI result.
`CapRuntime` is not yet connected to a certificate/refinement theorem, so this is
runtime performance, not certified-runtime performance.

### When the Lean variant copies: versioned compression

`capruntimeuf` also compares compression with no retained version against
compression where a pre-write snapshot is read after each write (the
`versioned` variants). That snapshot is a live reference across `set!`, so Lean
copy-on-write copies the array; the unique variants update in place.

Best ns / mean ns for the compression-only phase, same chain and path:

| n | Array Nat unique | Array Nat versioned | ByteArray unique | ByteArray versioned | runtime unique | runtime versioned |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 32 | 194 / 211 | 1,513 / 1,584 | 211 / 227 | 643 / 1,240 | 216 / 226 | 611 / 689 |
| 128 | 818 / 937 | 16,823 / 21,928 | 767 / 845 | 2,697 / 3,139 | 690 / 798 | 2,608 / 2,821 |
| 256 | 1,337 / 1,769 | 51,166 / 65,100 | 1,321 / 1,607 | 5,596 / 6,261 | 1,322 / 1,556 | 5,725 / 6,219 |

At 256 the versioned/unique ratio is ~38× for `Array Nat`, ~4.2× for direct
`ByteArray`, and ~4.3× for `CapRuntime`. Both ByteArray variants copy the compact
byte buffer; the array copies boxed `Nat` storage, so it is far more expensive.
This demonstrates the actual trigger: a live pre-write version, not the presence
of Lean or of an ownership wrapper. A destructive C backend avoids the copy only
if the algorithm does not need the old bytes; if it needs an undo/version log,
it must copy or log them too.

## Split views versus immutable slices

`bench/CapRuntimeTransform.lean` (`lake exe capruntimetransform`) recursively
splits one backing allocation and writes every byte:

- **array-range**: idiomatic Lean, one unique `Array UInt8`, index ranges;
- **immutable-slice**: one backing `Array`, two live logical slices; each write
  and merge copies;
- **runtime-view**: `CapRuntime.View` over one `ByteArray`; the two views are
  disjoint and write in place.

Best ns for the whole transform, 20 repetitions:

| n | array-range | immutable-slice | runtime-view |
| ---: | ---: | ---: | ---: |
| 256 | 1,252–1,400 | 71,885–78,550 | 23,785–25,605 |
| 1,024 | 5,534–5,657 | 1,047,433–1,166,121 | 94,811–103,049 |
| 4,096 | 21,491–23,021 | 13,291,079–14,729,905 | 456,870–463,307 |

At 4,096 the runtime view is **~29× faster than the immutable-slice API**,
because it avoids copying the backing array. It is still **~20× slower than the
unique index-range Array**, because every `View.write?` re-enters the allocation
lookup/handle check. This is a real framework advantage over a safe sharing API,
but not yet competitive with optimized index-range Lean. The fix is bulk/leaf
writes and a cheaper view-to-buffer path, followed by the certified refinement.

### After bulk fill and the runtime Owned mode

`View.fill?` performs one allocation lookup and a direct `ByteArray` loop.
`CapRuntime.Owned` is a private whole-buffer handle with `fillRange`; it carries
no ghost state. Same recursive/split workload, best ns, 20 repetitions:

| n | Array fill loop | ByteArray fill loop | runtime Owned | runtime View | recursive Array | immutable slice |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 256 | 526 | 486 | 622 | 726 | 1,410 | 77,006 |
| 1,024 | 2,219 | 1,699 | 2,064 | 3,103 | 5,384 | 1,165,846 |
| 4,096 | 8,029 | 6,173 | 8,311 | 14,342 | 21,375 | 16,096,317 |

The Owned mode is within ~4% of the optimized array fill loop at 4,096, ~2.6×
faster than the recursive index-range transform, and ~1,900× faster than the
immutable-slice API. It is still ~35% slower than the direct ByteArray loop at
4,096. The per-write `View.write?` path is no longer the bottleneck; remaining
cost is the wrapper/loop and the checksum outside the timed region.

This is the runtime half of the affine model: a private whole-buffer handle and a
direct mutable path. The static one-use checker still needs to be attached to
this runtime Owned type; the existing `bench/OwnedStatic.lean` checker is the
prototype. No certification/refinement is claimed for this runtime yet.

### Dynamic sealed handle cost

`CapRuntime.SealedOwned` carries a shared `used` flag; `take` refuses a consumed
or copied handle. In the bulk-fill transform (one consume per range, not per
byte), it costs about 2% over the unsealed `Owned` mode:

| n | runtime Owned | runtime SealedOwned | array fill loop | immutable slice |
| ---: | ---: | ---: | ---: | ---: |
| 256 | 450 | 485 | 398 | 55,293 |
| 1,024 | 1,690 | 1,740 | 1,515 | 871,730 |
| 4,096 | 6,603 | 6,720 | 5,290 | 10,855,184 |

The control `CapRuntimeSealedTest.lean` verifies that a consumed handle and a
copy of a live handle both refuse a second use. This is the dynamic option; the
compile-time token checker remains the zero-overhead path.
