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
