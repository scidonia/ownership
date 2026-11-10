# Union-find on the array write path

This directory is a benchmark, not part of the proof development. The program is
hand-written Lean: it is not generated from the ownership discipline, and no rule
in the development checks it. What it does is exercise the same runtime mechanism
the discipline models — Lean's copy-on-write array update — on code outside the
certified fragment, to answer a runtime question the development is about: Lean's array
update mutates in place while the array is unshared, and copies when a second
reference is live.

The program is union-find with path halving and union by size over two `Array
Nat`s, compiled to a native binary (`lean_exe unionfind`). Two variants run the
same algorithm:

- **unique** — the loop carries the only reference to the parent array, so each
  `Array.set!` takes the in-place branch;
- **shared** — a snapshot of the current parent array is taken each iteration
  and read after the update, so the array is still shared at the write and each
  `set!` copies.

The union-find state is checksummed and printed, so the two variants can be
compared for functional equality; a separate `liveness_sum` keeps the snapshot
used and is not part of the state.

## A checked program, emitted and built

The union-find program above is hand-written, and the discipline does not check it.
The other direction is real: `scripts/emit_program.lean` defines programs in the
model language (`Ownership.Code`), has the discipline's checker accept them, and
emits them as Lean into `bench/Generated.lean`. The bench package's `generated`
target builds that emitted file into a binary.

```
nix develop -c lake env lean scripts/emit_program.lean   # checker + emitter
cd bench && nix develop -c lake build generated
./.lake/build/bin/generated
```

The family is `m` sequential in-place writes into the owned array, alternating
two scalar indices. The checker requires the array's multiplicity to be one at
every write, so every emitted program is a certified in-place path; there is no
certified shared variant to compare with.

| writes | ns per write | total ms |
| ---: | ---: | ---: |
| 200 | 7091 | 1.4 |
| 1000 | 1452 | 1.5 |
| 4000 | 337 | 1.3 |

Read this as a **flat total**: the three programs take about 1.4 ms each, so the
per-write figure falls as `m` grows because a fixed setup cost dominates, not
because writes get cheaper. A copying update would scale with the array, and a
per-write loop would scale with `m`; neither appears.

Two limits of the unrolled form, both measured: elaborating `m` nested lets costs
compiler time (62 s for 4 000 writes), and Lean's default recursion depth has to
be raised for four thousand. Larger `m` needs a loop, which the model language
does not have. So the generated path is a correctness connection at modest `m`,
not a substitute for the loop benchmark.

## A static alias/linearity check

`bench/Alias.lean` provides `#alias_check term`, an elaboration-time check over
real Lean terms. It tracks array-typed `fun`/`let` binders by de Bruijn index and
applies three rules:

* a variable in a **borrow** position (receiver of `size`, `getD`, `uget`, `back?`)
  may occur any number of times; a variable in a **move** position (receiver of a
  write, argument to any other call, returned, or rebound) is a use, at most one
  per path;
* an `if` takes the **maximum** over branches, not the sum, so one move in each
  branch is linear;
* an owning array occurring under a lambda **past the parameter spine** is a
  capture and is refused outright.

| File | Shape | Verdict |
| --- | --- | --- |
| `AliasOk.lean` | transfer `let b := a.set! …; b.set! …`, and a `foldl` loop | accepted |
| `AliasUfThread.lean` | union-find's `find`: two borrows, one move, return | accepted |
| `AliasBad.lean` | `let b := a; … a … b` | rejected: `'a' is moved 2 times` |
| `AliasBadCapture.lean` | `(fun _ => a) () … a` | rejected: `'a' is captured in a closure` |
| `AliasBadShared.lean` | `snapshot` retained while `a` is updated | rejected: `'a' is moved 2 times` |

```
cd bench && nix develop -c lake env lean AliasOk.lean         # exit 0
cd bench && nix develop -c lake env lean AliasUfThread.lean   # exit 0
cd bench && nix develop -c lake env lean AliasBad.lean        # exit 1
```

Scope: only array-typed binders (no arrays in structures or fields); unknown
functions count as consuming, since borrow inference is a backend property the
surface does not carry; the `if` condition is not analysed for moves; and one term
is checked at a time. This is the surface half of the discipline — it discharges
the multiplicity-one premise of the model's `setArr` rule — while `Ownership.Accounted`
is the semantic half.

## Build and run

```sh
cd bench
nix develop -c lake build
./.lake/build/bin/unionfind
```

The binary is `bench/.lake/build/bin/unionfind` (about 5 MB, Lean static runtime).

## What the generated C says

The emitted code calls `lean_array_set` at every update
(`bench/.lake/build/ir/UnionFind.c`). In the pinned toolchain that is a static
inline in `include/lean/lean.h` which bounds-checks and forwards to
`lean_array_uset`, and `lean_array_uset` calls `lean_ensure_exclusive_array`:

```c
static inline lean_object * lean_array_uset(lean_object * a, size_t i, lean_object * v) {
    lean_object * r = lean_ensure_exclusive_array(a); ... }
```

So the write path is copy-on-write **by construction**: the only branch on
sharing is the runtime reference-count test. `nm` finds no `lean_array_uset`
symbol because it is a header inline compiled into `UnionFind.c.o`.

Static inspection fixes the mechanism, not the disposition. Which side of
`lean_is_exclusive` a call takes is a runtime fact; the measurements below are
the evidence for it.

## Measured

Observed on 10 November 2026, Lean `4.35.0-rc3`, one Linux x86-64 machine, three
repetitions per case with the minimum reported. `m = 4n`. Run-to-run variation is
around ten to twenty percent, so read the ratios, not the absolute values.

The first block holds `n` and `m` fixed between the two variants, which is the
only like-for-like comparison.

| mode | n | m | ms | ns/op | union-find checksum |
| --- | ---: | ---: | ---: | ---: | ---: |
| unique | 2000 | 8000 | 0 | 66 | 1288397 |
| shared | 2000 | 8000 | 4 | 559 | 1288397 |
| unique | 4000 | 16000 | 1 | 71 | 7372734 |
| shared | 4000 | 16000 | 18 | 1142 | 7372734 |
| unique | 8000 | 32000 | 2 | 75 | 34565462 |
| shared | 8000 | 32000 | 69 | 2174 | 34565462 |
| unique | 16000 | 64000 | 4 | 72 | 128170418 |
| shared | 16000 | 64000 | 338 | 5288 | 128170418 |

The checksums agree within each pair: sharing changes the cost, not the result.

The second block grows `n` for the unique variant, where `m` grows with `n`.

| mode | n | m | ms | ns/op |
| --- | ---: | ---: | ---: | ---: |
| unique | 100000 | 400000 | 30 | 76 |
| unique | 400000 | 1600000 | 139 | 87 |
| unique | 1600000 | 6400000 | 1079 | 168 |

## Reading it

At fixed `n`, the two variants differ only in whether a second reference is live
at the write. Unique holds a flat 66–75 ns per operation while `n` grows eightfold;
shared's per-operation cost doubles with `n` (559 → 1142 → 2174 → 5288 ns), which
is what an `O(n)` copy per update looks like.

In the second block the per-operation cost is flat at 76–87 ns while the array
fits in cache (0.8 MB and 3.2 MB), then rises to 168 ns at 1.6M elements
(12.8 MB): that is memory behaviour of the same in-place update, not a change of
branch.

An earlier version of this table printed totals only, across blocks that varied
`m` and `n` together, and the unique block looked superlinear. It was a units
problem: totals are not comparable when the operation count changes; ns/op at
fixed `n` is.

## What this does and does not show

It shows the **runtime disposition**: the same algorithm and the same results,
near-constant cost per operation when the array is unique, and cost growing with
the array size when every update shares it. That is an observation about this
binary and this machine, and the C inspection above shows the mechanism it
exercises is Lean's copy-on-write array update.

It does **not** certify the union-find program: that program is hand-written, and
the recognised fragment is a `setAt` shape, so its data-dependent loop, computed
indices and arithmetic are outside it. The discipline-driven binary is the
emitted two-write program above, and its scope is the fragment's straight-line
array code. The step the model certifies — an owned array's scalar write, and its
refusal when the handle is aliased — is also exercised in `OwnershipTest/Array.lean`
(`execSet` accepted, `aliasSet` refused).
