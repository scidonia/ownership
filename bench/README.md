# Union-find on the array write path

This directory is a benchmark, not part of the proof development. It answers a
runtime question the development is about but does not certify: Lean's array
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

The checksum is returned and printed so neither loop can be discarded.

## Build and run

```sh
cd bench
nix develop -c lake build
./.lake/build/bin/unionfind
```

or from the repository root:

```sh
nix develop -c bash -c 'cd bench && lake build && ./.lake/build/bin/unionfind'
```

The binary is `bench/.lake/build/bin/unionfind`.

## Measured

Observed on 10 November 2026, Lean `4.35.0-rc3`, this machine; a single run, so
the numbers are indicative rather than a benchmark suite. `m = 4n` operations.

| mode | n | m | ms |
| --- | ---: | ---: | ---: |
| unique | 100000 | 400000 | 38 |
| unique | 400000 | 1600000 | 183 |
| unique | 1600000 | 6400000 | 1651 |
| shared | 2000 | 8000 | 5 |
| shared | 4000 | 16000 | 19 |
| shared | 8000 | 32000 | 75 |

Read the two blocks differently. For **unique**, `m` quadruples while `n` stays in
the same regime: the time follows the operation count (38 → 183 → 1651 ms), the
per-update cost staying roughly constant with cache effects as `n` grows. For
**shared**, `m = 4n` grows with `n`: doubling `n` quadruples the time
(5 → 19 → 75 ms), the signature of an `O(n)` copy at every update rather than an
in-place write. The same algorithm, the same binary, a different disposition.

## What this does and does not show

It shows the **runtime disposition**: the same algorithm is near-linear when the
array is unique and quadratic when each update shares it, which is the cost cliff
the ownership discipline exists to make statically predictable. That is an
observation about this binary on this machine.

It does **not** certify the program. The development's checker runs on its model
languages, and the recognised fragment is a `setAt` shape; union-find's
data-dependent loop, computed indices and arithmetic are outside it. The step
that the model *can* certify — an owned array's scalar write, and its refusal
when the handle is aliased — is exercised in `OwnershipTest/Array.lean`
(`execSet` accepted, `aliasSet` refused).
