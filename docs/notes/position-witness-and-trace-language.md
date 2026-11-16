# Position: union-find is the witness, and the trace language is the limit

Two corrections to how this repository's pieces have been framed, and the
research problem they jointly define. Written 2026-11-16, at commit
`ab9ed32`.

## 1. Union-find is not an algorithm to verify; it is the witness for the thesis

Treating union-find as a correctness target mistakes its role. Its role here is
to be the algorithm where ownership is observable as cost:

- `bench/UnionFind.lean` runs two variants of the same algorithm (path halving,
  union by size): **unique** — the loop carries the only reference to the parent
  array — and **shared** — a snapshot is taken each iteration so the array is
  shared at the write. Same answers (checksums agree), different cost: ~66–75 ns
  per iteration unshared at every measured size, rising to 5,288 ns shared at
  the largest. Sharing changes the cost, not the result. This is the
  copy-on-write complexity stake the paper leads with.
- `Ownership/` is the model that says *when* the unique variant's in-place
  update is justified: the counted accounting (`Accounted`), the exclusivity
  theorems, the LCNF projection of the real `setAt`.
- `Cap/` is where the discipline executes: `Cap/UnionFind.lean` (guard example)
  and `Cap/UFRun.lean` (checked-world client) show the checker *accepting* the
  writes the discipline licenses.

So union-find is the carrier, not the subject. "Prove general union-find
correctness" is known mathematics and mostly beside the point.

## 2. The executable language is a trace language

`Cap/`'s command languages (`UCmd`, and the `Cmd` lists that `#own_prog`
elaborates to) are finite, straight-line sequences. `checkWorld` folds them.
There is no loop and no recursion in the language, so an algorithm whose
control flow is data-dependent — union-find's `find` chasing parents to a fixed
point — *cannot be a program in the discipline*. The current "union-find
client" is the honest consequence of that: the chase is a Lean function with
fuel in the host, and only each iteration's write passes through the checker.

Two consequences, both deliberate:

- **Safety is loop-independent already.** `union_wf` preserves the world
  invariant per checked write however the host iterates; the discipline's
  guarantee does not need the loop in-language.
- **The result stays outside the certificate.** Termination, progress and the
  postcondition of `find` are not stated or proved. `ufTrace_partition` is
  about a fixed trace, not about the algorithm.

And no elaboration trick closes this: `fillCmds`-style unrolling works only
because its bound is static.

## 3. The research problem, restated

Not "verify union-find" but **close the loop on the witness**: one union-find
in which the same artifact is simultaneously

1. run by the checked discipline (its writes and its control flow),
2. certified exclusive by the `Ownership/` accounting (so the in-place update
   is licensed, not observed after the fact), and
3. measured in-place by the runtime evidence (the `lean-examples` probe).

Today each leg exists separately and none meets the others on union-find:

| leg | exists as | missing link |
|---|---|---|
| discipline accepts the writes | `Cap/UFRun.lean` (`union_wf`) | control flow is host-side; no exclusivity statement |
| model licenses in-place | `Ownership/` `Accounted`, exclusivity theorems | not instantiated on a running algorithm's trace |
| runtime shows the cost gap | `bench/UnionFind.lean` | outside the certified fragment; observed, not certified |

## 4. The closures, in dependency order

1. **A bounded loop in the executable language.** A read expression over the
   backend plus `while fuel cond body`; invariant preservation is fuel
   induction over the existing `checkWorld_wf` pattern; termination is
   fuel-bounded refusal (partial correctness, stated as such). This makes
   `find` a *program*, so the certificate covers the control flow.
2. **Connect the executable recursion to the model's.** `Ownership/` already
   has the recursive shape — `.callAt` with frame isolation
   (`callAt_frame_confined`); the `Cap/` language has nothing corresponding.
   With (1) in place, the correspondence question becomes well-posed.
3. **Instantiate the accounting on the loop's write trace.** The witness's
   uniqueness is per-iteration; `Ownership.Accounted` preservation through the
   loop body is the theorem that licenses in-place update for every iteration,
   not just one.
4. **Compiled, measured evidence.** Only after (3) does a timing claim about
   *this* union-find mean anything; until then the bench number remains an
   observation of hand-written code outside the fragment.

Each step is a research item, not a slice; the first is the only one that is
purely an engineering extension of the current executable language.
