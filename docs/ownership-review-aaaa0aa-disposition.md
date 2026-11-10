# Disposition of the review at `aaaa0aa`

Review: `docs/ownership-review-aaaa0aa.md` (10 November 2026). This file records
what was done for each finding and what remains open.

| Finding | Status | Response |
| --- | --- | --- |
| 1. Two-level composition has inconsistent premises | withdrawn; regression proved; claim surfaces corrected; repair open | `OwnershipTest/IsolatedAccounting.lean` proves the general impossibility (`isolated_accounting_impossible`) and instantiates it on the outer entry and the isolated-accounting assumption (`two_level_isolated_entry_impossible`), both with only `propext`, `Classical.choice`, `Quot.sound`. The paper's introduction and chain theorem, `AGENTS.md`, `README.md`, and the module header and section docstrings in `Ownership/CountedNested.lean` now record the composition as withdrawn rather than demonstrated; `counted_nested_chain_two_levels` remains in the development as a regression target. No depth-two instance is claimed. A repair — a suspended-frame owner component or a global ownership ledger related to the local checker — is not attempted here and is the outstanding work. |
| 2. Surface alias checking accepts ownership violations | reclassified as experimental; gaps recorded; ordered checker open | The paper calls it experimental and says it is not a sound usage checker; `AGENTS.md` and `bench/README.md` state the same. `bench/AliasKnownGaps.lean` records the three accepted counterexamples (read after move, consuming condition, two owners from one read), and `bench/AliasOk.lean` pairs the first with two accepted variants (read before the move; read through the returned binding). An ordered ownership-state analysis — availability, condition before branches, branch-state merge, ownership effects for calls and projections, and no fresh owner from a read — is not implemented. The claim that it discharges the model's multiplicity-one premise is removed. |
| 3. Benchmark unit and crossover | corrected | `bench/UnionFind.lean` prints nanoseconds per **outer iteration**; the paper and `bench/README.md` say so and describe what an iteration contains. The `70 + 0.3·n` fit and the `n ≈ 230` crossover are removed; the remaining statement is qualitative and bounded to the measured range. |
| 3b. Generated harness retains its input | addressed as far as measurable | The harness builds a fresh array per trial outside the timed region. The fixed cost that dominates the flat total is not explained, and the consuming write's disposition is not verified; the paper and README no longer present the flat total as an in-place timing result. Instrumenting the write path is outstanding. |
| 4. Verification record stale | refreshed | `docs/notes/artifacts/final-revision-check.txt` now carries this revision and date, the current census counts, the regression theorems in the axiom list, and the `scripts/check_all.sh` run. |
| 5. Keep the paper centred on the valid result | addressed | The two-level composition is removed from the paper's claims; the one-level counted-fragment theorem and the net edge effect remain, and the runtime paragraph is labelled as observation. |
| Title breadth (`Observed`) | addressed earlier | The observation boundary (cells, result, fault, trace; allocator cursor outside) is stated in §6 and in the introduction. |

## Open items

1. **Repair the two-level composition.** Give the inner call an accounting that
   retains the suspended caller's roots — a frame component derived from actual
   caller ownership, or a global ledger with a proved relation to the local
   checker — and inhabit a closed depth-two counted instance. Keep
   `two_level_isolated_entry_impossible` as the regression that forbids dropping
   framed roots.
2. **Ordered alias analysis.** Replace binder counting with an ownership-state
   analysis over the surface, and keep `bench/AliasKnownGaps.lean` as its
   acceptance suite: each program there must be refused once the analysis exists.
3. **Instrument the write path** so a benchmark can report the disposition of the
   consuming write rather than inferring it from totals.
