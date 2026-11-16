# The capability ledger, from the ground up

A tutorial on how the `Cap/` subsystem fits together: what problem it solves, how
each layer builds on the one below, what is proved at each step, and where the
honest boundaries are. Every name in backticks is a declaration in the
repository; `nix develop -c bash scripts/check_all.sh` rebuilds and re-checks
everything described here.

## 1. The problem

Lean's type system has no linearity. If a program holds a mutable array, nothing
in the type system stops it from keeping a second reference and observing (or
breaking) an in-place update. Rust solves this with ownership and borrowing,
enforced by the borrow checker. The question this repository asks is:

> Can Rust-like rules be enforced *from outside* the host type system — by a
> checked data structure rather than by types?

The `Cap/` subsystem is the executable half of the answer. (The `Ownership/`
side is the model-theoretic half, aimed at the paper; this tutorial is about
`Cap/`.)

The design idea, in one sentence: **a ledger owns all authority; capabilities
are inert names; every use is checked against the current state.** A capability
is just a number. It does nothing by itself. All power comes from the ledger
saying, at the moment of use, "this capability may write these bytes."

## 2. The stack, bottom to top

```
algorithms as clients        Cap/UFRun.lean          union-find through the checked route
sealed certificates          Cap/Runner.lean         Prog, ClosedProgram, composition
unified checker/interpreter  Cap/Unified.lean        UCmd, checkWorld
world (state)                Cap/World.lean          owners + backends + loans
world invariant              Cap/WorldInvariant.lean the bundle every command preserves
suspension                   Cap/Suspend.lean        loans = retired lender leaves
context                      Cap/Context.lean        many owners, allocation, disposal
invariants                   Cap/Invariant.lean      leaves-within, well-formedness
joins                        Cap/Join.lean           sibling-only fractional merge
loans (bookkeeping)          Cap/Loans.lean          lifetimes, loans, liveness
owners                       Cap/Ledger.lean         trees of leaves, guards, splits
shares                       Cap/Share.lean          exact 1/n arithmetic
footprints                   Cap/Footprint.lean      byte intervals
identities                   Cap/Id.lean             distinct name types
```

Read it bottom-up. Each layer only trusts the ones below it, and each layer's
theorems say exactly what that layer guarantees.

## 3. Names are not pointers (`Cap/Id.lean`)

Everything the ledger tracks gets its own identity type: `AllocId` (which
allocation), `CapId` (which capability), `LoanId`, `LifetimeId`. They are
distinct tagged naturals — you can write `⟨3⟩` for one — and being distinct
types means the checker can never confuse an allocation for a capability.

This matters because of the central discipline: **a capability is a name, and
names are free to copy.** Copying a name grants nothing, because every *use* is
checked.

## 4. Shares: who may do what (`Cap/Share.lean`)

A capability's *share* of a resource is a fraction `q/D`: a numerator `q` over a
context-wide denominator `D`. The whole resource is `D/D`; half is `D/2` over
`D`, and so on.

The rules the arithmetic enforces (`ShareWf`, `Splits`, `no_two_writes`):

- a split produces shares that add up to exactly what was there;
- only the *whole* share may write;
- therefore two partial shares can never both write.

That is the whole fractional-uniqueness story: writing requires `q = D`, and the
ledger's accounting makes `q = D` achievable by at most one capability at a
time.

## 5. Footprints: which bytes (`Cap/Footprint.lean`)

A *footprint* is a half-open interval `[lo, hi)` of an allocation's bytes.
`splitAt` cuts an interval in two; the proofs say the pieces are disjoint,
adjacent, and cover the original. A capability's authority is a share **and** a
footprint together: *this much of these bytes*.

## 6. The ledger: trees of authority (`Cap/Ledger.lean`)

An `Owner` (one per allocation) holds a tree of leaves. Each `Leaf` is a
capability with its footprint, its share numerator `q`, a ceiling (`readOnly` or
`readWrite`), and a state (`active`, `retired`, `consumed`). Internal nodes come
in two flavours:

- **spatial** — the children split the byte range (disjoint footprints);
- **fractional** — the children split the share over the *same* range.

The key measure is the **budget**: at any byte `x`, the sum of shares of all
leaves covering `x`. The invariant of the whole design is `Owner.Covered`: at
every byte of the allocation the budget is exactly `D` — nothing is
unaccounted-for, nothing is double-counted. Splits preserve the budget by
construction (`frac_split_budget`, `spatial_split_budget`); the sibling-only
fractional join (`Cap/Join.lean`) merges two leaves back into one of summed
share and preserves it too, and is refused if the children carry the same
capability id.

The write guard is a decidable check (`Owner.writableB`): the named leaf exists,
is `active`, holds the *whole* share, allows writes, and the index is inside its
footprint. `writableB_sound` says a positive decision really is the `Writable`
predicate — the executable check and the logical guard never drift apart.

## 7. Many owners: the context (`Cap/Context.lean`, `Cap/Invariant.lean`)

A `Ctx` is a list of owners plus the denominator and a fresh-allocation
counter. `Ctx.Realizes` says every owner is covered and allocation ids are
distinct. `Cap/Invariant.lean` adds the stronger bundle `Ctx.WellFormed`:
`Realizes`, plus every owner well formed (its leaves stay inside its own
allocation — `Owner.LeavesWithin`), plus all capability ids across all owners
distinct.

The important theorems are the *preservation* ones: allocation, disposal, and
both kinds of split, dispatched to their owner, all preserve
`Ctx.WellFormed` — provided the fresh identifiers are genuinely fresh for the
whole context. Freshness is not a detail; it is what stops a new capability from
colliding with an old one and inheriting its authority.

## 8. The world: owners plus bytes (`Cap/World.lean`, `Cap/WorldInvariant.lean`)

A `World` is the context, the backends (one byte buffer per allocation), and the
loan bookkeeping. `World.WellFormed` bundles:

1. the context invariant;
2. **functionality** — each allocation resolves to at most one owner;
3. **storage agreement** — the found owner's backend has the owner's length.

`World.update_storage` is the workhorse: replacing one owner by a same-length
result keeps the heap agreement. Every checked command's preservation proof ends
in it.

## 9. The unified language (`Cap/Unified.lean`)

Here the checker becomes the interpreter. `UCmd` is the command language:

| command | ledger effect |
|---|---|
| `alloc n rootId disposal` | fresh owner, fresh capabilities, empty backend |
| `write a id i v` | guarded by `writableB` |
| `splitAt a id id1 id2 k` | spatial split of a leaf at byte `k` |
| `splitFraction a id id1 id2 q1 q2` | fractional split, shares summing to the parent's |
| `join a node newId` | merge a fractional node's children |
| `beginLoan a lender loanId` | retire the lender's leaf; record the loan |
| `endLoan a loanId` | remove the record; restore the leaf |
| `free a d` | dispose, only through the recorded disposal capability |
| `nop` | — |

`checkWorld` runs a command list and returns either an error or the world it
executed. One theorem covers all of it:

```
checkWorld_wf : checkWorld w cs = .ok w' → w.WellFormed → w'.WellFormed
```

Every accepted execution preserves the invariant — allocation, splits, joins,
loans, disposal included. `checkWorld_rel` then derives the older `World.Rel`
from it.

### A walk through `uLifecycle`

The concrete fixture runs the whole discipline end to end:

```
.alloc 4 ⟨3⟩ ⟨4⟩            -- fresh 4-byte owner ⟨1⟩; root cap ⟨3⟩, disposal ⟨4⟩
.write ⟨1⟩ ⟨3⟩ 0 7          -- whole-share write at byte 0
.splitAt ⟨1⟩ ⟨3⟩ ⟨5⟩ ⟨6⟩ 2  -- leaf ⟨3⟩ → ⟨5⟩ covers [0,2), ⟨6⟩ covers [2,4)
.write ⟨1⟩ ⟨5⟩ 0 8          -- write through the left half's capability
.splitFraction ⟨1⟩ ⟨5⟩ ⟨7⟩ ⟨8⟩ 32 32  -- ⟨5⟩ → two half-shares ⟨7⟩, ⟨8⟩
.join ⟨1⟩ ⟨7⟩ ⟨9⟩           -- merge them back into whole-share ⟨9⟩
.write ⟨1⟩ ⟨9⟩ 1 9          -- writable again: the join restored the whole share
.free ⟨1⟩ ⟨4⟩               -- disposal through the recorded capability
```

`uLifecycle_ok` (by `decide`) says it is accepted; `uLifecycle_wf` says the
final world is well formed; `uLifecycle_snapshot` says the pre-existing 64-byte
owner's bytes are untouched zeros. Between the fractional split and the join a
write through `⟨7⟩` would be *refused* — a half share cannot write — and the
budget arithmetic is what makes that decision sound.

## 10. Loans: suspension, not tracking (`Cap/Suspend.lean`, loans in `Cap/Unified.lean`)

Loans reuse the leaf state the write guard already consults. `beginLoan`
retires the lender's leaf; since `writableB` requires `.active`, a write through
the lender is then refused *by the same guard* — no parallel machinery. The
refusal is a theorem with a positive control: `uLoan_write_before` (accepted),
`uLoan_suspended_write_refused` (the same write refused while the loan is
outstanding), and after `endLoan` the write is accepted again (`uLoanRun_ok`).

Stated limits, on purpose: the borrower is the lender's own id (exclusive
suspension, not a reborrow capability), and the `Cap/Policy.lean` liveness
conjunction is a predicate form the checker does not consult.

## 11. Certificates and the sealed boundary (`Cap/Runner.lean`)

A `Prog pre` is a command list packaged with the proof that the checker accepts
it from `pre`: `ok : checkWorld pre cmds = .ok post`. You cannot construct one
without the derivation — that is what makes it a certificate rather than a bare
function. `checkWorld_append` lets certificates compose (`Prog.seq`): the second
program provably starts in the first's post-world.

`ClosedProgram` is the sealed form: commands accepted from the canonical empty
world (`World.emptyWorld`, no owners, no bytes). Its only observation is a
snapshot of the final world; `closed64_snapshot` proves the allocate-and-fill
example reads back 32 ones then 32 twos. The residual honesty: Lean has no
module opacity, so `World` itself remains public — the seal is by discipline,
not by the module system.

## 12. Algorithms as clients (`Cap/UFRun.lean`)

Union-find runs over the checked world. Reads are observations of the pure
backends — the discipline constrains writes — and `union` issues its writes
through `World.writeChecked`, so `union_wf` preserves the invariant. The
concrete trace (attach 1 under 0, 3 under 2, 2 under 0) is accepted, lands on
the parent array `[0,0,0,2]`, and every pair of the four nodes is `Same` in the
functional partition relation (`ufTrace_partition`) — the link to
`Cap/UFPartition.lean` and `Cap/UFCompress.lean`, where the reachability and
one-step-compression facts live.

## 13. Backends: two implementations, one model (`Cap/Backend.lean`, `Cap/BackendArr.lean`)

The pure `Backend` (a byte list with a length proof) is the specification.
`BackendArr` is the same interface over Lean's `ByteArray`. The refinement says
they agree — `empty_refines`, `read_refines`, `write_refines`, and the
fold-level `fills_refine` — and the 64-byte two-range fill through the
byte-array route produces the reference bytes (`ba64_snapshot`), all depending
only on `propext`.

The tempting next sentence — "the byte array is updated in place" — is exactly
the sentence this repository refuses to write here: Lean's runtime *may* mutate
a uniquely referenced `ByteArray`, but that is not observable from inside, so
nothing in `Cap/` claims it. Observing and certifying in-place update is the
`Ownership/` side's subject (LCNF projection, runtime evidence). The timing
observation (`bench/CapBATiming.lean`: list 73,959 ns/rep, byte array 47,688,
reference 51,956, one interpreted run, agreeing checksums) is recorded with the
same caveat.

## 14. What is not claimed

- No concurrency, no FFI, no real runtime.
- No read discipline: reads are free observations.
- Loans are exclusive suspension; no reborrows, no nested lifetimes in the
  executable language.
- The sealed boundary is not module-enforced.
- No in-place-update or compiled-performance claim anywhere in `Cap/`.
- Union-find correctness is the concrete four-node instance, not the general
  theorem.

## 15. The research-scale remainder

1. **A read discipline** — fractional read permissions through the guard, and a
   second, non-suspending loan mode. Design work plus re-proving every
   preservation theorem.
2. **General union-find correctness** — termination for compression (a rank
   potential) plus ownership accounting of the write trace; the first theorem
   that would use the discipline to prove an algorithm right, not just safe.
3. **The in-place observation problem** — connecting ledger exclusivity to
   Lean's runtime reference counts. The `Ownership/` side carries this; its
   named open obligations are the emitted recursive callee (N10), step agreement
   inside the pair-live window, and store-trace coverage.
4. **A genuine sealed boundary** — needs an opaque runtime or a verified-backend
   embedding; a policy decision about axioms, not just a proof.
5. **Compiled measurements** — a native binary with a defensible methodology;
   only interesting once (3) moves.
6. **Full lifecycle bookkeeping** — `BeginOK.lender_ne_borrower`, non-root
   lifetimes, disposal refused while any loan is outstanding at any owner.

## 16. Reproduce everything

```bash
nix develop -c lake build Cap          # the whole subsystem
nix develop -c bash scripts/check_all.sh   # builds + axiom audit + claim census + paper + report
lake env lean bench/CapBATiming.lean   # the three-backend timing observation
```

The axiom audit (`scripts/check_axioms.lean`) is the hygiene gate: every
headline theorem depends only on `propext`, `Classical.choice` and
`Quot.sound` — Lean's standard three — with no `sorry`, no new axioms, no
`native_decide`.
