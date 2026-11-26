# The capability ledger, from the ground up

A tutorial on how the `Cap/` subsystem fits together: what problem it solves, how
each layer builds on the one below, what is proved at each step, and where the
honest boundaries are. Every name in backticks is a declaration in the
repository; `nix develop -c bash scripts/check_all.sh` rebuilds and re-checks
everything described here except the `llvm-bridge` composition, whose separate
package is built on a worker (§16).

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
integrated two-find client   Cap/UFIntegrated.lean   two sealed finds on the previous state's bytes
sealed certificates          Cap/Runner.lean         Prog, ClosedProgram, composition
unified checker/interpreter  Cap/Unified.lean        UCmd, checkWorld
world (state)                Cap/World.lean          owners + backends + loans
world invariant              Cap/WorldInvariant.lean the bundle every command preserves
delegation invariant         Cap/Borrow.lean         chain base, detachment, terminal-or-delegated
delegation chain             Cap/Delegation.lean     rooted path, checked begin/end
coupled chain state          Cap/Discipline.lean     world/chain correspondence
sealed execution             Cap/Integrated.lean     checked multi-allocation commands
reconstruction forest        Cap/Reconstruction.lean subdivision rules, restoration obligations
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
| `beginBorrow a lender borrower loanId` | retag the active leaf to the borrower; record the loan |
| `endBorrow a loanId` | retag the terminal borrower back to the lender; remove the record |
| `free a d` | dispose, only through the recorded disposal capability |
| `nop` | — |

`checkWorld` runs a command list and returns either an error or the world it
executed. One theorem covers all of it:

```
checkWorld_wf : checkWorld w cs = .ok w' → w.CommandInv → w'.WellFormed

def CommandInv (w : World) : Prop :=
  w.WellFormed ∧ Ctx.HistoryOK w.ctx ∧ Ctx.LoansReady w.ctx
```

Every accepted execution preserves the carrier — allocation, splits, joins,
borrow/return, disposal included. `checkWorld_rel` then derives the older
`World.Rel` from it.

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

## 10. Borrowing: retagging the active leaf (`Cap/Retag.lean`, `Cap/Borrow.lean`)

Borrow moves the whole authority to a distinct borrower. `beginBorrow` retags
the lender's active leaf to the borrower's name and appends a loan record;
`endBorrow` retags the terminal borrower back to the lender and removes the
record. A write through the lender is therefore refused after the borrow and
accepted again after the return, both by the same leaf-name guard.

The record carries the chain base, so a reborrow names the borrower as the next
lender and the return order is the nesting order. `World.BorrowOK` states the
integrated invariant --- distinct loan/lender/borrower/lifetime names, issued and
live names, a recorded base, global lender detachment, an active terminal or a
delegated successor, adjacent-edge resource agreement, and issued-order
monotonicity from which acyclicity is derived --- and
`World.checkWorld_fullInv` preserves it together with the top-level invariant.
`World.delegationChains_ok` additionally assumes `World.LoansChainOrderOK`,
because the world loan list's order is not determined by `BorrowOK`.

Stated limits, on purpose: the world `UCmd` path still refuses a split or
fractional join while any loan is outstanding on the allocation. That guard is
allocation-wide, so it also refuses a split of an independent sibling range. The
reconstruction model (below) implements borrowed subdivision and
restoration, but `World.splitAtChecked` does not consult it; full world
integration is not claimed.

### Borrowed subdivision and reconstruction (`Cap/Reconstruction.lean`)

The retag chain represents one unresolved path. Borrowed subdivision needs a
forest of obligations instead. `Reconstruction.State` pairs the reference heap
with a forest whose interior nodes record the checked spatial or fractional rule
that produced them, the issued and retired names, and the outstanding `Restore`
obligations. `State.Inv` is frontier coverage, forest validity and the ownership
account `State.Accounts`: the budget at every byte is still `D`, every recorded
rule is checked, and the account constrains current authority-node identities,
issuance coverage, retirement, dormant lenders, restoration realization,
resource agreement and restoration order. The account is not a structural
restatement of the forest: it relates the forest to `issued`, `retired` and
`restores`, so a retired or dormant name is not a current leaf
(`State.Accounts.retired_not_current`,
`State.Accounts.dormant_not_current`) and an appended obligation naming an
unissued party breaks the predicate (`State.Accounts.cons_restore_not_accounts`).

`Restore.Depends r r'` means `r'.lender = r.borrower`; `State.RestoreOrder`
requires every dependency to strictly decrease the index in `restores`, which is
the direction borrowing prepends. `State.Accounts.dependency_wellFounded` rules
out a positive delegation cycle and `State.Accounts.restore_reaches_terminal`
finds a finite path from every obligation to a terminal forest node with the
recorded resource agreeing along it. A suspended terminal parent is connected to
its current rule descendants by `Forest.suspended_frontier_realizes`.
`bench/CapRestorationOrder.lean` records the two-edge cycle that the earlier
fields admit and the repaired account rejects, together with a valid nested
borrow and a missing-terminal refusal.

`State.borrow` retags a current fragment and records the dormant lender.
`State.splitSpatial` and `State.splitFraction` subdivide a current fragment ---
including a borrowed one --- while checking that the children partition the
parent and that no child name was ever issued or retired. `State.reconstruct`
restores a suspended parent only when both children match its recorded rule and
neither has been subdivided or lent further, retiring the two child names.
`State.return` restores the lender only after the borrowed resource is
reconstructed and no loan descends from the borrower. Each operation preserves
`State.Inv` (`State.splitSpatial_inv`, `State.splitFraction_inv`,
`State.reconstruct_inv`, `State.borrow_inv`, `State.return_inv`); the split
frames leave outstanding obligations untouched, and
`State.return_none_of_no_leaf` records the refusal of a return before
reconstruction.

This is the reconstruction model, not the world command route. `Cap.World` still
refuses any split or fractional join while a loan is outstanding on the
allocation (`World.splitAtChecked_refuses_with_loan`), so a split of an
independent sibling range is refused on the `UCmd` path. Removing that
allocation-wide test and consulting the forest is the named next integration;
nothing here claims it.

The sealed boundary is `Cap/Integrated.lean`, re-exported as `Cap/Sealed.lean`:
a private constructor and invariant proof over the multi-allocation state, with
`alloc`, `write`, `borrow`, `splitSpatial`, `splitFraction`, `reconstruct`,
`return`, `free`, and a whole-run `run` over the checked `Cmd` list. `State.Inv`
requires distinct live allocation identifiers, every component's `State.Inv`
(including the ownership account `State.Accounts`) and `State.Storage`, and it
relates each component's issued names to a session-persistent capability history.
The allocation and capability histories are append-only: an accepted command
only adds names, and `free` leaves them intact (`State.free_histories_intact`).
`State.alloc` refuses an identifier in `allocsIssued` and an initial capability
name in `issued`. A freed
identifier therefore cannot be reissued (`State.realloc_after_free_refused`) and
an old capability cannot authorize a replacement allocation
(`State.alloc_reusing_old_capability_refused`); a fresh identifier with fresh
names is accepted (`State.alloc_fresh_after_free_some`).
Its observations are a heap snapshot, byte read, per-fragment authority, retired
names, outstanding restoration obligations and the live allocation list.
`Sealed.lifecycle64` runs the 64-byte example and `Sealed.reuseLifecycle` runs a
second full cycle on the first's output. The retired single-allocation
`Cap/ReconstructionSealed.lean` is gone; its controls live in
`bench/CapIntegrated.lean`.

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

`Cap/UFReuse.lean` closes the reuse requirement on the functional model. From
`[0,0,1,2,2]` the first full-path compression from node 3 is exactly
`[0,0,0,0,2]` (`reuseFirst_eq`); `reuseFirst_ranked` proves the output is still a
ranked forest, and `reuseFirst_accepts_second` supplies the second operation's
rank bound and reachability certificate, so the second input is the first
output's certificate rather than a restated array. The second compression from
node 4 is exactly `[0,0,0,0,0]` (`reuseSecond_eq`), and the partition
preservation composes back to the starting partition (`reuseTwoFinds_same_iff`).
The world-based sealed `UFRunner` is not threaded through this example: it
stores its world, representation and rank privately and exposes only one find's
observation, so a second call would need a successor-runner operation and a new
rank certificate.

`Cap/UFIntegrated.lean` runs the two calls through the integrated sealed
boundary instead. A parent array is held in one allocation's bytes: `decode`
reads a buffer as a `UF.Arr`, `Rep s a arr` says the allocation's snapshot
decodes to `arr`, and `Rep.fits` bounds every value by a byte. `chase?` follows
parent pointers with `Sealed.read?`; `compressPath` writes the root at every
path node with `Sealed.write` through the whole-share capability; and
`sealedFind` returns the root with the successor sealed state. `chase?_eq`
proves the sealed chase is the functional `UF.findRootF`/`rootPath` whenever the
reads agree with the array, and `ufStart_reads`/`ufFirstState_reads` discharge
that for the two successive states. The first find from node 3 leaves
`[0,0,0,0,2]` and the second, run on the first call's returned state from node
4, leaves `[0,0,0,0,0]` — the functional certificate's exact arrays. A fresh
find from node 4 on the start state instead leaves `[0,0,0,2,0]`
(`ufSecond_consumes`). `ufSecond_invariant` re-exports the sealed invariant
(including each component's ownership account). A two-allocation variant is
framed as well: `ufSecondOther_invariant` re-exports the invariant for the whole
state, and `ufSecondOwnershipFrames_of_ok` records that both allocations' current
fragments are still whole active read--write fragments, no access name was
retired, no return obligation was recorded, both heaps still hold their bytes, and
both allocations are live and distinct. Not proved: a
general per-write refinement or frame law over sealed command lists — the final
arrays are kernel-checked computations of the actual run, not instances of a
derived write lemma.

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
- Borrowing moves whole authority by retagging. On the world `UCmd` path a
  split or fractional join is refused while any loan is outstanding on the
  allocation; the allocation-wide guard does not consult the reconstruction
  forest, so the reconstruction model's borrowed subdivision is not integrated
  into the world path.
- The sealed boundary is not module-enforced. The sealed path is the integrated
  multi-allocation reconstruction state; the world `UCmd` path is a separate
  theorem surface and is not routed through the forest.
- No in-place-update or compiled-performance claim anywhere in `Cap/`.
- Union-find correctness is the concrete five-node reuse instance and the
  four-node write-discipline instance, not the general theorem. The two-find
  reuse is proved on the functional model and, on that instance, through the
  integrated sealed boundary (`Cap/UFIntegrated.lean`). The world-based sealed
  `UFRunner` is still not threaded, and no general per-write refinement or frame
  law over sealed command lists is proved.
- No C, ABI or physical ownership refinement. `llvm-bridge` proves one compiled
  store kernel's exact bounded behaviour and composes it with one authorized
  integrated byte write at a caller-supplied address window
  (`store8_exec_write_comp`, `sealed_store8_write_comp`). The representation
  premise, a loader's address assignment for more than one allocation, the IR
  projection, the ABI, native execution and live-handle replay remain stated
  assumptions or trust obligations.
- Reuse prevention is a session-persistent allocation and capability history,
  not an allocation generation, a physical-slot check or a runtime reclamation
  rule. Replaying an old immutable sealed state is outside the model.
- No claim that `World.splitAtChecked` consults the reconstruction forest.

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
7. **World reconstruction integration** — removing the allocation-wide
   split/join loan test from the `UCmd` path, consulting the reconstruction
   forest instead, and carrying one integrated world-and-restoration invariant
   through checked execution and the sealed world boundary. The reconstruction
   model and its sealed boundary exist; the `World.splitAtChecked` route does
   not yet use them.
8. **A general low-level bridge** — extending the single-kernel composition of
   `llvm-bridge` to an address assignment for more than one allocation, a
   semantic justification of the IR projection, the ABI and the installation of
   the verified body. The present theorem is one authorized write against a
   caller-supplied memory representation, not a C or physical ownership
   refinement.

## 16. Reproduce everything

```bash
nix develop -c lake build Cap          # the whole subsystem
nix develop -c bash scripts/check_all.sh   # builds + axiom audit + claim census + paper + report
nix develop -c lake env lean scripts/check_cap_axioms.lean  # borrowing, reconstruction and reuse axioms
bash scripts/check_cap_docs.sh --rev WORKTREE               # live-documentation claim census
lake env lean bench/CapBATiming.lean   # the three-backend timing observation
```

The axiom audit (`scripts/check_axioms.lean`) is the hygiene gate: every
headline theorem depends only on `propext`, `Classical.choice` and
`Quot.sound` — Lean's standard three — with no `sorry`, no new axioms, no
`native_decide`.

The `llvm-bridge` package is separate: it needs a sibling `lean-llvm` checkout
at its pinned Lean release and the `Cap` projection pushed beside it. It is
built on a worker, not from this checkout
(`llvm-bridge/scripts/build-remote.sh`; `llvm-bridge/README.md` states the
layout and `llvm-bridge/EVIDENCE.md` records the builds). No local Lean build of
that package was run for this revision.

The LaTeX outputs were not rebuilt at this revision because the worker image
has no LaTeX installation: `report/capability-report.pdf`,
`report/cap-tutorial.pdf` and `paper/sealed-ownership.pdf` are older than their
`.tex` sources. The sources are updated; the PDFs are not.
