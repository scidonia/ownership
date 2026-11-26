# Repository working notes

## Build and checks

- The Lean toolchain comes from the nix dev shell. From the repository root:
  `nix develop -c lake build Ownership` builds the development,
  `nix develop -c lake build OwnershipTest` builds the tests, and
  `nix develop -c lake build OwnershipLcnf` builds the LCNF projection target.
- `llvm-bridge/` is a separate Lake package and is not part of those targets: it
  requires a sibling `lean-llvm` checkout at its own pinned Lean release and is
  built on a worker (`llvm-bridge/scripts/build-remote.sh`; the builds and axiom
  footprints are recorded in `llvm-bridge/EVIDENCE.md`).
- LaTeX outputs are not rebuilt in this environment: the worker image has no
  LaTeX installation, so `report/capability-report.pdf`,
  `report/cap-tutorial.pdf` and `paper/sealed-ownership.pdf` can be older than
  their `.tex` sources. The sources are what these notes describe.
- Every module under `OwnershipTest/` belongs to the `OwnershipTest` Lean
  library, and `OwnershipTest.lean` imports each one, so
  `lake build OwnershipTest` elaborates the executable fixtures together with
  the proof modules.
- The measurement CLI is checked from the sibling checkout:
  `(cd ../lean-examples && nix develop -c lake env lean ../ownership/scripts/dump_executor.lean)`.
  Its per-constructor `setAt branch report:` lines are produced only after the
  focused branch-local AST gate in that script accepts both replayed `Path`
  alternatives and rejects its token-preserving near misses.
- The projection check replays the private `execP` and runs `projectPrefix` on
  its `PTree.set` branch:
  `(cd ../lean-examples && nix develop -c lake env bash -c 'export LEAN_PATH="../ownership/.lake/build/lib/lean:$LEAN_PATH"; lean ../ownership/scripts/check_projection.lean')`.
  It asserts that the recognizer accepts the real declaration, that the
  recognized array argument is the declaration's own parameter, that the
  recognized fragment has the pinned fourteen operations, that the binders the
  projected model reads are pairwise distinct (the only repeated name is the
  index decrement, which the recognizer requires to be the index itself), and
  that `Ownership.check` accepts the projected model from
  `Ownership.Runner.initCtx` — the target theorem's checker-acceptance
  hypothesis, instantiated on the real declaration. It then asserts that eleven
  token-preserving near misses are rejected while the unmutated declaration is
  still accepted: an increment inserted between the check and the write, the two
  pre-bounds projection indices swapped, the pre-bounds increments duplicated,
  the index increment dropped, the two-object node decrement dropped, the
  `Array.size` and `Nat.decLt` bindings' values exchanged, the `Nat.decLt`
  arguments swapped, the two bounds alternatives' constructor labels exchanged,
  the two bounds alternatives' bodies exchanged, the write reading the box's
  scalar source instead of the boxed binder, and an extra argument on
  `Array.set!`. The label exchange is the fixture
  that a positional "second alternative is `Bool.true`" selection cannot
  survive; the body exchange moves the write body onto the first alternative
  while keeping both labels; the operand case bypasses the box chain while
  keeping every call token; the extra-argument case keeps every recognized
  operand in place, so only the explicit arity check rejects it. The
  `Array.size`/`Nat.decLt` exchange keeps every
  call and argument token and changes only which binder receives which call, so
  it is a structure fixture rather than a compilable program. The same script
  reifies the captured declaration as a `Code .impure` value and has the kernel
  check its recognition, its variable layout and `Ownership.check` acceptance
  (`decide`, plus `projected_check` instantiated on it), and it asserts that the
  reified artifact decodes to the replayed declaration's prefix.
- The nested projection check replays the private `setAt` and runs
  `projectNested` on its `Path.index` branch:
  `(cd ../lean-examples && nix develop -c lake env bash -c 'export LEAN_PATH="../ownership/.lake/build/lib/lean:$LEAN_PATH"; lean ../ownership/scripts/check_nested_projection.lean')`.
  It asserts that the recognizer accepts the real declaration, that the
  recognized fragment has the pinned 25 operations, that the path's projections
  are its three fields, that the put-back uses the extracted parent, the
  selected index and the recursive result, and that the child check reads the
  pair's second projection. It then asserts that ten token-preserving near
  misses are rejected while the unmutated declaration is still accepted: an
  extra pair or extracted-child increment, a put-back through the path's array
  field, at the bounds result or of the extracted child, swapped pair
  projections, a flipped check flag, a dropped pair decrement, the update body
  moved onto `Bool.false`, swapped `Bool` labels, and a recursive call reading
  the raw extracted child. The recognizer itself is structural; the conditional
  model correspondence is in `OwnershipLcnf/NestedSemantics.lean`, and the
  emitted recursive callee remains an outstanding obligation.
- The captured LCNF artifacts are gated by `scripts/check_artifacts.sh`: it
  checks the sibling revision, that its working tree is clean at that revision
  (ignored build outputs such as `.lake/` are excluded), and the flake's Lean;
  it then regenerates the `execP` and
  nested `setAt` captures and diffs them against `docs/notes/artifacts/`.
- `scripts/check_decl.lean` is the reflection bridge: it reads a declaration's
  mono LCNF from the sibling's olean, replays the compiler pipeline to impure
  LCNF, and reports whether `projectPrefix` and `projectNested` accept it. Run it
  from the sibling:
  `(cd ../lean-examples && nix develop -c lake env bash -c 'export LEAN_PATH="../ownership/.lake/build/lib/lean:$LEAN_PATH"; lean ../ownership/scripts/check_decl.lean')`.
  It accepts the captured private `setAt` (25 operations) and rejects a different
  real function (`setLeaf`), which is the point: reflection is general, the
  recogniser's fragment is not. A declaration whose mono body is not saved in the
  olean is reported as such rather than guessed.
- `bench/Alias.lean` is an **experimental** alias/linearity check for a surface of
  Lean terms: `#alias_check term` tracks array-typed binders by de Bruijn index,
  allows borrowed reads (`size`, `getD`, `uget`, `back?`), at most one move per
  path, takes the maximum over `if` branches, and refuses a capture past the
  parameter spine. Accepted: `bench/AliasOk.lean` and `bench/AliasUfThread.lean`
  (union-find's `find` threading). Rejected: `bench/AliasBad.lean`,
  `bench/AliasBadCapture.lean`, `bench/AliasBadShared.lean`. It is not sound as a
  usage checker: it tracks binders rather than owners, does not record a consumed
  owner, ignores moves in conditions, and treats two reads of a container as two
  independent owners. `bench/AliasKnownGaps.lean` records three violating programs
  it currently accepts; closing them needs an ordered ownership-state analysis. It
  therefore does not discharge the model's multiplicity-one premise;
  `Ownership.Accounted` is the semantic half.
- `bench/OwnedStatic.lean` is an **experimental** statically checked ownership
  surface: `Owned` hides its payload behind a private constructor and field, the
  only operations are `new`, `write` and `read?`, and `#own_check` reflects an
  elaborated definition and rejects a handle used more than once in its scope.
  Accepted `bench/OwnedAccept.lean`; rejected `bench/OwnedReject.lean` (the same
  handle used twice) and `bench/OwnedNoAccess.lean` (the payload field is
  private). Run from `bench/`:
  `nix develop -c bash -c 'export LEAN_PATH=.:$LEAN_PATH; lean -o OwnedStatic.olean OwnedStatic.lean && lean OwnedAccept.lean'`.
  It is a usage check over the reflected term, not a linear type: Lean permits
  duplication, which the check refuses. `bench/OwnedDemo.lean` is the
  runtime-guarded counterpart, where a shared flag refuses the second use.
  The fractional context algebra is now the subsystem's `Cap.Share`
  (`ShareWf`, `Splits`, `Writable`, `no_two_writes`); the earlier
  `bench/OwnedTyping.lean` prototype is removed rather than kept beside it.
- `Cap/` is stage 1 of `docs/lean-fractional-ownership-design.md`, the proposed
  ownership and borrowing subsystem with fractional uniqueness. It is a separate
  root and namespace from `Ownership/`, because the paper's model owns
  `Ownership.Ctx`, `Ownership.Heap` and the count-share `Ownership.Share`.
  `Cap.Id` gives allocation, capability, loan and lifetime identities distinct
  types; `Cap.Share` gives exact shares over a context denominator (`ShareWf`,
  `Splits`, `Writable`, `no_two_writes`, `join_le`, `split_whole`, with the
  parent-bound side condition stated rather than derived); `Cap.Footprint` gives
  half-open intervals, views, `Within`, and `splitAt` with disjointness,
  adjacency, coverage and the within-preservation proof. Build with
  `nix develop -c lake build Cap`; `scripts/check_all.sh` includes it. The
  remaining stages are the context ledger and transitions, the typed core and
  semantics, then the elaborator, runner and backend refinement.
- `Cap/Ledger.lean` is stage 2a of the ledger: `Leaf` carries a footprint, share,
  ceiling and state; `Tree` has fractional and spatial nodes; `budget` is the
  frontier sum at a byte; `frac_split_budget` and `spatial_split_budget` state that
  a split preserves the budget and the sibling joins restore it. Leaf replacement is
  first-occurrence (`Tree.find?`, `Tree.replace`) and `Tree.budget_replace` proves it
  preserves the budget. At the owner level, `Owner` carries an allocation, its
  length, a root tree and a disposal capability; `Owner.Covered` is the byte-wise
  full-budget invariant; `Owner.split_covered` composes a split with
  `budget_replace`; `Owner.init_covered` establishes coverage at allocation; and
  `Owner.Writable`/`Owner.Readable` are the write and read guards (active, whole
  share and read--write ceiling for a write; positive share and active for a read).
  `Owner.splitFraction?` splits a leaf into two shares adding to its own and
  `splitFraction_covered` preserves coverage; `Owner.writeByte?` takes the write
  guard as a proof and performs the heap write, with `writeByte_sound` returning the
  guard and the read-back byte. The multi-owner context, disposal entitlements
  across owners, lifetimes and the lifecycle transitions remain the next slice.
- `Cap/Loans.lean` is the pure lifetime and loan bookkeeping: `LifeState`,
  `Lifetime`, `Loan`, `LoanCtx`, `findLifetime?`, `findLoan?`, `parent`, `live`;
  `BeginOK` collects the freshness, liveness and parent-liveness conditions and
  `begin` appends the lifetime and loan (`begin_mem_lifetime`, `begin_mem_loan`);
  `endLoan` removes a present loan whose lifetime is live
  (`endLoan_removes_loan`). `BeginOK` now binds the loan to the lifetime it inserts
  (`loan.lifetime = life.id`) and requires distinct lender and borrower
  capabilities; `endLoan` refuses while a recorded loan descends from the ended
  loan's lifetime (`hasDescendant_sound`, `endLoan_none_of_descendant`). `Loan`
  records the chain base (`Loan.base`), and `endBorrowBookkeeping` performs the
  return-side bookkeeping: it ends the returned loan's lifetime and removes its
  record. It has no heap and no capability ledger; the outstanding loans are the
  subject of `World.BorrowOK`, and the command level reads the three facts it
  needs through `Ctx.LoansReady`.
- `Cap/WorldInvariant.lean` bundles the world invariant: `Ctx.WellFormed`,
  `Ctx.Functional` (each allocation resolves to at most one owner) and
  `World.StorageMatches` (the found owner has a backend of its length).
  `Ctx.functional_of_nodup` derives functionality from distinct allocation ids;
  `Ctx.update_functional` and `Ctx.free_functional` preserve it;
  `World.rel_of_wellFormed` bridges to the older `World.Rel`; and
  `World.write?_wellFormed`/`World.freeWith?_wellFormed` preserve the bundle.
  `World.splitAtChecked` is the checked spatial split at an allocation's owner
  (the owner and both children must be fresh for the context);
  `World.splitAtChecked_sound` names the owner, the freshness facts and the
  resulting context; `World.update_storage` keeps the heap agreement through a
  same-length owner replacement; and `World.splitAtChecked_wf` preserves the
  bundle. `World.splitFractionChecked`/`World.joinChecked` are the checked
  fractional split and join, with `_wf` preservation; the context-side join
  preservation is `Ctx.joinFractionOwner_wellFormed` (in `Cap/Invariant.lean`,
  using `Ctx.update_ids_nodup_of_sub` and `Owner.joinFraction?_wellFormed`).
  Loans and disposal uniqueness are not in this layer yet.
- `Cap/Invariant.lean` is the stronger owner/context invariant: `Owner.LeavesWithin`
  (every leaf lies in the owner's allocation and extent), `Owner.WellFormed`
  (coverage, leaves within, disposal recorded), and `Ctx.WellFormed` (realization,
  per-owner well-formedness, distinct capability ids). Established at initialisation
  and preserved by `alloc`, `free`/`freeWith?`, and the dispatched spatial and
  fractional splits, with the tree's first-occurrence replace infrastructure
  (`find?_replace_eq`, `ids_replace_perm`, `leaves_replace_nodup`). Split
  preservation assumes owner id distinctness and freshness, and context-wide child
  freshness; the module records each hypothesis. `DisposalPresent` is a disjunction
  (a leaf or absence from the tree's ids), chosen so initialisation is
  unconditional; loans, storage agreement and one-entitlement-per-allocation are
  not in this invariant yet.
- `Cap/Context.lean` is the multi-owner context: a list of owners plus the
  denominator and a fresh-allocation counter. `Ctx.Realizes` requires every owner to
  be covered and the allocation identifiers to be distinct; `Ctx.alloc` appends a
  fresh, fully covered owner (`alloc_realizes`) and `Ctx.free` removes one by
  allocation (`free_realizes`). `Ctx.update` replaces an owner, with
  `update_preserves_other`, `update_covered` and `update_nodup`;
  `splitAtOwner?`/`splitFractionOwner?` dispatch a split to an owner and preserve
  `Realizes`; `Ctx.joinFractionOwner?` dispatches the sibling-only fractional join
  and preserves `Realizes` (`joinFractionOwner_realizes`); `freeWith?` requires the
  recorded disposal capability and refuses a wrong one (`freeWith?_wrong`). Capability identifiers are collected by
  `Tree.ids`/`Owner.ids`/`Ctx.ids`, with `Ctx.Fresh`; `alloc_ids_nodup` shows a
  fresh root and disposal identifier keep the identifiers distinct. Internal split
  nodes record provenance identifiers that are not access capabilities and are
  excluded from `Tree.ids`. Owner-level dispatch (`splitAtOwner?`,
  `splitFractionOwner?`) is not freshness-checked itself; the deep checker is.
  The loan state is part of the context (`Ctx.loans`), and the three loan facts
  the command dispatcher needs are carried by `Ctx.LoansReady`, preserved by
  every checked command.
- `Cap/Join.lean` is the sibling-only fractional join: `Tree.findFrac?` and
  `Tree.replaceNode` locate and replace a fractional node, `budget_replaceNode`
  preserves the budget when the replacement matches, `joinChildren?` merges two
  leaf children that agree on allocation, footprint, ceiling and state into one
  leaf of summed share (positivity by `omega`), and `Owner.joinFraction?` preserves
  coverage (`joinFraction_covered`) and the allocation identifier
  (`joinFraction_alloc`), and the length (`joinFraction?_len`). A join whose
  children carry the same capability id is refused
  (`joinChildren?_alias_none`, `Owner.joinFraction_alias_none`). The capability ids
  of a successful join are characterised: `joinFraction?_ids_perm` is the exact
  permutation (the two child ids removed, `newId` added), `joinFraction?_ids_sub`
  the membership bound, and `joinFraction?_ids_nodup` preserves distinctness for a
  fresh `newId`. Arbitrary same-resource recombination, the common-partition
  normaliser and provenance beyond node shape are not implemented.
- `Cap/Ledger.lean`'s `Tree.find?_replace_ne`: replacing the leaf `id` by a
  subtree that does not contain `id'` leaves the lookup of `id'` unchanged. This
  is the structural fact the loan invariant's preservation needs for splits and
  joins: a suspended lender's leaf is elsewhere (and the replacement's
  identifiers are fresh), so its lookup survives.
- `Cap/Context.lean`'s `Ctx` carries `issued : List CapId`, the issuance history.
  The world-level split, fractional-split and join check a new identifier
  against it (as well as against the live set) and extend it on success, so a
  retired name is never reissued by those transitions; `Cap/Issuance.lean`
  records the regression (`reuseSplit_refused`: a split reusing the retired root
  identifier as a child is refused, with `reuseSplit_prefix_ok` and
  `reuseSplitControl_ok` as controls) and proves the history grows
  (`splitAtChecked_issued_sub`, `joinChecked_issued_sub`). Allocation's own
  identifier check also tests the history (`World.historyOK_allocChecked`), and
  the general history-preservation invariant is `World.CommandInv`'s second
  conjunct, preserved by every checked command (`checkWorld_top`).
- `Cap/IProg.lean` is the indexed program interface: `IProg Γ α Q` starts with
  permission context `Γ`, returns `a : α` and ends with `Q a`; context-changing
  constructors (`alloc`, `splitAt`, `splitFraction`, `join`, `beginBorrow`,
  `endBorrow`, `free`) carry their evidence, so stale or refused operations are
  not programs
  (`stale_child_refused` shows a reused parent id makes the freshness evidence
  uninhabited). `evalIProg` is a total
  fuelled evaluator. The explicit-outcome evaluator `runIProg` distinguishes
  completion, fuel exhaustion and a refused world check (`IOutcome`);
  `evalIProg_eq_run` shows the `Option` evaluator is that outcome with the
  refusal cause erased, and `runIProg_no_refusal` proves a typed program is
  never refused, each command's check discharged by its typing evidence
  (`World.write_succeeds`, `World.allocChecked_succeeds`,
  `splitAtChecked_succeeds`, `splitFractionChecked_succeeds`,
  `joinChecked_succeeds`, `beginBorrowChecked_succeeds`,
  `endBorrowChecked_succeeds`, `World.freeChecked_succeeds`).
  `evalIProg_post` is the layer's soundness theorem:
  execution from a world matching the context ends in a world matching the
  postcondition, `w'.ctx = Q a ∧ w'.CommandInv`: the run keeps well-formedness,
  the issuance history and loan readiness. `iLifecycle` is the indexed
  lifecycle (alloc, write, split, write, free) with all evidence derived, and
  its run is accepted, well formed, on the typed post-context, and leaves the
  pre-existing backend untouched. `iClosed` is the closed-run lifecycle from
  `World.emptyWorld`: accepted, ends with no owners (`iClosed_closed`), well
  formed (`iClosed_sound`), and the disposed allocation's backend is gone
  (`iClosed_freed`). The post-contexts use `getD` so the type function is
  computable; `iFracLifecycle` adds a fractional split and join to the lifecycle
  and is accepted (`iFracLifecycle_ok`). `iLoanLifecycle` adds a borrow and a
  return, with the context-level loan-readiness evidence, and is accepted
  (`iLoanLifecycle_ok`); `iDelegationLifecycle` runs a two-level delegation and
  is accepted (`iDelegationLifecycle_ok`).
- `Cap/Typed.lean` is the context-preserving program fragment, repaired:
  `Owned Γ α` gives reads, writes and monadic sequencing over a fixed permission
  context, and its read and write constructors take `Ctx.CanRead`/`Ctx.CanWrite`
  evidence, so an access the context does not permit is not a program. There is
  no raw accessor and no representation index: a data-dependent index cannot
  obtain evidence here, and the chase lives in `Cap/UFCertified.lean`. The
  evaluator has an explicit outcome (`OOutcome`: done, exhausted, refused);
  `runOwned_wf` preserves the invariant, `runOwned_ctx` leaves the context
  unchanged, and `runOwned_no_refusal` proves a typed program is never refused
  from a matching, well-formed world (the read evidence and invariant make reads
  observations, and `World.write_succeeds` makes writes succeed). Context-changing
  transitions remain in `UCmd`.
- `Cap/UFRun.lean` is the union-find client of the checked world: reads are
  observations of the pure backends (`readParent`, `find` with fuel), and `union`
  issues writes through `World.writeChecked`, so `union_wf` preserves the world
  invariant. The concrete trace (1 under 0, 3 under 2, 2 under 0) is accepted
  (`ufTrace_ok`), its final world is well formed (`ufTrace_wf`), its backend
  parent array is the functional model's `[0,0,0,2]` (`ufTrace_backend`), and
  every pair of the four nodes is `Same` in the functional relation
  (`ufTrace_partition`). No path compression in the client, no read discipline:
  the checked route governs writes only.
- `Cap/UFChecked.lean` repairs the union-find's access discipline: `UFRep w a id n`
  is the representation predicate of a whole-share read-write parent array whose
  stored bytes are all valid node indices. It turns a *runtime* index `i < n`
  into static access evidence (`UFRep.canRead`, `UFRep.canWrite`) — the missing
  link that a program-text index cannot supply — and proves every represented
  parent read returns a value below `n` (`readParent?_lt`) and below 256, which is
  what the recursive chase needs for its next index. `findRootC` is the chase
  typed by that evidence, `compressC` the one-step compression through
  `writeChecked`, `compressC_ok` its non-refusal (the guard is the
  representation's own) and `compressC_wf` invariant preservation. The backend
  is read as the functional model's array (`UFArr`): `readParent?_step` makes
  each read the model's `step`, `findRootC_eq_of_stops` identifies a completed
  chase with `UF.findRootF`, and `findRootC_root`/`findRootC_reachable` give
  the result's root and reachability facts. The compression corresponds exactly
  to `UF.compress` (`compressC_UFArr`), so `compressC_same_sound` transfers the
  model's partition soundness: a compression to a reachable node creates no new
  `Same` pair. It is the checked read route over the pure backend, not an
  interpreter, FFI or in-place claim; full path compression and termination
  without fuel remain outside it.
- `Cap/UFCertified.lean` is the certified algorithm-facing interface:
  `compressC_trace` shows that a checked compression write is a one-command
  `UCmd` trace, connecting the concrete write to `checkWorld_write_guard`;
  `compressCertFull`/`compressPathCertFull`/`compressRootPathCertFull` preserve
  `FullInv` along the compression (the first two also preserve `UFRep`);
  `compressPathCertFull_trace`/`compressRootPathCertFull_trace` identify their
  results with the corresponding `checkWorld` trace; a
  `Cert pre α post` is a total computation from any world satisfying `pre` to a
  value and world satisfying `post`. `readParentCert` returns a parent value with
  its range proof and its identity as the functional model's `step`;
  `compressCert` performs the checked write and preserves `UFRep` and the world
  invariant; `findCompressCert` runs the chase and compresses the queried node to
  the root it reached, proving the returned value is a root of the represented
  forest, the representation and invariant survive, and `Same` is preserved in
  both directions. It requires a ranked forest and a byte-sized node domain
  (`n ≤ 256`). Reads additionally return the byte bound `v < 256` and carry
  `UFRep`/`WellFormed` into their postcondition. `Cert.pure` and `Cert.bind`
  give sequential composition when the continuation's precondition follows from
  the first postcondition; `Cert.bindDep` additionally hands the continuation the
  first value *and its postcondition*, with the continuation's post indexed by
  that value, so a continuation that needs a runtime proof at construction is
  expressible: `readThenCompressCert` reads a parent and compresses the same node
  to the value read, returning that value. `Ranked.reach_lt` bounds
  reachable nodes, and
  `stopsAt_of_ranked` bounds the chase by the rank; the rank completion is
  `findRootC_ranked_root`. A rank function is not required: `Acyclic` excludes a
  positive iterate returning to an in-range non-root, and `stopsAt_of_acyclic`
  obtains completion within `n + 1` steps by pigeonhole over the `n + 1`
  iterates (`findRootC_acyclic_root` is the certified corollary). A one-node
  root is acyclic and a two-node cycle is not; both controls are `example`s in
  the module. `acyclic_of_ranked` shows a ranked forest is acyclic (via
  `iter_root`), so `uWorld_ranked` yields the concrete instance `uWorld_acyclic`;
  the bridge uses no choice axiom. `findRootF_lt` and `findRootC_lt` bound a
  completed chase by the represented length. `Cap/UFForest.lean` adds the
  construction predicate `Built p n rank`: the identity or zero forest with rank
  its index, closed under linking two roots with the second of larger rank.
  `built_length`, `built_ranked` (same rank) and `built_bounds` hold, and
  `forest_acyclic` derives `Acyclic` from a `Forest` witness; a concrete union
  step and its acyclicity are examples. `uWorld_built` certifies the concrete
  64-byte zero array (`Built.zero`); an arbitrary runtime array still needs a
  construction witness. The partition equivalence is
  `compressC_same_iff`/`compress_same_iff_of_root`, built on orbit linearity
  (`reach_or_reach_of_common`), the root-is-terminal fact (`root_reach_eq`) and
  root-reach preservation (`reach_root_compress`). Full path compression is
  `UF.compressAll`, iterating one-step compression over a supplied path; under a
  root, in-range path nodes that each reach it, `compressAll_same_iff` proves the
  partition preserved in both directions, and the concrete 3→2→1 path lands on
  the constant array. `UFRunner` seals a world with the combined invariant, the
  representation, its backend and the rank (private fields);
  `UFRunner.findRoot` runs single-node find-and-compress, and `ufRunner_findRoot`
  proves the closed execution on the concrete 64-byte zero forest returns root 0;
  it is computable and evaluates, but is not yet the full-path state-threaded
  runner; the
  acyclicity route's run of the same forest is `uWorld_findRoot_acyclic` (65 fuel
  at node 3, root 0);
  `UFRunner.findRootSnapshot` returns the root with a copy of the allocation's
  bytes, and `ufRunner_findRootSnapshot` proves the observation is
  `(0, 64 zero bytes)`. The compression path is derived from the chase
  (`rootPath`): every node on it is in range and reaches the search's result
  (`rootPath_mem_reach_from`, `rootPath_mem_reach_result`), so
  `rootPath_compress_same_iff` proves full-path partition preservation along the
  path the chase itself takes. `compressBuf`/`compressPathCert` fold
  `compressCert` over a node list; `compressRootPathCert` runs the fold on
  `rootPath`, `compressRootPathCert_compressAll` identifies the final array with
  `UF.compressAll`, and `compressRootPathCert_same_iff` transports the partition
  theorem to the executed writes; `compressAll_example`/`compressSingle_example`
  distinguish [0,0,1,2] full-path from single-node compression. These
  certificates are computable, but the sealed runner is not yet threaded through
  the full path, and the C stage remains.
- `Cap/UFReuse.lean` is the reusable two-find client on the functional model.
  From the five-node forest `[0,0,1,2,2]` the chase from node 3 reads the path
  `[3,2,1]`, and `reuseFirst_eq` proves the full-path compression is exactly
  `[0,0,0,0,2]`. That output is the second operation's input certificate, not a
  restated array: `reuseFirst_ranked` proves it is still a ranked forest under
  the identity rank, and `reuseFirst_accepts_second` supplies the rank bound,
  the root the second chase stops at, and the in-range reachability of every
  node on its path. The second chase from node 4 reads `[4,2]`, and
  `reuseSecond_eq` proves its compression is exactly `[0,0,0,0,0]`. Both
  operations preserve the partition via `compressAll_same_iff`
  (`reuseFirst_same_iff`, `reuseSecond_same_iff`), and `reuseTwoFinds_same_iff`
  composes them back to the starting partition. `decide` appears only on finite
  list arithmetic: the exact arrays, paths and roots, and the per-index ranked
  cases, with no `native_decide`; the proofs depend on no axiom beyond
  `propext`, `Classical.choice` and `Quot.sound`. The sealed `UFRunner` is not
  threaded through this example: its world, representation and rank are private
  and it returns only one find's observation, so a second call would need a
  successor-runner operation and a new rank certificate for the post-state; the
  functional successor-runner is `Cap/UFReuseRunner.lean`.
  `bench/CapUnionFindReuse.lean` repeats the exact arrays as executable guards.
- `Cap/UFReuseRunner.lean` is the state-threaded sealed runner on the functional
  model. `PathRunner origin n rank` has a private constructor and private fields
  for the current array, its length, the ranked-forest certificate, the
  partition witness against the origin and the recorded compression history.
  `PathRunner.find` returns the root together with the successor runner whose
  array is the predecessor's with the chase's `rootPath` compressed to that
  root; the successor keeps the origin, the domain and the rank function, so a
  second call reads the first call's output array and history rather than the
  origin. `compressAll_length`, `ranked_compress`/`ranked_compressAll` and
  `compressAll_chase_ranked` show full-path compression preserves the length
  and the ranked-forest certificate; the rank decrease along the chase is
  `findRootF_rank_le` and `rootPath_rank_lt`, and the partition is preserved by
  `compressAll_chase_same_iff`. On the five-node example
  `reuseRunnerFirst_parent` and `reuseRunnerSecond_parent` give exactly
  `[0,0,0,0,2]` and `[0,0,0,0,0]`; `reuseRunnerSecond_consumes` states that the
  second call is run on the first successor (whose array differs from
  `reuseStart`), that the successor's history is `[3,2,1]` followed by `[4,2]`,
  and that a fresh find from node 4 on the origin records the longer single path
  `[4,2,1]` and leaves node 3 pointing at 2, so its final array is
  `[0,0,0,2,0]` rather than `[0,0,0,0,0]`. `reuseRunnerSecond_same_iff`
  composes the partition back to the origin, and the runner's `ranked`/`acyclic`
  accessors expose the two certificates. The runner is general over finite
  histories it records itself; it has no union, no amortised-complexity claim,
  no byte-backend correspondence, and the rank function is fixed for the run.
  The sealed `UFCertified.UFRunner`, which wraps a world and a representation
  predicate, is unchanged; this runner threads the functional `UF.Arr`. The
  controls are `bench/CapUFReuseRunner.lean`.
- `Cap/UFGeneric.lean` is the general full-path union-find through the sealed
  boundary. `decode`/`Rep` relate an allocation's bytes to a parent array, and
  `Rep.read` derives the read agreement from the representation itself. Reads go
  through `Sealed.read?`, the heap's index read: existence and bounds only, not a
  capability check. Writes are capability-checked: `Writable` is the whole active
  read--write leaf named by the capability and spanning `[0, n)`,
  `Writable.write_exists` derives acceptance from it, and
  `Writable.write_preserved`/`Writable.frames` keep it. The bounded chase
  `chase?` returns `some (root, path)` only when the reads reach a fixed point and
  `none` on fuel exhaustion; it never reports `(x, [])` for an exhausted search.
  `chase?_none_iff` makes the contract exact (`none` iff the functional chase does
  not stop within the fuel), `chase?_some_spec` identifies a `some` result with
  `UF.findRootF`/`rootPath`, and `chase?_eq_ranked` shows a ranked forest always
  completes at `rank x + 1`, so an exhausted chase cannot masquerade as a root
  find. The single-write laws are `sealed_write_component`,
  `sealed_write_snapshot_self` and `sealed_write_frames`; the last preserves
  `WriteFrame`, whose `component` field says every other allocation's full
  `Reconstruction.State` is unchanged, so its bytes, `Storage` certificate and
  ownership observations all survive. `WriteFrame.component_other` exposes that
  component equality through a lookup witness and `WriteFrame.storage_other` the
  `Storage` equivalence; `WriteFrame.rel_write` adds that, where an address map
  relates to the state, the relation survives the write and another allocation's
  window and bytes are unchanged. `compressPath_spec` lifts the write law over
  the compression path, and `sealedFind_spec` proves for an arbitrary represented
  ranked forest that the find completes, the root is the functional root and a
  fixed point, the post-buffer represents exactly
  `UF.compressAll p r (rootPath p fuel x)`, the array stays ranked, acyclic and
  in range, `UF.Same` is preserved in both directions, the successor keeps
  `Writable` and satisfies `State.Inv`, and every unrelated allocation's full
  component is framed. `findRanked` is the wrapper whose fuel is
  the rank bound rather than a caller choice; `findRanked_spec` returns the
  successor `Precondition` and `findRanked_twice` runs two calls on an arbitrary
  forest without reconstructing preconditions. The byte representation caps
  `n ≤ 256` (`Precondition.fits`), and no large-scale performance is claimed.
  The command-list form of that frame is supplied at the integrated boundary, so
  an accepted run frames an untargeted allocation there as well. What this layer
  does not supply is the compiled-bridge connection: the address-map relation is
  a logical window assignment, not a loader's assignment for the compiled kernel,
  and the ABI, a loader and native execution stay outside the model.
- `Cap/UFIntegrated.lean` instantiates the general theorems on the five-node
  forest `[0,0,1,2,2]`. `ufStart_precondition` supplies the general
  preconditions; `ufFirst_spec` is `findRanked_spec` on the fixture, and
  `ufFirst_general` identifies the computed root `0` and array `[0,0,0,0,2]`.
  The second call consumes the first call's successor (`ufSecond_general`,
  `ufSecond_run`), leaving `[0,0,0,0,0]`, matching
  `reuseRunnerFirst`/`reuseRunnerSecond`; a fresh find from node 4 on the start
  state instead leaves `[0,0,0,2,0]` (`ufSecond_consumes`).
  `ufSecond_invariant`/`ufSecondOther_invariant` re-export `Sealed.state_inv`,
  `ufSecondOwnershipFrames_of_ok` records that the whole-share capabilities,
  retired names, return obligations, both heaps and both live identities are
  unchanged, and `ufSecondOther_frames` covers a second allocation. The
  `decide`-based root/snapshot options are the compiled controls, and
  `bench/CapUFIntegrated.lean` also exercises the exhaustion contract (zero or
  insufficient fuel is a refused find, never a root) and the write-authority
  predicate. The runnable driver is `lake exe capuf`
  (`bench/CapUFDriver.lean`): it executes both calls through the general path
  and repeats them with an unrelated allocation, failing if any root or snapshot
  differs. On the pinned rc3 build it printed roots `0,0,0`, parent
  `[0,0,0,0,0]` and unrelated allocation `[5,0,0]`.
- `llvm-bridge/` is the compiled-C kernel package, outside the `Cap` library.
  `c/store8.c` is `void store8(uint8_t *p, uint64_t i, uint8_t v) { p[i] = v; }`;
  `scripts/emit-ir.sh` compiles it on a worker, and `ir/store8.ll` is clang's
  emission projected onto the parser's surface. `LlvmBridge/Store8.lean` pins the
  committed text to the AST with a `#guard`, proves the emitted body's behaviour
  at the call site is exactly the reference store's single bounded outcome under
  `x.toNat < 2 ^ 63` (`Beh_store8IR_iff`: no `ub` run and no divergent run), the
  written byte and the frame (`store8IR_byte`, `store8IR_frame`), and a
  refinement against a reference kernel (`store8IR_refines_store8Ref`). `LlvmBridge/Ownership.lean`
  relates one integrated allocation's heap bytes to the bridge's byte memory:
  `allocAddr` with `allocAddr_injective` for one window, `MemRep m buf base` with
  `MemRep.set`/`MemRep.frame_write`, `write_authority` derived from the write
  command's guard, and `store8_exec_write_comp`/`sealed_store8_write_comp` —
  completion at every positive budget, the represented post-state, the frame,
  the written byte on both sides, other allocations unchanged and the integrated
  invariant. The assumptions are stated, not discharged: the caller supplies
  `MemRep` and `base`; `off < 2 ^ 63` is the pointer-width premise; injectivity
  is within one window, and two allocations' disjointness is the hypothesis of
  `MemRep.frame_write`, not a loader theorem; the IR projection is assumed and
  parser/AST agreement is textual; the capability route is the integrated
  reconstruction guard, not `World.Writable`; and the ABI, native compilation,
  installation, physical storage and replay of a copied live handle remain trust
  or proof obligations (`Cap.Sealed.boundaryClaims`). No full C/ABI or physical
  ownership refinement is claimed. It builds only on a worker against a sibling
  `lean-llvm` checkout (`scripts/build-remote.sh`), and `EVIDENCE.md` records
  those builds.
- `Cap/Marshal.lean` is the verified marshalling layer for the closed code
  universe. `Codec c` carries `encode : El c → List UInt8`, `decode`, and
  `decode_encode`; `codec` supplies one for every code (tagged products/sums,
  length-prefixed lists, unary `Nat`). `Marshal c` and `Marshal.Rep` relate a
  buffer to its ghost `El c` value. `World.allocWithChecked` allocates a fresh
  owner whose backend is initialised from bytes, with `allocWithChecked_wf` and
  `allocWithChecked_succeeds`; `Marshal.alloc` proves the initial `Rep` and
  `Marshal.read`/`read_rep` decode a represented buffer, and
  `Marshal.readC`/`readC_rep` require `Ctx.CanReadRange` over the backend's
  bytes; `Marshal.writeC`/`writeC_rep`/`writeC_fullInv` require
  `Ctx.CanWriteRange` and an encoded-length equality, preserve `Rep` and
  `FullInv`, and their byte-wise checker trace reaches exactly `writeC`
  (`writeC_trace_ok`, `writeC_trace_eq`); `bench/CapMarshal.lean` exercises
  whole-range product decoding, the left-only spatial refusal, same-length
  replacement, differently sized encodings, and the empty-range policy (an
  existing empty backend is still required);
  `Marshal.free` delegates to `World.freeChecked` (`free_wf`, `free_fullInv`),
  and `alloc_fullInv` lifts byte-initialised allocation to `FullInv`. Storage remains `El c`, not an
  arbitrary type: `SafeValue` is encoding, not confinement.
- `Cap/UFCompress.lean` adds bounded root finding and one-step compression to the
  functional model: `findRootF` chases parents with fuel, `StopsAt` records a
  reached fixed point, `findRootF_root`/`findRootF_reachable` give the root and
  reachability facts, `compress p x r := p.set x r`, and
  `compress_same_sound` shows a compression from a reachable root creates no new
  `Same` pairs (with the reach-avoiding lemmas alongside). It is one-step
  compression on the functional model: not full path compression, not the
  ownership layer, and no termination or complexity claim.
- `Cap/UFPartition.lean` is the functional union-find relation: `Reachable` by
  parent steps, `Same` by a common root (proved reflexive, symmetric and
  transitive), and the simple `union p a b := p.set b a`. It proves `union_same`
  and conditional class preservation, the concrete trace ending at
  `[0,0,0,2]`, and `uf3_same_all` (every pair below 4 is `Same`). It has no
  ownership, no root finding, no rank and no path compression; the `set`-based
  union is not the general union-find.
- `Cap/HashSet.lean` is a linear-probing hash set under the discipline: one
  eight-slot whole-share read--write allocation, `Table.insert` probing and writing
  through the owner's `Writable` guard (derived from the example owner), a read-only
  `contains`, and `insert_length` showing the table length is preserved. The
  concrete colliding insertions 3, 11, 19 fill slots 3, 4, 5; `contains 11` is true,
  `contains 4` is false, and the length stays 8. No resizing, deletion, hashing
  theorem or complexity claim.
- `Cap/UnionFind.lean` is the union-find example under the write discipline: one
  whole-share read--write leaf covers a four-element parent/rank allocation;
  `UF.writeParent` takes the owner's `Writable` guard as a proof and preserves the
  store length; `ufOwner_writable` supplies the guard for in-range indices and
  `ufOwner_not_writable_4` shows index 4 has none. The concrete run (attach 1 under
  0, 3 under 2, 2 under 0) has parent `[0,0,0,2]` (`uf3_parent`), every `findRoot`
  returns 0 (`uf3_find_all`), and the lengths are preserved (`uf3_lengths`). It is
  an example of the discipline, not a verified union-find against an
  equivalence-class model.
- `Cap/Disposal.lean` is the one legal-disposal predicate: `DisposalState` pairs a
  world with a loan context; `Legal` requires the found owner, its coverage, the
  recorded disposal entitlement, an empty loan list and a reconstructed root
  (a single active whole-share leaf over the allocation); `free?` is the checked
  route through `World.freeWith?`, and the facts are `free?_none_of_not_legal`,
  `free?_legal`, `free?_removes_owner`, `free?_none_after_free`,
  `free?_none_of_spatial_root` (an unsupported spatial decomposition refuses),
  the entitlement and loan refusals, and concrete examples. It is not yet wired into
  `Cap.Unified`, and names are invalidated by owner removal rather than by arena
  generations.
- `Cap/World.lean` is the world of owners, mutable backends and loans: the heap
  map is a function from allocations to `Backend`, the permission context
  carries the `LoanCtx` (`Ctx.loans`, seeded everywhere with
  `LoanCtx.rootOnly`: one live root lifetime, no loans), `World.Rel` combines
  `Ctx.Realizes` with the per-owner buffer length, `write?` takes the owner's `Writable` guard as a
  proof and replaces the backend, and `freeWith?` dispatches through the context's
  disposal check and clears the backend. `write_rel` and `freeWith_rel` preserve the
  relation. It is a pure world, not the interpreter, an FFI path or a concurrency
  claim.
- `Cap/History.lean` is the issuance-history invariant: `Ctx.HistoryOK`
  (`issued` duplicate-free and every live identifier in it), with
  `Ctx.historyOK_alloc` (fresh root and disposal identifiers, distinct),
  `Ctx.historyOK_free` (history unchanged, live set shrinks) and
  `Ctx.historyOK_update_of_ids` (an owner replacement, including a retag, whose
  identifier set is unchanged), plus the membership bounds
  `Owner.splitAt?_ids_sub`, `splitFraction?_ids_sub` and
  `joinFraction?_ids_sub'`. Allocation's checker tests the history, and the
  indexed allocation constructor carries the corresponding premises. Each
  command's history preservation now lives beside its transition
  (`World.historyOK_write`, `historyOK_splitAtChecked`,
  `historyOK_splitFractionChecked`, `historyOK_joinChecked`,
  `historyOK_freeChecked`, `historyOK_allocChecked`, `historyOK_beginBorrow` and
  `historyOK_endBorrow`), and `Cap/TopInvariant.lean` proves the command carrier:
  `World.TopInv` (well-formedness together with `HistoryOK`) is what
  `World.CommandInv` extends with `Ctx.LoansReady`, and whole executions preserve
  `CommandInv` (`checkWorld_top`), with concrete instances (`emptyWorld_top`,
  `uWorld_top`). Disposal legality is `Cap/Disposal.lean`.
- `Cap/Access.lean` gives the access evidence the certified instructions carry:
  `Ctx.CanWrite` (the owner is found and the write guard accepts) and
  `Ctx.CanRead` (the owner is found and the capability is readable at the
  index). A matching well-formed world supplies the backend and bounds:
  `World.read_succeeds` and `World.write_succeeds` (\(\file{Cap/IProg.lean}\)
  for the write) prove a certified access is never refused, and
  `World.no_two_canwrite` proves two certified writes at one byte name the same
  capability. Every indexed constructor's evidence covers its checker:
  `splitAtChecked_succeeds`, `World.allocChecked_succeeds` and
  `World.freeChecked_succeeds`, together with the two access success lemmas,
  give "a typed command of the indexed layer is never refused". `IProg.read` and `IProg.write` carry these predicates, and so do `Owned`'s, so an
  unauthorised access is not a program; `runOwned_no_refusal` extends the
  no-refusal guarantee to the fragment from a matching, well-formed world.
- `Cap/Exclusivity.lean` turns coverage into write exclusivity:
  `Tree.budget_leaf_ge` (a present, unconsumed leaf covering a byte contributes
  its share to the budget) and `Tree.budget_two_leaves` (two distinct such
  leaves contribute both shares) give `Owner.no_two_writable`: at a byte of a
  well-formed owner, two writable capabilities have the same identifier. So the
  discipline's central "nothing bad" property — at most one writer per byte — is
  a theorem, not an assumption.
- `Cap/Runner.lean` is the sealed certificate form the runner handoff accepts:
  `Prog pre` packages a command list with `checkWorld pre cmds = .ok post`, so it
  cannot exist without the checker's derivation; `Prog.snapshot` observes only an
  immutable buffer from the post-world. `checkWorld_append` runs an appended list
  from the first part's result, so `Prog.seq` composes certificates: the second
  program starts in the first's post-world. `World.emptyWorld` (no owners, no
  backends) is well formed (`emptyWorld_wf`); `ClosedProgram` packages commands
  accepted from the empty world, with `post` chosen from the run, `post_ok`
  spending the acceptance, `wf` giving the final world's invariant, and
  `snapshot` the only observation; `closed64` is the concrete allocate/fill
  example with `closed64_snapshot` proving the 32 ones then 32 twos. `p64` is the
  concrete 64-byte
  certificate and `p64_snapshot` is its result. `World` is still public pure
  model data; the sealed construction path, the combined invariant and the full
  command set are in place, while the C runtime boundary, physical storage
  independence and concurrency remain outside the model.
- `Cap/Indexed.lean` is the world-indexed computation type: `Ix pre α post` runs
  from `pre` and ends in `post a`; `ret` and `bind` thread the worlds, with the
  continuation's precondition forced to be the first computation's post-world;
  `writeIx` carries the ledger guard and the backend write, and its post-index is
  the world the guarded write produces. `prog_run` computes a two-write program at
  elaboration` and `prog_sound` shows `checkWorld` reaches the same post-world.
  Indices are ordinary `World` values; there is no hidden-index elaborator, so
  symbolic programs are not inferred.
- `Cap/Unified.lean` is the command language: a value-carrying
  `UCmd` (`write`, `splitAt`, `splitFraction`, `join`, `free`, `alloc`,
  `beginBorrow`, `endBorrow`, `nop`), `World.writeChecked`
  which checks the ledger's `writableB` and performs the backend write,
  `World.splitAtChecked` for spatial splits, `World.freeChecked` for disposal
  through the recorded capability, `World.allocChecked` for allocation with
  fresh identifiers, and `checkWorld` as checker and interpreter at once.
  `writeChecked_sound` names the owner, guard, backend and replacement;
  `writeChecked_wf`, `World.splitAtChecked_wf`, `World.freeChecked_wf` and
  `World.allocChecked_wf` preserve the world invariant, `checkWorld_wf` takes the
  command carrier `World.CommandInv` (`WellFormed` together with `HistoryOK` and
  `Ctx.LoansReady`) and concludes `World.WellFormed` for every command, and
  `checkWorld_rel` derives `World.Rel` from it; the concrete 64-byte world is
  well formed (`uWorld_wf`),
  the run through this route snapshots 32 ones then 32 twos (`uRun_snapshot`),
  and its world remains related (`uProgram_rel`). `uLifecycle` runs
  alloc/write/spatial split/write/fractional split/join/write/free through this
  route: it is accepted
  (`uLifecycle_ok`), its final world is well formed (`uLifecycle_wf`), and the
  untouched pre-existing backend reads back its initial zeros
  (`uLifecycle_snapshot`). Snapshot observation and the sealed boundary's
  full-path state threading are not yet commands of this language.
- `Cap/Certify.lean` records the kernel-checked certificate for a closed program:
`certifiedProgram_checked : Checked certifiedOwner 12 certifiedProgram` by
`unfold Checked; decide` (no axioms), and `certifiedProgram_covered` carrying
coverage through it. The surface elaborator does not emit this term; the module
shows the certificate it would have to emit, not proof-producing elaboration.
- `Cap/Surface.lean` is the surface front end: `#own_prog owner D { ... }` with
  `write`, `splitAt`, `splitFraction` and `nop`, elaborating to `Cmd` and running
  `Cap.check` at elaboration time; acceptance is logged and refusal is a compile
  error with the checker's message. It emits no proof term, and `splitFraction`
  derives positivity with `by decide`, so a non-reducible share is refused. The
  positive example splits a 64-byte leaf, writes both halves and splits the left
  half 32/32. `bench/CapSurfaceReject.lean` holds the out-of-range write, the
  out-of-range split and the non-summing shares, each refused with its message. It
  is not the hidden-index elaborator of the design. `#own_cert n : o D { ... }`
  translates the same surface commands to the deep list and declares
  `theorem n : Checked o D [..] := by unfold Checked; decide` through the ordinary
  command elaborator, so the kernel checks the certificate; `Cap.surfaceCert` is a
  concrete instance. A deep-list form `#own_cert n : o D := cs` is also available.
- `Cap/Core.lean` is the deep command language and its executable checker:
  `Cmd` for write, spatial split, fractional split and no-op; `Owner.writableB` with
  `writableB_sound`; `check` returning `Except String Owner`; and `Checked` as its
  success predicate. Proved: the empty program is accepted, a failing guard is an
  error, an accepted write carries `o.Writable` (`write_checked`), accepted splits
  invoke succeeding transitions and name a leaf with the required bounds/shares,
  `check_covered` carries coverage through a whole run, and the read-only write is
  refused (`readOnly_write_not_accepted`). Splits require `Owner.FreshIds` of the
  two child identifiers, so duplicates and the reused parent identifier are refused
  with `msgFresh` (`splitAt_checked_fresh`, `splitFraction_checked_fresh`; regressions
  in `bench/CapFreshness.lean`). It is a deep syntax and checker for the owner layer
  only, not surface elaboration, not a heap semantics, and acceptance is checker
  acceptance rather than execution safety.
- `Cap/Discipline.lean` couples a `World` with a delegation chain.
  `World.delegationChains` groups the outstanding loans by `(allocation, base)`
  and builds a chain per group; `World.delegationChains_ok` proves that every
  chain is valid, that the chains cover every world loan, that each chain's
  `toLoans` is exactly that group's subsequence of the world loan list, and that
  the flattened projection is a permutation of it. The theorem assumes
  `World.LoansChainOrderOK` in addition to `BorrowOK`, because `BorrowOK` does
  not order the loan list. `State.OK` is the single-chain pairing: the world
  satisfies `FullInv`, the chain is valid, the loan list is exactly the chain's
  edges, and the holder is the active leaf with the chain's resource
  description; the initial 64-byte state satisfies it (`initialState_OK`) and a
  checked write through the holder preserves it (`State.write_OK`).
  `State.beginBorrow` drives `World.beginBorrowChecked` and appends the loan to
  the chain through the checked `begin?`; `State.endBorrow` drives
  `World.endBorrowChecked` and pops through `end?`. `State.beginBorrow_OK` and
  `State.endBorrow_OK` preserve the correspondence. `bench/CapRealization.lean`
  carries the G2 control — the borrower's write is still observed through the
  restored lender after the return, with the lender's write refused while
  borrowed — and the G3 control, where the outer return is refused while the
  inner loan is live and the inner-first order succeeds.
- `Cap/Delegation.lean` is the delegation-chain vocabulary:
  `Edge` records lender, borrower, allocation and resource description; the
  chain stores one resource descriptor that every edge must agree with, so
  delegation never changes the allocation, footprint, share or ceiling.
  `Chain.path` is `base :: edges.map (·.borrower)`; `Chain.OK` requires that
  path to be nodup, distinct loan identifiers, non-alias edges, the first edge
  to be lent by the base, every later edge by the previous borrower, and the
  stored holder to equal the derived holder
  (`Chain.derivedHolder`: the innermost borrower, or the base when empty).
  Distinct lender and borrower lists are not enough — the two-edge cycle
  `a → b, b → a` has both and is rejected by the path condition — and a chain
  cannot name an unrelated holder. Raw `begin`/`end` are unchecked structural
  transformations; `begin?`/`end?` are the checked operations, and `beginCheck`
  decides resource agreement, current-holder lending, fresh identities against
  the path and a live lifetime, with `beginCheck_sound` turning the executable
  check into the admissibility the preservation theorems consume.
  `Chain.ofPath` assembles a chain from loans by following borrower-to-lender
  links back to the base, and `Chain.toLoans` fills the loan record from the
  chain's resource description. It is the chain vocabulary of the world
  correspondence in `Cap/Discipline.lean`;
  `bench/CapChainRepair.lean` holds the cycle, holder, wrong-lender, reused
  borrower, duplicate-loan and changed-resource controls, each paired with the
  affirmative case on the same fixture.
- `Cap/Retag.lean` and `Cap/Borrow.lean` are the retag accounting model:
  `Tree.retag` renames a leaf without changing its budget (`Tree.retag_budget`),
  `Owner.retagLeaf?` requires an active lender and a fresh name
  (`retagLeaf?_budget`, `_covered`, `_len`), and `World.BorrowOK` is the
  integrated delegation invariant: distinct loan, lender, borrower and lifetime
  names (`LoansDistinctOK`), no self-alias (`LoansNonAliasOK`), issuance of every
  name a loan mentions (`LoansIssuedOK`), live and bounded lifetimes
  (`LifetimesBoundedOK`), an owner at each allocation (`LoansAllocOK`), global
  detachment of every lender from the live identifier lists (`LoansDetachedOK`),
  a recorded chain base and base-or-chain lender (`LoansBaseOK`), an active
  terminal borrower or a delegated successor with the leaf's resource
  description (`LoansTerminalOK`), agreement of adjacent edges on base,
  allocation, footprint, share and ceiling (`LoansAgreeOK`), issued-order
  monotonicity (`LoansOrderOK`), and the derived `BorrowAcyclic`. It is preserved
  by writes (`borrowOK_write`), fresh allocation (`borrowOK_allocChecked`),
  checked disposal (`borrowOK_freeChecked`), spatial split
  (`borrowOK_splitAtChecked`), fractional split
  (`borrowOK_splitFractionChecked`), join (`borrowOK_joinChecked`), borrow
  (`borrowOK_beginBorrow`) and return (`borrowOK_endBorrow`), and
  `borrowOK_loansReady` derives the command-level `Ctx.LoansReady`.
  `World.beginBorrowChecked`/`endBorrowChecked` retag the active leaf to a
  distinct borrower and back; return refuses while another loan borrowed from
  the same borrower or a descendant loan is live. Splits and fractional joins
  refuse while any loan is outstanding for the allocation, and the typed
  split/join constructors carry that evidence. `bench/CapBorrow.lean` exercises
  borrower write, lender refusal, loan removal, restoration, free-during-borrow
  refusal, split-during-borrow refusal and nested return order;
  `bench/CapDelegation.lean` adds the distinct-borrower controls on the checked
  world route (borrow, reborrow, return order, disposal, and the same borrow
  through a fractional split), each refusal paired with its affirmative case.
- `Cap/Sealed.lean` is the sealed execution boundary, and it is an alias module
  over `Cap.Integrated`: `Sealed` is `Integrated.Sealed`, and `initial`, `run`,
  `snapshot`, the checked operations and the observation aliases re-export that
  boundary. There is no `World`/`UCmd` sealed entry point and no certified world
  import. `Sealed.run` executes a list of integrated `Cmd` values, carries
  `State.run_inv`, and returns no state on a refused step. The observations are a
  per-allocation snapshot, byte read, fragment description, retired names,
  outstanding return obligations and live allocation list. The private
  integrated constructor and invariant proof are what prevent manufacture.
  `boundaryClaims` lists the executable-edge claims with their status: integrated
  command execution and invariant preservation are proved, while the C store
  trace, physical reference counts and physical storage independence are runtime
  contracts and concurrency is excluded; `boundary_no_physical_proof` records
  that no physical claim is marked proved. Lean has no module opacity, so this
  seals the *construction* path, not physical storage: the pure model's data is
  shared by copied values, which is the C runner's contract, not a theorem.
  `bench/CapSealAccept.lean` builds the canonical state, runs integrated
  commands and observes the bytes; `bench/CapSealReject.lean` checks that the
  constructor and the retired world entry point are unavailable, and
  `bench/CapSealPeekReject.lean` checks the representation field.
- `Cap/Reconstruction.lean` is the borrowed-subdivision model. A `Forest` records
  the checked spatial or fractional rule at every interior node, and its
  `budget` is the frontier sum (`budget_eq_toTree`); `Valid` requires every
  recorded rule to be checked. `RuleValid` gives the two rules: a spatial rule
  needs equal allocation and ceiling, active disjoint children whose intervals
  partition the parent, and the inherited share; a fractional rule needs equal
  footprint and ceiling, positive child shares summing to the parent's.
  `Forest.splitSpatialAt`/`splitFractionAt` preserve the budget and validity,
  and `reconstructAt` restores a suspended parent from two children matched to
  its recorded rule. `State` pairs the forest with the reference heap, the
  issued and retired names and the outstanding `Restore` obligations; `State.Inv`
  is frontier coverage, forest validity and the ownership accounting predicate
  `State.Accounts`, and `State.Storage` separately says the heap holds that
  `State.Accounts` constrains current
  authority-node identities, issuance coverage, retirement, dormant lenders,
  restoration realization, resource agreement and restoration order, so a
  retired or dormant name is not a current leaf
  (`State.Accounts.retired_not_current`,
  `State.Accounts.dormant_not_current`) and an appended restoration naming an
  unissued party breaks it (`State.Accounts.cons_restore_not_accounts`). The
  account is not a structural restatement of the forest: its fields
  (`nodeIds_nodup`, `issue_covers`, `retired_absent`, `restores_issued`,
  `borrowers_nodup`, `lenders_nodup`, `lender_ne_borrower`, `dormant_absent`,
  `borrower_not_rule`, `restore_realized`, `node_agrees`, `nested_agrees`,
  `restore_order`, `rule_fragments_issued`) relate the forest to `issued`,
  `retired` and `restores`, so changing only those histories can invalidate it.
  `Restore.Depends r r'` means `r'.lender = r.borrower`; `State.RestoreOrder`
  requires every such dependency to strictly decrease the index in `restores`.
  Since borrowing prepends a record, dependencies run from later records to
  earlier ones. `State.Accounts.dependency_wellFounded` rules out a positive
  delegation cycle, and `State.Accounts.restore_reaches_terminal` shows every
  outstanding obligation reaches a terminal forest node by a finite path with
  the recorded resource agreeing along it; `Forest.suspended_frontier_realizes`
  connects a suspended parent to its `Forest.nodes` entry, its rule descendants
  and the descendant frontier budget. `bench/CapRestorationOrder.lean` checks
  that the earlier fields admit a two-edge cycle while the repaired account
  rejects it, that a longer cycle and a missing terminal are rejected, and that
  a valid nested borrow is accepted.
  `State.write`,
  `borrow`, `splitSpatial`, `splitFraction`, `reconstruct` and `return` are
  checked, each preserving `State.Inv` (`State.*_inv`) and `State.Storage`
  (`State.*_storage`), with the obligation frames
  `splitSpatial_frames_restores`/`splitFraction_frames_restores` and the
  refusals `return_none_of_no_leaf` (return before reconstruction),
  `splitSpatial_none_of_issued` and `splitFraction_none_of_retired`. This is a
  component model, not the world command path: `World.splitAtChecked` still tests
  the allocation-wide loan exclusion, recorded by
  `World.splitAtChecked_refuses_with_loan`, so the world `UCmd` split/join guard
  does not consult this forest.
  `bench/CapReconstruction.lean` drives the 64-byte borrow/split/write/
  reconstruct/return lifecycle with each refusal paired to its affirmative case.
- `Cap/Integrated.lean` is the one integrated sealed semantics: `State` is a
  list of `Reconstruction.State` keyed by `AllocId` together with the persistent
  allocation history `allocsIssued` and capability history `issued`, and
  `State.Inv` requires distinct allocation identifiers, a duplicate-free
  persistent allocation history containing every live identifier, every
  component's `State.Inv` (including `State.Accounts`) and `State.Storage`, and
  the capability history covering every component-issued name. `Cmd` is the
  checked command language (`alloc`,
  `write`, `borrow`, `splitSpatial`, `splitFraction`, `reconstruct`, `ret`,
  `free`); every command names its allocation, and `State.exec` refuses an
  absent one. `State.exec_inv` and `State.run_inv` preserve `State.Inv`;
  `State.exec_frames_other` shows that an accepted command leaves every other
  allocation's lookup — and therefore its snapshot — unchanged, and
  `State.run_frames_other` lifts that frame over a whole command list: a run
  whose commands all avoid an allocation leaves its component lookup unchanged,
  with `State.run_snapshot_other` and `State.run_storage_other` giving the bytes
  and the `Storage` certificate directly. `State.free` is
  accepted only for a single whole active leaf with no outstanding return
  obligation, read structurally by `wholeActiveB_iff`, and it leaves both
  histories intact (`State.free_histories_intact`). `State.alloc` refuses an
  allocation identifier in `allocsIssued` and an initial capability name in
  `issued`, so a freed identifier cannot be reissued
  (`State.realloc_after_free_refused`, `State.realloc_initial64_refused`) and an
  old capability cannot authorize a replacement
  (`State.alloc_reusing_old_capability_refused`); a fresh allocation with fresh
  names is accepted (`State.alloc_fresh_after_free_some`). `Prog` is the typed
  wrapper: a command list together with the boolean check from an invariant start
  state, and `Prog.never_refuses` derives an accepting run. `Sealed` is the
  private multi-allocation boundary with snapshot, byte-read, fragment,
  retired-name and obligation observations; an accepted sealed write is exactly
  the underlying state's accepted write command (`Sealed.write_ok_iff`), and a
  command the state accepts produces a sealed successor
  (`Sealed.write_exists_of_exec`), which is what a capability-derived write uses.
  `Sealed.run` executes a whole command
  list; `Sealed.run_ok_iff` identifies an accepted sealed run with the underlying
  accepted `State.run`, and `Sealed.run_frames_other` returns a `Sealed.RunFrame`
  for an allocation no command targets, so that allocation's component, bytes and
  `Storage` certificate are unchanged. `Sealed.lifecycle64` is the 64-byte
  borrow/split/write/reconstruct/return cycle, `Sealed.reuseLifecycle` runs a
  second cycle on its output, and
  `Sealed.alloc` adds a second allocation. `bench/CapIntegrated.lean` exercises
  independent two-allocation borrowing, an independent sibling split while a
  loan is outstanding, the return order, the free guard and the refusal controls
  retained from the retired single-allocation sealed module;
  `bench/CapIntegratedPeekReject.lean` checks the sealed representation and
  constructor are private. The world `World`/`UCmd` path and `World.FullInv`
  remain as separate theorems on their own state, and `World.splitAtChecked`
  keeps its allocation-wide loan guard. The sealed path is the integrated
  reconstruction language; it does not claim to route `World` through the forest.
- `Cap/AddressMap.lean` is the finite address assignment for that integrated
  state: `Window` is `[base, base + len)`, `Map` maps live `AllocId`s to windows,
  and `Map.WellFormed` requires distinct keys, pairwise-disjoint windows and
  `base + len ≤ 2 ^ 64`. `Rel`/`Covers` relate every live allocation to
  exactly one window of its recorded length, `Map.within`/`addr?` produce an
  address only for an in-window offset, and `Map.addr?_lt` bounds a produced
  address by `2 ^ 64` without wraparound. `Rel.alloc`, `Rel.free` and `Rel.write`
  preserve the relation; `Rel.write` frames every other allocation's lookup and
  snapshot, and `WriteFrame.rel_write` lifts that to a sealed write: an accepted
  `Sealed.write` preserves `Rel` and leaves an unrelated allocation's window and
  bytes unchanged. `Rel.run_other` carries that frame across a whole command
  list, and the fixture runs a two-command list (`exampleRun`) that targets only
  `⟨0⟩`: `example_run_other` keeps `⟨3⟩`'s component, bytes and `Storage`
  certificate and its window as they were. The two-allocation fixture proves
  writing `⟨0⟩` leaves `⟨3⟩`'s window and bytes unchanged, and
  `alloc_refuses_overlap` plus the fixture checks
  refuse overlapping, missing and out-of-window addresses. This is a logical
  window model only: it is not a loader's address assignment and is not wired
  into `llvm-bridge`.
- `Cap/Trace.lean` states trace properties of the checker language:
  `checkWorld_cons_ok` splits an accepted command list at its first command, and
  `checkWorld_write_guard` proves that a write at any position of an accepted
  trace held its guard (owner found in the context, `Writable`) at the world
  reached just before it. The command language carries no access evidence by
  design; this is the property its run-time check has, while `IProg`, `Owned`
  and `Cert` are the evidence-bearing client surfaces.
- `Cap/FullInv.lean` is the combined invariant this stage carries:
  `World.FullInv w := w.TopInv ∧ w.BorrowOK` (world well-formedness, issuance
  history and the integrated delegation invariant). `World.checkWorld_fullInv`
  proves it preserved by whole executions, command by command;
  `World.fullInv_commandInv` derives the command carrier, and
  `World.emptyWorld_fullInv` is the canonical initial state.
- `Cap/Exec.lean` is the instruction interpreter over the backend: `fill` and
  `snapshot` instructions, `exec` returning the final backend and observation, the
  64-byte example (`exec_example`), a single-fill refinement to `Heap.fill?`
  (`exec_fill_refines`), the example's agreement with `Heap.example64Buf`
  (`exec_example_refines_heap`), and the out-of-range fill failure
  (`execFill_beyond`). It is an interpreter over the pure backend for one
  allocation, not the reference interpreter or a compiler guarantee.
- `Cap/BackendRun.lean` runs the 64-byte example on that backend: fills `[0,32)`
  with 1 and `[32,64)` with 2, and proves the snapshot is the reference heap's
  (`exampleBackend_snapshot`, `exampleBackend_rel`, both by `decide`). It is a
  concrete run, not the interpreter, an FFI claim or a performance result.
- `Cap/BackendArr.lean` is the byte-array-backed backend: `BackendArr` stores a
  `ByteArray`; `toBackend` reads its data back as a byte list; `empty_refines`,
  `read_refines`, `write_refines` and the fold-level `fills_refine` state
  agreement with the pure `Backend`; the 64-byte two-range fill refines the pure
  run (`ba64_refines`) whose snapshot is the reference bytes (`pure64_snapshot`
  by `decide`, `ba64_snapshot`). In-place update at runtime is not observable
  here and is not claimed. `bench/CapBATiming.lean` times the list backend, the
  byte-array backend and the reference heap on the same 64-byte fill-and-sum
  pattern with agreeing checksums; observed in one interpreted run on this
  machine: 73,959 ns per repetition (list), 47,688 (byte array), 51,956
  (reference). Interpreted and environment-dependent; no in-place update is
  observed or claimed.
- `Cap/Backend.lean` is the pure mutable-backend model for one allocation:
  `Backend` with a buffer and length proof, `Rel` to the reference heap,
  `empty_rel`, `read_refines`, `write_refines`, `write_preserves_len` and
  `write_then_read`. It is a state-machine refinement, not an FFI or compiler
  guarantee.
- `bench/CapTiming.lean` times the pure backend and the reference heap on the
  64-byte fill/snapshot pattern. Observed at this revision: 47,643 ns per
  repetition for the backend model and 32,648 ns for the reference model, equal
  checksums, interpreted evaluation. These are measurements of the two models'
  operation sequences, not of an interpreter, an optimised backend, FFI or
  allocation/GC, and they are environment-dependent.
- `scripts/check_cap_controls.sh` runs the capability fixtures with their intended
  diagnostics: the admission, prototype and freshness positives must elaborate, and
  the alias/axiom/wrong-domain/surface/reflective negatives must fail with the
  named message. `scripts/check_all.sh` includes it.
- `scripts/check_cap_axioms.lean` is the axiom audit for the borrowing,
  reconstruction and reuse results: it prints the axioms of the combined-invariant
  preservation theorems, the chain and discipline preservation lemmas, the
  reconstruction and sealed-reconstruction invariants, and the two-find reuse
  example, so an unproved assumption appears as `sorryAx` or as an axiom outside
  Lean's standard three. `scripts/check_cap_docs.sh` is the documentation census:
  each row names a tracked path, a literal needle and a side of the change
  (`drop` claims absent after the discipline update, `add` claims present), and
  `--control <rev>` asserts the base column while `--rev WORKTREE` asserts the
  working tree. It flattens each file before the literal search, so line wrapping
  and TeX indentation do not affect a match.
- `bench/CapNegative.lean` holds the checked negative controls: a read-only, a
  consumed and a half-share leaf cannot authorise a write, and one identifier is
  not a join pair.
- `Cap/Bytes.lean` is the reference byte heap: buffers as `List UInt8` keyed by
  `AllocId`, with `read?`, `write?`, `fill?`, `snapshot?` and `alloc`. Proved:
  `write_get`, `write_preserves_length`, `write_ne`, the 64-byte example
  (`example64_snapshot`, left sum 32, right sum 64), two readers of the right half
  each summing 64 (`right_readers_both_64`), and `snapshot_independent` (a snapshot
  is a copy). It carries no permission ledger: the guards and the budget live in
  `Cap.Ledger`, and connecting the two is the next slice. `Heap.alloc` replaces an
  existing buffer at the same identifier.
- `Cap/Code.lean` is the closed value universe: codes for `Nat`, `Bool`,
  `UInt8`, `Unit`, products, sums and lists, with `El` denoting each. There is no
  code for a reference, a function or a closure. That closure does not make every
  type isomorphic to a coded type harmless: `Unit → Nat` is bijective with
  `El .nat`, and such a function can capture an array. A bijection is an encoding
  property, not confinement.
- `Cap/Admission.lean` separates logical encoding from storage. `SafeValue T` is a
  closed `Code` and a `Bij T (El code)` with both inverse laws: logical
  encodability, not confinement. `SafeType` holds a `code` and
  `new : Array UInt8 → El code`, and `SafeType.init` applies it to a fresh
  allocation's bytes; no arbitrary `T` is stored, so an initialiser cannot hand the
  arena a closure over the protected storage. `#admit_encoding T bij` reflects the
  named declaration, checks its type is `Bij T (El c)` for a closed code, and
  audits axioms. Accepted `bench/AdmissionAccept.lean` (`Pair` encoded by
  `.prod .nat .nat`); `bench/NatThunkAdmission.lean` shows `Unit → Nat` is
  encodable by `.nat` while `retainBuffer` can capture an array — the gate accepts
  the encoding, and the storage type is what excludes it. Refused
  `bench/AdmissionReject.lean` (axiom-supported) and
  `bench/AdmissionWrongDomain.lean` (a bijection of another type).
  `bench/AdmissionParam.lean` composes bijections as functions, and
  `bench/UniverseDemo.lean` admits coded types by the identity.
- `bench/UnionFind.lean` is a hand-written union-find benchmark on `Array Nat`,
  outside the certified fragment. It compares an unshared and a shared variant at
  equal `n` and `m`; the printed figure is nanoseconds per outer iteration (two
  finds, and a union store only where one is taken), not per store, and the
  generated family's flat total does not establish an in-place timing result.
  `bench/README.md` carries the numbers, the method and the limitations.
- `scripts/emit_program.lean` is the other direction of the bridge: it defines a
  program in the model language, has `check` accept it, and emits it as Lean into
  `bench/Generated.lean`, which the bench package's `generated` target builds into
  a binary. Run `nix develop -c lake env lean scripts/emit_program.lean`, then
  `(cd bench && nix develop -c lake build generated && ./.lake/build/bin/generated)`.
  The emitted program's output agrees with the model interpreter's result. The
  emitted code is the fragment's straight-line array writes; the ownership
  operations are dropped because Lean's reference counting inserts them. The
  timing harness builds a fresh input per trial but does not verify the consuming
  write's disposition.
- The claim census is gated by `scripts/check_claims.sh`: it extracts every
  `\lean{…}` token from `paper/ownership-skeleton.tex`, requires each token to
  have a row in `docs/notes/claim-map.md` and each row to be cited by a token,
  runs `#check` for the declaration rows under `nix develop -c lake env lean`,
  checks that module rows name paths that exist, and admits runtime-primitive,
  concept and expression rows only through the classification the script carries,
  with a reason per row. `--generate` rebuilds the map from that classification
  and the checked-in copy is compared byte for byte; `--self-test` proves the
  detector by failing an orphan token, an uncited row and a nonexistent
  declaration each with its own diagnostic.
- `scripts/check_all.sh` runs the whole suite in one go — the three Lean builds,
  the axiom audit, the claim census with its self-test, the artifact and runtime
  gates when `../lean-examples` is present, and the paper build. Without the
  sibling it reports those two as skipped and prints the pinned provisioning
  commands; `--require-sibling` makes their absence an error.
- The pair projection check replays the private `setAt` and runs `projectPair` on
  its `Path.left`/`Path.right` arms:
  `(cd ../lean-examples && nix develop -c lake env bash -c 'export LEAN_PATH="../ownership/.lake/build/lib/lean:$LEAN_PATH"; lean ../ownership/scripts/check_pair_projection.lean')`.
  It asserts the recognizer accepts both arms, binds the selected/retained
  fields, the child call, the reset/reuse joins and the oset/copy branches, and
  rejects 28 token-preserving near misses (14 per arm) while the unmutated arms
  remain accepted. The model term is read off the operands; the execution
  correspondence with `Ownership.Pair.runP` is a named next step.
  Runtime evidence for the layout write path is
  `(cd ../lean-examples && nix develop -c lake exe inplace)`, and the IR gate is
  `(cd ../lean-examples && nix develop -c lake build ScidoniaTest)`. The results,
  the count accounting and the replay/backend assumptions are recorded in
  `docs/notes/OWNERSHIP_RUNTIME_EVIDENCE.md`; they are supporting measurement,
  not a refinement proof.
- The borrow-inference decision log is
  `(cd ../lean-examples && nix develop -c lake env lean -Dtrace.Compiler.inferBorrow=true ../ownership/scripts/dump_executor.lean)`.
  The pinned signatures and the probe copy's reasons are recorded in
  `docs/notes/artifacts/borrow-inference.txt`; it is a compiler decision log,
  not a linearity certificate or a pass rate.
- The runtime binding is gated by `scripts/check_runtime_binding.sh`: it runs
  the artifact gate, the sibling's IR-shape build, checks the generated C and
  runtime-header primitives for the `setAt` write, and runs the linked probe
  modes with the check off and on. The captured evidence is
  `docs/notes/artifacts/backend-binding.txt`. It binds the pinned evidence and
  observed behaviour, not the C semantics.
- `runtime-bridge/` is the compiled reproducer for the in-place context
  dependence: `(cd runtime-bridge && nix develop -c lake build)`, then
  `nix develop -c lake exe probe <mode>`; the modes and expected results are in
  its README. It requires the sibling by path and does not modify it.

## How behaviour is tested

- A behaviour contract is a page in `tests/<topic>-contract.md` (actor, Given,
  When, Then, Why) executed by the Lean fixture the page names:
  `tests/nested-contract.md` with `OwnershipTest/Recursive.lean`,
  `tests/wrong-frame-contract.md` with `OwnershipTest/WrongFrame.lean`,
  `tests/open-frame-return-contract.md` with
  `OwnershipTest/OpenFrameReturn.lean`, and
  `tests/distinct-binders-contract.md` with
  `OwnershipTest/DistinctBinders.lean`.
- `tests/recursive-frame-contract.md` (N5) with `OwnershipTest/RecursiveFrame.lean`
  is the recursive-frame contract: `checkN` accepts a `.callAt` body confined to
  the state it was handed and refuses a body that opens the suspended frame's own
  emptied array with a take-out/put-back. The refused body's exit is not what
  differs: it returns variable 3, the call's own state, exactly the handle the
  accepted body returns. What refuses it is frame isolation: the isolated context
  leaves the parent array dead, so the take-out's first requirement — that the
  array be an owned handle — fails.
  `OwnershipTest/RecursiveProof.lean` imports it alongside the other contract
  fixtures, so `lake build OwnershipTest` elaborates both guards (affirmative
  control first).
- `tests/struct-branch-contract.md` (S1/S2) is executed by the shell fixture
  `tests/struct-branch-assert.sh`, not by a `checkN` fixture, because its
  subject is the executable measurement CLI. The page provisions the pinned
  sibling checkout before the commands; the fixture itself invokes the CLI once
  from that checkout, captures its output in a `mktemp` directory removed by a
  trap, and asserts the labelled `setAt branch report:` record for the
  requested `Path` constructor. The contract is report completeness only: it
  does not establish that the labels follow from the AST, which the focused
  branch-local gate in `scripts/dump_executor.lean` checks separately.
- `OwnershipTest/CountedFamily.lean` is the parameterised one-level case study:
  for every outer slot `i < n`, leaf slot `j < n` and value `w` it proves the
  entry accounting, the protocol boundary and its accounting, the counted
  child-call contract, and the whole `counted_nested_chain` conclusion
  (`family_chain`, with `family_chain_two` its length-two instance). The bound is
  the only length fact the proof uses: the slot facts come from
  `Array.getElem?_setIfInBounds_self_of_lt` and the count equation from
  `IncomingCount_set_fill` on the all-scalar array. It imports its own heap and
  contexts rather than reusing the fixed fixtures, because the family varies the
  outer slot, the leaf slot and the value.
- Fixtures without a page (`OwnershipTest/Array.lean`,
  `OwnershipTest/Nested.lean`, `OwnershipTest/RecursiveProof.lean`,
  `OwnershipTest/PairBranchProof.lean`) are regression and artifact checks.
- `OwnershipTest/RecursiveProof.lean` imports the four contract fixtures, so
  `lake build OwnershipTest` elaborates every guard; each fixture imports only
  `Ownership.Nested` and defines its own heap, environment and context.
- Fixtures are local and deterministic: concrete `Heap`, `Env`, `Ctx` and
  `NCode` values. No network, model, clock, C executable or external service
  stands in for an owned object.
- A fixture puts the affirmative `#guard` (the accepted program) before the
  essential `#guard` (the refused program), so a refusal is not a wholesale
  rejection. Run one fixture with
  `nix develop -c bash -c 'lake build Ownership && lake env lean OwnershipTest/<Fixture>.lean'`.
- Recursive and algebraic claims are theorems, not guards: the artifacts
  (`OwnershipTest/Nested.artifact`, `OwnershipTest.RecursiveProof.artifact`, which
  now binds the body's designated write and both restored slots) and
  the countermodels (`OwnershipTest.RecursiveProof.stale_rejected`,
  `shared_rejected`, `incShared_rejected`) are kernel-checked, each negative
  paired with the same-checker positive control `oneLevel_accepted`. The exit
  rule (one open frame permits only the extracted element to return) and
  binder-distinctness refusals are asserted by their fixtures' guards, because
  they are checker policy at the client boundary rather than consequences of
  `checkN_sound`.
- The one-pair model's claims are theorems in
  `OwnershipTest/PairBranchProof.lean`: `unique_left_run`, `unique_right_run`,
  `shared_left_copy` and `shared_right_copy` bind the exact poststate, and
  `shared_rejected`/`incShared_rejected` are the same `checkP` refusals paired
  with the executable positive control `#guard (checkP ctx0 pairCodeLeft).isSome`.
  The pair model is not the emitted `setAt` AST or a backend claim.
- A proof module may define its own case heaps but imports the fixture modules
  it complements and does not restate or weaken their assumptions.

## Proof hygiene

- No `sorry`, `admit` or new axioms. `#print axioms` for the headline theorems
  lists `propext`, `Classical.choice` and `Quot.sound`; if `native_decide` were
  used, the theorem using it would be named here. `OwnershipTest/RecursiveProof.lean`
  prints the axioms for `checkN_sound`, `callAt_frame_sound` and its own artifact;
  `OwnershipTest/Array.lean` prints them for the entry invariant, its positive
  control and countermodels, the `TakeOutsOK` derivation and the recursive call's
  full contract (`callAt_frame_confined`, whose confinement half carries the
  `AnnotationsIn` premise). The derivation's
  heap/program agreement premise (`Ownership.Nested.Agrees`) is a real hypothesis,
  not a hidden assumption: `takeOutsOK_of_entryInv` and
  `checkN_sound_of_entryInv` both require it, because the checker cannot see which
  object a slot holds.
- `Ownership.Nested.ExtractionExclusive` is the model-level extraction and
  restoration disposition: every take-out and put-back target array cell is
  `Heap.Exclusive`, proved from `Inv`, `Agrees` and checker acceptance by
  `checkN_extraction_exclusive`, with the `EntryInv` entry point
  `Ownership.Entry.checkN_extraction_exclusive_of_entryInv`. It covers the
  `Ownership.Nested` write only: `OwnershipLcnf.NestedSemantics.execNested`'s own
  take-out/`setArray` stores are not claimed. The counted composition is now
  proved at its boundaries (`Ownership/CountedNested.lean`: `counted_takeOut`,
  `counted_restore`, `counted_nested_chain`), with the pair-live state's absence
  from `Accounted` kernel-checked in `OwnershipTest/CountedNested.lean`. The counted interpreter's whole trace is now related to the
  model's run by `NestedOutcome.Compat`
  (`OwnershipLcnf.execCounted_full_fragment`), so what remains outstanding is the
  emitted recursive callee (N10), a step-by-step agreement inside the pair-live
  window (`HeapCompat` is not an invariant there), and store-trace coverage of the
  extraction and restoration dispositions (Gap 4/Stage 4).
  `OwnershipTest/ExtractionExclusive.lean` instantiates the nested result on the
  depth-two path certificate and prints the axioms.
- `OwnershipLcnf.principal_supported_path` (`OwnershipLcnf/Principal.lean`) is
  the nested composed theorem: it composes `index_path_simulates_model`,
  `counted_nested_chain` and `execCounted_protocol_boundary` at one arbitrary
  level of a finite supported path, conditional on the child-call contract
  `Ownership.CountedChildCall` (N10). `OwnershipTest/Principal.lean` supplies
  every premise at the recogniser's own layout on a reified transcription of the
  captured declaration, so `OwnershipTest.principal_instance` has no
  hypotheses and each conjunct is type-ascribed; the retained-parent copy is its
  explanatory negative control. `OwnershipLcnf.principal_counted_fragment` is the
  whole-fragment companion at the same level: `execCounted` runs the whole
  `p.fragment` from the entry machine through the counted block, the child call
  and the restoration, the counted child call is consumed where the interpreter
  reaches it, the restoration's `mutate` branch is derived at the call's output
  heap, and the counted outcome is `NestedOutcome.Compat` to the model's run of
  `Path.build` (`HeapCompat` on the heaps, literal equality on the result, the
  fault and the write trace). `OwnershipTest.counted_fragment_instance` is its
  closed instance (`OwnershipTest/PrincipalCounted.lean`), with its type inferred
  from the theorem. The boundary fixtures carry the retained-parent controls; a
  T1-specific `HeapCompat` non-vacuity control is not a declaration in this
  revision. The two fixtures are separate modules because one module elaborating
  both together exhausted memory.
  `OwnershipLcnf.NestedLayout` constrains
  eighteen read binders (slots `0`–`17`): the emitted index decrement acts on
  the index binder itself, the recognizer reads `p.indexDec = p.index`, and the
  layout constrains no separate slot for it — so a fixture's `assign` value for
  `indexDec` is unconstrained and unused.
- The heap and the checker are models: `Ownership/Heap.lean` says so
  explicitly. `Ownership/`'s theorems are statements about those models.
  `OwnershipLcnf/Semantics.lean` adds the AST link: `execAST` executes the
  operation trace the projection walk emitted for the declaration and returns
  nothing unless the declaration decodes to the expected prefix, so
  `execAST_recognized` makes the recognition hypothesis load-bearing;
  `prefix_simulates_model` (fragment level) and `project_sound` (over the
  actual declaration) relate the executed prefix's `PrefixOutcome` — heap,
  write result binder, returned handle, target, disposition, fault, trace — to
  `Ownership.run (p.toModel assign)`; `projected_check` is the checker
  acceptance; `recognized_write_in_place` is the in-place result for arbitrary
  in-bounds index and replacement from `EntryInv`, with
  `initializer_prefix_in_place` and `nonzero_prefix_in_place` as corollaries and
  `designated_write_in_place`/`initializer_designated_write_in_place` as the
  model-level forms. `OwnershipLcnf/NoAbort.lean` names the abort property:
  `prefix_abort_impossible` proves the recognized prefix never reports the
  `.notExclusive` check fault, under `EntryInv` and the recognizer. That is the
  emitted semantics; the runtime `lean_is_exclusive` correspondence is contract
  A6 and is not proved for the linked executable. All of that is relative to the primitive, constructor-layout
  and call-signature contracts A1–A12 in that module's header and to the layout
  and initial-state agreement premises. Those theorems stop at the designated
  write's return; the index's own `inc`/`dec` pair and the continuation with its
  recursive call are named non-claims, and nothing there relates the replay to
  the backend input, to physical counted references, or to physical memory.
- `OwnershipLcnf/NestedSemantics.lean` adds the same link for the recognized
  nested prefix: `execNested` interprets the recognizer's trace, and
  `index_prefix_simulates_model` consumes `projectNested` to relate the executed
  prefix to `Ownership.Nested.runN` of the take-out/call/put-back model term,
  over the N1–N12 contracts in its header. `OwnershipTest/NestedEmitted.lean`
  instantiates it with a changed leaf, a restored child slot, an untouched
  sibling, outside-footprint preservation and a re-established `EntryInv`. The
  child-call contract (`ChildContract`) is a hypothesis and the emitted
  recursive callee's body is not captured; that link remains an outstanding
  obligation.
- `Ownership/Path.lean` derives the agreement and annotation premises from a
  path instead of per-client facts: `MutableFootprint.trans`,
  `ClientReachable.trans` and `AnnotationsIn.trans` are proved, `build` reads
  the nested program off a level chain, `agrees_of_path` composes `Agrees`
  through take-out/call/put-back, and `annotationsIn_of_path` lifts every
  annotation into the root's footprint. `OwnershipTest/PathAgreement.lean` is
  the certificate: it obtains `Agrees` and `AnnotationsIn` from those theorems
  and feeds them to `takeOutsOK_of_entryInv` and `callAt_frame_confined`. The
  emitted machine-level `NestedAgrees` still needs the recognizer's operand
  identities and the reified machine fields.
- `Ownership/PathSafety.lean` turns the path theory into depth-independent
  results: `path_run_safe` covers an arbitrary level list through
  `checkN_sound_of_entryInv`, `level_call_confined` is `callAt_frame_confined`
  at a level of the path, and `client_retention`/`clientSeparated_preserved`
  keep client-reachable references outside the footprint (the latter with the
  three explicit non-growth facts, discharged by the depth-three certificate).
  It does not prove arbitrary runtime recursion, the emitted callee or
  continuation, or physical reference counts; callbacks are outside the
  fragment.
- `Ownership/PathConsolidation.lean` consolidates the premises those results
  take: `checkNF_build` derives the built program's checker acceptance and its
  final context, `childConfined_of_path` derives `ChildConfined` at every level,
  `agrees_extract_restore` derives the extract/restore leaf's agreement,
  `slotRefs_runN`/`writesIn_build`/`footprint_contained` derive the post-state
  footprint's non-growth from the run's write account, and
  `observation_retention`/`callback_retention` carry client retention to the
  interface's produced values. The remaining supplied premises are the leaf
  (emitted callee) contract, the heap-shape facts `Acyclic` and `Closed`, and the
  interface's own observation separation. `OwnershipTest/PathConsolidation.lean`
  instantiates every derivation on the depth-three path.
- The finite level list is a **named, narrowed** row, not a completed
  connection: `calls_build`/`extractions_build` bound the built program's call
  structure by the list's length and `callBody_build` shows each call's embedded
  body is the remaining list, so the model's recursion is syntactic descent.
  The emitted `setAt` recursive callee's body is not captured (N10) and the
  executor's call rule is not established, so `Ownership/PathConsolidation.lean`'s
  section on the finite list states the boundary and what a connection would
  need; nothing there is an executor certificate, and the depth of recursion the
  model covers is the program's own syntax, not data-dependent runtime depth.
- `Ownership/CountedPair.lean` accounts for the take-out pair: the parent and
  child handles transfer into the fresh pair (no new component owners), the two
  projections increment, and freeing the unique pair releases both edges, so the
  boundary counts equal the entry counts (`pair_accounting`,
  `pair_traffic_neutral`, `boundary_correspondence`). The no-free,
  retained-alias and shared-entry controls are in `OwnershipTest/CountedPair.lean`;
  the free is the restricted one-cell form and persistence/address identity are
  named limits.
- `Ownership/PutBack.lean` gives restoration both dispositions and derives the
  exclusive one: `putBack_exclusive_of_wellFormed` takes the counted-pair
  boundary and the child-call boundary (`ChildCall.parent` via
  `callAt_frame_confined`), with functional restoration and count preservation
  separate; the copy branch and the retained-reference/footprint controls are in
  the fixture. N11 cites it; the emitted call boundary and `child_rc`/
  `child_persistent` remain premises.
- `OwnershipLcnf/PathRecursion.lean` discharges `ChildContract` for a finite
  level list by induction: the tail contract is the hypothesis, the leaf the
  base, and `index_path_simulates_model` takes no arbitrary `ChildContract`. The
  induction derives `ChildContract` only: `Ownership.CountedChildCall`'s `edges`
  field (the call's `EdgePreserved` effect on the caller's heap) is an explicit
  premise of every theorem that consumes it at a leaf body, and the caller's
  accounting at the body's return is *derived* from that effect and the caller's
  accounting at the call (`CountedChildCall.accounted_of`); the instance supplies
  the effect from the leaf rewrite (`B_edges`). A body that is itself the counted
  chain has a *net* edge effect (`Ownership.counted_nested_chain_edges`), but
  composing it at a second level is not usable: the isolated-accounting premise is
  inconsistent (`OwnershipTest/IsolatedAccounting.lean`), so
  `counted_nested_chain_two_levels` is recorded as a regression, not a result. The leaf contract and N10
  remain; the module records that the model's flat environment cannot express the
  emitted per-invocation path re-projection.
- `OwnershipLcnf/RuntimeModel.lean` is the concrete runtime state for the
  `setAt` write: counts, persistence, fields, the exclusivity predicate, a
  guarded allocator, the check's ok/abort outcomes and both array-set
  dispositions, with a structural correspondence to `Ownership.Heap`.
  `checkExclusive_no_abort`/`setAt_inPlace_of_entryInv` derive the unreachable
  abort and the in-place write; shared, persistent and dirty-cursor controls are
  in the fixture. Fidelity to `lean_is_exclusive`/`lean_array_uset` (A6/A8), A10,
  address identity and free/cascade remain the residual trust; no
  linked-executable claim.

- `Ownership/CompleteAccounting.lean` is the complete ownership and
  reference-count accounting relation: `Accounted support H env c` conjoins
  `Inv`, a duplicate-free, sound, complete and reference-bound enumeration of the
  owning variables, the live-cell domain, and the count equation
  `H.rc r = IncomingCount H r + EnvOwnerCount c support r`. The initializer
  establishes it (`Accounted.initCtx`); the retained predicates are corollaries
  (`Accounted.ownersAccounted`, `Accounted.countFidelity`); and the count-one
  fact is derived rather than read off the integer
  (`Accounted.count_one_dichotomy`, `Accounted.at_most_one_owner`,
  `Accounted.incoming_le_one`). The context effects preserve it with named
  premises (`Accounted.setDead`, `Accounted.setScalar`, `Accounted.move`,
  `Accounted.decOne`), as do the take-out, the put-back and the in-place scalar
  store at the interpreter's own post-states (`Accounted.takeOut`,
  `Accounted.putBack`, `Accounted.setFieldsScalar`, `Accounted.setArrInPlace`),
  on the edge-count lemmas `IncomingCount_set_*`. Each refused configuration is
  paired with a proved `Inv` at the same state (`alias_rejected`,
  `inc_rejected`, `bindAlone_rejected`, `outOfRange_rejected`,
  `scalarOverwrite_rejected`), and `decTwo_rejected` is a schema over accounted
  pre-states. `Ownership.Supported` is the context-indexed counted fragment:
  every continuation is indexed at the context the checker's matching rule
  threads, every constructor carries the checker's own rule there, and the
  accounting certificates the checker cannot see (a fresh alias target, a fresh
  scalar-`.let` target) are further premises. Apart from those certificates, the
  fragment's two restrictions on the checker's accepted set are that `.inc` does
  not occur (`inc_rejected`) and that every `.dec` is `.dec x 1`
  (`decTwo_rejected`), so the fragment is check acceptance restricted to the
  counted constructors:
  `OwnershipLcnf.Prefix.toModel_supported` places the certified flat model in
  it. The take-out's no-second-edge premise is no longer
  client-supplied: `Accounted.incoming_eq_one_of_slot` derives it from the
  relation, the array's slot and the checker's count-one condition, and
  `Accounted.takeOutOfSlot` states that step without it.
  `OwnershipTest/CompleteAccounting.lean` carries the computable guards, the
  four `Supported` controls (affirmative first) and the axiom prints;
  `scripts/check_axioms.lean` audits every declaration of the new module.

- `Ownership/Fractional.lean` reads that accounting as a fractional permission:
  `Share n = 1/n`, `fractional_accounting` states that the owning variables and
  incoming edges together hold the whole permission, `unique_whole_permission`
  identifies uniqueness with the whole permission in one holder, and `shared_share`
  is the graded case of `n` holders at `1/n`. This is the correspondence to
  fractional-uniqueness type systems, whose fractions are our multiplicities; their
  grades are erased at runtime, and so are ours — the model's counts are read from
  the heap, and a token argument in `Prop` would be erased too, so it could justify
  the compiler's decision but not replace the check that takes it.

- `Ownership/CountedNested.lean` joins the counted protocol to the complete
  accounting. `HeapCompat Hc Ha` is the boundary relation: the two heaps agree on
  every cell and the counted cursor is no lower, with
  `HeapCompat.eq_of_cursor_eq` as the control that the cursor is the only slack;
  `Accounted.of_compat` carries the relation across it, using
  `HeapCompat.IncomingCount` (the extra cursor range holds no cell, by
  `Accounted.domain`). `EdgePreserved Hin Hout` is the *effect* a call must have
  for the caller's accounting to survive: equal incoming-edge counts, a
  non-decreasing cursor, and no new cells; `EdgePreserved.of_compat` reads it off
  a `HeapCompat` only together with the input heap's live-cell domain, which
  `HeapCompat` alone does not imply. `counted_takeOut` lands the entry at the
  protocol boundary with the fresh-name side conditions *derived*, `restorationBoundary_of_accounted`
  derives the boundary's cells, counts, persistence and the entry's distinctness
  from accounting, `CountedChildCall` adds exactly one field to the child-call
  contract — the call's edge effect `EdgePreserved Hin Hout` — and
  `counted_restore` derives the mutate branch and carries the accounting there,
  while `accounted_of_edges` derives the caller's `Accounted` at the body's
  return from its accounting at the call (so no post-call accounting is
  supplied), and `counted_nested_chain` composes the three with the model's own
  `runN` of the
  take-out/call/restore term related by `HeapCompat`. `run_compat`/`runN_compat`
  relate the model language's runs at two `HeapCompat` heaps **for copy-free
  runs**: `Code.setArr`'s copy branch allocates at each heap's own cursor, so the
  lemmas take the premise that every recorded write flag is `true` (which the
  child call's `writes_exclusive` supplies). The chain is not edge-preserving
  step by step — the take-out lowers the extracted child's incoming count by one
  and the restoration raises it by one — but its **net** run is:
  `counted_nested_chain_edges` concludes `EdgePreserved H Hf` between the entry
  and `counted_nested_chain`'s restored counted heap (entry → boundary by
  `counted_takeOut` and `HeapCompat.IncomingCount_of_dom`, boundary → call
  output by the child's `edges`, call output → final by the restoration's slot
  fill), and `OwnershipTest/CountedFamily.lean` instantiates it as
  `family_chain_edges` with `IncomingCount_fam_final_one` reading the identity
  off at the extracted child. That net effect stands on its own.
  Composing it at a second level is not claimed: the inner call's isolated
  accounting would drop the suspended parent's owning root while its count-one cell
  remains in the heap, so the two-level statement's premise is inconsistent.
  `OwnershipTest/IsolatedAccounting.lean` proves the general impossibility
  (`isolated_accounting_impossible`) and instantiates it on the outer entry and the
  isolated assumption (`two_level_isolated_entry_impossible`); kernel acceptance of
  the implication therefore says nothing about an instance, and the composition is
  withdrawn. The child call stays contractual and
  the emitted callee is not captured (N10); the mid-pair state is not `Accounted`
  and its refusal is proved, so the relation is a boundary relation rather than an
  every-instruction one. `OwnershipTest/CountedNested.lean` carries the boundary
  guards, the positive restoration and the counted copy-branch control, and prints
  the axioms.

- `OwnershipLcnf/CountedTrace.lean` reads the recognised trace's counted
  operations off the recognizer (`countedOp`, `countedOf_fragment`,
  `countedPrefix_fragment`) and defines the counted interpreter `execCounted`,
  whose five counted clauses run the captured take-out, the two component
  increments, the pair's restricted decrement and the derived restoration.
  `execCounted_protocol_boundary` states the counted block's boundary: through
  the pair's release the counted heap is `CountedPair.protocol`'s, it is
  `HeapCompat` to the model's take-out heap (reusing
  `Ownership.PathConsolidation.protocol_cells`), and every non-heap machine field
  agrees with `execNested`'s. It also derives the nested correspondence's two
  exclusivity premises from accounting (`childContract_of_accounted`,
  `index_fragment_simulates_model_of_accounted`,
  `index_prefix_simulates_model_of_accounted`), leaving the originals unchanged.
  The counted interpreter's whole trace is proved
  (`execCounted_full_fragment`): the fragment splits at the pair's release
  (`countedPrefix` is the release-terminated span, `countedSuffix` the rest, and
  `fragment_decomp` the split, so the split is the recognised shape's and not a
  numeric cutoff), the counted block reaches `execCounted_protocol_boundary`'s
  state, and the post-release span runs the child assertion, the call at that
  state (with the caller's accounting at the body's return derived from the
  call's `EdgePreserved` effect), the restoration at the call's output heap and the return
  (`execCounted_suffix`). The entry point is `execCountedAST`, so the recogniser's
  verdict is spent by the theorem, and the counted outcome is
  `NestedOutcome.Compat` to the model's run: `HeapCompat` on the heaps and literal
  equality on the result, the fault and the write trace. No step-by-step agreement
  between `execCounted` and `execNested` inside the pair-live window is claimed
  (`HeapCompat` is not an invariant there, and between the take-out and the
  release the counted heap carries the pair), and the counted composition's own
  model-level statement is `Ownership.counted_nested_chain`.

- `Ownership/Preservation.lean` is preservation through accepted execution.
  `Ownership.supported_run` takes a `Supported` program, an `Accounted` state and
  the supplied store-slot premise `StoreSlots`, and concludes checker acceptance
  (`supported_check`), the fault-free run, exclusively flagged writes, the
  relation at the interpreter's final state at the support the step arithmetic
  determines (`resultSupport`), and `AccountedAlong` — the relation at every
  state the run reaches, with each array store reached at an exclusive target
  (`supported_store_exclusive`). `StoreSlots` is the one fact neither a checker
  rule nor any component of `Inv` can see, since no context records what a cell's
  slot holds; it is discharged at the initializer (`storeSlots_init`) and its
  absence is refuted (`nonScalarStore_rejected`). `AccountedEntry` packages
  `Accounted` with `EntryInv` for the initializer (`Entry.initAccounted`) without
  claiming either implies the other: `aliasEntryInv` is an `EntryInv` state no
  support accounts and `accountedNotEntryInv` an accounted state with no
  `EntryInv`. `Runner.store_exclusive` instantiates the measured write.
  `OwnershipTest/Preservation.lean` carries the affirmative-then-negative
  computable guards, both refusal theorems with their positive controls, and the
  axiom prints.
