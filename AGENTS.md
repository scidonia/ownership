# Repository working notes

## Build and checks

- The Lean toolchain comes from the nix dev shell. From the repository root:
  `nix develop -c lake build Ownership` builds the development,
  `nix develop -c lake build OwnershipTest` builds the tests, and
  `nix develop -c lake build OwnershipLcnf` builds the LCNF projection target.
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
  loan's lifetime (`hasDescendant_sound`, `endLoan_none_of_descendant`). It has no
  heap and no capability ledger, and the loans are not yet consulted by
  `Cap.Ledger`'s guards; a live inner reborrow is still not integrated.
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
  `splitFractionOwner?`) is not freshness-checked itself; the deep checker is. The loan
  threading of the session and the freshness-preserving disposal proof are next.
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
- `Cap/UFRun.lean` is the union-find client of the checked world: reads are
  observations of the pure backends (`readParent`, `find` with fuel), and `union`
  issues writes through `World.writeChecked`, so `union_wf` preserves the world
  invariant. The concrete trace (1 under 0, 3 under 2, 2 under 0) is accepted
  (`ufTrace_ok`), its final world is well formed (`ufTrace_wf`), its backend
  parent array is the functional model's `[0,0,0,2]` (`ufTrace_backend`), and
  every pair of the four nodes is `Same` in the functional relation
  (`ufTrace_partition`). No path compression in the client, no read discipline:
  the checked route governs writes only.
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
  `free?_legal`, `free?_removes_owner`, `free?_none_after_free`, the entitlement
  and loan refusals, and concrete examples. It is not yet wired into
  `Cap.Unified`, and names are invalidated by owner removal rather than by arena
  generations.
- `Cap/World.lean` is the world of owners, mutable backends and loans: the heap
  map is a function from allocations to `Backend`, the world also carries a
  `LoanCtx` (seeded everywhere with `LoanCtx.rootOnly`: one live root lifetime,
  no loans), `World.Rel` combines `Ctx.Realizes` with the per-owner buffer
  length, `write?` takes the owner's `Writable` guard as a
  proof and replaces the backend, and `freeWith?` dispatches through the context's
  disposal check and clears the backend. `write_rel` and `freeWith_rel` preserve the
  relation. It is a pure world, not the interpreter, an FFI path or a concurrency
  claim.
- `Cap/Suspend.lean` is leaf suspension and restoration: `Owner.suspendLeaf?`
  retires an active leaf and `Owner.resumeLeaf?` reactivates a retired one, with
  the find/replace/ids/budget characterisations, the budget preservation (only
  `.consumed` zeroes), the round trip (`resumeLeaf?_of_suspendLeaf?`), and the
  guard facts: a suspended leaf is not writable (`suspendLeaf?_not_writable`) and
  restoration returns the original writability (`resumeLeaf?_writable`).
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
  certificate and `p64_snapshot` is its result. `World` is still public pure model data; the
  sealed runtime boundary, the complete invariant and the full command set remain
  the runner handoff's P0 work.
- `Cap/Indexed.lean` is the world-indexed computation type: `Ix pre α post` runs
  from `pre` and ends in `post a`; `ret` and `bind` thread the worlds, with the
  continuation's precondition forced to be the first computation's post-world;
  `writeIx` carries the ledger guard and the backend write, and its post-index is
  the world the guarded write produces. `prog_run` computes a two-write program at
  elaboration` and `prog_sound` shows `checkWorld` reaches the same post-world.
  Indices are ordinary `World` values; there is no hidden-index elaborator, so
  symbolic programs are not inferred.
- `Cap/Unified.lean` is the first slice of the review's R1: a value-carrying
  `UCmd` (`write`, `splitAt`, `splitFraction`, `join`, `free`, `alloc`,
  `beginLoan`, `endLoan`, `nop`), `World.writeChecked`
  which checks the ledger's `writableB` and performs the backend write,
  `World.splitAtChecked` for spatial splits, `World.freeChecked` for disposal
  through the recorded capability, `World.allocChecked` for allocation with
  fresh identifiers, and `checkWorld` as checker and interpreter at once.
  `writeChecked_sound` names the owner, guard, backend and replacement;
  `writeChecked_wf`, `World.splitAtChecked_wf`, `World.freeChecked_wf`,
  `World.allocChecked_wf` and `checkWorld_wf` preserve the world invariant
  (`World.WellFormed`) through every command, and `checkWorld_rel` derives
  `World.Rel` from it; the concrete 64-byte world is well formed (`uWorld_wf`),
  the run through this route snapshots 32 ones then 32 twos (`uRun_snapshot`),
  and its world remains related (`uProgram_rel`). `uLifecycle` runs
  alloc/write/split/write/free through this route: it is accepted
  (`uLifecycle_ok`), its final world is well formed (`uLifecycle_wf`), and the
  untouched pre-existing backend reads back its initial zeros
  (`uLifecycle_snapshot`). Joins, loans and a snapshot command are not yet in
  this language; they remain in the owner layer.
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
- `Cap/Nested.lean` is the two-level borrow model: `Lender` with active/suspended
  states, `beginBorrow` suspending the lender and issuing a borrower, `endBorrow`
  restoring the suspended lender without returning the borrower, and
  `Lender.canWrite` combining activity with `Policy.Writable`. Proved:
  `begin_suspends`, `end_restores`, `suspended_not_writable` and `nested_begin`
  (a nested borrow restores to the parent state). Footprints and ledger capability
  states are not threaded, and the full frame rule with suspended obligations is not
  proved.
- `Cap/Policy.lean` combines the owner write guard with loan liveness:
  `Policy.Writable` is the owner guard and `LoanCtx.live` of the named lifetime;
  `writable_owner`/`writable_live` project, `not_writable_of_dead` refuses a dead
  lifetime, `live_of_find` and `live_false_of_endLoan` connect liveness to lookups
  and to ending a loan, and `not_writable_after_endLoan` is the policy corollary.
  It is a predicate combination, not an executable checker, and the session does
  not thread a loan context yet.
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
- `bench/CapNegative.lean` holds the checked negative controls: a read-only, a
  consumed and a half-share leaf cannot authorise a write, and one identifier is
  not a join pair.
- `Cap/Session.lean` is the single-owner end-to-end state: an owner, the reference
  heap and the denominator. `Session.Realizes` is the owner's coverage;
  `create_realizes`, `splitAt_realizes` and `fill_realizes` preserve it. `fill?`
  takes the ledger's `Writable` guard for every byte it writes. The 64-byte
  acceptance run is concrete: a spatial split tree over `[0,32)` and `[32,64)`,
  fills of 1 and 2 through the guards, and `exampleRun_snapshot` proves the
  snapshot is 32 ones followed by 32 twos. The run builds the split tree by hand;
  the dynamic split transitions are covered by the `Cap.Ledger` theorems. The
  session now carries a `LoanCtx`; `fillGuarded?` requires `Policy.Writable` for
  every byte (owner guard plus a live lifetime) and preserves `Realizes`.
  `Session.free?` removes the allocation only when no loan is outstanding
  (`free_refused_of_loan`), and succeeds when the buffer is present
  (`free_succeeds_of_no_loan`); `Heap.free?` removes the buffer.
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
