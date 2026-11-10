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
