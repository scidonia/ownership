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
