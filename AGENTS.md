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

## How behaviour is tested

- A behaviour contract is a page in `tests/<topic>-contract.md` (actor, Given,
  When, Then, Why) executed by the Lean fixture the page names:
  `tests/nested-contract.md` with `OwnershipTest/Recursive.lean`,
  `tests/wrong-frame-contract.md` with `OwnershipTest/WrongFrame.lean`,
  `tests/open-frame-return-contract.md` with
  `OwnershipTest/OpenFrameReturn.lean`, and
  `tests/distinct-binders-contract.md` with
  `OwnershipTest/DistinctBinders.lean`.
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
  (`OwnershipTest/Nested.artifact`, `OwnershipTest.RecursiveProof.artifact`) and
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
  used, the theorem using it would be named here.
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
  model-level forms. All of that is relative to the primitive, constructor-layout
  and call-signature contracts A1–A12 in that module's header and to the layout
  and initial-state agreement premises. Those theorems stop at the designated
  write's return; the index's own `inc`/`dec` pair and the continuation with its
  recursive call are named non-claims, and nothing there relates the replay to
  the backend input, to physical counted references, or to physical memory.
