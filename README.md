# Ownership

Lean 4 research on the ownership and reference-counting core of the Scidonia
compiler work.

## What we are doing

Lean's runtime updates an object in place when its reference count is one. The
broader goal is to show that a suitable source-level type discipline can
guarantee that behaviour for the structured updates we care about, as the
program is lowered to LCNF, without adding linear types to Lean's kernel.

This repository isolates the ownership/RC core of that goal:

- `Ownership/Pair.lean` models the two-field `Path.left`/`Path.right` update.
  The exclusive branch reuses the pair cell in place; the shared branch copies
  it, with the old pair's count dropping for the consumed handle and the
  retained sibling's count increasing for the new pair's reference.
- `Ownership/Nested.lean` models the recursive ownership frame used by the
  structured `takeOut` path, including the one-open-frame return rule and
  distinct take-out binders as checker policy.
- `OwnershipLcnf/` recognizes the scalar-array write prefix in the replayed
  `execP` LCNF — branch identity by constructor, primitive arities, exact
  argument identities — and executes the recognized code itself: `execAST` runs
  the operation trace the recognizer walked for the declaration and refuses
  anything that does not decode to the expected prefix, so the correspondence
  theorem is about the actual AST and uses its recognition hypothesis.
- `scripts/dump_executor.lean` replays the impure LCNF that Lean emits for
  `setAt`, inspects the branch-local alternatives, and reports the selected and
  retained fields and the reuse/copy disposition. The report is emitted only
  after a focused gate accepts both real alternatives and rejects
  token-preserving near misses.
- `tests/` contains the behavior contracts for the recursive and branch-report
  routes; `OwnershipTest/` contains the executable fixtures, countermodels and
  kernel-checked proof modules.

The current result is a model-level certificate plus a proved connection from
the replayed LCNF to it, for the pinned scalar-array update. `OwnershipLcnf`
recognizes the `execP` `PTree.set` alternative, executes the recognized code,
and proves — under the named primitive and backend/runtime contracts, with the
write's index and replacement derived through the projection and box chain from
the node's reified fields — that an in-bounds designated update is fault-free,
selects the in-place branch, and leaves the target address and returned handle
the root, for arbitrary index and replacement, with a nonzero value-changing
case. A reified transcription of the captured declaration has its recognition
and checker acceptance checked by the kernel, and
`scripts/check_projection.lean` exercises the recognizer on the real
declaration, rejecting eleven token-preserving near misses. This is not a compiler
proof: the certified prefix stops at the designated write's return, and the
continuation, the recursive `execP` call, the source-to-target correspondence,
the replay-to-backend identity and the physical runtime are separate claims in
`PLAN.md`.

## Building

The Lean version is pinned by `lean-toolchain` and provided by the Nix flake.

```sh
nix develop -c lake build Ownership
nix develop -c lake build OwnershipTest
nix develop -c lake build OwnershipLcnf
```

`OwnershipTest` builds the executable fixtures and proof modules; the full
testing policy is in `AGENTS.md`.

## Contracts and the sibling checkout

The behavior contracts and their commands are in `tests/`. The branch-report
contracts require a pinned `../lean-examples` checkout; the page
`tests/struct-branch-contract.md` contains the checkout/setup step and the exact
commands. The report route is report completeness only; the focused gate in
`scripts/dump_executor.lean` checks the replayed AST's branch relations
separately.

## Layout

| Path | Contents |
|---|---|
| `Ownership/` | Lean library: heap/code, recursive ownership frames, one-pair model |
| `OwnershipTest/` | Executable fixtures, countermodels and proof modules |
| `OwnershipLcnf/` | Recognizer and AST execution of the pinned `execP` write prefix, and its correspondence to the model |
| `scripts/` | Measurement CLI over the replayed impure LCNF |
| `tests/` | Behavior contracts and sibling-checkout setup |
| `docs/` | Steering notes and captured LCNF artifacts |
| `PLAN.md` | Research plan, claims and non-claims |
| `AGENTS.md` | Build/test policy and repository notes |
| `LICENSE`, `NOTICE` | Apache-2.0 and copyright |

## What is not claimed

- The `Pair` and `Nested` models are not the emitted LCNF AST or a backend
  claim; the link to the emitted code is measured in the CLI, not proved.
- The `OwnershipLcnf` link is proved for one pinned declaration's
  `PTree.set` alternative, not for an arbitrary emitted program. It stops at
  the designated write's return: the index's own `inc`/`dec` pair, the
  continuation and the recursive `execP` call are named non-claims. What the
  proofs call an array is the modelled heap, and the model's count of one is
  not a physical reference count; the replay is not identified with the backend
  input, and none of this says a compiled program mutates memory.
- The branch-report route does not establish the AST labels; the separate
  branch-local gate does, and no claim is made about the compiled backend.
- The heap's `dec` is a count model; freeing and cascade behaviour remain in the
  sibling runtime model.
- Source interpreter correctness, source-to-target correspondence and the C
  backend are later, separate claims.
- No `sorry`, `admit` or new axioms; the proof hygiene policy is in `AGENTS.md`.

## License

Apache License, Version 2.0. See `LICENSE`. Copyright 2026 Scidonia Limited;
see `NOTICE`.
