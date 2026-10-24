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
- `scripts/dump_executor.lean` replays the impure LCNF that Lean emits for
  `setAt`, inspects the branch-local alternatives, and reports the selected and
  retained fields and the reuse/copy disposition. The report is emitted only
  after a focused gate accepts both real alternatives and rejects
  token-preserving near misses.
- `tests/` contains the behavior contracts for the recursive and branch-report
  routes; `OwnershipTest/` contains the executable fixtures, countermodels and
  kernel-checked proof modules.

The current result is a model-level certificate plus a branch-local survey of
the replayed LCNF. The emitted-AST certificate, the source-to-target
correspondence, the source interpreter's functional correctness and the C
backend are separate claims in `PLAN.md`; they are not made here.

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
| `OwnershipLcnf/` | Partial projection from the replayed `execP` branch into the model |
| `scripts/` | Measurement CLI over the replayed impure LCNF |
| `tests/` | Behavior contracts and sibling-checkout setup |
| `docs/` | Steering notes and captured LCNF artifacts |
| `PLAN.md` | Research plan, claims and non-claims |
| `AGENTS.md` | Build/test policy and repository notes |
| `LICENSE`, `NOTICE` | Apache-2.0 and copyright |

## What is not claimed

- The `Pair` and `Nested` models are not the emitted LCNF AST or a backend
  claim; the link to the emitted code is measured in the CLI, not proved.
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
