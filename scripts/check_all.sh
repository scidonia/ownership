#!/usr/bin/env bash
#
# One entry point for the whole check suite.
#
#   bash scripts/check_all.sh                 run everything the checkout allows
#   bash scripts/check_all.sh --require-sibling
#                                             also fail if ../lean-examples is absent
#
# Sibling-free: the three Lean builds, the axiom audit, the claim census and its
# negative controls, and the paper build.
# Needs ../lean-examples at the pinned revision: the artifact gate and the runtime
# binding gate. Without the sibling those two are reported as skipped, and their
# provisioning command is printed.
set -uo pipefail
cd "$(dirname "$0")/.."

require_sibling=0
[ "${1:-}" = "--require-sibling" ] && require_sibling=1

fail=0
run() {
  echo "== $* =="
  if ! "$@"; then
    echo "FAILED: $*" >&2
    fail=1
  fi
}

run nix develop -c lake build Ownership
run nix develop -c lake build OwnershipLcnf
run nix develop -c lake build OwnershipTest
run nix develop -c lake env lean scripts/check_axioms.lean
run nix develop -c bash scripts/check_claims.sh
run nix develop -c bash scripts/check_claims.sh --self-test

if [ -d ../lean-examples ]; then
  run nix develop -c bash scripts/check_artifacts.sh
  run nix develop -c bash scripts/check_runtime_binding.sh
else
  echo "== sibling-dependent gates =="
  echo "SKIPPED: scripts/check_artifacts.sh and scripts/check_runtime_binding.sh need" >&2
  echo "  ../lean-examples at 66e64334a1c968d829903b8aec8d22f7e3b9fd3f. Provision it with:" >&2
  echo "  git clone git@github.com:scidonia/lean-examples.git ../lean-examples" >&2
  echo "  git -C ../lean-examples checkout 66e64334a1c968d829903b8aec8d22f7e3b9fd3f" >&2
  [ "$require_sibling" -eq 1 ] && fail=1
fi

echo "== paper =="
if ! ( cd paper && latexmk -pdf -interaction=nonstopmode ownership-skeleton.tex ); then
  echo "FAILED: paper build" >&2
  fail=1
fi

if [ "$fail" -ne 0 ]; then
  echo "check_all: FAILED" >&2
  exit 1
fi
echo "check_all: OK"
