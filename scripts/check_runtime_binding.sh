#!/usr/bin/env bash
# Bind the certified setAt write to the pinned toolchain's backend evidence and
# to the linked probe's observed behaviour.
#
# It does not prove the C runtime's semantics. It checks that the pinned
# revision, clean tree, artifact captures, IR-shape gate, generated C and runtime
# header carry the primitives the runtime model names, and that the linked probe
# behaves as the model predicts with the exclusivity check on and off.
set -euo pipefail
cd "$(dirname "$0")/.."

sibling=${1:-"../lean-examples"}

./scripts/check_artifacts.sh "$sibling"

# The backend-input shape gate: ScidoniaTest's IRShape reads the post-RC IR of
# setAt/execP and asserts the constructs and order.
(cd "$sibling" && nix develop -c lake build ScidoniaTest >/dev/null)

# The generated C for the path write, and the runtime header it calls.
layout_c="$sibling/.lake/build/ir/Scidonia/FracPerm/StateVar/Layout5.c"
[ -f "$layout_c" ] || { echo "missing $layout_c" >&2; exit 1; }
for pat in 'setAt___redArg' 'lean_array_fget' 'lean_array_fset' 'lean_is_exclusive'; do
  grep -q "$pat" "$layout_c" || { echo "Layout5.c lacks $pat" >&2; exit 1; }
done

prefix=$(nix develop -c lean --print-prefix | tail -n 1)
header="$prefix/include/lean/lean.h"
[ -f "$header" ] || { echo "missing $header" >&2; exit 1; }
for pat in 'lean_is_exclusive' 'lean_array_uset' 'lean_array_set_core'; do
  grep -q "$pat" "$header" || { echo "lean.h lacks $pat" >&2; exit 1; }
done

# The linked probe: the certified shapes are in place, the closed pure-array
# controls copy (and abort when the check is armed).
(cd runtime-bridge && nix develop -c lake build >/dev/null)

expect() {
  local mode=$1 check=$2 want=$3
  local out status
  set +e
  out=$(cd runtime-bridge && SCIDONIA_CHECK_INPLACE="$check" nix develop -c lake exe probe "$mode" 2>&1)
  status=$?
  set -e
  if [ "$status" != "$want" ]; then
    echo "probe $mode (check=$check): exit $status, expected $want" >&2
    printf '%s\n' "$out" >&2
    exit 1
  fi
  printf 'probe %s check=%s exit=%s\n' "$mode" "$check" "$status"
}

# The armed copy controls must fail specifically by the in-place exclusivity
# abort, not by an ordinary observation mismatch (which exits 2).
expect_abort() {
  local mode=$1
  local out status
  set +e
  out=$(cd runtime-bridge && SCIDONIA_CHECK_INPLACE=1 nix develop -c lake exe probe "$mode" 2>&1)
  status=$?
  set -e
  if [ "$status" != "1" ]; then
    echo "probe $mode (check=1): exit $status, expected the exclusivity abort (1)" >&2
    printf '%s\n' "$out" >&2
    exit 1
  fi
  case "$out" in
    *"not exclusively owned"*|*"in-place check"*) ;;
    *)
      echo "probe $mode (check=1): exit 1 without the exclusivity abort diagnostic" >&2
      printf '%s\n' "$out" >&2
      exit 1
      ;;
  esac
  printf 'probe %s check=1 exit=1 abort=exclusive\n' "$mode"
}

expect separate-exact 0 0
expect separate-spare 0 0
expect inline-io 0 0
expect sealed 0 0
expect inline-exact 0 0
expect closed-case 0 0
expect differential 0 0
expect separate-exact 1 0
expect inline-io 1 0
expect sealed 1 0
expect_abort inline-exact
expect_abort closed-case

echo "runtime binding: pinned artifacts, IR shapes, C/runtime primitives and probe modes agree"
