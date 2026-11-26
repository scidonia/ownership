#!/usr/bin/env bash
#
# Build llvm-bridge and audit its axiom footprint on the remote worker.
#
#   scripts/build-remote.sh --session <worker-session> [options]
#
# Options:
#   --session <id>    worker session (or LLVM_BRIDGE_SESSION)
#   --remote <path>   the gcloud-remote.ts transport (or LLVM_BRIDGE_REMOTE)
#   --lake <path>     lake to run on the worker (or LLVM_BRIDGE_LAKE; default
#                     `lake` on the worker's PATH).  A worker whose `lake` is a
#                     project wrapper needs the plain binary, e.g.
#                     /nix/store/<lean4>/bin/lake.
#   --llvm-lib <dir>  the LeanLLVM checkout to push (default: ../lean-llvm)
#   --dir <path>      worker-side base directory, relative to the login home
#                     (default: llvm, or LLVM_BRIDGE_REMOTE_ROOT)
#
# Nothing is built here.  The sibling checkout is copied to the worker, its
# package definition replaced by scripts/worker-lean-llvm-lakefile.toml (a
# projection with no Mathlib requirement), and the bridge is built against it.
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
session=${LLVM_BRIDGE_SESSION:-}
remote=${LLVM_BRIDGE_REMOTE:-}
lake=${LLVM_BRIDGE_LAKE:-lake}
llvm_lib=$(cd "$here/../../lean-llvm" 2>/dev/null && pwd || true)
root=${LLVM_BRIDGE_REMOTE_ROOT:-llvm}

usage() {
  sed -n '2,22p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
}

while [ $# -gt 0 ]; do
  case "$1" in
    --session) session=${2:?--session needs a value}; shift 2 ;;
    --remote) remote=${2:?--remote needs a value}; shift 2 ;;
    --lake) lake=${2:?--lake needs a value}; shift 2 ;;
    --llvm-lib) llvm_lib=${2:?--llvm-lib needs a value}; shift 2 ;;
    --dir) root=${2:?--dir needs a value}; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "build-remote: unknown argument '$1'" >&2; usage >&2; exit 64 ;;
  esac
done

if [ -z "$remote" ]; then
  echo "build-remote: pass --remote <gcloud-remote.ts> or set LLVM_BRIDGE_REMOTE" >&2
  exit 64
fi
if [ -z "$session" ]; then
  echo "build-remote: pass --session <id> or set LLVM_BRIDGE_SESSION" >&2
  exit 64
fi
if [ -z "$llvm_lib" ] || [ ! -d "$llvm_lib/LeanLLVM" ]; then
  echo "build-remote: --llvm-lib must name a LeanLLVM checkout (looked at '${llvm_lib:-<unset>}')" >&2
  exit 64
fi

run() { "$remote" run --session "$session" -- "$1"; }
copy_to() { "$remote" copy --session "$session" --to "$1" "$2" >/dev/null; }

echo "== provisioning the sibling package on the worker =="
run "mkdir -p '$root/lean-llvm'"
copy_to "$llvm_lib/LeanLLVM" "$root/lean-llvm"
copy_to "$llvm_lib/lean-toolchain" "$root/lean-llvm/lean-toolchain"
copy_to "$here/scripts/worker-lean-llvm-lakefile.toml" "$root/lean-llvm/lakefile.toml"

echo "== pushing the bridge =="
copy_to "$here" "$root"

echo "== building on the worker =="
run "export PATH=$(dirname "$lake"):\$PATH; \
  echo lake: \$(command -v lake); lake --version | head -1; \
  lean --version | head -1; clang --version | head -1; \
  cd '$root/llvm-bridge' && lake build && lake env lean scripts/check-axioms.lean"
