#!/usr/bin/env bash
#
# Fetch clang's emission for c/store8.c from the remote worker and, unless
# --check is given, install it as ir/store8.raw.ll and ir/store8.ll.
#
#   scripts/emit-ir.sh --session <worker-session> [options]
#
# Options:
#   --session <id>   worker session (or LLVM_BRIDGE_SESSION)
#   --remote <path>  the gcloud-remote.ts transport (or LLVM_BRIDGE_REMOTE)
#   --check          compare the fetch with the committed files instead of
#                    installing it; exit 1 on any difference
#   --dir <path>     worker-side directory, relative to the login home
#                    (default: llvm/emit, or LLVM_BRIDGE_REMOTE_DIR)
#
# The compilation runs on the worker, never here: clang, llvm-as and the two
# files this script reads back are all produced remotely.
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
session=${LLVM_BRIDGE_SESSION:-}
remote=${LLVM_BRIDGE_REMOTE:-}
remote_dir=${LLVM_BRIDGE_REMOTE_DIR:-llvm/emit}
check=0

usage() {
  sed -n '2,17p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
}

while [ $# -gt 0 ]; do
  case "$1" in
    --session) session=${2:?--session needs a value}; shift 2 ;;
    --remote) remote=${2:?--remote needs a value}; shift 2 ;;
    --dir) remote_dir=${2:?--dir needs a value}; shift 2 ;;
    --check) check=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "emit-ir: unknown argument '$1'" >&2; usage >&2; exit 64 ;;
  esac
done

if [ -z "$remote" ]; then
  echo "emit-ir: pass --remote <gcloud-remote.ts> or set LLVM_BRIDGE_REMOTE" >&2
  exit 64
fi
if [ -z "$session" ]; then
  echo "emit-ir: pass --session <id> or set LLVM_BRIDGE_SESSION" >&2
  exit 64
fi

run() { "$remote" run --session "$session" -- "$1"; }
copy_to() { "$remote" copy --session "$session" --to "$1" "$2" >/dev/null; }
copy_from() { "$remote" copy --session "$session" --from "$1" "$2" >/dev/null; }

run "mkdir -p '$remote_dir'"
copy_to "$here/c/store8.c" "$remote_dir/store8.c"
copy_to "$here/scripts/project-ir.sed" "$remote_dir/project-ir.sed"

# -O1 is the emitted body the theorems are about: the alloca spills of -O0 are
# not part of this kernel's boundary.  llvm-as checks the emission is valid IR
# before the projection touches it.
run "cd '$remote_dir' \
  && clang --version | head -1 > clang-version.txt \
  && clang -std=c11 -S -emit-llvm -O1 -o store8.raw.ll store8.c \
  && llvm-as store8.raw.ll -o /dev/null \
  && sed -E -f project-ir.sed store8.raw.ll > store8.ll"

stage=$(mktemp -d)
trap 'rm -rf "$stage"' EXIT
copy_from "$remote_dir/store8.raw.ll" "$stage/store8.raw.ll"
copy_from "$remote_dir/store8.ll" "$stage/store8.ll"
copy_from "$remote_dir/clang-version.txt" "$stage/clang-version.txt"

echo "clang: $(cat "$stage/clang-version.txt")"

if [ "$check" -eq 1 ]; then
  status=0
  if ! diff -u "$here/ir/store8.raw.ll" "$stage/store8.raw.ll"; then
    echo "emit-ir: ir/store8.raw.ll differs from the worker's emission" >&2
    status=1
  fi
  if ! diff -u "$here/ir/store8.ll" "$stage/store8.ll"; then
    echo "emit-ir: ir/store8.ll differs from the worker's projection" >&2
    status=1
  fi
  if [ "$status" -eq 0 ]; then
    echo "emit-ir: the committed IR reproduces from c/store8.c on the worker"
  fi
  exit "$status"
fi

cp "$stage/store8.raw.ll" "$here/ir/store8.raw.ll"
cp "$stage/store8.ll" "$here/ir/store8.ll"
echo "emit-ir: installed ir/store8.raw.ll and ir/store8.ll"
