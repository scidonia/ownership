#!/usr/bin/env bash
# Rebuild the pinned LCNF artifacts and compare them with the committed bytes.
#
# The gate binds the sibling revision, the flake's Lean and the two artifacts
# the projection and nested recognizers are stated against:
#
#   docs/notes/artifacts/execP.lcnf.txt        (the captured execP replay)
#   docs/notes/artifacts/setAt-nested.lcnf.txt (the captured setAt replay)
#
# Run from anywhere; the script resolves the repository root from its own path.
set -euo pipefail
cd "$(dirname "$0")/.."

sibling=${1:-"../lean-examples"}
pin=66e64334a1c968d829903b8aec8d22f7e3b9fd3f

actual=$(git -C "$sibling" rev-parse HEAD)
if [ "$actual" != "$pin" ]; then
  echo "sibling is at $actual, expected $pin" >&2
  exit 1
fi

if ! nix develop -c lean --version | grep -q '4.35.0-rc3'; then
  echo "the flake's Lean is not 4.35.0-rc3" >&2
  exit 1
fi

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

(cd "$sibling" && nix develop -c lake env lean ../ownership/scripts/capture_nested.lean) \
  > "$work/nested.txt" 2>&1
diff -u docs/notes/artifacts/setAt-nested.lcnf.txt "$work/nested.txt"

(cd "$sibling" && nix develop -c lake env lean ../ownership/scripts/dump_executor.lean) \
  > "$work/execp.txt" 2>&1
sed -n '/^```text$/,/^```$/p' docs/notes/artifacts/execP.lcnf.txt | sed '1d;$d' \
  > "$work/execp-fenced.txt"
diff -u "$work/execp-fenced.txt" "$work/execp.txt"

echo "artifacts match the pinned sibling and toolchain"
