#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
if grep -R -nE '^import Cap(\.|$)|^import CapCertified' "$root/CapRuntime.lean" "$root/CapRuntime"; then
  echo "runtime imports ghost/certificate modules" >&2
  exit 1
fi
echo "runtime import boundary: OK"
