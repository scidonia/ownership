#!/usr/bin/env bash
# Run the capability subsystem's positive and negative fixtures.
#
# Positive fixtures must elaborate. Negative fixtures must fail, and must report
# the intended diagnostic; a rejection for an unrelated reason does not count.
set -uo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
export LEAN_PATH="$root/.lake/build/lib/lean:${LEAN_PATH:-}"

fail=0
out=$(mktemp)
trap 'rm -f "$out"' EXIT

# The reflective prototype's API is a bench-local module.
if ! (cd bench && lean -o OwnedStatic.olean OwnedStatic.lean >"$out" 2>&1); then
  echo "FAILED: OwnedStatic.lean did not elaborate" >&2
  sed -n '1,40p' "$out" >&2
  fail=1
fi
export LEAN_PATH="$root/bench:$LEAN_PATH"

check_ok() {
  local f=$1
  if ! (cd bench && lean "$f" >"$out" 2>&1); then
    echo "FAILED: $f did not elaborate" >&2
    sed -n '1,40p' "$out" >&2
    fail=1
  fi
}

check_fail() {
  local f=$1 pat=$2
  if (cd bench && lean "$f" >"$out" 2>&1); then
    echo "FAILED: $f was accepted" >&2
    fail=1
  elif ! grep -q "$pat" "$out"; then
    echo "FAILED: $f did not report '$pat'" >&2
    sed -n '1,40p' "$out" >&2
    fail=1
  fi
}

check_ok AdmissionAccept.lean
check_ok AdmissionParam.lean
check_ok NatThunkAdmission.lean
check_ok UniverseDemo.lean
check_ok CapNegative.lean
check_ok CapMarshal.lean
check_ok CapBorrow.lean
check_ok CapSealAccept.lean
check_ok CapFreshness.lean
check_ok OwnedAccept.lean
check_ok OwnedDemo.lean

check_fail AdmissionReject.lean "non-standard axioms"
check_fail AdmissionWrongDomain.lean "does not have type Bij"
check_fail CapSurfaceReject.lean "write refused"
check_fail CapSurfaceReject.lean "splitAt refused"
check_fail CapSurfaceReject.lean "splitFraction refused"
check_fail OwnedReject.lean "used 2 times"
check_fail OwnedNoAccess.lean "is private"
check_fail CapSealReject.lean "Cap.Sealed.mk"
check_fail CapSealReject.lean "Cap.Sealed.ofRun"
check_fail CapSealPeekReject.lean "is private"

if [ "$fail" -ne 0 ]; then
  echo "capability controls: FAILED" >&2
  exit 1
fi
echo "capability controls: OK"
