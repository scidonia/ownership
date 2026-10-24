#!/usr/bin/env bash
# Assert the structured branch record the measurement CLI reports for one
# `Path` constructor of `Scidonia.FracPerm.StateVar.Layout5.setAt`.
#
#   bash tests/struct-branch-assert.sh left
#   bash tests/struct-branch-assert.sh right
#
# Invokes `scripts/dump_executor.lean` once from the sibling checkout, which is
# where `lake env` supplies the sibling's oleans, and reads the CLI's output.
set -uo pipefail

usage() {
  echo "usage: bash tests/struct-branch-assert.sh left|right" >&2
  exit 2
}

if [ "$#" -ne 1 ]; then
  usage
fi

case "$1" in
  left)
    SCENARIO=S1
    SIDE=left
    SELECTED=0
    RETAINED=1
    ;;
  right)
    SCENARIO=S2
    SIDE=right
    SELECTED=1
    RETAINED=0
    ;;
  *)
    usage
    ;;
esac

ROOT=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
SIBLING="$ROOT/../lean-examples"

if [ ! -d "$SIBLING" ]; then
  echo "$SCENARIO control failed: sibling checkout '$SIBLING' is not present; the measurement CLI cannot be invoked." >&2
  exit 1
fi

CAPTURE_DIR=$(mktemp -d) || {
  echo "$SCENARIO control failed: could not create a temporary capture directory." >&2
  exit 1
}
trap 'rm -rf -- "$CAPTURE_DIR"' EXIT
OUT="$CAPTURE_DIR/dump.txt"

if ! ( cd -- "$SIBLING" && nix develop -c lake env lean "$ROOT/scripts/dump_executor.lean" ) >"$OUT" 2>&1; then
  echo "$SCENARIO control failed: the measurement CLI did not exit successfully." >&2
  echo "--- last 20 captured lines ---" >&2
  tail -n 20 -- "$OUT" >&2
  exit 1
fi

# The single detector for a labelled record line: prints the body of every line
# whose text begins with the given label. Both the index-shape control and the
# branch-report assertion below go through it, so a detector that cannot see a
# label cannot pass either one.
record_body() {
  local label=$1 line
  while IFS= read -r line; do
    case "$line" in
      "$label "*) printf '%s\n' "${line#"$label "}" ;;
    esac
  done <"$OUT"
}

# Affirmative control: the dump reached the structured write path and reported
# the index shape it already measures.
mapfile -t INDEX < <(record_body "setAt index shape:")
if [ "${#INDEX[@]}" -ne 1 ]; then
  echo "$SCENARIO control failed: expected exactly one 'setAt index shape:' record, observed ${#INDEX[@]}." >&2
  exit 1
fi
if ! [[ "${INDEX[0]}" =~ ^checkArray=\(some\ [0-9]+\)\ takeOut=\(some\ [0-9]+\)\ checkElem=\(some\ [0-9]+\)\ setAt=\(some\ [0-9]+\)\ putBack=\(some\ [0-9]+\),\ calls=[0-9]+,\ incs=[0-9]+$ ]]; then
  echo "$SCENARIO control failed: 'setAt index shape:' record is not the measured labeled shape." >&2
  echo "  record: setAt index shape: ${INDEX[0]}" >&2
  exit 1
fi
echo "control: setAt index shape: ${INDEX[0]}"

# The binding of one labelled key in a record body, independent of the other
# fields and of their order; prints nothing when the key is absent.
field_value() {
  local body=$1 want=$2 part key value
  local -a parts=()
  IFS=';' read -r -a parts <<<"$body"
  for part in "${parts[@]}"; do
    part=${part# }
    part=${part% }
    [[ "$part" == *=* ]] || continue
    key=${part%%=*}
    if [ "$key" = "$want" ]; then
      printf '%s\n' "${part#*=}"
      return 0
    fi
  done
  return 1
}

EXPECTED="$SCENARIO assertion failed: expected exactly one 'setAt branch report:' record for ctor=Path.$SIDE binding selected=$SELECTED; retained=$RETAINED; exclusive=reuse; shared=copy."

# One invocation may report several constructors; the contract is the single
# record for this side, not a record count for the whole output.
mapfile -t REPORT < <(record_body "setAt branch report:")
MATCHING=()
for body in "${REPORT[@]}"; do
  if [ "$(field_value "$body" ctor)" = "Path.$SIDE" ]; then
    MATCHING+=("$body")
  fi
done
if [ "${#MATCHING[@]}" -ne 1 ]; then
  echo "$EXPECTED" >&2
  echo "  observed ${#MATCHING[@]} record(s) with ctor=Path.$SIDE among ${#REPORT[@]} 'setAt branch report:' record(s)." >&2
  exit 1
fi

BODY=${MATCHING[0]}
declare -A OBSERVED=()
PROBLEM=""
IFS=';' read -r -a FIELDS <<<"$BODY"
for field in "${FIELDS[@]}"; do
  field=${field# }
  field=${field% }
  if [[ "$field" != *=* ]]; then
    PROBLEM="field '$field' is not a key=value binding"
    break
  fi
  key=${field%%=*}
  value=${field#*=}
  if [ -n "${OBSERVED[$key]+set}" ]; then
    PROBLEM="field '$key' is bound more than once"
    break
  fi
  OBSERVED[$key]=$value
done

declare -A EXPECT_FIELD=(
  [ctor]="Path.$SIDE"
  [selected]="$SELECTED"
  [retained]="$RETAINED"
  [exclusive]="reuse"
  [shared]="copy"
)

if [ -z "$PROBLEM" ] && [ "${#OBSERVED[@]}" -ne "${#EXPECT_FIELD[@]}" ]; then
  PROBLEM="expected ${#EXPECT_FIELD[@]} bindings, observed ${#OBSERVED[@]}"
fi
if [ -z "$PROBLEM" ]; then
  for key in "${!EXPECT_FIELD[@]}"; do
    if [ -z "${OBSERVED[$key]+set}" ]; then
      PROBLEM="missing binding '$key'"
      break
    fi
    if [ "${OBSERVED[$key]}" != "${EXPECT_FIELD[$key]}" ]; then
      PROBLEM="binding '$key' is '${OBSERVED[$key]}', expected '${EXPECT_FIELD[$key]}'"
      break
    fi
  done
fi

if [ -n "$PROBLEM" ]; then
  echo "$EXPECTED" >&2
  echo "  record: setAt branch report: $BODY" >&2
  echo "  $PROBLEM." >&2
  exit 1
fi

echo "assertion passed: setAt branch report: $BODY"
