#!/usr/bin/env bash
# Census of the documentation claims about the integrated borrowing discipline.
#
# Each row names a tracked path, a literal needle, and the side of the change the
# needle belongs to:
#
#   drop  a claim that the integrated discipline removes; it must be present at
#         the base revision and absent after the change.
#   add   a claim the integrated discipline introduces; it must be absent at the
#         base revision and present after the change.
#
# Every file is flattened (newlines to spaces, runs of spaces to one) before the
# literal search, so line wrapping and TeX indentation never affect a match. The
# flattened file makes each count either 0 or 1.
#
# Usage:
#   scripts/check_cap_docs.sh --control <base-rev>   assert the base column
#   scripts/check_cap_docs.sh --rev <census-rev>     assert the census column
#   scripts/check_cap_docs.sh --rev WORKTREE         read the working tree
#
# Exits 0 only when every row meets its expectation for the selected side.
set -uo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"

usage() {
  sed -n '2,20p' "$0" | sed 's/^# \{0,1\}//'
}

mode=
rev=
while [ $# -gt 0 ]; do
  case "$1" in
    --control)
      [ $# -ge 2 ] || { echo "check_cap_docs.sh: --control needs a revision" >&2; exit 2; }
      mode=control; rev=$2; shift 2 ;;
    --rev)
      [ $# -ge 2 ] || { echo "check_cap_docs.sh: --rev needs a revision" >&2; exit 2; }
      mode=census; rev=$2; shift 2 ;;
    -h|--help)
      usage; exit 0 ;;
    *)
      echo "check_cap_docs.sh: unknown argument: $1" >&2
      usage >&2
      exit 2 ;;
  esac
done

if [ -z "$mode" ]; then
  echo "check_cap_docs.sh: select --control <rev> or --rev <rev>" >&2
  exit 2
fi

if [ "$rev" != WORKTREE ]; then
  if ! git rev-parse --verify --quiet "$rev^{tree}" >/dev/null; then
    echo "check_cap_docs.sh: not a revision: $rev" >&2
    exit 2
  fi
fi

# Emit the flattened contents of one tracked path at the selected source.
read_path() {
  local path=$1
  if [ "$rev" = WORKTREE ]; then
    if [ ! -f "$path" ]; then
      return 1
    fi
    tr '\n' ' ' <"$path" | tr -s ' '
  else
    git show "$rev:$path" | tr '\n' ' ' | tr -s ' '
  fi
}

fail=0
rows=0

while IFS='|' read -r kind path needle; do
  case "$kind" in
    ''|'#'*) continue ;;
    drop|add) ;;
    *)
      echo "check_cap_docs.sh: bad row kind: $kind" >&2
      fail=1
      continue ;;
  esac

  rows=$((rows + 1))

  if ! flat=$(read_path "$path"); then
    echo "MISSING $path at $rev" >&2
    fail=1
    continue
  fi

  count=$(printf '%s\n' "$flat" | grep -cF -- "$needle")

  if [ "$mode" = control ]; then
    case "$kind" in
      drop) want=present ;;
      add)  want=absent ;;
    esac
  else
    case "$kind" in
      drop) want=absent ;;
      add)  want=present ;;
    esac
  fi

  if [ "$count" -gt 1 ]; then
    echo "AMBIGUOUS $path: needle occurs $count times at $rev: $needle" >&2
    fail=1
    continue
  fi

  case "$want:$count" in
    present:0) echo "MISSING $path: expected '$needle' at $rev" >&2; fail=1 ;;
    absent:1)  echo "STALE $path: found '$needle' at $rev" >&2; fail=1 ;;
  esac
done <<'ROWS'
drop|AGENTS.md|the loans are not yet consulted by
drop|AGENTS.md|`beginLoan`, `endLoan`, `free`
drop|AGENTS.md|`beginLoan`, `endLoan`, `nop`
drop|AGENTS.md|`beginLoanChecked_succeeds`
drop|AGENTS.md|context-level suspension/resumption evidence
drop|AGENTS.md|The loan invariant is `Cap/LoansInv.lean`
drop|AGENTS.md|`World.FullInv w := w.TopInv ∧ w.LoansOK`
drop|AGENTS.md|suspension/restoration
drop|AGENTS.md|Joins, loans and a snapshot command are not yet in
drop|AGENTS.md|not yet connected to `World`/`FullInv`
drop|AGENTS.md|Borrow/return correspondence is not yet implemented
drop|AGENTS.md|The transitions are not yet in `UCmd`
drop|AGENTS.md|The delegation invariant is not yet part of the bundle
drop|AGENTS.md|Cap/LoansInv.lean
drop|AGENTS.md|Cap/Reborrow.lean
drop|AGENTS.md|Cap/Suspend.lean
drop|AGENTS.md|Cap/Nested.lean
drop|AGENTS.md|Cap/Policy.lean
drop|AGENTS.md|Cap/Session.lean
drop|AGENTS.md|preserve the world invariant (`World.WellFormed`) through every command
drop|AGENTS.md|`Cap/TopInvariant.lean` completes it
add|AGENTS.md|LoansDetachedOK
add|AGENTS.md|CommandInv
drop|docs/notes/cap-tutorial.md|Cap/Suspend.lean
drop|docs/notes/cap-tutorial.md|`beginLoan a lender loanId`
drop|docs/notes/cap-tutorial.md|`endLoan a loanId`
drop|docs/notes/cap-tutorial.md|Loans: suspension, not tracking
drop|docs/notes/cap-tutorial.md|`beginLoan`
drop|docs/notes/cap-tutorial.md|`endLoan`
drop|docs/notes/cap-tutorial.md|suspension, not a reborrow capability
drop|docs/notes/cap-tutorial.md|`Cap/Policy.lean` liveness
drop|docs/notes/cap-tutorial.md|Loans are exclusive suspension
drop|docs/notes/cap-tutorial.md|checkWorld_wf : checkWorld w cs = .ok w' → w.WellFormed → w'.WellFormed
add|docs/notes/cap-tutorial.md|CommandInv
drop|report/cap-tutorial.tex|\file{Cap/Suspend.lean}
drop|report/cap-tutorial.tex|beginLoan (a : AllocId)
drop|report/cap-tutorial.tex|endLoan (a : AllocId)
drop|report/cap-tutorial.tex|\section{Loans: suspension, not tracking}
drop|report/cap-tutorial.tex|\lean{beginLoan} retires
drop|report/cap-tutorial.tex|\file{Cap/Policy.lean} liveness
drop|report/cap-tutorial.tex|Loans are exclusive suspension
drop|report/cap-tutorial.tex|checkWorld w cs = .ok w' → w.WellFormed → w'.WellFormed
add|report/cap-tutorial.tex|CommandInv
drop|report/capability-report.tex|\file{Cap/Policy.lean}
drop|report/capability-report.tex|\file{Cap/Nested.lean}
drop|report/capability-report.tex|\file{Cap/Session.lean}
drop|report/capability-report.tex|\file{Cap/Reborrow.lean}
drop|report/capability-report.tex|\texttt{Cap/Reborrow.lean}
drop|report/capability-report.tex|= World.TopInv} $\land$ \texttt{World.LoansOK}
drop|report/capability-report.tex|Loans are the suspension discipline
drop|report/capability-report.tex|\texttt{beginLoan} retires
drop|report/capability-report.tex|\texttt{beginLoan} and
drop|report/capability-report.tex|suspension/resumption evidence
drop|report/capability-report.tex|def Policy.Writable
drop|report/capability-report.tex|theorem begin_suspends
drop|report/capability-report.tex|def Session.fillGuarded?
drop|report/capability-report.tex|covering suspension and restoration
drop|report/capability-report.tex|allocation, suspension and restoration
drop|report/capability-report.tex|historyOK\_beginLoanChecked
drop|report/capability-report.tex|historyOK\_endLoanChecked
drop|report/capability-report.tex|\file{Cap/LoansInv.lean} states
drop|report/capability-report.tex|Splits, joins, loans and disposal are not yet in that
drop|report/capability-report.tex|but a live inner reborrow integrated with the ledger is still absent
add|report/capability-report.tex|World.BorrowOK
drop|docs/lean-fractional-ownership-design.md|Restoration and lifetime-dependency proofs completed
add|docs/lean-fractional-ownership-design.md|integrated authority invariant
drop|paper/sealed-ownership.tex|has nested execution controls but is not yet covered by the combined preservation theorem
drop|paper/sealed-ownership.tex|including the remaining integration of delegation
drop|paper/sealed-ownership.tex|The combined theorem covers the command language's suspension loans
drop|paper/sealed-ownership.tex|Distinct-borrower delegation is an executable extension with its own developing invariant
drop|paper/sealed-ownership.tex|suspension-loan begin/end
drop|paper/sealed-ownership.tex|w.TopInv ∧ w.LoansOK
drop|paper/sealed-ownership.tex|These facts are not yet a preservation theorem
drop|paper/sealed-ownership.tex|predicate does not state that a lender with delegated authority is absent from the active frontier
drop|paper/sealed-ownership.tex|or that a downstream edge preserves the allocation
drop|paper/sealed-ownership.tex|The suspension-based \lean{LoansOK} is not interchangeable with this delegation predicate
add|paper/sealed-ownership.tex|Delegation by retagging is part of the combined invariant
add|paper/sealed-ownership.tex|the delegation mechanism is covered by the combined preservation theorem
drop|Cap/Context.lean|single-owner `Cap.Session` exercises the transitions meanwhile
drop|Cap/Borrow.lean|This slice does not yet update
drop|Cap/Borrow.lean|That integration is the next step
drop|Cap/IProg.lean|w'.ctx = Q a ∧ w'.WellFormed
drop|Cap/IProg.lean|execution from a well-formed world that matches the typing context
add|Cap/IProg.lean|w'.ctx = Q a ∧ w'.CommandInv
# Borrowing, reconstruction and reusable-client surfaces. The removed rows are
# claims the repaired chain and the separate reconstruction model replace; the
# added rows are the live-documentation statements of the new surfaces, each
# with its boundary stated.
drop|AGENTS.md|an explicit holder equal to the base on an empty chain
drop|paper/sealed-ownership.tex|This sequence is an evaluation requirement, not a claimed artifact result
drop|paper/sealed-ownership.tex|Integrated invariant and primitive preservation
drop|paper/sealed-ownership.tex|Distinct-borrower transitions in that theorem
drop|paper/sealed-ownership.tex|The intended discipline includes this operation
add|AGENTS.md|Cap/Reconstruction.lean
add|AGENTS.md|the one integrated sealed semantics
add|AGENTS.md|World.splitAtChecked_refuses_with_loan
add|AGENTS.md|derived holder
add|AGENTS.md|reuseFirst_accepts_second
add|docs/notes/cap-tutorial.md|The sealed boundary is `Cap/Integrated.lean`
add|docs/notes/cap-tutorial.md|No claim that `World.splitAtChecked` consults the reconstruction forest
add|report/capability-report.tex|borrowed subdivision, reconstruction and restoration invariant
add|report/capability-report.tex|two-find reusable compression on the functional model
add|report/cap-tutorial.tex|Borrowed subdivision and reconstruction
add|paper/sealed-ownership.tex|World-guard integration (open)
add|paper/sealed-ownership.tex|the sealed path now executes the integrated multi-allocation reconstruction language
add|paper/sealed-ownership.tex|reuseFirst\_accepts\_second
add|paper/sealed-ownership.tex|The sealed boundary executes the reconstruction language
# Ownership accounting, persistent histories, the sealed two-find client and the
# composed compiled-store theorem. Each row is a claim introduced after the base
# revision; the remaining assumptions are recorded beside the positive result.
add|AGENTS.md|The account is not a structural restatement of the forest
add|AGENTS.md|a freed identifier cannot be reissued
add|AGENTS.md|No full C/ABI or physical ownership refinement is claimed
add|AGENTS.md|store8_exec_write_comp
add|docs/notes/cap-tutorial.md|The account is not a structural restatement of the forest
add|docs/notes/cap-tutorial.md|not an allocation generation, a physical-slot check
add|docs/notes/cap-tutorial.md|integrated sealed boundary instead
add|docs/notes/cap-tutorial.md|store8_exec_write_comp
add|docs/notes/cap-tutorial.md|The LaTeX outputs were not rebuilt at this revision
add|report/cap-tutorial.tex|The account is not a structural restatement of the forest
add|report/cap-tutorial.tex|A freed identifier therefore cannot be reissued
add|report/cap-tutorial.tex|Cap/UFIntegrated.lean} runs the two calls
add|report/cap-tutorial.tex|store8\_exec\_write\_comp
add|report/cap-tutorial.tex|The LaTeX outputs were not rebuilt at this revision
add|report/capability-report.tex|not a structural restatement of the forest
add|report/capability-report.tex|Cap/UFIntegrated.lean} runs the two calls
add|report/capability-report.tex|A compiled store composed with an authorized write
add|report/capability-report.tex|The LaTeX outputs are rebuilt from these sources at this revision
add|paper/sealed-ownership.tex|its invariant includes an ownership account over issued
add|paper/sealed-ownership.tex|general sealed union-find theorem with its two-find instance
add|paper/sealed-ownership.tex|One instance of the schema is proved for a single authorized byte write
add|paper/sealed-ownership.tex|The LaTeX outputs are rebuilt from these sources
add|paper/sealed-ownership.tex|No full C/ABI refinement and no physical ownership refinement is claimed
# The finite address-map relation is a model layer, not a loader assignment.
add|AGENTS.md|Cap/AddressMap.lean
add|AGENTS.md|finite address assignment for that integrated
add|docs/notes/cap-tutorial.md|with disjointness, in-window address lookup
add|docs/notes/cap-tutorial.md|live allocations to concrete windows
# An accepted sealed write frames the unrelated allocation's full component,
# its storage certificate and any address-map window, not only its snapshot.
add|AGENTS.md|WriteFrame.component_other
add|AGENTS.md|lifts that to a sealed write
add|docs/notes/cap-tutorial.md|single-write frame
add|docs/notes/cap-tutorial.md|every unrelated allocation's full component
add|docs/notes/cap-tutorial.md|lifts that frame to a sealed write
add|report/cap-tutorial.tex|single-write frame
add|report/cap-tutorial.tex|WriteFrame.rel\_write
add|report/capability-report.tex|the frame of every other allocation's full component
add|report/capability-report.tex|are framed (\texttt{WriteFrame}
add|paper/sealed-ownership.tex|frames every other allocation's full
add|paper/sealed-ownership.tex|WriteFrame.rel\_write
# The command-list frame: a whole accepted run leaves an untargeted allocation's
# component, bytes and `Storage` certificate unchanged, and the address-map
# relation carries that frame across a list. The compiled boundary stays open.
add|AGENTS.md|State.run_frames_other
add|AGENTS.md|Sealed.run_frames_other
add|AGENTS.md|Rel.run_other
add|docs/notes/cap-tutorial.md|State.run_frames_other
add|docs/notes/cap-tutorial.md|Sealed.run_frames_other
add|docs/notes/cap-tutorial.md|Rel.run_other
# The strengthened reconstruction invariant: recursive resource coherence,
# allocation scope, the write guard's allocation binding, derived terminal
# realization, and the adversarial regression witnesses.
add|AGENTS.md|recursive resource coherence `Forest.Coherent`
add|AGENTS.md|State.Scope.rule_scope
add|AGENTS.md|State.Inv.restore_terminal_frontier
add|AGENTS.md|Forest.coherent_suspension_realizes
add|AGENTS.md|State.WriteGuard`
add|AGENTS.md|State.write_guard
add|AGENTS.md|bench/CapInvariantWitness.lean
add|AGENTS.md|witnessA_frontier_overstated
add|AGENTS.md|witnessB_not_inv
add|AGENTS.md|State.Inv.write_scope
add|docs/notes/cap-tutorial.md|component allocation scope `State.Scope`
add|AGENTS.md|`Forest.Coherent` and `State.Scope`
ROWS

if [ "$fail" -ne 0 ]; then
  echo "capability docs census: FAILED" >&2
  exit 1
fi

echo "capability docs census: OK ($rows rows, $rev)"
