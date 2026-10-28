/-
The checked prefix cannot abort.

`Semantics.exec` gives the emitted exclusivity check its abort branch: when the
array is not exclusive it reports `.notExclusive` (`OwnershipLcnf/Semantics.lean`,
the `checkExclusive` rule). This module names the property that the checked
prefix never reaches that branch, and derives it from the recognized prefix and
the entry invariant.

What this theorem does not say: it does not prove that `lean_is_exclusive` is
true in the running binary. The check's runtime meaning is contract A6 in
`Semantics.lean`; the array-update runtime meaning is A8. Relating the model's
`exclusive?` to the runtime's counter is the named outstanding refinement (A10),
so the dynamic abort is impossible *in the emitted semantics under those
contracts*, not yet in the linked executable.
-/
import OwnershipLcnf.Semantics

open Lean
open Lean.Compiler.LCNF

namespace OwnershipLcnf

/-- The abort condition at the semantic boundary: the prefix reports a fault. -/
def PrefixAborts (out : Option PrefixOutcome) : Prop :=
  ∃ o, out = some o ∧ o.fault ≠ none

/-- The recognized `setAt` prefix never reports the exclusivity fault and lands
its designated write in place, given the entry invariant and the recognition.
The `.notExclusive` branch of the `checkExclusive` rule is not taken.

This is the emitted-semantics form of "the abort is impossible". The runtime
`assertExclusive`/`lean_is_exclusive` correspondence remains contract A6; see the
module header. -/
theorem prefix_abort_impossible {code : Code .impure} {p : Prefix}
    {assign : FVarId → Ownership.Var} (hproj : projectPrefix code = some p)
    (hl : Layout assign p) (s : Machine) (env : Ownership.Env) (H : Ownership.Heap)
    (root : Ownership.Ref) (client : List Ownership.Ref) (i v : Nat) (o : Ownership.Obj)
    (hEntry : Ownership.Entry.EntryInv H env (Ownership.Runner.initCtx root) root client)
    (hag : Agrees assign p s env H root i v)
    (hcell : H.cells root = some o)
    (hin : i < o.fields.size) :
    ¬ PrefixAborts (PrefixOutcome.ofExec assign p (execAST assign p code s)) := by
  obtain ⟨hout, -⟩ :=
    recognized_write_in_place hproj hl s env H root client i v o hEntry hag hcell hin
  intro ⟨out, hout', hfault⟩
  rw [hout] at hout'
  injection hout' with hEq
  subst hEq
  exact hfault rfl

end OwnershipLcnf
