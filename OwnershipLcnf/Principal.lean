/-
The composed principal guarantee for the recognised flat write.

The model, the recognised LCNF and the runtime model are separate semantics.
This module states the conjunction the paper calls the principal guarantee: the
recognised prefix's designated write is the in-place outcome, the model run is the
same outcome, and the runtime model's `setAt` returns an in-place result with the
correspondence preserved.

`OwnersAccounted` and `CountFidelity` are environment-side and heap/runtime-side
accounting contracts. They are hypotheses of the guarantee, not consequences of
`Inv`; `alias_not_accounted` shows why the environment side is needed. The
theorem does not claim that the linked C runtime or the emitted recursive callee
implements these contracts.
-/
import OwnershipLcnf.Semantics
import OwnershipLcnf.RuntimeModel
import Ownership.Accounting

set_option linter.unusedVariables false

namespace OwnershipLcnf

open Ownership

/-- The flat recognised write: model in-place, LCNF in-place, and runtime-model
in-place, under the entry invariant, the accounting contracts and the primitive
contracts. -/
theorem principal_write
    {code : Lean.Compiler.LCNF.Code Lean.Compiler.LCNF.Purity.impure}
    {p : Prefix} {assign : Lean.FVarId → Var}
    (hproj : projectPrefix code = some p) (hl : Layout assign p)
    (s : Machine) (env : Env) (H : Heap)
    (root : Ref) (client : List Ref) (i v : Nat) (o : Obj)
    (hEntry : Entry.EntryInv H env (Runner.initCtx root) root client)
    (hacc : OwnersAccounted (Runner.initCtx root))
    (vars : List Var)
    (hcount : CountFidelity H (Runner.initCtx root) vars)
    (hag : Agrees assign p s env H root i v)
    (hcell : H.cells root = some o) (hin : i < o.fields.size)
    {R : Runtime.RHeap} {o' : Runtime.RObj}
    (hc : Runtime.Corr H R) (ho' : R.cells root = some o') :
    PrefixOutcome.ofExec assign p (execAST assign p code s) =
        some (inPlaceOutcome root i v o H) ∧
      PrefixOutcome.ofModel (Ownership.run (Prefix.toModel assign p) env H) =
        inPlaceOutcome root i v o H ∧
      ∃ H',
        Runtime.setAt R root i (Val.scalar v) =
            some (Runtime.SetOutcome.inPlace H' root) ∧
          Runtime.Corr (inPlaceOutcome root i v o H).heap H' ∧
            (inPlaceOutcome root i v o H).target = some root ∧
              ((H'.cells root).bind fun o => o.field? i) = some (Val.scalar v) := by
  have hrec := recognized_write_in_place (assign := assign) (p := p)
    hproj hl s env H root client i v o hEntry hag hcell hin
  refine ⟨hrec.1, hrec.2, ?_⟩
  exact Runtime.setAt_inPlace_of_entryInv (H := H) (R := R) (env := env)
    (root := root) (client := client) (i := i) (vn := v) (o := o) (o' := o')
    hEntry hc hcell ho' hin

end OwnershipLcnf
