/-
The composed principal guarantee for the recognised flat write.

The model, the recognised LCNF and the runtime model are separate semantics.
This module states the conjunction the paper calls the principal guarantee: the
recognised prefix's designated write is the in-place outcome, the model run is the
same outcome, and the runtime model's `setAt` returns an in-place result with the
correspondence preserved.

The accounting contracts are model-layer statements, not premises of
`principal_write`. `Accounted` is the complete relation; it implies the retained
predicates (`Accounted.ownersAccounted`, `Accounted.countFidelity`) and supplies
the count-one dichotomy, and `principal_accounted` below consumes it at the
initializer. Nothing here transports that relation into a runtime guarantee: the
two heaps in the conclusion are formally defined models, and the linked C runtime
and the emitted recursive callee are outside this theorem.

`Prefix.toModel_supported` places the certified flat model in the counted
fragment.
-/
import OwnershipLcnf.Semantics
import OwnershipLcnf.RuntimeModel
import Ownership.Accounting
import Ownership.CompleteAccounting

set_option linter.unusedVariables false

namespace OwnershipLcnf

open Ownership

/-- The flat recognised write: model in-place, LCNF in-place, and runtime-model
in-place, under the entry invariant, the correctness-agreement premise and the
primitive contracts. The accounting contracts are not premises: they are
consequences of `Accounted`, consumed by `principal_accounted`. -/
theorem principal_write
    {code : Lean.Compiler.LCNF.Code Lean.Compiler.LCNF.Purity.impure}
    {p : Prefix} {assign : Lean.FVarId → Var}
    (hproj : projectPrefix code = some p) (hl : Layout assign p)
    (s : Machine) (env : Env) (H : Heap)
    (root : Ref) (client : List Ref) (i v : Nat) (o : Obj)
    (hEntry : Entry.EntryInv H env (Runner.initCtx root) root client)
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

/-- The certified flat model is in the counted fragment: the recognised
prefix's projected model binds the exclusivity check's result, writes through it
and returns it, which `Supported` admits from the initializer's own slots. -/
theorem Prefix.toModel_supported {root : Ownership.Ref}
    (assign : Lean.FVarId → Ownership.Var) (p : Prefix) (hl : Layout assign p) :
    Supported (Runner.initCtx root) (p.toModel assign) := by
  show Supported (Runner.initCtx root)
    (.let (assign p.checkResult) (.checkAlias (assign p.array))
      (.setArr (assign p.checkResult) (assign p.index) (assign p.value)
        (.ret (assign p.checkResult))))
  refine Supported.bindAlias (c := Runner.initCtx root) (x := assign p.array)
    (y := assign p.checkResult)
    (k := .setArr (assign p.checkResult) (assign p.index) (assign p.value)
      (.ret (assign p.checkResult))) ?_ ?_ ?_
  · rw [hl.array]
    exact Runner.initCtx_us_zero root
  · rw [hl.check]
    simp [Runner.initCtx]
  · refine Supported.setArr
      ((Runner.initCtx root).move (assign p.array) (assign p.checkResult))
      (assign p.checkResult) (assign p.index) (assign p.value)
      (.ret (assign p.checkResult)) ?_
    refine Supported.ret _ (assign p.checkResult) ?_
    rw [Ctx.move_us_y, hl.array]
    exact Or.inl (Runner.initCtx_us_zero root)

/-- The accounting relation is consumed rather than assumed: at the initializer
it yields the environment-side predicate, the count-fidelity equation at the
relation's own support (what the removed `hcount` premise asserted), and the
count-one dichotomy at the root reference, whose checker count is one. -/
theorem principal_accounted {support : List Var} {H : Heap} {root : Ref}
    (h : Accounted support H (Runner.initEnv root) (Runner.initCtx root)) :
    OwnersAccounted (Runner.initCtx root) ∧
      CountFidelity H (Runner.initCtx root) support ∧
      ((EnvOwnerCount (Runner.initCtx root) support root = 1 ∧
          IncomingCount H root = 0) ∨
        (EnvOwnerCount (Runner.initCtx root) support root = 0 ∧
          IncomingCount H root = 1)) := by
  have hmul : (Runner.initCtx root).mult root = 1 := by simp [Runner.initCtx]
  exact ⟨h.ownersAccounted, h.countFidelity, h.count_one_dichotomy hmul⟩

end OwnershipLcnf
