/-
The composed principal guarantee for the recognised flat write, and the nested
guarantee for one level of a finite supported path.

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
and the emitted recursive callee are outside these theorems.

`principal_supported_path` is the nested companion, for one arbitrary level of a
finite supported path. It composes the recognised prefix's model correspondence
(`index_path_simulates_model`), the counted extraction/call/restoration protocol
(`counted_nested_chain`) and the counted interpreter's recognised-prefix boundary
(`execCounted_protocol_boundary`) under one completely accounted entry and one
explicitly contractual child call (`CountedChildCall`, N10). Its premises are the
level list's data (`PathContract`), the layout and the recogniser's verdict at
this level, the initial machine/model agreement, and the accounted entry; the
child call is the recursion hypothesis and the emitted callee's body is not
captured. The conclusion is the reached in-place store: the boundary and final
accounting, the pair release and cursor, both exclusive targets, the mutate
disposition, the functional restoration and its restored slot, the model run's
own completion and its copy-free trace, the counted prefix's boundary, and the
child frame and restoration locality.

`Prefix.toModel_supported` places the certified flat model in the counted
fragment.
-/
import OwnershipLcnf.Semantics
import OwnershipLcnf.RuntimeModel
import Ownership.Accounting
import Ownership.CompleteAccounting
import OwnershipLcnf.PathRecursion
import OwnershipLcnf.CountedTrace

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

/-- The certified flat model is in the counted fragment: the recognised prefix's
projected model binds the exclusivity check's result to the check slot, writes
through it and returns it. Its premises are read off the layout — the alias
source is the count-one owned handle at the array slot, and the store's four
premises hold at the moved context, where the check result carries that handle
and the index and replacement slots are scalars. -/
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
      (.ret (assign p.checkResult))) ?_ ?_ ?_ ?_
  · rw [hl.array]
    exact Runner.initCtx_us_zero root
  · rw [hl.array]
    exact Runner.initCtx_multOf_zero root
  · rw [hl.check]
    simp [Runner.initCtx]
  · refine Supported.setArr
      ((Runner.initCtx root).move (assign p.array) (assign p.checkResult))
      (assign p.checkResult) (assign p.index) (assign p.value)
      (.ret (assign p.checkResult)) ?_ ?_ ?_ ?_ ?_
    · rw [hl.check, Ctx.move_us_y, hl.array]
      exact Runner.initCtx_us_zero root
    · rw [hl.check, Ctx.multOf, Ctx.move_refOf_y, hl.array]
      exact Runner.initCtx_multOf_zero root
    · rw [hl.index, hl.check, hl.array]
      simp [Ctx.move, Runner.initCtx]
    · rw [hl.value, hl.check, hl.array]
      simp [Ctx.move, Runner.initCtx]
    · refine Supported.ret _ (assign p.checkResult) ?_
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

/-! ## The nested principal guarantee -/

/-- The nested principal guarantee, for one arbitrary level of a finite
supported path.

The recognised prefix at this level is related to the model's run of the whole
path (`index_path_simulates_model`), the counted extraction/call/restoration
protocol is composed at the same entry (`counted_nested_chain`), and the counted
interpreter's recognised prefix reports the protocol's boundary
(`execCounted_protocol_boundary`). The level list, the level, the selected index,
the call's value and path scalars and the leaf body are parameters: this is not a
fixture instance.

Premise suppliers: `hproj` the recogniser's verdict on `code`; `hl`/`hm` the
emitted fresh binders and this level's operand identification; `hag` the initial
machine/model agreement; `hpath` the level list's data and the leaf body's
contract; `hacc` the accounted entry; `hcall` the child-call boundary of
`Ownership.CountedChildCall`, which is a contract on the admitted model body the
recursive call runs (N10) and not on the emitted callee. The emitted callee's
body is not captured, so termination is contractual and the trace agreement is
the recognised prefix's alone.

The conclusion is the reached in-place store. Group 1 is the recognition-to-model
correspondence (`trace`, `run`, `copyFree`); Group 2 the counted protocol's
boundary and final accounting, pair release, cursor, both exclusive targets, the
mutate disposition, the functional restoration and its restored slot, and the
post-call `HeapCompat`; Group 3 the counted interpreter's recognised-prefix
boundary; Group 4 the child call's frame and the restoration's locality. The
whole-path outside-`MutableFootprint H rA` non-growth is not concluded: it needs
the leaf's write account (`WritesIn`). -/
theorem principal_supported_path
    {code : Lean.Compiler.LCNF.Code Lean.Compiler.LCNF.Purity.impure}
    {p : NestedPrefix} {assign : Lean.FVarId → Ownership.Var}
    (declName takeOut : Lean.Name)
    (hproj : projectNested declName takeOut code = some p)
    (hl : NestedLayout assign p)
    (path value : Ownership.Var) (body : Ownership.Nested.NCode)
    (rest : List Ownership.Path.Level) (l : Ownership.Path.Level)
    (s : NestedMachine) (mEnv : Ownership.Env) (H : Ownership.Heap)
    (rA : Ownership.Ref) (o : Ownership.Obj) (i v pv : Nat)
    (childRef : Ownership.Ref)
    (hm : LevelMatch assign p l path value rA o i childRef)
    (hag : NestedAgrees assign p s mEnv H rA i v pv)
    (c : Ownership.Ctx) (tip : Ownership.Ref) (cb : Ownership.Ctx) (y : Ownership.Var)
    (hpath : PathContract path value body tip l rest H mEnv c cb y)
    {support : List Ownership.Var}
    (hacc : Ownership.Accounted support H mEnv c)
    {Hout : Ownership.Heap}
    (hcall : Ownership.CountedChildCall
      (Ownership.CountedPair.protocol H rA childRef i).2 Hout
      ((mEnv.set l.parentVar (.ref rA)).set l.childVar (.ref childRef))
      ((c.move l.arrayVar l.parentVar).bindOwned l.childVar childRef)
      l.childVar path value (Ownership.Path.build path value body rest) rA childRef
      (l.childVar :: Ownership.replaceVar support l.arrayVar l.parentVar)) :
    ∃ Hm envm ws Hf,
      -- Group 1: recognition to the model's run of the whole path
      NestedOutcome.ofExec assign p
          (execNestedAST declName takeOut assign
            (Ownership.Path.build path value body rest) p code s) =
        some (NestedOutcome.ofModel
          (Ownership.Nested.runN (Ownership.Path.build path value body (l :: rest)) mEnv H)) ∧
      Ownership.Nested.runN (Ownership.Path.build path value body (l :: rest)) mEnv H =
        .done Hm envm (.ref rA) ws ∧
      (∀ w ∈ ws, w.2 = true) ∧
      -- Group 2: the counted protocol at the boundary and at the end
      Ownership.Accounted
        (l.childVar :: Ownership.replaceVar support l.arrayVar l.parentVar)
        (Ownership.CountedPair.protocol H rA childRef i).2
        ((mEnv.set l.parentVar (.ref rA)).set l.childVar (.ref childRef))
        ((c.move l.arrayVar l.parentVar).bindOwned l.childVar childRef) ∧
      Ownership.HeapCompat (Ownership.CountedPair.protocol H rA childRef i).2
        (Ownership.Path.blankLevel H l) ∧
      (Ownership.CountedPair.protocol H rA childRef i).2.cells H.next = none ∧
      (Ownership.CountedPair.protocol H rA childRef i).2.next = H.next + 1 ∧
      Ownership.Heap.Exclusive (Ownership.CountedPair.protocol H rA childRef i).2 rA ∧
      Ownership.Heap.Exclusive (Ownership.CountedPair.protocol H rA childRef i).2 childRef ∧
      Ownership.PutBack.disposition? Hout rA i = some .mutate ∧
      Ownership.PutBack.putBack Hout rA i childRef = some (rA, Hf) ∧
      Hf = Ownership.PutBack.mutate Hout rA (Ownership.PutBack.parentAfter o i) i childRef ∧
      ((Ownership.PutBack.parentAfter o i).fields.setIfInBounds i (.ref childRef))[i]? =
        some (.ref childRef) ∧
      Ownership.Accounted
        ((Ownership.replaceVar
            (Ownership.replaceVar
              (l.childVar :: Ownership.replaceVar support l.arrayVar l.parentVar)
              l.childVar l.resultVar) l.parentVar l.restoredVar).erase l.resultVar)
        Hf
        ((((mEnv.set l.parentVar (.ref rA)).set l.childVar (.ref childRef)).set
            l.resultVar (.ref childRef)).set l.restoredVar (.ref rA))
        (((((c.move l.arrayVar l.parentVar).bindOwned l.childVar childRef).move
            l.childVar l.resultVar).move l.parentVar l.restoredVar).setUs l.resultVar .dead) ∧
      Ownership.HeapCompat Hf Hm ∧
      -- Group 3: the counted interpreter's recognised prefix
      (execCounted assign (Ownership.Path.build path value body rest)
          (countedPrefix p.fragment) s).1.heap =
        (Ownership.CountedPair.protocol s.heap rA childRef i).2 ∧
      Ownership.HeapCompat
        (execCounted assign (Ownership.Path.build path value body rest)
          (countedPrefix p.fragment) s).1.heap
        (s.heap.set rA { o with fields := o.fields.setIfInBounds i (.scalar 0) }) ∧
      (execCounted assign (Ownership.Path.build path value body rest)
          (countedPrefix p.fragment) s).1.env =
        (execNested assign (Ownership.Path.build path value body rest)
          (countedPrefix p.fragment) s).1.env ∧
      (execCounted assign (Ownership.Path.build path value body rest)
          (countedPrefix p.fragment) s).1.nodes =
        (execNested assign (Ownership.Path.build path value body rest)
          (countedPrefix p.fragment) s).1.nodes ∧
      (execCounted assign (Ownership.Path.build path value body rest)
          (countedPrefix p.fragment) s).1.pairs =
        (execNested assign (Ownership.Path.build path value body rest)
          (countedPrefix p.fragment) s).1.pairs ∧
      (execCounted assign (Ownership.Path.build path value body rest)
          (countedPrefix p.fragment) s).1.callPath =
        (execNested assign (Ownership.Path.build path value body rest)
          (countedPrefix p.fragment) s).1.callPath ∧
      (execCounted assign (Ownership.Path.build path value body rest)
          (countedPrefix p.fragment) s).1.childVar =
        (execNested assign (Ownership.Path.build path value body rest)
          (countedPrefix p.fragment) s).1.childVar ∧
      (execCounted assign (Ownership.Path.build path value body rest)
          (countedPrefix p.fragment) s).1.writes =
        (execNested assign (Ownership.Path.build path value body rest)
          (countedPrefix p.fragment) s).1.writes ∧
      -- Group 4: the child call's frame and the restoration's locality
      (∀ q, ¬ Ownership.Entry.MutableFootprint
          (Ownership.CountedPair.protocol H rA childRef i).2 childRef q →
        Hout.cells q = (Ownership.CountedPair.protocol H rA childRef i).2.cells q) ∧
      (∀ q, q ≠ rA → Hf.cells q = Hout.cells q) := by
  -- the level's slot facts at the entry heap
  obtain ⟨hcellSlot, hslotSlot, -⟩ := hpath.slots l (by simp)
  have hr : c.refOf l.arrayVar = some rA := by
    rw [hpath.levelCtx.ref_arr, hm.arr]
  have hcell : H.cells rA = some o := by
    simpa [hm.arr, hm.obj] using hcellSlot
  have hslot : o.fields[i]? = some (.ref childRef) := by
    simpa [hm.obj, hm.idx, hm.child] using hslotSlot
  have hidx : mEnv l.indexVar = some (.scalar i) := by
    obtain ⟨-, h, -⟩ := hpath.envok.1
    rw [hm.idx] at h
    exact h
  have hmultChild : c.mult childRef = 1 := by
    rw [← hm.child]
    exact hpath.levelCtx.mult_child
  have hmultArr : c.mult rA = 1 := by
    rw [← hm.arr]
    exact hpath.levelCtx.mult_arr
  -- the taken-out child's cell, the boundary's distinctness, and the two heap
  -- facts `Accounted` supplies
  obtain ⟨_, hb⟩ := restorationBoundary_of_accounted hacc hpath.levelCtx.us_arr
    (by unfold Ownership.Ctx.multOf; rw [hpath.levelCtx.ref_arr]; exact hpath.levelCtx.mult_arr)
    hr hmultChild hcell hslot
  have hne : rA ≠ childRef := hb.distinct
  have hccNone : H.cells childRef ≠ none :=
    hacc.inv.rc_ne_zero (by rw [hmultChild]; exact Nat.le_refl 1)
  obtain ⟨oc, hcc⟩ : ∃ oc, H.cells childRef = some oc := by
    cases h : H.cells childRef with
    | none => exact absurd h hccNone
    | some oc => exact ⟨oc, rfl⟩
  have hnextH : H.cells H.next = none := by
    cases hc : H.cells H.next with
    | none => rfl
    | some o' => exact absurd (hacc.domain H.next o' hc) (Nat.lt_irrefl H.next)
  have hexH : H.exclusive? rA = true :=
    (Ownership.Heap.exclusive?_eq_true).mpr (hacc.inv.exclusive hmultArr)
  -- the chain's checker acceptance, derived from the path's own discipline
  have hbuild : Ownership.Nested.checkNF c []
      (Ownership.Path.build path value body (l :: rest)) =
      some (Ownership.PathConsolidation.levelFinal c l) :=
    Ownership.PathConsolidation.checkNF_build rest l hpath.levelCtx hpath.shapes
      hpath.counts hpath.chained hpath.checkBody hpath.retBody hpath.retOwned
      hpath.retRef hpath.endsAt hpath.countFree
  have hchainBuild : Ownership.chain l.arrayVar l.indexVar l.parentVar l.childVar childRef
      path value l.resultVar l.restoredVar (Ownership.Path.build path value body rest) =
      Ownership.Path.build path value body (l :: rest) := by
    simp [Ownership.chain, Ownership.Path.build, hm.child]
  have hchk : Ownership.Nested.checkN c
      (Ownership.chain l.arrayVar l.indexVar l.parentVar l.childVar childRef path value
        l.resultVar l.restoredVar (Ownership.Path.build path value body rest)) =
      some (Ownership.PathConsolidation.levelFinal c l) := by
    rw [hchainBuild, Ownership.Nested.checkN]
    exact hbuild
  -- Group 2: the counted chain
  obtain ⟨Hf, Hm₂, envm₂, vm, ws₂, hcAccB, hcCompatB, hcPair, hcCursor, hcExP,
    hcExC, hcDisp, hcPb, hcRestored, hcAccF, hcRun, hcCopyFree, hcCompatF⟩ :=
    counted_nested_chain (a := l.arrayVar) (i := l.indexVar) (fst := l.parentVar)
      (snd := l.childVar) (eR := childRef) (path := path) (x := value)
      (result := l.resultVar) (restored := l.restoredVar) (r := rA) (o := o)
      (idx := i) (Hout := Hout) (ctx' := Ownership.PathConsolidation.levelFinal c l)
      (body := Ownership.Path.build path value body rest)
      hacc hchk hr hcell hslot hidx hcall
  -- the restored slot, from the chain's own restoration statement
  obtain ⟨-, hslotOut⟩ := counted_nested_chain_restoration
    (a := l.arrayVar) (i := l.indexVar) (fst := l.parentVar) (snd := l.childVar)
    (eR := childRef) (path := path) (x := value) (result := l.resultVar)
    (restored := l.restoredVar) (r := rA) (o := o) (idx := i) (Hout := Hout)
    (ctx' := Ownership.PathConsolidation.levelFinal c l)
    (body := Ownership.Path.build path value body rest)
    hacc hchk hr hcell hslot hidx hcall
  -- the boundary's compatibility is the blanked level
  have hcCompatBlank : Ownership.HeapCompat
      (Ownership.CountedPair.protocol H rA childRef i).2
      (Ownership.Path.blankLevel H l) := by
    simpa [Ownership.Path.blankLevel, hm.arr, hm.obj, hm.idx] using hcCompatB
  -- Group 1: the recogniser's model correspondence
  obtain ⟨htrace, Hm₁, envm₁, ws₁, hrun₁, hcopy₁⟩ :=
    index_path_simulates_model declName takeOut assign p code hproj hl path value body
      rest l s mEnv H rA o i v pv childRef hm hag c tip cb y hpath
  -- both runs are the same term: the chain is the build, at the same entry
  have hrunEq : Ownership.Nested.runN
      (Ownership.chain l.arrayVar l.indexVar l.parentVar l.childVar childRef path value
        l.resultVar l.restoredVar (Ownership.Path.build path value body rest)) mEnv H =
      Ownership.Nested.runN (Ownership.Path.build path value body (l :: rest)) mEnv H := by
    rw [hchainBuild]
  have hrunChain : Ownership.Nested.runN
      (Ownership.Path.build path value body (l :: rest)) mEnv H =
      .done Hm₂ envm₂ vm ws₂ := by
    rw [← hrunEq]
    exact hcRun
  -- the two runs coincide at the counted chain's model witnesses
  have hdoneEq : (Ownership.Res.done Hm₂ envm₂ vm ws₂) =
      (Ownership.Res.done Hm₁ envm₁ (.ref rA) ws₁) := hrunChain ▸ hrun₁
  injection hdoneEq with _ _ hvm hws
  have hrunG1 : Ownership.Nested.runN
      (Ownership.Path.build path value body (l :: rest)) mEnv H =
      .done Hm₂ envm₂ (.ref rA) ws₂ := by
    rw [← hvm]
    exact hrunChain
  have hcopyG1 : ∀ w ∈ ws₂, w.2 = true := by
    intro w hw
    rw [hws] at hw
    exact hcopy₁ w hw
  -- Group 3: the counted interpreter's recognised prefix at this machine
  have hb3 := execCounted_protocol_boundary (assign := assign) (p := p)
    (body := Ownership.Path.build path value body rest) (s := s) (rA := rA)
    (childRef := childRef) (idx := i) (o := o) (oc := oc) hl
    hag.array_machine hag.nodes (by rw [hag.heap]; exact hcell)
    (by rw [hag.heap]; exact hcc) hslot hne (by rw [hag.heap]; exact hnextH)
    (by rw [hag.heap]; exact hexH)
  refine ⟨Hm₂, envm₂, ws₂, Hf, htrace, hrunG1, hcopyG1, hcAccB, hcCompatBlank,
    hcPair, hcCursor, hcExP, hcExC, hcDisp, hcPb, hcRestored, hslotOut, hcAccF,
    hcCompatF, hb3.1, hb3.2.1, hb3.2.2.1, hb3.2.2.2.1, hb3.2.2.2.2.1,
    hb3.2.2.2.2.2.1, hb3.2.2.2.2.2.2.1, hb3.2.2.2.2.2.2.2, hcall.call.confined, ?_⟩
  intro q hq
  rw [hcRestored]
  exact Ownership.Heap.set_other (H := Hout) (r := rA) (r' := q) _ hq

end OwnershipLcnf
