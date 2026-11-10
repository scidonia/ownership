/-
The suspended-frame inconsistency, as a regression.

`counted_nested_chain_two_levels` asks for complete accounting of the inner call's
heap under `Nested.isolatedCtx`. That context makes the suspended parent's variable
dead while the parent's count-one cell remains in the heap, so for the parent the
inner equation would read 1 = 0 + 0. The first theorem below proves the general
impossibility; the second instantiates it on the outer entry and the isolated
assumption that the two-level theorem takes, deriving `False`.

The two-level composition statement is therefore recorded as not usable: its
premise is inconsistent, and kernel acceptance of the implication says nothing
about an instance. The net edge effect (`counted_nested_chain_edges`) is unaffected.

Counterproof from the review of revision `aaaa0aa`, kernel-checked here.
-/
import Ownership.CountedNested

open Ownership

/-- Global accounting cannot forget the suspended parent's root while retaining
its count-one cell in the heap. -/
theorem isolated_accounting_impossible
    {support supportIn : List Var} {H : Heap} {env envIn : Env} {c : Ctx}
    {owner state path value : Var} {r child : Ref}
    (hacc : Accounted support H env c)
    (howned : c.us owner = .owned) (href : c.refOf owner = some r)
    (hm : c.mult r = 1) (hne : r ≠ child) :
    ¬ Accounted supportIn H envIn (Nested.isolatedCtx c state path value child) := by
  intro hinner
  have hmem : owner ∈ support := hacc.support_complete owner howned
  have hf : owner ∈ support.filter (fun z => c.us z = .owned ∧ c.refOf z = some r) := by
    rw [List.mem_filter]
    exact ⟨hmem, by simp [howned, href]⟩
  have hpos : 0 < EnvOwnerCount c support r := by
    exact List.length_pos_iff_exists_mem.mpr ⟨owner, hf⟩
  have hsum := hacc.mult_eq r
  rw [hm] at hsum
  have hincoming : IncomingCount H r = 0 := by omega
  have hzero :
      EnvOwnerCount (Nested.isolatedCtx c state path value child) supportIn r = 0 := by
    unfold EnvOwnerCount
    have hno : ∀ z, ¬ ((Nested.isolatedCtx c state path value child).us z = .owned ∧
        (Nested.isolatedCtx c state path value child).refOf z = some r) := by
      intro z
      by_cases hz : z = state
      · subst z
        simp [Nested.isolatedCtx, Ne.symm hne]
      · simp [Nested.isolatedCtx, hz]
    simp [hno]
  have hsumIn := hinner.mult_eq r
  change c.mult r = IncomingCount H r +
    EnvOwnerCount (Nested.isolatedCtx c state path value child) supportIn r at hsumIn
  rw [hm, hincoming, hzero] at hsumIn
  omega

#print axioms isolated_accounting_impossible

/-- The outer chain entry and the isolated-accounting assumption of
`counted_nested_chain_two_levels` are jointly inconsistent. -/
theorem two_level_isolated_entry_impossible
    {support supportIn : List Var} {H : Heap} {env : Env} {c : Ctx}
    {a i fst snd path value result restored : Var} {r child : Ref}
    {o : Obj} {idx : Nat} {body : Nested.NCode} {ctx' : Ctx}
    (hacc : Accounted support H env c)
    (hchk : Nested.checkN c
      (chain a i fst snd child path value result restored body) = some ctx')
    (hr : c.refOf a = some r) (hcell : H.cells r = some o)
    (hslot : o.fields[idx]? = some (.ref child))
    (hinner : Accounted supportIn (CountedPair.protocol H r child idx).2
      (Nested.isolateEnv ((env.set fst (.ref r)).set snd (.ref child)) snd path value)
      (Nested.isolatedCtx ((c.move a fst).bindOwned snd child) snd path value child)) :
    False := by
  obtain ⟨ha, hma, _, he, hfstDead, hsndDead, hfs, rchk, hrchk, _, _, _⟩ :=
    Nested.checkNF_takeOut_some (ctx' := ctx')
      (show Nested.checkNF c [] (Nested.NCode.takeOut a i fst snd child
        (.callAt snd path value result body (.putBack fst result i restored (.ret restored)))) =
        some ctx' from hchk)
  have hrr : rchk = r := Option.some.inj (hrchk.symm.trans hr)
  subst rchk
  have hfst : c.us fst ≠ .owned := by rw [hfstDead]; decide
  have hsnd : c.us snd ≠ .owned := by rw [hsndDead]; decide
  obtain ⟨oc, hb⟩ := restorationBoundary_of_accounted hacc ha hma hr he hcell hslot
  have hB := (counted_takeOut hacc ha hma hr he hfst hsnd hfs hb.distinct.symm
    hcell hslot).1
  have howned : ((c.move a fst).bindOwned snd child).us fst = .owned := by
    simp [Ctx.bindOwned, Ctx.move, hfs, ha]
  have href : ((c.move a fst).bindOwned snd child).refOf fst = some r := by
    simp [Ctx.bindOwned, Ctx.move, hfs, hr]
  have hm : ((c.move a fst).bindOwned snd child).mult r = 1 := by
    change c.mult r = 1
    simpa [Ctx.multOf, hr] using hma
  exact isolated_accounting_impossible hB howned href hm hb.distinct hinner

#print axioms two_level_isolated_entry_impossible
