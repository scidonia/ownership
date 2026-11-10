# Ownership review at aaaa0aa

Reviewed: 10 November 2026  
Revision: `aaaa0aa9becdc9db4c41386fa3e129b93c48d68c`  
Comparison: the previous review at `48a1ac0`  
Purpose: assess the current ITP manuscript and implementation, including the latest cost-model and alias-check claims.

## Assessment

The core work is materially stronger. The whole counted-fragment correspondence is now present, post-call accounting is derived from a call's edge effect, the one-level example has a parameterised family, and the manuscript uses LIPIcs with conventional theorem statements and useful figures. The old criticism that counted correspondence stops at pair release is no longer applicable.

There are, however, three concrete issues to fix before treating the current manuscript as ready. The most serious is an inconsistent premise in the two-level composition theorem. The new surface checker also accepts ownership violations, and the latest runtime-cost wording misidentifies the measured unit.

These findings do not invalidate the inhabited one-level counted-fragment theorem. They limit additional claims made around it.

## Verification performed for this review

- Built `Ownership`, `OwnershipLcnf`, and `OwnershipTest` together using the official Lean 4.35.0-rc3 release: success, 58 jobs.
- Ran `scripts/check_axioms.lean`: 188 axiom-audit declarations, with only `propext`, `Classical.choice`, and `Quot.sound` appearing.
- Compiled the current `bench/Alias.lean` and ran three added source counterexamples: all were accepted.
- Kernel-checked two additional lemmas, reproduced below, proving the isolated-accounting contradiction and its application to the outer premises used by the two-level theorem. Their axiom footprint is the same standard set.
- Inspected the current PDF and its source. It is a 17-page A4 LIPIcs document, with references on page 17; the opening and simulation figure have substantially improved.

The Lean checks used the matching release directly, not the Nix shell. The sibling-dependent backend/runtime gates and the runtime benchmarks were not freshly rerun. No tracked repository files were modified by this review.

## 1. Major: two-level composition has inconsistent premises

Location: `Ownership/CountedNested.lean`, `counted_nested_chain_two_levels`, especially its `haccIn` premise at lines 1499–1501.

At the outer counted boundary, the parent and child have owning handles in the caller context. The parent is count one. Complete accounting therefore says it has one owning root and zero incoming heap edges.

The theorem then requires complete accounting of the same heap under the inner call's `isolatedCtx`. That context makes the suspended parent's variable dead, exposes only the child reference as owned, and retains the caller's multiplicities. Nothing removes the parent cell or its stored count.

For the parent, the inner accounting equation consequently requires:

```text
1 = 0 incoming edges + 0 owning roots
```

This is a contradiction. It is not merely a missing fixture or an inconvenient assumption. The second lemma below derives `False` from a subset of the outer theorem's premises, including the requested isolated `Accounted` state. Its body parameter can be instantiated with the nested inner chain appearing in `counted_nested_chain_two_levels`.

Lean accepts the existing composition theorem because an implication from inconsistent premises can be proved. Kernel acceptance alone does not establish that such a theorem has an applicable instance. The closed one-level fragment instance does not discharge this two-level premise.

### Repair

Separate the child's permission to access a handle from the global accounting of existing owners. Two possible implementations are:

- Keep a global ownership ledger while the local checker/environment is isolated; prove the relation between local permissions and that ledger.
- Extend accounting with a suspended-frame owner component. At call entry, transfer the inaccessible caller owners into that component; at return, restore the caller's active ownership. The frame component must come from actual caller ownership, not arbitrary ghost credits.

The count equation then includes the suspended parent even while the child cannot name it. Add a genuine closed depth-two counted instance after repairing the theorem, with all premises inhabited. Retain the impossibility lemma as a regression documenting why dropping framed roots is invalid.

Until the repair exists, describe `counted_nested_chain_two_levels` as an unusable composition statement and remove claims that it demonstrates executable two-level counted composition. The one-level counted result and the net edge-effect theorem remain valuable.

## 2. Major for the new surface claim: alias checking is insufficient

Location: `bench/Alias.lean`, particularly `uses` at lines 37–58; the final workflow paragraph in manuscript Section 7; the corresponding claims in `bench/README.md` and `AGENTS.md`.

The checker counts consuming occurrences and ignores borrowed reads. It does not track whether a particular owner has already been consumed. It also explicitly omits uses in an `ite` condition.

All three commands below were accepted by the actual checker on the pinned Lean release:

```lean
import Alias

-- The old array is read after the consuming write.
#alias_check (fun (a : Array Nat) =>
  let b : Array Nat := a.set! 0 1
  (b, a.getD 0 0))

-- The condition consumes the array; the branch still uses it.
#alias_check (fun (a : Array Nat) =>
  if (a.set! 0 1).getD 0 0 = 1 then a else a.set! 1 2)

-- Repeated element reads introduce aliases in separate array binders.
#alias_check (fun (outer : Array (Array Nat)) =>
  let a : Array Nat := outer.getD 0 #[]
  let b : Array Nat := outer.getD 0 #[]
  (a.set! 0 1, b))
```

The first example already lies within the simple `Array Nat` surface: its failure cannot be attributed only to unsupported arrays stored inside structures. Counting one move does not make subsequent reads of the old owner legal. A compiler may need to preserve the original value for those reads and copy at the write. The second case violates the checker's intended use discipline because condition effects are not counted. The third demonstrates why fresh binder names alone do not establish fresh ownership of their referents.

This review establishes acceptance of these examples, not a particular compiled allocation trace for each example. They suffice to refute the current claimed ownership-use property of the checker. Its separate connection to actual RC=1 also has no proved source-to-model bridge.

### Repair

Use a forward ownership-state analysis: borrowing requires an available owner, consuming a binding makes the old binding unavailable, conditions are analysed before their branches, and branch outputs must merge compatible usage states. Calls and projections need specified ownership effects; a read returning an array reference cannot automatically create an independent exclusive owner. Include elaborated type aliases and supported expression forms in the coverage decision.

Pair each negative example with an accepted variant, such as reading the old value before moving the array or reading through the returned updated binding.

For the paper now, label the macro an experimental usage checker and remove the statement that it discharges the model's multiplicity-one premise. There is no need to make a complete Lean surface checker a prerequisite for the existing mechanisation paper.

## 3. Runtime evidence: correct the unit and the crossover claim

Locations: `bench/UnionFind.lean:115`, `bench/README.md`, manuscript Section 7's new cost-model paragraph.

The benchmark prints `best / m`. Here `m` is the number of outer union-find iterations, not the number of `Array.set!` calls. Each iteration runs two finds, which can perform multiple path-halving stores, and some iterations perform no union store. The shared snapshot is created specifically on successful union branches.

Consequently, the 66–75 ns and 559–5288 ns values are per outer union-find iteration, including its other work. They are not measured latency per array update. The reported ratio is a useful comparison of the two whole benchmark variants at equal input sizes and iteration counts, subject to the experiment's stated limitations.

The suggested expressions

```text
unique ≈ 70 ns
shared ≈ 70 ns + 0.3 ns × n
```

do not cross near `n = 230`: the shared expression exceeds the unique expression for every positive `n`. Approximately 230 is where the extra linear term equals the estimated fixed term. It is also below the smallest reported size, 2000, so it is an extrapolated overhead scale, not an observed crossover.

### Repair

- Relabel the numbers as ns per union-find iteration/union attempt.
- If reporting a per-store coefficient or copy bandwidth, instrument actual stores and copying dispositions first. The current amortised coefficient does not directly measure either quantity.
- Retain the qualitative result that the shared workload scales with array size while the unshared workload is much flatter over the measured range.
- Describe any fitted formula as a rough workload-level summary, report the method and range, and remove the crossover wording.
- Keep the benchmark outside the certified fragment, as the paper already states. The source emitter's checker acceptance and output agreement likewise do not prove preservation of RC=1 through Lean compilation.

### Additional generated-benchmark concern: retained input

The generated timing harness defines:

```lean
let mk : IO (Array Nat) := pure ((List.replicate n 0).toArray)
```

and invokes that same action in repeated trials. This can retain one input array across trials. I compiled and ran a small native program using that exact construction/repetition pattern with an instrumented single update. The input address repeated across trials, each updated output had a different address, and the generated C inserted `lean_inc_ref` immediately before `lean_array_set`.

An exclusivity read earlier in that native program returned `true`: the increment was inserted later, at the consuming update. Thus a borrowed count check before the timer is not by itself evidence that the write is exclusive.

This was a focused reproduction of the harness pattern, not a rerun of the full generated 4000-write binary. It is enough to require checking the generated benchmark's input lifetime and C call site before describing its roughly flat total as an in-place timing result. Prepare a genuinely exclusive input per trial outside the measured region and verify the consuming write's disposition. A first copy of the retained large array is a plausible explanation for a fixed timed cost; the existing measurements alone do not rule it out.

## What is now persuasive

The inhabited one-level result has the right shape for the paper's central conditional theorem: recognition is consumed, the full counted fragment runs through restoration and return, the final state is related to the abstract run, accounting is derived at the relevant boundaries, and a changing leaf supplies a nontrivial instance. This is meaningful progress over the previous prefix-only correspondence.

Replacing assumed post-call accounting with a specified edge effect and a derivation is also a better modular interface. The frame problem above shows exactly where that interface still needs an access/accounting distinction for recursive use.

The manuscript now looks like a proceedings paper. Its main remaining presentation issue is the breadth suggested by “unobservable updates”: `Observed` proves equality of selected observations of the counted and abstract model outcomes at the specified boundary. It does not itself establish arbitrary source-context equivalence with a separately formalised immutable-array semantics. Keep that distinction explicit when interpreting the title and conclusion.

## Immediate agent tasks

1. Repair or withdraw the two-level composition claim; design explicit accounting for suspended roots and inhabit a depth-two counted instance.
2. Reclassify the surface checker as experimental, add the accepted counterexamples as negative regressions, and implement ordered use-state checking before restoring a stronger claim.
3. Correct the benchmark units and remove the unsupported crossover interpretation.
4. Refresh the verification record at the final revision. Its base revision/date still refer to `70b325b` and 3 November while the current tree has later proof and benchmark changes.
5. Keep the paper centred on the valid counted-fragment theorem and its proof. These fixes do not require a verified C runtime or arbitrary Lean recursion.

## Appendix: kernel-checked framing counterproof

Save the following as `IsolatedAccounting.lean` outside the module tree and run it from the ownership repository with:

```bash
nix develop -c lake env lean /absolute/path/IsolatedAccounting.lean
```

It was checked after the three library targets built at the reviewed revision. Both printed axiom sets contain only `propext`, `Classical.choice`, and `Quot.sound`.

```lean
import Ownership.CountedNested

open Ownership

-- Global accounting cannot forget the suspended parent's root while retaining
-- its count-one cell in the heap.
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
  have hzero : EnvOwnerCount (Nested.isolatedCtx c state path value child) supportIn r = 0 := by
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

-- These are precisely the outer chain entry and the isolated-accounting
-- assumption used by counted_nested_chain_two_levels. The remaining premises
-- of that theorem cannot repair their inconsistency.
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
```
