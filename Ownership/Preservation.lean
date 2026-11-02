/-
Preservation through accepted execution for the counted supported fragment.

`Ownership.Supported` is check acceptance restricted to the counted constructors:
every constructor carries the checker's own rule at that constructor, plus the
accounting certificates the checker cannot see. Here the checker's acceptance is
recovered (`Ownership.supported_check`), and the run it admits is followed with the
complete accounting relation at every state it reaches (`supported_run`).

Two premises are supplied, not derived. `Accounted` is the entry relation.
`StoreSlots` is the one fact neither a checker rule nor any component of `Inv`
can see: at the store the run reaches, the array cell's selected slot holds a
scalar, so the in-place write replaces a value rather than an edge. It is
discharged at the initializer (`storeSlots_init`) and it carries the store's own
pre- and post-state (`supported_store_exclusive`).

`AccountedAlong` is the conclusion, never a hypothesis: at each instruction the
relation holds at the interpreter's own post-state, and at each array store the
target is exclusive. Its `True` clauses are of two kinds: a lookup the
interpreter faults on, which the run's fault-freedom conjunct has already
excluded — `Supported`'s premises pin every environment binding and cell the run
reads (`Inv.isRef`, `Inv.scalar`, `Inv.cell_of_ref`) — and the `.inc` and
`.dec x n` with `n ≠ 1` forms, which the fragment has no constructor for, so
`supported_run` never reaches them. No clause is vacuous under the theorem's
premises.

`AccountedEntry` packages the two entry facts a client supplies. The packaging
adds no implication: `EntryInv` does not imply `Accounted` (`aliasEntryInv` is an
`EntryInv` state no support accounts), and `Accounted` does not imply `EntryInv`
(`accountedNotEntryInv`).
-/
import Ownership.CompleteAccounting
import Ownership.Entry
import Ownership.Runner

namespace Ownership

/-! ## The supplied store-slot premise -/

/-- The scalar-slot premise the checker's `.setArr` rule cannot see: at the store
the run reaches, the array cell's selected slot holds a scalar, so the in-place
write is an edge-neutral replacement rather than an edge insertion. The
recursion follows `run`'s dispatch on `Supported` code — the fragment has no
`.inc`, and its `.dec` is always the single-count form — and is `True` where
there is nothing to justify: the `.ret` case and every lookup the interpreter
faults on. The premise is supplied from the heap and environment alone, so it may
not assume the invariant. In particular the slot must exist: an
out-of-bounds index is a silent no-op for `Array.set!`, and this premise keeps
that case outside the fragment's claim. -/
def StoreSlots (H : Heap) (env : Env) : Code → Prop
  | .ret _ => True
  | .let x (.lit n) k => StoreSlots H (env.set x (.scalar n)) k
  | .let x (.size a) k =>
      match env a with
      | some (.ref r) =>
          match H.cells r with
          | some o => StoreSlots H (env.set x (.scalar o.fields.size)) k
          | none => True
      | _ => True
  | .let x (.isShared y) k =>
      match env y with
      | some (.ref r) => StoreSlots H (env.set x (.scalar (if H.rc r > 1 then 1 else 0))) k
      | _ => True
  | .let y (.checkAlias x) k =>
      match env x with
      | some (.ref r) => StoreSlots H (env.set y (.ref r)) k
      | _ => True
  | .inc _ _ _ => True
  | .dec x _ k =>
      match env x with
      | some (.ref r) => StoreSlots (H.dec r 1) (env.erase x) k
      | _ => True
  | .check _ k => StoreSlots H env k
  | .setArr x i v k =>
      ∃ r o idx val old, env x = some (.ref r) ∧ env i = some (.scalar idx) ∧
        env v = some (.scalar val) ∧ H.cells r = some o ∧
        o.fields[idx]? = some (.scalar old) ∧
        StoreSlots (H.set r { o with fields := o.fields.set! idx (.scalar val) })
          (env.set x (.ref r)) k

/-! ## The support the run ends with -/

/-- The support the run ends with: the handle move follows the alias and the
decrement erases its variable. Every other instruction leaves the support alone,
exactly as the accounting lemmas do. -/
def resultSupport : Code → List Var → List Var
  | .ret _, support => support
  | .let y (.checkAlias x) k, support => resultSupport k (replaceVar support x y)
  | .let _ _ k, support => resultSupport k support
  | .inc _ _ k, support => resultSupport k support
  | .dec x _ k, support => resultSupport k (support.erase x)
  | .check _ k, support => resultSupport k support
  | .setArr _ _ _ k, support => resultSupport k support

/-! ## The relation along the run -/

/-- Every state the run reaches satisfies the complete relation, at the support
the step arithmetic determines; at each array store the target is exclusive.
This is a conclusion, never a hypothesis. The clauses mirror `run` one step at a
time. A clause is `True` either at a lookup the interpreter faults on — which
`supported_run`'s fault-freedom conjunct excludes — or at an instruction form the
counted fragment has no constructor for, which never reaches this predicate
because `supported_run` only instantiates it at `Supported` code. -/
def AccountedAlong (H : Heap) (env : Env) (c : Ctx) (support : List Var) : Code → Prop
  | .ret _ => Accounted support H env c
  | .let x (.lit n) k =>
      Accounted support H (env.set x (.scalar n)) (c.setUs x .scalar) ∧
        AccountedAlong H (env.set x (.scalar n)) (c.setUs x .scalar) support k
  | .let x (.size a) k =>
      match env a with
      | some (.ref r) =>
          match H.cells r with
          | some o =>
              Accounted support H (env.set x (.scalar o.fields.size)) (c.setUs x .scalar) ∧
                AccountedAlong H (env.set x (.scalar o.fields.size)) (c.setUs x .scalar)
                  support k
          | none => True
      | _ => True
  | .let x (.isShared y) k =>
      match env y with
      | some (.ref r) =>
          Accounted support H (env.set x (.scalar (if H.rc r > 1 then 1 else 0)))
              (c.setUs x .scalar) ∧
            AccountedAlong H (env.set x (.scalar (if H.rc r > 1 then 1 else 0)))
              (c.setUs x .scalar) support k
      | _ => True
  | .let y (.checkAlias x) k =>
      match env x with
      | some (.ref r) =>
          Heap.Exclusive H r ∧
            Accounted (replaceVar support x y) H (env.set y (.ref r)) (c.move x y) ∧
            AccountedAlong H (env.set y (.ref r)) (c.move x y) (replaceVar support x y) k
      | _ => True
  | .inc _ _ _ => True
  | .dec x 1 k =>
      match c.refOf x with
      | some r =>
          Accounted (support.erase x) (H.dec r 1) (env.erase x)
              ((c.dec r 1).setUs x .dead) ∧
            AccountedAlong (H.dec r 1) (env.erase x) ((c.dec r 1).setUs x .dead)
              (support.erase x) k
      | none => True
  | .dec _ _ _ => True
  | .check _ k => Accounted support H env c ∧ AccountedAlong H env c support k
  | .setArr x i v k =>
      match env x, env i, env v with
      | some (.ref r), some (.scalar idx), some (.scalar val) =>
          match H.cells r with
          | some o =>
              Heap.Exclusive H r ∧
                Accounted support
                    (H.set r { o with fields := o.fields.set! idx (.scalar val) })
                    (env.set x (.ref r)) c ∧
                  AccountedAlong
                    (H.set r { o with fields := o.fields.set! idx (.scalar val) })
                    (env.set x (.ref r)) c support k
          | none => True
      | _, _, _ => True

/-! ## The checker accepts the fragment -/

/-- `Supported` implies checker acceptance: each constructor carries the checker's
rule at that constructor together with the accounting certificates the checker
cannot see — `bindLit` has no checker premise, so its premise is certificate
alone. So the fragment is the counted part of the checker's accepted set. -/
theorem supported_check {c : Ctx} {s : Code} (h : Supported c s) :
    ∃ c', check c s = some c' := by
  induction h with
  | ret c x hx => exact ⟨c, by simp [check, hx]⟩
  | bindLit c x n k hx hk ih =>
    obtain ⟨c', hc'⟩ := ih
    exact ⟨c', hc'⟩
  | bindSize c x a r k hx ha hr hk ih =>
    obtain ⟨c', hc'⟩ := ih
    exact ⟨c', by simp [check, hr, ha, hc']⟩
  | bindShared c x y r k hx hy hr hk ih =>
    obtain ⟨c', hc'⟩ := ih
    exact ⟨c', by simp [check, hr, hy, hc']⟩
  | bindAlias c x y k hx hm hy hk ih =>
    obtain ⟨c', hc'⟩ := ih
    exact ⟨c', by simp [check, hx, hm, hc']⟩
  | check c x k hx hm hk ih =>
    obtain ⟨c', hc'⟩ := ih
    exact ⟨c', by simp [check, hx, hm, hc']⟩
  | setArr c x i v k hx hm hi hv hk ih =>
    obtain ⟨c', hc'⟩ := ih
    exact ⟨c', by simp [check, hx, hm, hi, hv, hc']⟩
  | decOne c x r k hx hr hlt hk ih =>
    obtain ⟨c', hc'⟩ := ih
    exact ⟨c', by simp [check, hr, hx, hlt, hc']⟩

/-! ## The headline theorem -/

/-- Preservation through accepted execution: a supported program from an
accounted state, with the store-slot premise, runs without a fault, records only
exclusive writes, satisfies the complete relation at every state it reaches, and
satisfies it at the final state at the support the step arithmetic determines. -/
theorem supported_run {c : Ctx} {s : Code} (hs : Supported c s)
    {support : List Var} {H : Heap} {env : Env}
    (hacc : Accounted support H env c) (hslots : StoreSlots H env s) :
    ∃ c' H' env' v ws,
      check c s = some c' ∧
      run s env H = .done H' env' v ws ∧
      (∀ w ∈ ws, w.2 = true) ∧
      Accounted (resultSupport s support) H' env' c' ∧
      AccountedAlong H env c support s := by
  induction hs generalizing support H env with
  | ret c x hx =>
    exact ⟨c, H, env, (env x).getD .erased, [], by simp [check, hx], rfl, by simp,
      hacc, hacc⟩
  | bindLit c x n k hx hk ih =>
    obtain ⟨c', H', env', rv, ws, hchk, hrun, hws, hpost, halong⟩ :=
      ih (Accounted.setScalar hacc n hx) hslots
    refine ⟨c', H', env', rv, ws, ?_, hrun, hws, hpost, ?_⟩
    · exact hchk
    · show Accounted support H (env.set x (.scalar n)) (c.setUs x .scalar) ∧
        AccountedAlong H (env.set x (.scalar n)) (c.setUs x .scalar) support k
      exact ⟨Accounted.setScalar hacc n hx, halong⟩
  | bindSize c x a r k hx ha hr hk ih =>
    have henv : env a = some (.ref r) := hacc.inv.isRef ha hr
    obtain ⟨o, hcell⟩ := hacc.inv.cell_of_ref ha hr
    have hslots' : StoreSlots H (env.set x (.scalar o.fields.size)) k := by
      simpa only [StoreSlots, henv, hcell] using hslots
    obtain ⟨c', H', env', rv, ws, hchk, hrun, hws, hpost, halong⟩ :=
      ih (Accounted.setScalar hacc o.fields.size hx) hslots'
    refine ⟨c', H', env', rv, ws, ?_, ?_, hws, hpost, ?_⟩
    · simpa [check, hr, ha] using hchk
    · simpa [run, henv, hcell] using hrun
    · simp only [AccountedAlong, henv, hcell]
      exact ⟨Accounted.setScalar hacc o.fields.size hx, halong⟩
  | bindShared c x y r k hx hy hr hk ih =>
    have henv : env y = some (.ref r) := hacc.inv.isRef hy hr
    have hslots' : StoreSlots H (env.set x (.scalar (if H.rc r > 1 then 1 else 0))) k := by
      simpa only [StoreSlots, henv] using hslots
    obtain ⟨c', H', env', rv, ws, hchk, hrun, hws, hpost, halong⟩ :=
      ih (Accounted.setScalar hacc (if H.rc r > 1 then 1 else 0) hx) hslots'
    refine ⟨c', H', env', rv, ws, ?_, ?_, hws, hpost, ?_⟩
    · simpa [check, hr, hy] using hchk
    · simpa [run, henv] using hrun
    · simp only [AccountedAlong, henv]
      exact ⟨Accounted.setScalar hacc (if H.rc r > 1 then 1 else 0) hx, halong⟩
  | bindAlias c x y k hx hm hy hk ih =>
    obtain ⟨r, hr, hmul⟩ := Ctx.multOf_eq_one hm
    have henv : env x = some (.ref r) := hacc.inv.isRef (Or.inl hx) hr
    have hex : Heap.Exclusive H r := hacc.inv.exclusive hmul
    have htrue : H.exclusive? r = true := Heap.exclusive?_eq_true.mpr hex
    have hslots' : StoreSlots H (env.set y (.ref r)) k := by
      simpa only [StoreSlots, henv] using hslots
    have hmoved : Accounted (replaceVar support x y) H (env.set y (.ref r)) (c.move x y) :=
      Accounted.move hacc hx hr hy
    obtain ⟨c', H', env', rv, ws, hchk, hrun, hws, hpost, halong⟩ :=
      ih hmoved hslots'
    refine ⟨c', H', env', rv, ws, ?_, ?_, hws, hpost, ?_⟩
    · simpa [check, hx, hm] using hchk
    · simpa [run, henv, htrue] using hrun
    · simp only [AccountedAlong, henv]
      exact ⟨hex, hmoved, halong⟩
  | check c x k hx hm hk ih =>
    obtain ⟨r, hr, hmul⟩ := Ctx.multOf_eq_one hm
    have henv : env x = some (.ref r) := hacc.inv.isRef (Or.inl hx) hr
    have htrue : H.exclusive? r = true :=
      Heap.exclusive?_eq_true.mpr (hacc.inv.exclusive hmul)
    obtain ⟨c', H', env', rv, ws, hchk, hrun, hws, hpost, halong⟩ := ih hacc hslots
    refine ⟨c', H', env', rv, ws, ?_, ?_, hws, hpost, ?_⟩
    · simpa [check, hx, hm] using hchk
    · simpa [run, henv, htrue] using hrun
    · show Accounted support H env c ∧ AccountedAlong H env c support k
      exact ⟨hacc, halong⟩
  | setArr c x i v k hx hm hi hv hk ih =>
    obtain ⟨r, hr, hmul⟩ := Ctx.multOf_eq_one hm
    have henv_x : env x = some (.ref r) := hacc.inv.isRef (Or.inl hx) hr
    obtain ⟨idx, hidx⟩ := hacc.inv.scalar i hi
    obtain ⟨val, hval⟩ := hacc.inv.scalar v hv
    obtain ⟨o, hcell⟩ := hacc.inv.cell_of_ref (Or.inl hx) hr
    have hex : Heap.Exclusive H r := hacc.inv.exclusive hmul
    have htrue : H.exclusive? r = true := Heap.exclusive?_eq_true.mpr hex
    obtain ⟨rs, os, idxs, vals, olds, hxe, hie, hve, hcs, hslot, hslots_k⟩ := hslots
    have hrs : rs = r := by
      rw [henv_x] at hxe
      simpa using hxe.symm
    have his : idxs = idx := by
      rw [hidx] at hie
      simpa using hie.symm
    have hvs : vals = val := by
      rw [hval] at hve
      simpa using hve.symm
    have hos : os = o := by
      rw [hrs, hcell] at hcs
      simpa using hcs.symm
    rw [his, hos] at hslot
    rw [hrs, his, hvs, hos] at hslots_k
    have hpost_pred : Accounted support
        (H.set r { o with fields := o.fields.set! idx (.scalar val) })
        (env.set x (.ref r)) c :=
      Accounted.setArrInPlace hacc hx hr hcell hslot
    obtain ⟨c', H', env', rv, ws, hchk, hrun, hws, hpost, halong⟩ :=
      ih hpost_pred hslots_k
    refine ⟨c', H', env', rv, (r, true) :: ws, ?_, ?_, ?_, hpost, ?_⟩
    · simpa [check, hx, hm, hi, hv] using hchk
    · rw [show run (.setArr x i v k) env H =
          (run k (env.set x (.ref r))
            (H.set r { o with fields := o.fields.set! idx (.scalar val) })).addWrite (r, true)
          from by simp [run, henv_x, hidx, hval, hcell, htrue], hrun]
      rfl
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · rfl
      · exact hws w hw
    · simp only [AccountedAlong, henv_x, hidx, hval, hcell]
      exact ⟨hex, hpost_pred, halong⟩
  | decOne c x r k hx hr hlt hk ih =>
    have henv : env x = some (.ref r) := hacc.inv.isRef (Or.inl hx) hr
    have hslots' : StoreSlots (H.dec r 1) (env.erase x) k := by
      simpa only [StoreSlots, henv] using hslots
    have hdec : Accounted (support.erase x) (H.dec r 1) (env.erase x)
        ((c.dec r 1).setUs x .dead) :=
      Accounted.decOne hacc hx hr hlt
    obtain ⟨c', H', env', rv, ws, hchk, hrun, hws, hpost, halong⟩ :=
      ih hdec hslots'
    refine ⟨c', H', env', rv, ws, ?_, ?_, hws, hpost, ?_⟩
    · simpa [check, hr, hx, hlt] using hchk
    · simpa [run, henv] using hrun
    · simp only [AccountedAlong, hr]
      exact ⟨hdec, halong⟩

/-- The store's own pre- and post-state: it is reached with its target
exclusive and its slot scalar, and the post-state is accounted at the checker's
unchanged context. -/
theorem supported_store_exclusive {c : Ctx} {x i v : Var} {k : Code}
    {support : List Var} {H : Heap} {env : Env}
    (hs : Supported c (.setArr x i v k)) (hacc : Accounted support H env c)
    (hslots : StoreSlots H env (.setArr x i v k)) :
    ∃ r o idx val,
      env x = some (.ref r) ∧ env i = some (.scalar idx) ∧
        env v = some (.scalar val) ∧ H.cells r = some o ∧
          Heap.Exclusive H r ∧
            Accounted support
              (H.set r { o with fields := o.fields.set! idx (.scalar val) })
              (env.set x (.ref r)) c := by
  cases hs with
  | setArr c x i v k hx hm hi hv hk =>
    obtain ⟨r, hr, hmul⟩ := Ctx.multOf_eq_one hm
    have henv_x : env x = some (.ref r) := hacc.inv.isRef (Or.inl hx) hr
    obtain ⟨idx, hidx⟩ := hacc.inv.scalar i hi
    obtain ⟨val, hval⟩ := hacc.inv.scalar v hv
    obtain ⟨o, hcell⟩ := hacc.inv.cell_of_ref (Or.inl hx) hr
    obtain ⟨rs, os, idxs, vals, olds, hxe, hie, hve, hcs, hslot, _⟩ := hslots
    have hrs : rs = r := by
      rw [henv_x] at hxe
      simpa using hxe.symm
    have his : idxs = idx := by
      rw [hidx] at hie
      simpa using hie.symm
    have hvs : vals = val := by
      rw [hval] at hve
      simpa using hve.symm
    have hos : os = o := by
      rw [hrs, hcell] at hcs
      simpa using hcs.symm
    rw [his, hos] at hslot
    exact ⟨r, o, idx, val, henv_x, hidx, hval, hcell, hacc.inv.exclusive hmul,
      Accounted.setArrInPlace hacc hx hr hcell hslot⟩

/-! ## The entry packaging -/

/-- The two entry facts a client supplies, kept separate: `Accounted` is the count
relation; `EntryInv` is the footprint and separation condition. Neither implies
the other, and both directions are proved: `aliasEntryInv` is an `EntryInv` state
that no support accounts, and `accountedNotEntryInv` is an accounted state with
no `EntryInv`. So the packaging is a record, not a new implication. -/
structure AccountedEntry (support : List Var) (H : Heap) (env : Env) (c : Ctx)
    (root : Ref) (client : List Ref) : Prop where
  accounted : Accounted support H env c
  entry : Entry.EntryInv H env c root client

namespace Entry

/-- The initializer establishes both entry facts. -/
theorem initAccounted (n : Nat) :
    AccountedEntry [0] (Runner.initHeap n).2 (Runner.initEnv (Runner.initHeap n).1)
      (Runner.initCtx (Runner.initHeap n).1) (Runner.initHeap n).1 [] :=
  { accounted := Accounted.initCtx n
    entry := Entry.initEntryInv n }

end Entry

/-- The entry condition does not imply the count relation: the alias
configuration has the fresh array's footprint, separation and root completeness,
while its two owners share one count, so no support accounts it. -/
theorem aliasEntryInv (n : Nat) :
    Entry.EntryInv (aliasHeap n) (aliasEnv n) (aliasCtx n) (Runner.initHeap n).1 [] ∧
      ∀ support, ¬ Accounted support (aliasHeap n) (aliasEnv n) (aliasCtx n) := by
  refine ⟨{ toInv := (alias_rejected n).1
            uniqueTree := Entry.freshArray_unique n
            separated := Entry.freshArray_separated n
            complete := ?_ }, (alias_rejected n).2⟩
  intro x r hx hr
  have hroot : Entry.MutableFootprint (aliasHeap n) (Runner.initHeap n).1
      (Runner.initHeap n).1 :=
    Entry.MutableFootprint.root (o := ⟨Array.replicate n (Val.scalar 0), 1, false⟩)
      (by simp [aliasHeap, Runner.initHeap]) (by simp)
  by_cases hx0 : x = 0
  · subst hx0
    have hr0 : r = (Runner.initHeap n).1 := by
      simpa [aliasCtx, Ctx.bindOwned, Ctx.setUs, Runner.initCtx] using hr.symm
    subst hr0
    exact hroot
  · by_cases hx1 : x = 1
    · subst hx1
      have hr0 : r = (Runner.initHeap n).1 := by
        simpa [aliasCtx, Ctx.bindOwned] using hr.symm
      subst hr0
      exact hroot
    · by_cases hx2 : x = 2
      · subst hx2
        rw [show (aliasCtx n).us 2 = U.scalar from by
          simp [aliasCtx, Ctx.bindOwned, Runner.initCtx, hx0]] at hx
        exact absurd hx (by decide)
      · rw [show (aliasCtx n).us x = U.dead from by
          simp [aliasCtx, Ctx.bindOwned, Runner.initCtx, hx0, hx1, hx2]] at hx
        exact absurd hx (by decide)

/-- The count relation does not imply the entry condition: the two-cell witness is
accounted, but its root has count two, so the footprint's uniqueness fails at the
root itself. -/
theorem accountedNotEntryInv :
    Accounted [0, 1] inRangeHeap witnessEnv witnessCtx ∧
      ¬ Entry.EntryInv inRangeHeap witnessEnv witnessCtx 0 [] := by
  refine ⟨outOfRange_accepted, ?_⟩
  intro h
  have hrc : Heap.rc inRangeHeap 0 = 1 :=
    h.uniqueTree 0 (Entry.MutableFootprint.root (o := ⟨#[Val.scalar 0], 2, false⟩)
      (by simp [inRangeHeap]) (by simp))
  have htwo : Heap.rc inRangeHeap 0 = 2 := by decide
  omega

/-! ## The initializer's slots and the measured write -/

/-- The initializer's store slot: the size-`n` fresh array has a scalar at index
`0`, which is the value the measured write's index variable carries. -/
theorem storeSlots_init {n : Nat} (hn : 0 < n) :
    StoreSlots (Runner.initHeap n).2 (Runner.initEnv 0) (Runner.execSet 0 3 1 2) := by
  unfold Runner.execSet
  refine ⟨0, ⟨Array.replicate n (Val.scalar 0), 1, false⟩, 0, 0, 0, ?_, ?_, ?_, ?_, ?_,
    trivial⟩
  · simp [Env.set]
  · simp [Runner.initEnv, Env.set]
  · simp [Runner.initEnv, Env.set]
  · simp [Runner.initHeap]
  · rw [Array.getElem?_replicate]
    simp [hn]

/-- The support the measured write ends at: the alias move carries the one
handle from slot 0 to the check result's slot 3. -/
theorem storeSupport_eq : resultSupport (Runner.execSet 0 3 1 2) [0] = [3] := by
  decide

/-- The measured write prefix, through the preservation theorem: it runs without
a fault, records one exclusive write, ends accounted at the moved support, and
its target is exclusive at the initializer. -/
theorem Runner.store_exclusive {n : Nat} (hn : 0 < n) :
    ∃ H' env' v ws,
      run (execSet 0 3 1 2) (initEnv 0) (initHeap n).2 = .done H' env' v ws ∧
      (∀ w ∈ ws, w.2 = true) ∧
      Accounted (resultSupport (execSet 0 3 1 2) [0]) H' env'
        ((initCtx 0).move 0 3) ∧
      Heap.Exclusive (initHeap n).2 (initHeap n).1 := by
  have hsup : Supported (initCtx 0) (execSet 0 3 1 2) := by
    unfold execSet
    refine Supported.bindAlias (c := initCtx 0) (x := 0) (y := 3)
      (k := .setArr 3 1 2 (.ret 3)) ?_ ?_ ?_ ?_
    · exact initCtx_us_zero 0
    · exact initCtx_multOf_zero 0
    · simp [initCtx]
    · refine Supported.setArr ((initCtx 0).move 0 3) 3 1 2 (.ret 3) ?_ ?_ ?_ ?_ ?_
      · simp [Ctx.move_us_y, initCtx]
      · simp [Ctx.multOf, initCtx]
      · simp [Ctx.move_us_other, initCtx]
      · simp [Ctx.move_us_other, initCtx]
      · refine Supported.ret _ _ ?_
        simp [Ctx.move_us_y, initCtx]
  obtain ⟨c', H', env', rv, ws, hchk, hrun, hws, hpost, _⟩ :=
    supported_run hsup (Accounted.initCtx n) (storeSlots_init hn)
  have hc' : c' = (initCtx 0).move 0 3 := by
    rw [Runner.execSet_check] at hchk
    exact (Option.some.inj hchk).symm
  subst hc'
  refine ⟨H', env', rv, ws, hrun, hws, hpost, ?_⟩
  refine ⟨⟨Array.replicate n (Val.scalar 0), 1, false⟩, ?_, rfl, rfl⟩
  simp [initHeap]

end Ownership
