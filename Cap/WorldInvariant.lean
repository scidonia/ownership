/-
World-level invariant for the capability world.

The invariant combines three components:

* `Ctx.WellFormed` (`Cap.Invariant`): the context realizes its owners
  (`Ctx.Realizes`: every owner is covered by the budget and allocation
  identifiers are distinct), every owner is well formed at the context
  denominator, and the context's capability identifiers are distinct.
* `Ctx.Functional`: each allocation resolves to at most one owner. Here it is
  stated through `Ctx.findOwner?`, so it also pins the value found by the
  lookup: any owner recorded at the found allocation is the found owner.
* `World.StorageMatches`: the owner found for an allocation has a backend in
  the heap whose buffer length is the owner's length.

`World.WellFormed` bundles the three. The older `World.Rel` (`Cap.World`) is
`Ctx.Realizes` together with a storage agreement quantified over the owner
list; `World.rel_of_wellFormed` shows the new bundle implies it. The bridge is
`Ctx.findOwner?_eq_some_of_mem_of_functional`: for a functional context, every
recorded owner is the value looked up at its allocation.

What is proved:

* `Ctx.functional_of_nodup`: a context with distinct allocation identifiers is
  functional, so `Ctx.Functional` is a consequence of `Ctx.Realizes` rather
  than an independent assumption in the bundle.
* `Ctx.update_functional` and `Ctx.free_functional`: a context update whose
  replacement sits at the updated allocation, and unconditional disposal,
  preserve functionality from distinctness of allocation identifiers.
  `Ctx.freeWith?_functional` is the guarded-disposal version.
* `Ctx.freeWith?_eq_free`: a successful disposal-guarded free is exactly the
  unconditional `Ctx.free`, which lets the world-level proof factor the heap
  through the context operation.
* `World.rel_of_wellFormed`: `World.WellFormed` implies the existing
  `World.Rel`.
* `World.write?_wellFormed` and `World.freeWith?_wellFormed`: the existing world
  operations preserve `World.WellFormed`. Write takes the same `Writable` guard
  proof as `World.write?`; it needs no further hypothesis. Disposal is
  dispatched through the recorded disposal capability, as in
  `World.freeWith?`, and needs no further hypothesis either.

Explicit hypotheses beyond the invariant:

* `Ctx.update_functional` needs `o'.alloc = a`: the replacement must occupy the
  allocation it replaces, otherwise the context's allocation-identifier list
  changes and distinctness is lost. It takes the allocation distinctness
  `(C.owners.map (·.alloc)).Nodup` directly; `C.Realizes` supplies it.
* `Ctx.free_functional` and `Ctx.freeWith?_functional` take the same
  allocation distinctness (again `C.Realizes` supplies it).
* The write preservation uses `Backend.write_preserves_len` for the length
  agreement; it does not need the guard hypothesis `hg` to be inhabited beyond
  its appearance in the operation.

What is not proved: loans, disposal uniqueness, split commands, any liveness or
well-bracketing property of the heap, and any relation between backends other
than the buffer-length agreement. Nothing here changes the existing modules;
this file only imports them.
-/
import Cap.World
import Cap.Invariant
import Cap.Suspend

namespace Cap

/-- Each allocation resolves to at most one owner: the owner found at `a` is
the only recorded owner whose allocation is `a`. -/
def Ctx.Functional (C : Ctx) : Prop :=
  ∀ (a : AllocId) (o o' : Owner),
    C.findOwner? a = some o → o' ∈ C.owners → o'.alloc = a → o' = o

/-- The owner found for an allocation has a backend whose buffer length is the
owner's length. -/
def World.StorageMatches (w : World) : Prop :=
  ∀ (a : AllocId) (o : Owner), w.ctx.findOwner? a = some o →
    ∃ b, w.heaps a = some b ∧ b.buf.length = o.len

/-- The world invariant: context well-formedness, functional lookup, and
storage agreement. -/
def World.WellFormed (w : World) : Prop :=
  Ctx.WellFormed w.ctx ∧ Ctx.Functional w.ctx ∧ w.StorageMatches

/-! ### Lookup lemmas -/

/-- A recorded owner makes the lookup at its allocation succeed. -/
theorem Ctx.findOwner?_isSome_of_mem {C : Ctx} {o : Owner} (hmem : o ∈ C.owners) :
    ∃ o', C.findOwner? o.alloc = some o' := by
  unfold Ctx.findOwner?
  cases hf : C.owners.find? (fun x => x.alloc = o.alloc) with
  | none =>
    have h := (List.find?_eq_none.mp hf) o hmem
    simp at h
  | some o' => exact ⟨o', rfl⟩

/-- A functional context returns a recorded owner from the lookup at its own
allocation. -/
theorem Ctx.findOwner?_eq_some_of_mem_of_functional {C : Ctx}
    (hf : C.Functional) {o : Owner} (hmem : o ∈ C.owners) :
    C.findOwner? o.alloc = some o := by
  obtain ⟨z, hz⟩ := Ctx.findOwner?_isSome_of_mem hmem
  have hzo : o = z := hf o.alloc z o hz hmem rfl
  simpa [hzo] using hz

/-- Distinct allocation identifiers make the lookup functional. -/
theorem Ctx.functional_of_nodup {C : Ctx}
    (hnd : (C.owners.map (·.alloc)).Nodup) : C.Functional := by
  intro a o o' hfind ho' halloc
  have hfind' : C.owners.find? (fun x => x.alloc = a) = some o := hfind
  have homem : o ∈ C.owners := List.mem_of_find?_eq_some hfind'
  have hoalloc : o.alloc = a := by simpa using List.find?_some hfind'
  exact alloc_eq_of_mem hnd ho' homem (halloc.trans hoalloc.symm)

/-! ### Functional update and free -/

/-- The allocation list of an update whose replacement occupies the updated
allocation is the old allocation list. -/
theorem update_alloc_map (l : List Owner) (a : AllocId) (o' : Owner)
    (halloc : o'.alloc = a) :
    (l.map (fun x => if x.alloc = a then o' else x)).map (·.alloc)
      = l.map (·.alloc) := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.map_cons]
    rw [ih]
    by_cases hy : y.alloc = a
    · simp [hy, halloc]
    · simp [hy]

/-- Updating a functional context at the replacement's own allocation keeps it
functional, provided allocation identifiers are distinct. -/
theorem Ctx.update_functional {C : Ctx} {a : AllocId} {o' : Owner}
    (halloc : o'.alloc = a) (hnd : (C.owners.map (·.alloc)).Nodup) :
    (C.update a o').Functional := by
  apply Ctx.functional_of_nodup
  dsimp only [Ctx.update]
  rw [update_alloc_map C.owners a o' halloc]
  exact hnd

/-- Unconditional disposal preserves functionality. -/
theorem Ctx.free_functional {C : Ctx} {a : AllocId}
    (hnd : (C.owners.map (·.alloc)).Nodup) : (C.free a).Functional := by
  apply Ctx.functional_of_nodup
  dsimp only [Ctx.free]
  have hmap : (C.owners.filter (fun o => o.alloc ≠ a)).map (·.alloc)
      = List.filter (fun x => x ≠ a) (C.owners.map (·.alloc)) := by
    rw [List.filter_map]
    rfl
  rw [hmap]
  exact List.Nodup.sublist List.filter_sublist hnd

/-- A successful disposal-guarded free is the unconditional free. -/
theorem Ctx.freeWith?_eq_free {C C' : Ctx} {a : AllocId} {d : CapId}
    (h : C.freeWith? a d = some C') : C' = C.free a := by
  unfold Ctx.freeWith? at h
  cases hf : C.findOwner? a with
  | none => simp [hf] at h
  | some o =>
    by_cases hd : o.disposal = d
    · simp only [hf, hd, ite_true, Option.some.injEq] at h
      exact h.symm
    · simp [hf, hd] at h

/-- Disposal guarded by the recorded disposal capability preserves
functionality. -/
theorem Ctx.freeWith?_functional {C C' : Ctx} {a : AllocId} {d : CapId}
    (h : C.freeWith? a d = some C') (hnd : (C.owners.map (·.alloc)).Nodup) :
    C'.Functional := by
  rw [Ctx.freeWith?_eq_free h]
  exact Ctx.free_functional hnd

/-! ### The world invariant -/

/-- The world invariant implies the older storage-by-owners relation. -/
theorem World.rel_of_wellFormed {w : World} (hwf : w.WellFormed) : w.Rel := by
  refine ⟨hwf.1.1, ?_⟩
  intro o ho
  have hfind : w.ctx.findOwner? o.alloc = some o :=
    Ctx.findOwner?_eq_some_of_mem_of_functional hwf.2.1 ho
  exact hwf.2.2 o.alloc o hfind

/-- Write through the owner guard preserves the world invariant. -/
theorem World.write?_wellFormed {w w' : World} {a : AllocId} {id : CapId}
    {i : Nat} {v : UInt8}
    {hg : ∀ o, w.ctx.findOwner? a = some o → o.Writable w.ctx.D id i}
    (h : w.write? a id i v hg = some w') (hwf : w.WellFormed) :
    w'.WellFormed := by
  unfold World.write? at h
  cases hf : w.ctx.findOwner? a with
  | none => simp [hf] at h
  | some o =>
    cases hb : w.heaps a with
    | none => simp [hf, hb] at h
    | some b =>
      cases hbw : b.write i v with
      | none => simp [hf, hb, hbw] at h
      | some b' =>
        simp [hf, hb, hbw] at h
        cases h
        refine ⟨hwf.1, hwf.2.1, ?_⟩
        intro a0 o0 hfind
        by_cases hx : a0 = a
        · cases hx
          rw [hf] at hfind
          have ho0 : o0 = o := (Option.some.inj hfind).symm
          subst o0
          obtain ⟨b0, hb0, hlen⟩ := hwf.2.2 a o hf
          rw [hb] at hb0
          have hbb : b0 = b := (Option.some.inj hb0).symm
          subst b0
          refine ⟨b', by simp, ?_⟩
          rw [Backend.write_preserves_len hbw]
          exact hlen
        · obtain ⟨b0, hb0, hlen⟩ := hwf.2.2 a0 o0 hfind
          exact ⟨b0, by simp [hx, hb0], hlen⟩

/-- Disposal through the recorded disposal capability preserves the world
invariant; the backend at the allocation is cleared. -/
theorem World.freeWith?_wellFormed {w w' : World} {a : AllocId} {d : CapId}
    (h : w.freeWith? a d = some w') (hwf : w.WellFormed) :
    w'.WellFormed := by
  unfold World.freeWith? at h
  cases hc : w.ctx.freeWith? a d with
  | none => simp [hc] at h
  | some ctx' =>
    simp only [hc, Option.some.injEq] at h
    cases h
    have hctx : Ctx.WellFormed ctx' := Ctx.freeWith?_wellFormed hwf.1 hc
    have hfun : Ctx.Functional ctx' := Ctx.freeWith?_functional hc hwf.1.1.2
    have heq : ctx' = w.ctx.free a := Ctx.freeWith?_eq_free hc
    subst ctx'
    refine ⟨hctx, hfun, ?_⟩
    intro b0 o0 hfind
    have hfind' : (w.ctx.free a).owners.find? (fun x => x.alloc = b0) = some o0 := hfind
    have hmem : o0 ∈ (w.ctx.free a).owners := List.mem_of_find?_eq_some hfind'
    have hoalloc : o0.alloc = b0 := by simpa using List.find?_some hfind'
    obtain ⟨hmemC, hne⟩ := List.mem_filter.mp hmem
    have hne' : o0.alloc ≠ a := by simpa using hne
    have hb0ne : b0 ≠ a := fun hba => hne' (hoalloc.trans hba)
    have hfindC : w.ctx.findOwner? b0 = some o0 := by
      have h1 := Ctx.findOwner?_eq_some_of_mem_of_functional hwf.2.1 hmemC
      rwa [hoalloc] at h1
    obtain ⟨b, hb, hlen⟩ := hwf.2.2 b0 o0 hfindC
    exact ⟨b, by simp [hb, hb0ne], hlen⟩

/-- A checked spatial split at the owner of an allocation. The owner and both
children must be fresh for the context. -/
def World.splitAtChecked (w : World) (a : AllocId) (id id1 id2 : CapId) (k : Nat) :
    Except String World :=
  match w.ctx.findOwner? a with
  | none => .error "split: no owner for the allocation"
  | some o =>
    if ∀ l ∈ w.ctx.loans.loans, l.alloc ≠ a then
      if hf : o.FreshIds id1 id2 ∧ id1 ∉ w.ctx.ids ∧ id2 ∉ w.ctx.ids
                ∧ id1 ∉ w.ctx.issued ∧ id2 ∉ w.ctx.issued
                ∧ (∃ c, o.root.find? id = some c ∧ c.state = .active) then
        match hs : w.ctx.splitAtOwner? o id id1 id2 k with
        | some C' => .ok { w with ctx := { C' with issued := id1 :: id2 :: w.ctx.issued } }
        | none => .error "split: refused"
      else .error "split: capability identifiers are not fresh"
    else .error "split: outstanding loan"

theorem World.splitAtChecked_sound {w w' : World} {a : AllocId} {id id1 id2 : CapId}
    {k : Nat} (h : w.splitAtChecked a id id1 id2 k = .ok w') :
    ∃ o C', w.ctx.findOwner? a = some o ∧ o.FreshIds id1 id2 ∧
      id1 ∉ w.ctx.ids ∧ id2 ∉ w.ctx.ids ∧
      w.ctx.splitAtOwner? o id id1 id2 k = some C' ∧
      w' = { w with ctx := { C' with issued := id1 :: id2 :: w.ctx.issued } } := by
  unfold World.splitAtChecked at h
  split at h
  · simp at h
  · rename_i o hf
    split at h
    · rename_i halloc
      split at h
      · rename_i hfr
        split at h
        · rename_i C' hs
          simp only [Except.ok.injEq] at h
          exact ⟨o, C', hf, hfr.1, hfr.2.1, hfr.2.2.1, hs, h.symm⟩
        · simp at h
      · simp at h
    · simp at h

/-- Replacing one owner by a split result of the same length keeps the heap
agreement. -/
theorem World.update_storage {w : World} {o o' : Owner}
    (hwf : w.WellFormed) (hfind : w.ctx.findOwner? o.alloc = some o)
    (halloc : o'.alloc = o.alloc) (hlen : o'.len = o.len) :
    ({ w with ctx := w.ctx.update o.alloc o' } : World).StorageMatches := by
  intro a' o'' hfind''
  have hmem'' : o'' ∈ (w.ctx.update o.alloc o').owners :=
    List.mem_of_find?_eq_some hfind''
  have ho''alloc : o''.alloc = a' := by
    have h := List.find?_some (p := fun x : Owner => decide (x.alloc = a'))
      (show (w.ctx.update o.alloc o').owners.find? (fun x => decide (x.alloc = a')) = some o'' by
        simpa [Ctx.findOwner?] using hfind'')
    simpa using h
  by_cases ho'' : o'' = o'
  · subst ho''
    subst a'
    obtain ⟨b, hb, hb_len⟩ := hwf.2.2 o.alloc o hfind
    exact ⟨b, by simpa [halloc] using hb, by rw [hb_len, hlen]⟩
  · have hmem_old : o'' ∈ w.ctx.owners := by
      unfold Ctx.update at hmem''
      have hmem_map : o'' ∈ w.ctx.owners.map (fun x : Owner => if x.alloc = o.alloc then o' else x) := hmem''
      obtain ⟨x, hx, hxo⟩ := List.mem_map.mp hmem_map
      by_cases hxa : x.alloc = o.alloc
      · have : o'' = o' := by
          rw [← hxo]
          simp [hxa]
        exact absurd this ho''
      · have : o'' = x := by
          rw [← hxo]
          simp [hxa]
        subst x
        exact hx
    have hfind_old : w.ctx.findOwner? a' = some o'' := by
      have holdfun : w.ctx.Functional := Ctx.functional_of_nodup hwf.1.1.2
      have := Ctx.findOwner?_eq_some_of_mem_of_functional holdfun hmem_old
      rwa [ho''alloc] at this
    obtain ⟨b, hb, hb_len⟩ := hwf.2.2 a' o'' hfind_old
    exact ⟨b, hb, hb_len⟩

/-- A successful checked split preserves the world invariant. -/
theorem World.splitAtChecked_wf {w w' : World} {a : AllocId} {id id1 id2 : CapId}
    {k : Nat} (h : w.splitAtChecked a id id1 id2 k = .ok w') (hwf : w.WellFormed) :
    w'.WellFormed := by
  obtain ⟨o, C', hf, hfids, hfresh1, hfresh2, hs, hw'⟩ := splitAtChecked_sound h
  subst w'
  have hmem : o ∈ w.ctx.owners := List.mem_of_find?_eq_some hf
  have hs' : w.ctx.splitAtOwner? o id id1 id2 k = some C' := hs
  unfold Ctx.splitAtOwner? at hs
  cases ho : o.splitAt? id id1 id2 k with
  | none => simp [ho] at hs
  | some o' =>
    simp only [ho, Option.map_some, Option.some.injEq] at hs
    subst C'
    have hwfC : (w.ctx.update o.alloc o').WellFormed :=
      Ctx.splitAtOwner_wellFormed hwf.1 hmem hfids hfresh1 hfresh2 hs'
    have ho'alloc : o'.alloc = o.alloc := Owner.splitAt?_alloc ho
    have ho'len : o'.len = o.len := Owner.splitAt?_len ho
    have hfun : (w.ctx.update o.alloc o').Functional :=
      Ctx.update_functional ho'alloc hwf.1.1.2
    have hoalloc : o.alloc = a := by
      have := List.find?_some (p := fun x : Owner => decide (x.alloc = a))
        (by simpa [Ctx.findOwner?] using hf)
      simpa using this
    have hfa : w.ctx.findOwner? o.alloc = some o := by
      simpa [hoalloc] using hf
    exact ⟨hwfC, hfun, World.update_storage hwf hfa ho'alloc ho'len⟩

/-- A checked disposal: no loan may be outstanding for the allocation, and the
recorded disposal capability must be accepted. -/
def World.freeChecked (w : World) (a : AllocId) (d : CapId) : Except String World :=
  match w.ctx.findOwner? a with
  | none => .error "free: no owner for the allocation"
  | some o =>
    if ∀ l ∈ w.ctx.loans.loans, l.alloc ≠ a then
      if ∀ l ∈ w.ctx.loans.loans, l.lender ∉ o.ids then
        match w.freeWith? a d with
        | some w' => .ok w'
        | none => .error "free: refused"
      else .error "free: outstanding loan"
    else .error "free: outstanding loan"

/-- A successful disposal preserves the world invariant. -/
theorem World.freeChecked_wf {w w' : World} {a : AllocId} {d : CapId}
    (h : w.freeChecked a d = .ok w') (hwf : w.WellFormed) : w'.WellFormed := by
  unfold World.freeChecked at h
  split at h
  · simp at h
  · rename_i o hfind
    split at h
    · rename_i halloc
      split at h
      · rename_i hloan
        cases hw : w.freeWith? a d with
        | none => simp [hw] at h
        | some w'' =>
          simp [hw] at h
          cases h
          exact World.freeWith?_wellFormed hw hwf
      · simp at h
    · simp at h

/-- A checked allocation: the next allocation identifier must be free and the
root and disposal capabilities fresh and distinct. The new owner's backend is
empty. -/
def World.allocChecked (w : World) (n : Nat) (rootId disposal : CapId)
    (pos : 0 < w.ctx.D) : Except String World :=
  if hf : (⟨w.ctx.nextAlloc⟩ : AllocId) ∉ w.ctx.owners.map (·.alloc) then
    if hfresh : rootId ∉ w.ctx.ids ∧ disposal ∉ w.ctx.ids ∧ rootId ≠ disposal
                ∧ rootId ∉ w.ctx.issued ∧ disposal ∉ w.ctx.issued then
      .ok { w with
            ctx := w.ctx.alloc ⟨w.ctx.nextAlloc⟩ n pos rootId disposal hf,
            heaps := fun x => if x = (⟨w.ctx.nextAlloc⟩ : AllocId) then some (Backend.empty n) else w.heaps x }
    else .error "alloc: capability identifiers are not fresh"
  else .error "alloc: stale allocation identifier"

/-- A successful allocation preserves the world invariant. -/
theorem World.allocChecked_wf {w w' : World} {n : Nat} {rootId disposal : CapId}
    {pos : 0 < w.ctx.D} (h : w.allocChecked n rootId disposal pos = .ok w')
    (hwf : w.WellFormed) : w'.WellFormed := by
  unfold World.allocChecked at h
  split at h
  · rename_i hf
    split at h
    · rename_i hfresh
      cases h
      refine ⟨Ctx.alloc_wellFormed (hfresh := hf) hwf.1 hfresh.1 hfresh.2.1 hfresh.2.2.1, ?_, ?_⟩
      · apply Ctx.functional_of_nodup
        simp only [Ctx.alloc, List.map_cons, List.nodup_cons]
        exact ⟨hf, hwf.1.1.2⟩
      · intro a' o' hfind
        unfold Ctx.findOwner? Ctx.alloc at hfind
        simp only [List.find?_cons] at hfind
        by_cases hx : (Owner.init ⟨w.ctx.nextAlloc⟩ n w.ctx.D pos rootId disposal).alloc = a'
        · simp [hx] at hfind
          cases hfind
          refine ⟨Backend.empty n, ?_, ?_⟩
          · rw [← hx]
            exact if_pos rfl
          · simp [Backend.empty, Owner.init]
        · simp [hx] at hfind
          have hmem : o' ∈ w.ctx.owners := List.mem_of_find?_eq_some hfind
          have hoalloc : o'.alloc = a' := by
            have h := List.find?_some (p := fun x : Owner => decide (x.alloc = a')) hfind
            simpa using h
          have hne : a' ≠ (⟨w.ctx.nextAlloc⟩ : AllocId) := by
            intro hcontra
            rw [hcontra] at hoalloc
            have : (Owner.init ⟨w.ctx.nextAlloc⟩ n w.ctx.D pos rootId disposal).alloc = ⟨w.ctx.nextAlloc⟩ := rfl
            exact hx (this.trans hcontra.symm)
          have hfind_old : w.ctx.findOwner? a' = some o' := by
            have holdfun : w.ctx.Functional := Ctx.functional_of_nodup hwf.1.1.2
            have := Ctx.findOwner?_eq_some_of_mem_of_functional holdfun hmem
            rwa [hoalloc] at this
          obtain ⟨b, hb, hlen⟩ := hwf.2.2 a' o' hfind_old
          exact ⟨b, by simp [hne, hb], hlen⟩
    · simp at h
  · simp at h
/-- A checked fractional split at the owner of an allocation. -/
def World.splitFractionChecked (w : World) (a : AllocId) (id id1 id2 : CapId)
    (q1 q2 : Nat) (p1 : 0 < q1) (p2 : 0 < q2) : Except String World :=
  match w.ctx.findOwner? a with
  | none => .error "split: no owner for the allocation"
  | some o =>
    if ∀ l ∈ w.ctx.loans.loans, l.alloc ≠ a then
      if o.FreshIds id1 id2 ∧ id1 ∉ w.ctx.ids ∧ id2 ∉ w.ctx.ids
          ∧ id1 ∉ w.ctx.issued ∧ id2 ∉ w.ctx.issued
          ∧ (∃ c, o.root.find? id = some c ∧ c.state = .active) then
        match w.ctx.splitFractionOwner? o id id1 id2 q1 q2 p1 p2 with
        | some C' => .ok { w with ctx := { C' with issued := id1 :: id2 :: w.ctx.issued } }
        | none => .error "split: refused"
      else .error "split: capability identifiers are not fresh"
    else .error "split: outstanding loan"

/-- A successful fractional split preserves the world invariant. -/
theorem World.splitFractionChecked_wf {w w' : World} {a : AllocId} {id id1 id2 : CapId}
    {q1 q2 : Nat} {p1 : 0 < q1} {p2 : 0 < q2}
    (h : w.splitFractionChecked a id id1 id2 q1 q2 p1 p2 = .ok w')
    (hwf : w.WellFormed) : w'.WellFormed := by
  unfold World.splitFractionChecked at h
  split at h
  · simp at h
  · rename_i o hf'
    split at h
    · rename_i halloc
      split at h
      · rename_i hfr
        split at h
        · rename_i C' hs
          simp only [Except.ok.injEq] at h
          cases h
          have hmem : o ∈ w.ctx.owners := List.mem_of_find?_eq_some hf'
          have hs' := hs
          unfold Ctx.splitFractionOwner? at hs
          cases ho : o.splitFraction? id id1 id2 q1 q2 p1 p2 with
          | none => simp [ho] at hs
          | some o' =>
            simp only [ho, Option.map_some, Option.some.injEq] at hs
            subst C'
            have hwfC : (w.ctx.update o.alloc o').WellFormed :=
              Ctx.splitFractionOwner_wellFormed hwf.1 hmem hfr.1 hfr.2.1 hfr.2.2.1 hs'
            have ho'alloc : o'.alloc = o.alloc := Owner.splitFraction?_alloc ho
            have ho'len : o'.len = o.len := Owner.splitFraction?_len ho
            have hfun : (w.ctx.update o.alloc o').Functional :=
              Ctx.update_functional ho'alloc hwf.1.1.2
            have hoalloc : o.alloc = a := by
              have := List.find?_some (p := fun x : Owner => decide (x.alloc = a))
                (by simpa [Ctx.findOwner?] using hf')
              simpa using this
            have hfa : w.ctx.findOwner? o.alloc = some o := by
              simpa [hoalloc] using hf'
            exact ⟨hwfC, hfun, World.update_storage hwf hfa ho'alloc ho'len⟩
        · simp at h
      · simp at h
    · simp at h

/-- A checked fractional join at the owner of an allocation; the fresh
identifier must not occur in the context. -/
def World.joinChecked (w : World) (a : AllocId) (node newId : CapId) :
    Except String World :=
  match w.ctx.findOwner? a with
  | none => .error "join: no owner for the allocation"
  | some o =>
    if newId ∉ w.ctx.ids ∧ newId ∉ w.ctx.issued then
      match w.ctx.joinFractionOwner? o node newId with
      | some C' => .ok { w with ctx := { C' with issued := newId :: w.ctx.issued } }
      | none => .error "join: refused"
    else .error "join: capability identifier is not fresh"

/-- A successful fractional join preserves the world invariant. -/
theorem World.joinChecked_wf {w w' : World} {a : AllocId} {node newId : CapId}
    (h : w.joinChecked a node newId = .ok w') (hwf : w.WellFormed) :
    w'.WellFormed := by
  unfold World.joinChecked at h
  split at h
  · simp at h
  · rename_i o hf'
    split at h
    · rename_i hfresh
      split at h
      · rename_i C' hs
        simp only [Except.ok.injEq] at h
        cases h
        have hmem : o ∈ w.ctx.owners := List.mem_of_find?_eq_some hf'
        have hs' := hs
        unfold Ctx.joinFractionOwner? at hs
        cases ho : o.joinFraction? node newId with
        | none => simp [ho] at hs
        | some o' =>
          simp only [ho, Option.map_some, Option.some.injEq] at hs
          subst C'
          have hwfC : (w.ctx.update o.alloc o').WellFormed :=
            Ctx.joinFractionOwner_wellFormed hwf.1 hmem hfresh.1 hs'
          have ho'alloc : o'.alloc = o.alloc := Owner.joinFraction_alloc ho
          have ho'len : o'.len = o.len := Owner.joinFraction?_len ho
          have hfun : (w.ctx.update o.alloc o').Functional :=
            Ctx.update_functional ho'alloc hwf.1.1.2
          have hoalloc : o.alloc = a := by
            have := List.find?_some (p := fun x : Owner => decide (x.alloc = a))
              (by simpa [Ctx.findOwner?] using hf')
            simpa using this
          have hfa : w.ctx.findOwner? o.alloc = some o := by
            simpa [hoalloc] using hf'
          exact ⟨hwfC, hfun, World.update_storage hwf hfa ho'alloc ho'len⟩
      · simp at h
    · simp at h

/-! ### Suspension and resumption -/

/-- Suspension keeps the owner's coverage: the budget is unchanged at every
byte. -/
theorem Owner.suspendLeaf?_covered {o o' : Owner} {D : Nat} {id : CapId}
    (h : o.suspendLeaf? id = some o') (hcov : o.Covered D) : o'.Covered D := by
  obtain ⟨_, _, _, rfl⟩ := Owner.suspendLeaf?_eq h
  intro x hx
  rw [Owner.suspendLeaf?_budget h x]
  exact hcov x hx

/-- Resumption keeps the owner's coverage. -/
theorem Owner.resumeLeaf?_covered {o o' : Owner} {D : Nat} {id : CapId}
    (h : o.resumeLeaf? id = some o') (hcov : o.Covered D) : o'.Covered D := by
  obtain ⟨_, _, _, rfl⟩ := Owner.resumeLeaf?_eq h
  intro x hx
  rw [Owner.resumeLeaf?_budget h x]
  exact hcov x hx

/-- Suspension keeps every leaf inside the owner's allocation and extent: the
updated leaf keeps its allocation and footprint. -/
theorem Owner.suspendLeaf?_leavesWithin {o o' : Owner} {id : CapId}
    (h : o.suspendLeaf? id = some o') (hlw : o.LeavesWithin) : o'.LeavesWithin := by
  obtain ⟨c, hf, _, rfl⟩ := Owner.suspendLeaf?_eq h
  intro id' c' hfind
  replace hfind : (o.root.replace id (fun c => .leaf { c with state := .retired })).find? id'
      = some c' := hfind
  by_cases h'id : id' = id
  · rw [h'id] at hfind
    rw [Tree.find?_replace_leaf_eq _ _ (fun c => { c with state := .retired }) (fun _ => rfl),
      hf] at hfind
    have hc' : c' = { c with state := .retired } := (Option.some.inj hfind).symm
    subst hc'
    exact hlw id c hf
  · rw [Tree.find?_replace_leaf_ne _ _ _ (fun c => { c with state := .retired }) (fun _ => rfl)
      h'id] at hfind
    exact hlw id' c' hfind

/-- Resumption keeps every leaf inside the owner's allocation and extent. -/
theorem Owner.resumeLeaf?_leavesWithin {o o' : Owner} {id : CapId}
    (h : o.resumeLeaf? id = some o') (hlw : o.LeavesWithin) : o'.LeavesWithin := by
  obtain ⟨c, hf, _, rfl⟩ := Owner.resumeLeaf?_eq h
  intro id' c' hfind
  replace hfind : (o.root.replace id (fun c => .leaf { c with state := .active })).find? id'
      = some c' := hfind
  by_cases h'id : id' = id
  · rw [h'id] at hfind
    rw [Tree.find?_replace_leaf_eq _ _ (fun c => { c with state := .active }) (fun _ => rfl),
      hf] at hfind
    have hc' : c' = { c with state := .active } := (Option.some.inj hfind).symm
    subst hc'
    exact hlw id c hf
  · rw [Tree.find?_replace_leaf_ne _ _ _ (fun c => { c with state := .active }) (fun _ => rfl)
      h'id] at hfind
    exact hlw id' c' hfind

/-- Suspension keeps the disposal entitlement present: the disposal capability
and the identifier list are unchanged. -/
theorem Owner.suspendLeaf?_disposalPresent {o o' : Owner} {id : CapId}
    (h : o.suspendLeaf? id = some o') (hd : o.DisposalPresent) : o'.DisposalPresent := by
  obtain ⟨c, hf, _, rfl⟩ := Owner.suspendLeaf?_eq h
  rcases hd with ⟨cd, hcd⟩ | hd
  · left
    by_cases hdid : o.disposal = id
    · rw [hdid] at hcd
      exact ⟨{ cd with state := .retired }, by
        show (o.root.replace id (fun c => .leaf { c with state := .retired })).find? o.disposal
            = some _
        rw [hdid, Tree.find?_replace_leaf_eq _ _ (fun c => { c with state := .retired })
          (fun _ => rfl), hcd]
        rfl⟩
    · exact ⟨cd, by
        show (o.root.replace id (fun c => .leaf { c with state := .retired })).find? o.disposal
            = some _
        rw [Tree.find?_replace_leaf_ne _ _ _ (fun c => { c with state := .retired }) (fun _ => rfl)
          hdid]
        exact hcd⟩
  · right
    show o.disposal ∉ (o.root.replace id (fun c => .leaf { c with state := .retired })).ids
    rw [Tree.ids_replace_leaf _ _ (fun c => { c with state := .retired }) (fun _ => rfl)]
    exact hd

/-- Resumption keeps the disposal entitlement present. -/
theorem Owner.resumeLeaf?_disposalPresent {o o' : Owner} {id : CapId}
    (h : o.resumeLeaf? id = some o') (hd : o.DisposalPresent) : o'.DisposalPresent := by
  obtain ⟨c, hf, _, rfl⟩ := Owner.resumeLeaf?_eq h
  rcases hd with ⟨cd, hcd⟩ | hd
  · left
    by_cases hdid : o.disposal = id
    · rw [hdid] at hcd
      exact ⟨{ cd with state := .active }, by
        show (o.root.replace id (fun c => .leaf { c with state := .active })).find? o.disposal
            = some _
        rw [hdid, Tree.find?_replace_leaf_eq _ _ (fun c => { c with state := .active })
          (fun _ => rfl), hcd]
        rfl⟩
    · exact ⟨cd, by
        show (o.root.replace id (fun c => .leaf { c with state := .active })).find? o.disposal
            = some _
        rw [Tree.find?_replace_leaf_ne _ _ _ (fun c => { c with state := .active }) (fun _ => rfl)
          hdid]
        exact hcd⟩
  · right
    show o.disposal ∉ (o.root.replace id (fun c => .leaf { c with state := .active })).ids
    rw [Tree.ids_replace_leaf _ _ (fun c => { c with state := .active }) (fun _ => rfl)]
    exact hd

/-- Suspension preserves the owner invariant. -/
theorem Owner.suspendLeaf?_wellFormed {o o' : Owner} {D : Nat} {id : CapId}
    (h : o.suspendLeaf? id = some o') (hwf : o.WellFormed D) : o'.WellFormed D :=
  ⟨Owner.suspendLeaf?_covered h hwf.1, Owner.suspendLeaf?_leavesWithin h hwf.2.1,
    Owner.suspendLeaf?_disposalPresent h hwf.2.2⟩

/-- Resumption preserves the owner invariant. -/
theorem Owner.resumeLeaf?_wellFormed {o o' : Owner} {D : Nat} {id : CapId}
    (h : o.resumeLeaf? id = some o') (hwf : o.WellFormed D) : o'.WellFormed D :=
  ⟨Owner.resumeLeaf?_covered h hwf.1, Owner.resumeLeaf?_leavesWithin h hwf.2.1,
    Owner.resumeLeaf?_disposalPresent h hwf.2.2⟩

/-- Mapping a conditional replacement that never fires over a list is the
identity. -/
theorem map_alloc_ite_self (l : List Owner) (a : AllocId) (o' : Owner)
    (hne : ∀ y ∈ l, y.alloc ≠ a) :
    l.map (fun y => if y.alloc = a then o' else y) = l := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    rw [List.map_cons, if_neg (hne y List.mem_cons_self),
      ih (fun z hz => hne z (List.mem_cons_of_mem y hz))]

/-- Updating the owner of an allocation whose allocation identifiers are
distinct by a replacement with the same identifier list keeps the flattened
identifier list. -/
theorem flatMap_update_ids_of_same (l : List Owner) (a : AllocId) (o o' : Owner)
    (hnd : (l.map (·.alloc)).Nodup) (hmem : o ∈ l) (hoa : o.alloc = a)
    (hids : o'.ids = o.ids) :
    (l.map (fun x => if x.alloc = a then o' else x)).flatMap Owner.ids
      = l.flatMap Owner.ids := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hnd' : (xs.map (·.alloc)).Nodup := (List.nodup_cons.mp hnd).2
    have hnx : x.alloc ∉ xs.map (·.alloc) := (List.nodup_cons.mp hnd).1
    by_cases hxa : x.alloc = a
    · have hxo : x = o := by
        rcases List.mem_cons.mp hmem with rfl | hmem'
        · rfl
        · exact absurd ((hoa.trans hxa.symm) ▸ List.mem_map_of_mem hmem') hnx
      subst hxo
      have htail : xs.map (fun y => if y.alloc = a then o' else y) = xs := by
        apply map_alloc_ite_self
        intro y hy hya
        exact hnx ((hya.trans hxa.symm) ▸ List.mem_map_of_mem hy)
      simp only [List.map_cons, hxa, if_true, List.flatMap_cons]
      rw [htail, hids]
    · have hmem' : o ∈ xs := by
        rcases List.mem_cons.mp hmem with h | hmem'
        · subst h
          exact absurd hoa hxa
        · exact hmem'
      simp only [List.map_cons, hxa, if_false, List.flatMap_cons]
      rw [ih hnd' hmem']

/-- A context update whose replacement has the replaced owner's identifier list
keeps the context's identifier list. -/
theorem Ctx.update_ids_of_same_ids {C : Ctx} {a : AllocId} {o o' : Owner}
    (hnd : (C.owners.map (·.alloc)).Nodup) (hmem : o ∈ C.owners) (hoa : o.alloc = a)
    (hids : o'.ids = o.ids) :
    (C.update a o').ids = C.ids := by
  simp only [Ctx.update, Ctx.ids]
  exact flatMap_update_ids_of_same C.owners a o o' hnd hmem hoa hids

/-- A context update whose replacement has the replaced owner's identifier list
keeps the context's identifiers distinct. -/
theorem Ctx.update_ids_nodup_of_same_ids {C : Ctx} {a : AllocId} {o o' : Owner}
    (hnd : (C.owners.map (·.alloc)).Nodup) (hmem : o ∈ C.owners) (hoa : o.alloc = a)
    (hids : o'.ids = o.ids) (hidsnodup : C.ids.Nodup) :
    (C.update a o').ids.Nodup := by
  rw [Ctx.update_ids_of_same_ids hnd hmem hoa hids]
  exact hidsnodup

/-- Replacing an owner by its suspension preserves the world invariant. -/
theorem World.suspend_update_wf {w : World} {a : AllocId} {o o' : Owner} {id : CapId}
    (hwf : w.WellFormed) (hf : w.ctx.findOwner? a = some o)
    (hs : o.suspendLeaf? id = some o') :
    ({ w with ctx := w.ctx.update o.alloc o' } : World).WellFormed := by
  have hmem : o ∈ w.ctx.owners := List.mem_of_find?_eq_some hf
  have hoalloc : o.alloc = a := by
    have h := List.find?_some (p := fun x : Owner => decide (x.alloc = a))
      (by simpa [Ctx.findOwner?] using hf)
    simpa using h
  have ho'alloc : o'.alloc = o.alloc := Owner.suspendLeaf?_alloc hs
  have ho'len : o'.len = o.len := Owner.suspendLeaf?_len hs
  have hwfC : (w.ctx.update o.alloc o').WellFormed := by
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · apply Ctx.update_covered
      · exact Owner.suspendLeaf?_covered hs (hwf.1.1.1 o hmem)
      · intro x hx _
        exact hwf.1.1.1 x hx
    · exact Ctx.update_nodup ho'alloc hwf.1.1.2
    · exact Ctx.update_wellFormed_owners (Owner.suspendLeaf?_wellFormed hs (hwf.1.2.1 o hmem))
        (fun x hx _ => hwf.1.2.1 x hx)
    · exact Ctx.update_ids_nodup_of_same_ids hwf.1.1.2 hmem rfl
        (Owner.suspendLeaf?_ids hs) hwf.1.2.2
  have hfun : (w.ctx.update o.alloc o').Functional :=
    Ctx.update_functional ho'alloc hwf.1.1.2
  have hfa : w.ctx.findOwner? o.alloc = some o := by
    simpa [hoalloc] using hf
  exact ⟨hwfC, hfun, World.update_storage hwf hfa ho'alloc ho'len⟩

/-- Replacing an owner by its resumption preserves the world invariant. -/
theorem World.resume_update_wf {w : World} {a : AllocId} {o o' : Owner} {id : CapId}
    (hwf : w.WellFormed) (hf : w.ctx.findOwner? a = some o)
    (hr : o.resumeLeaf? id = some o') :
    ({ w with ctx := w.ctx.update o.alloc o' } : World).WellFormed := by
  have hmem : o ∈ w.ctx.owners := List.mem_of_find?_eq_some hf
  have hoalloc : o.alloc = a := by
    have h := List.find?_some (p := fun x : Owner => decide (x.alloc = a))
      (by simpa [Ctx.findOwner?] using hf)
    simpa using h
  have ho'alloc : o'.alloc = o.alloc := Owner.resumeLeaf?_alloc hr
  have ho'len : o'.len = o.len := Owner.resumeLeaf?_len hr
  have hwfC : (w.ctx.update o.alloc o').WellFormed := by
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · apply Ctx.update_covered
      · exact Owner.resumeLeaf?_covered hr (hwf.1.1.1 o hmem)
      · intro x hx _
        exact hwf.1.1.1 x hx
    · exact Ctx.update_nodup ho'alloc hwf.1.1.2
    · exact Ctx.update_wellFormed_owners (Owner.resumeLeaf?_wellFormed hr (hwf.1.2.1 o hmem))
        (fun x hx _ => hwf.1.2.1 x hx)
    · exact Ctx.update_ids_nodup_of_same_ids hwf.1.1.2 hmem rfl
        (Owner.resumeLeaf?_ids hr) hwf.1.2.2
  have hfun : (w.ctx.update o.alloc o').Functional :=
    Ctx.update_functional ho'alloc hwf.1.1.2
  have hfa : w.ctx.findOwner? o.alloc = some o := by
    simpa [hoalloc] using hf
  exact ⟨hwfC, hfun, World.update_storage hwf hfa ho'alloc ho'len⟩

/-- A checked suspension: retire the leaf `id` of the owner of `a`, so the
write guard refuses through it while the suspension is outstanding. -/
def World.suspendChecked (w : World) (a : AllocId) (id : CapId) : Except String World :=
  match w.ctx.findOwner? a with
  | none => .error "suspend: no owner for the allocation"
  | some o =>
    match o.suspendLeaf? id with
    | some o' => .ok { w with ctx := w.ctx.update o.alloc o' }
    | none => .error "suspend: leaf is missing or not active"

/-- A successful suspension preserves the world invariant. -/
theorem World.suspendChecked_wf {w w' : World} {a : AllocId} {id : CapId}
    (h : w.suspendChecked a id = .ok w') (hwf : w.WellFormed) : w'.WellFormed := by
  unfold World.suspendChecked at h
  cases hf : w.ctx.findOwner? a with
  | none => simp [hf] at h
  | some o =>
    cases hs : o.suspendLeaf? id with
    | none => simp [hf, hs] at h
    | some o' =>
      simp only [hf, hs, Except.ok.injEq] at h
      subst h
      exact World.suspend_update_wf hwf hf hs

/-- A checked resumption: restore the leaf `id` of the owner of `a` to
active. -/
def World.resumeChecked (w : World) (a : AllocId) (id : CapId) : Except String World :=
  match w.ctx.findOwner? a with
  | none => .error "resume: no owner for the allocation"
  | some o =>
    match o.resumeLeaf? id with
    | some o' => .ok { w with ctx := w.ctx.update o.alloc o' }
    | none => .error "resume: leaf is missing or not retired"

/-- A successful resumption preserves the world invariant. -/
theorem World.resumeChecked_wf {w w' : World} {a : AllocId} {id : CapId}
    (h : w.resumeChecked a id = .ok w') (hwf : w.WellFormed) : w'.WellFormed := by
  unfold World.resumeChecked at h
  cases hf : w.ctx.findOwner? a with
  | none => simp [hf] at h
  | some o =>
    cases hr : o.resumeLeaf? id with
    | none => simp [hf, hr] at h
    | some o' =>
      simp only [hf, hr, Except.ok.injEq] at h
      subst h
      exact World.resume_update_wf hwf hf hr


/-- A contextual allocation check accepts whenever its conditions hold. -/
theorem World.allocChecked_succeeds {w : World} {n : Nat} {rootId disposal : CapId}
    {po : 0 < w.ctx.D}
    (hf : (⟨w.ctx.nextAlloc⟩ : AllocId) ∉ w.ctx.owners.map (·.alloc))
    (hfr : rootId ∉ w.ctx.ids ∧ disposal ∉ w.ctx.ids ∧ rootId ≠ disposal
           ∧ rootId ∉ w.ctx.issued ∧ disposal ∉ w.ctx.issued) :
    (w.allocChecked n rootId disposal po).isOk = true := by
  unfold World.allocChecked
  rw [dif_pos hf, dif_pos hfr]
  rfl

/-- A contextual disposal check accepts whenever its condition holds. -/
theorem World.freeChecked_succeeds {w : World} {a : AllocId} {d : CapId}
    (hs : (w.freeWith? a d).isSome)
    (halloc : ∀ o, w.ctx.findOwner? a = some o →
      ∀ l ∈ w.ctx.loans.loans, l.alloc ≠ a)
    (hloan : ∀ o, w.ctx.findOwner? a = some o →
      ∀ l ∈ w.ctx.loans.loans, l.lender ∉ o.ids) :
    (w.freeChecked a d).isOk = true := by
  unfold World.freeChecked
  cases hf : w.ctx.findOwner? a with
  | none =>
    exfalso
    unfold World.freeWith? Ctx.freeWith? at hs
    simp [hf] at hs
  | some o =>
    dsimp only
    rw [if_pos (halloc o hf), if_pos (hloan o hf)]
    cases hw : w.freeWith? a d with
    | none => rw [hw] at hs; simp at hs
    | some w' => rfl

/-- Disposal is refused while a loan remains outstanding for the allocation:
the loan's lender still occurs in the owner's live identifiers. -/
theorem World.freeChecked_refused_of_loan {w : World} {a : AllocId} {d : CapId}
    {o : Owner} {l : Loan}
    (hfind : w.ctx.findOwner? a = some o)
    (halloc : ∀ l ∈ w.ctx.loans.loans, l.alloc ≠ a)
    (hl : l ∈ w.ctx.loans.loans) (hin : l.lender ∈ o.ids) :
    w.freeChecked a d = .error "free: outstanding loan" := by
  unfold World.freeChecked
  rw [hfind]
  dsimp only
  rw [if_pos halloc]
  rw [if_neg (fun h => h l hl hin)]

/-- Disposal is refused while any loan is bound to the allocation, independent of
  the lender's current leaf identity. -/
theorem World.freeChecked_refused_of_alloc {w : World} {a : AllocId} {d : CapId}
    {o : Owner} {l : Loan}
    (hfind : w.ctx.findOwner? a = some o)
    (hl : l ∈ w.ctx.loans.loans) (ha : l.alloc = a) :
    w.freeChecked a d = .error "free: outstanding loan" := by
  unfold World.freeChecked
  rw [hfind]
  dsimp only
  rw [if_neg (fun h => h l hl ha)]

end Cap
