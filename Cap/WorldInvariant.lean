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

end Cap
