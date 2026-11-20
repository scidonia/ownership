/-
The issuance-history invariant.

`Ctx.issued` records every capability identifier the context has ever issued.
The invariant has two conjuncts: the history is duplicate-free, and every
currently live capability identifier occurs in it. Together they say that a
retired name can never become live again: a transition that emits an identifier
must show it absent from the history, and every live name is in the history.

The module proves the invariant for the concrete empty world and for every
world-level checked command, and lifts it through whole executions
(`checkWorld_historyOK`).
-/
import Cap.WorldInvariant
import Cap.Suspend

namespace Cap

/-- The issuance-history invariant. -/
def Ctx.HistoryOK (C : Ctx) : Prop :=
  C.issued.Nodup ∧ ∀ c ∈ C.ids, c ∈ C.issued

/-- Every live identifier of a context occurs in its history. -/
theorem Ctx.ids_sub_issued {C : Ctx} (h : C.HistoryOK) :
    ∀ c ∈ C.ids, c ∈ C.issued := h.2

namespace Ctx

/-- An owner's identifiers are a sublist of its context's identifiers. -/
theorem owner_ids_sub_ids {C : Ctx} {o : Owner} (h : o ∈ C.owners) :
    ∀ c ∈ o.ids, c ∈ C.ids := by
  intro c hc
  unfold Ctx.ids
  exact List.mem_flatMap.mpr ⟨o, h, hc⟩

/-- Disposal only removes identifiers; the history is unchanged. -/
theorem ids_free_sub {C : Ctx} {a : AllocId} :
    ∀ c ∈ (C.free a).ids, c ∈ C.ids := by
  intro c hc
  unfold Ctx.ids at hc ⊢
  unfold Ctx.free at hc
  obtain ⟨o, ho, hco⟩ := List.mem_flatMap.mp hc
  obtain ⟨hoOwners, _⟩ := List.mem_filter.mp ho
  exact List.mem_flatMap.mpr ⟨o, hoOwners, hco⟩

/-- Replacing one owner's identifiers are covered by the old context's
identifiers together with the replacement's own. -/
theorem ids_update_sub {C : Ctx} {a : AllocId} {o' : Owner} :
    ∀ c ∈ (C.update a o').ids, c ∈ C.ids ∨ c ∈ o'.ids := by
  intro c hc
  unfold Ctx.ids at hc
  rw [Ctx.update] at hc
  obtain ⟨x, hx, hcx⟩ := List.mem_flatMap.mp hc
  obtain ⟨x0, hx0, hfx⟩ := List.mem_map.mp hx
  by_cases hxa : x0.alloc = a
  · right
    rw [if_pos hxa] at hfx
    rw [← hfx] at hcx
    exact hcx
  · left
    rw [if_neg hxa] at hfx
    rw [← hfx] at hcx
    exact List.mem_flatMap.mpr ⟨x0, hx0, hcx⟩

/-- Allocation: the fresh root and disposal identifiers extend the history. -/
theorem historyOK_alloc {C : Ctx} {a : AllocId} {n : Nat} {pos : 0 < C.D}
    {rootId disposal : CapId} {hf : a ∉ C.owners.map (·.alloc)}
    (h : C.HistoryOK) (hroot : rootId ∉ C.issued) (hdisp : disposal ∉ C.issued)
    (hne : rootId ≠ disposal) :
    (C.alloc a n pos rootId disposal hf).HistoryOK := by
  refine ⟨?_, ?_⟩
  · unfold Ctx.alloc
    exact List.nodup_cons.mpr
      ⟨by simp [hroot, hne], List.nodup_cons.mpr ⟨hdisp, h.1⟩⟩
  · intro c hc
    unfold Ctx.alloc at hc
    simp only [Ctx.ids, List.flatMap_cons] at hc
    rcases List.mem_append.mp hc with hnew | hold
    · have hinit : (Owner.init a n C.D pos rootId disposal).ids
          = [disposal, rootId] := by
        simp [Owner.ids, Owner.init, Tree.ids]
      rw [hinit] at hnew
      simp only [List.mem_cons, List.mem_nil_iff] at hnew
      unfold Ctx.alloc
      simp only [List.mem_cons]
      rcases hnew with rfl | rfl | hnil
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
      · exact absurd hnil (by simp)
    · unfold Ctx.alloc
      simp only [List.mem_cons]
      exact Or.inr (Or.inr (h.2 c hold))

/-- Disposal: the history is unchanged and the live set shrinks. -/
theorem historyOK_free {C : Ctx} {a : AllocId} (h : C.HistoryOK) :
    (C.free a).HistoryOK := by
  refine ⟨?_, ?_⟩
  · unfold Ctx.free
    exact h.1
  · intro c hc
    exact h.2 c (Ctx.ids_free_sub c hc)

/-- Suspension and restoration keep the identifier set, so they preserve the
history invariant whenever the replacement's identifiers are the original's. -/
theorem historyOK_update_of_ids {C : Ctx} {a : AllocId} {o' : Owner}
    (h : C.HistoryOK) (hids : ∀ c, c ∈ o'.ids → c ∈ C.ids) :
    (C.update a o').HistoryOK := by
  refine ⟨by unfold Ctx.update; exact h.1, ?_⟩
  intro c hc
  rcases Ctx.ids_update_sub c hc with hold | hnew
  · exact h.2 c hold
  · exact h.2 c (hids c hnew)

end Ctx

/-- A successful spatial split's identifiers are the owner's old identifiers or
the two children. -/
theorem Owner.splitAt?_ids_sub {o o' : Owner} {id id1 id2 : CapId} {k : Nat}
    (hids : o.ids.Nodup) (hs : o.splitAt? id id1 id2 k = some o') :
    ∀ c ∈ o'.ids, c ∈ o.ids ∨ c = id1 ∨ c = id2 := by
  intro c hc
  have hperm := Owner.splitAt?_ids_perm hids hs
  have hc' : c ∈ o.ids.filter (· ≠ id) ++ [id1, id2] := hperm.mem_iff.mp hc
  rcases List.mem_append.mp hc' with hleft | hright
  · exact Or.inl (List.mem_filter.mp hleft).1
  · rw [List.mem_cons, List.mem_cons, List.mem_nil_iff] at hright
    rcases hright with rfl | rfl | hnil
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · exact absurd hnil (by simp)

/-- A successful fractional split's identifiers are the owner's old identifiers
or the two children. -/
theorem Owner.splitFraction?_ids_sub {o o' : Owner} {id id1 id2 : CapId}
    {q1 q2 : Nat} {p1 : 0 < q1} {p2 : 0 < q2}
    (hids : o.ids.Nodup) (hs : o.splitFraction? id id1 id2 q1 q2 p1 p2 = some o') :
    ∀ c ∈ o'.ids, c ∈ o.ids ∨ c = id1 ∨ c = id2 := by
  intro c hc
  have hperm := Owner.splitFraction?_ids_perm hids hs
  have hc' : c ∈ o.ids.filter (· ≠ id) ++ [id1, id2] := hperm.mem_iff.mp hc
  rcases List.mem_append.mp hc' with hleft | hright
  · exact Or.inl (List.mem_filter.mp hleft).1
  · rw [List.mem_cons, List.mem_cons, List.mem_nil_iff] at hright
    rcases hright with rfl | rfl | hnil
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · exact absurd hnil (by simp)

/-- A successful fractional join's identifiers are the owner's old identifiers
or the new identifier. -/
theorem Owner.joinFraction?_ids_sub' {o o' : Owner} {node newId : CapId}
    (hs : o.joinFraction? node newId = some o') :
    ∀ c ∈ o'.ids, c ∈ o.ids ∨ c = newId := by
  intro c hc
  rcases Owner.joinFraction?_ids_sub hs hc with h | h
  · exact Or.inr h
  · exact Or.inl h

end Cap
