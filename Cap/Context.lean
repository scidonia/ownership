/-
The multi-owner context.

A context is a list of owners plus the budget denominator and a fresh-allocation
counter. `Realizes` requires every owner's bytes to be fully covered and the
allocation identifiers to be distinct. Allocation appends a fully covered owner at
a fresh identifier; disposal removes the owner for an allocation.

Capability-identifier freshness across owners, disposal entitlements recorded per
owner, outstanding loans and the dispatch of the owner-level transitions over the
list are carried by the context itself; `Cap/Unified.lean` runs the checked
transitions over it.
-/
import Cap.Join
import Cap.Loans

namespace Cap

structure Ctx where
  owners : List Owner
  D : Nat
  nextAlloc : Nat
  /-- Every capability identifier ever issued in this context, including those
  of freed allocations. Historical freshness is checked against this list, so a
  consumed identity cannot be reissued within the same run. -/
  issued : List CapId
  /-- Outstanding loans and the lifetimes they are bound to. The loan state is
  part of the permission context, so a program's type can mention it. -/
  loans : LoanCtx

def Ctx.Realizes (C : Ctx) : Prop :=
  (∀ o ∈ C.owners, o.Covered C.D) ∧ (C.owners.map (·.alloc)).Nodup

/-- Replace the owner for allocation `a` by `o'`. -/
def Ctx.update (C : Ctx) (a : AllocId) (o' : Owner) : Ctx :=
  { C with owners := C.owners.map (fun x => if x.alloc = a then o' else x) }

def Ctx.ids (C : Ctx) : List CapId := C.owners.flatMap Owner.ids

/-- A capability identifier does not occur in the context. -/
def Ctx.Fresh (C : Ctx) (c : CapId) : Prop := c ∉ C.ids

/-- The owner recorded for an allocation, if any. -/
def Ctx.findOwner? (C : Ctx) (a : AllocId) : Option Owner :=
  C.owners.find? (fun o => o.alloc = a)

def Ctx.alloc (C : Ctx) (a : AllocId) (n : Nat) (pos : 0 < C.D) (rootId disposal : CapId)
    (hfresh : a ∉ C.owners.map (·.alloc)) : Ctx :=
  { owners := Owner.init a n C.D pos rootId disposal :: C.owners,
    D := C.D,
    nextAlloc := C.nextAlloc + 1,
    issued := rootId :: disposal :: C.issued,
    loans := C.loans }

theorem Ctx.alloc_realizes {C : Ctx} {a : AllocId} {n : Nat} {pos : 0 < C.D}
    {rootId disposal : CapId} {hfresh : a ∉ C.owners.map (·.alloc)}
    (hr : C.Realizes) : (C.alloc a n pos rootId disposal hfresh).Realizes := by
  refine ⟨?_, ?_⟩
  · intro o ho
    simp [Ctx.alloc] at ho
    rcases ho with rfl | ho
    · exact Owner.init_covered a n C.D pos rootId disposal
    · exact hr.1 o ho
  · dsimp [Ctx.alloc]
    have hmap : (Owner.init a n C.D pos rootId disposal :: C.owners).map (·.alloc)
        = a :: C.owners.map (·.alloc) := by
      simp [Owner.init]
    rw [hmap]
    exact List.nodup_cons.mpr ⟨hfresh, hr.2⟩

def Ctx.free (C : Ctx) (a : AllocId) : Ctx :=
  { C with owners := C.owners.filter (fun o => o.alloc ≠ a) }

theorem Ctx.free_realizes {C : Ctx} {a : AllocId} (hr : C.Realizes) :
    (C.free a).Realizes := by
  refine ⟨?_, ?_⟩
  · intro o ho
    exact hr.1 o (List.mem_filter.mp ho).1
  · dsimp [Ctx.free]
    have hmap : (C.owners.filter (fun o => o.alloc ≠ a)).map (·.alloc)
        = List.filter (fun x => x ≠ a) (C.owners.map (·.alloc)) := by
      rw [List.filter_map]
      rfl
    rw [hmap]
    exact List.Nodup.sublist List.filter_sublist hr.2

private theorem update_alloc_map (l : List Owner) (a : AllocId) (o' : Owner)
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

/-- Coverage of an owner other than the updated allocation is untouched. -/
theorem Ctx.update_preserves_other {C : Ctx} {a b : AllocId} {o o' : Owner}
    (hb : b ≠ a) (ho : o ∈ C.owners) (hcov : o.Covered C.D) :
    o.Covered (C.update a o').D := by
  have _ := hb
  have _ := ho
  simpa only [Ctx.update] using hcov

/-- If the replacement is covered and all other owners are covered, the updated
context is covered. -/
theorem Ctx.update_covered {C : Ctx} {a : AllocId} {o' : Owner}
    (ho' : o'.Covered C.D) (hr : ∀ o ∈ C.owners, o.alloc ≠ a → o.Covered C.D) :
    (∀ o ∈ (C.update a o').owners, o.Covered (C.update a o').D) := by
  intro o ho
  dsimp only [Ctx.update] at ho
  rw [List.mem_map] at ho
  obtain ⟨x, hx, rfl⟩ := ho
  show (if x.alloc = a then o' else x).Covered C.D
  split
  · exact ho'
  · rename_i hxa
    exact hr x hx hxa

/-- Allocation identifiers remain distinct when the replacement has the same
allocation identifier as the owner it replaces. -/
theorem Ctx.update_nodup {C : Ctx} {a : AllocId} {o' : Owner}
    (halloc : o'.alloc = a) (hnd : (C.owners.map (·.alloc)).Nodup) :
    ((C.update a o').owners.map (·.alloc)).Nodup := by
  rw [show (C.update a o').owners.map (·.alloc) = C.owners.map (·.alloc) from
    update_alloc_map C.owners a o' halloc]
  exact hnd

/-- Free an allocation only through its recorded disposal capability. -/
def Ctx.freeWith? (C : Ctx) (a : AllocId) (d : CapId) : Option Ctx :=
  match C.findOwner? a with
  | some o => if o.disposal = d then some (C.free a) else none
  | none => none

theorem Ctx.freeWith?_realizes {C C' : Ctx} {a : AllocId} {d : CapId}
    (h : C.freeWith? a d = some C') (hr : C.Realizes) : C'.Realizes := by
  unfold Ctx.freeWith? at h
  cases hf : C.findOwner? a with
  | none => simp [hf] at h
  | some o =>
    by_cases hd : o.disposal = d
    · simp [hf, hd] at h
      cases h
      exact Ctx.free_realizes hr
    · simp [hf, hd] at h

/-- A wrong disposal capability is refused. -/
theorem Ctx.freeWith?_wrong {C : Ctx} {a : AllocId} {d : CapId} {o : Owner}
    (hf : C.findOwner? a = some o) (hd : o.disposal ≠ d) : C.freeWith? a d = none := by
  unfold Ctx.freeWith?
  rw [hf]
  simp [hd]

/-- Dispatch a spatial split to the owner of an allocation, replacing that owner
and leaving the other owners alone. -/
def Ctx.splitAtOwner? (C : Ctx) (o : Owner) (id id1 id2 : CapId) (k : Nat) :
    Option Ctx :=
  (o.splitAt? id id1 id2 k).map (fun o' => C.update o.alloc o')

theorem Ctx.splitAtOwner_realizes {C C' : Ctx} {o : Owner} {id id1 id2 : CapId}
    {k : Nat} (hmem : o ∈ C.owners) (hs : C.splitAtOwner? o id id1 id2 k = some C')
    (hr : C.Realizes) : C'.Realizes := by
  unfold Ctx.splitAtOwner? at hs
  cases ho : o.splitAt? id id1 id2 k with
  | none => simp [ho] at hs
  | some o' =>
    simp [ho] at hs
    cases hs
    refine ⟨?_, ?_⟩
    · apply Ctx.update_covered
      · exact Owner.splitAt_covered ho (hr.1 o hmem)
      · intro x hx _
        exact hr.1 x hx
    · exact Ctx.update_nodup (Owner.splitAt?_alloc ho) hr.2

/-- Dispatch a fractional split to the owner of an allocation. -/
def Ctx.splitFractionOwner? (C : Ctx) (o : Owner) (id id1 id2 : CapId) (q1 q2 : Nat)
    (p1 : 0 < q1) (p2 : 0 < q2) : Option Ctx :=
  (o.splitFraction? id id1 id2 q1 q2 p1 p2).map (fun o' => C.update o.alloc o')

theorem Ctx.splitFractionOwner_realizes {C C' : Ctx} {o : Owner} {id id1 id2 : CapId}
    {q1 q2 : Nat} {p1 : 0 < q1} {p2 : 0 < q2}
    (hmem : o ∈ C.owners)
    (hs : C.splitFractionOwner? o id id1 id2 q1 q2 p1 p2 = some C')
    (hr : C.Realizes) : C'.Realizes := by
  unfold Ctx.splitFractionOwner? at hs
  cases ho : o.splitFraction? id id1 id2 q1 q2 p1 p2 with
  | none => simp [ho] at hs
  | some o' =>
    simp [ho] at hs
    cases hs
    refine ⟨?_, ?_⟩
    · apply Ctx.update_covered
      · exact Owner.splitFraction_covered ho (hr.1 o hmem)
      · intro x hx _
        exact hr.1 x hx
    · exact Ctx.update_nodup (Owner.splitFraction?_alloc ho) hr.2

/-- Dispatch a fractional join to the owner of an allocation, replacing that
owner and leaving the other owners alone. -/
def Ctx.joinFractionOwner? (C : Ctx) (o : Owner) (node newId : CapId) : Option Ctx :=
  (o.joinFraction? node newId).map (C.update o.alloc)

theorem Ctx.joinFractionOwner_realizes {C C' : Ctx} {o : Owner} {node newId : CapId}
    (hmem : o ∈ C.owners)
    (hs : C.joinFractionOwner? o node newId = some C')
    (hr : C.Realizes) : C'.Realizes := by
  unfold Ctx.joinFractionOwner? at hs
  cases ho : o.joinFraction? node newId with
  | none => simp [ho] at hs
  | some o' =>
    simp [ho] at hs
    cases hs
    refine ⟨?_, ?_⟩
    · apply Ctx.update_covered
      · exact Owner.joinFraction_covered ho (hr.1 o hmem)
      · intro x hx _
        exact hr.1 x hx
    · exact Ctx.update_nodup (Owner.joinFraction_alloc ho) hr.2

/-- Allocation of a fresh root and disposal identifier keeps the capability
identifiers distinct. -/
theorem Ctx.alloc_ids_nodup {C : Ctx} {a : AllocId} {n : Nat} {pos : 0 < C.D}
    {rootId disposal : CapId} {hfresh : a ∉ C.owners.map (·.alloc)}
    (hroot : rootId ∉ C.ids) (hdisp : disposal ∉ C.ids) (hne : rootId ≠ disposal)
    (hnd : C.ids.Nodup) :
    (C.alloc a n pos rootId disposal hfresh).ids.Nodup := by
  have hshape : (C.alloc a n pos rootId disposal hfresh).ids
      = [disposal, rootId] ++ C.ids := by
    simp [Ctx.alloc, Ctx.ids, Owner.ids, Owner.init, Tree.ids]
  rw [hshape, List.nodup_append]
  refine ⟨?_, hnd, ?_⟩
  · simp [hne, Ne.symm hne]
  · intro x hx y hy
    simp at hx
    rcases hx with rfl | rfl
    · intro hxy
      exact hdisp (hxy ▸ hy)
    · intro hxy
      exact hroot (hxy ▸ hy)

/-- Filtering owners can only shorten the flattened identifier list. -/
theorem flatMap_filter_sublist (l : List Owner) (p : Owner → Bool) :
    ((l.filter p).flatMap Owner.ids).Sublist (l.flatMap Owner.ids) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    by_cases hx : p x
    · simp only [List.filter, hx, if_true, List.flatMap_cons]
      exact List.Sublist.append (List.Sublist.refl _) ih
    · simp only [List.filter, hx, if_false, List.flatMap_cons]
      exact List.Sublist.cons _
        (List.Sublist.trans ih
          (List.sublist_append_right x.root.ids (List.flatMap Owner.ids xs)))

theorem Ctx.free_ids_nodup {C : Ctx} {a : AllocId} (h : C.ids.Nodup) :
    (C.free a).ids.Nodup := by
  dsimp [Ctx.free, Ctx.ids]
  exact List.Nodup.sublist (flatMap_filter_sublist C.owners (fun o => o.alloc ≠ a)) h

end Cap
