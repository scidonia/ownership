/-
Owner and context invariants for the capability ledger.

The ledger (`Cap.Ledger`) records one allocation per owner: a decomposition tree
whose leaves are capabilities, the allocation's length and the disposal
capability. This module states a *location* invariant on the leaves and a
*disposal* invariant on the owner, bundles them with the existing coverage
invariant, and shows that the owner-level and context-level transitions preserve
the bundle.

Invariant components:

* `Owner.Covered D` (from `Cap.Ledger`): every byte below `o.len` has budget `D`.
* `Owner.LeavesWithin`: every leaf that `Tree.find?` reaches lies inside the
  owner's allocation (`c.alloc = o.alloc`) and inside its extent (`c.hi ≤ o.len`).
* `Owner.DisposalPresent`: the disposal capability either names a leaf of the
  owner's tree, or is absent from the tree's access-capability identifiers
  (`o.root.ids`). The second branch is what allocation produces: `Owner.init`
  records a root id and a disposal id that need not coincide, and a disposal
  token that names no leaf is still a usable key because `Ctx.freeWith?`
  compares it with the recorded field only. Because `Tree.ids` excludes internal
  split-node ids, "absent from `o.root.ids`" means no *leaf* carries the id; an
  internal id that coincides with the disposal id would be a provenance label,
  not a capability.
* `Owner.WellFormed D` = coverage and both of the above.
* `Ctx.WellFormed` = `Ctx.Realizes` (from `Cap.Context`), per-owner
  well-formedness at the context denominator, and distinctness of all capability
  identifiers in the context (`C.ids.Nodup`).

What is proved:

* `Owner.init_wellFormed`: allocation establishes the owner invariant for any
  root and disposal identifier. Because `DisposalPresent` has the
  "no leaf carries it" branch, no side condition on `rootId`/`disposal` is
  needed; the strict "the disposal names a leaf" reading would instead require
  `disposal = rootId`, and `Owner.init_disposalPresent_of_eq` records that case.
* `Ctx.alloc_wellFormed`, `Ctx.free_wellFormed`, `Ctx.freeWith_wellFormed`:
  context allocation, unconditional disposal and disposal-guarded disposal
  preserve `Ctx.WellFormed`.
* `Owner.splitAt?_wellFormed`, `Owner.splitFraction?_wellFormed` and their
  context dispatchers `Ctx.splitAtOwner_wellFormed`,
  `Ctx.splitFractionOwner_wellFormed`: spatial and fractional splits preserve the
  invariant.
* `Owner.joinFraction?_wellFormed` and its context dispatcher
  `Ctx.joinFractionOwner_wellFormed`: the sibling-only fractional join preserves
  the invariant, via `Ctx.update_ids_nodup_of_sub` (the replacement owner's
  identifiers are old ones or the single fresh new identifier).
* A concrete 64-byte owner (and context) satisfying `Owner.WellFormed`.

Explicit hypotheses of the preservation theorems (beyond the invariant itself):

* `Ctx.alloc_wellFormed` needs the allocation identifier fresh among the owners'
  allocation identifiers, both `rootId` and `disposal` absent from `C.ids`, and
  `rootId ≠ disposal` (the last for `Ctx.ids.Nodup`; it is not needed for the new
  owner's `DisposalPresent`, which holds either way).
* `Ctx.free_wellFormed` and `Ctx.freeWith?_wellFormed` need no additional
  hypothesis: disposal removes owners, and `freeWith?` itself checks the recorded
  disposal capability.
* Splits need `o.ids.Nodup` (leaf and disposal identifiers distinct inside the
  owner). At the context level it is derived from `C.ids.Nodup` and
  `o ∈ C.owners`; the owner-level theorems take it as a hypothesis. It rules out
  a second leaf carrying the split leaf's id, which is what makes the disposal
  branch and the identifier list behave.
* The context split theorems additionally need `id1 ∉ C.ids` and `id2 ∉ C.ids`:
  the header's `o.FreshIds` only says the new identifiers are fresh for this
  owner, while the context's identifier list also contains the other owners.
  Freshness across the whole context cannot be derived from the owner-level
  split functions, so it is stated explicitly.
* The context split theorems take `o.FreshIds id1 id2` for the pairwise
  distinctness of the children and the freshness against the owner.
* The split bounds are not hypotheses: `Owner.splitAt?` succeeds only when the
  split index lies in the split leaf's range, and `Owner.splitFraction?` only
  when the two shares add to the leaf's share; a successful split supplies those
  facts. (The relevant child bounds are `Leaf.splitSpatial?_some` and
  `Leaf.splitFractionTree_some`.)

What is not proved: loans and lifetimes, storage agreement, the executable
transitions' guards beyond the split preconditions, and any liveness or
well-bracketing property of the heap. Nothing in this module touches the heap;
loans are imported only to keep the layer's imports as stated.
-/
import Cap.Context
import Cap.Loans
import Cap.Retag

namespace Cap

/-! ### The invariant -/

/-- Every leaf reached by `Tree.find?` lies inside the owner's allocation and
extent. -/
def Owner.LeavesWithin (o : Owner) : Prop :=
  ∀ (id : CapId) (c : Leaf), o.root.find? id = some c → c.alloc = o.alloc ∧ c.hi ≤ o.len

/-- The owner's disposal capability either names a leaf of its own tree or is
not an access-capability identifier of that tree. -/
def Owner.DisposalPresent (o : Owner) : Prop :=
  (∃ c, o.root.find? o.disposal = some c) ∨ o.disposal ∉ o.root.ids

/-- Complete owner invariant for this layer. -/
def Owner.WellFormed (o : Owner) (D : Nat) : Prop :=
  o.Covered D ∧ o.LeavesWithin ∧ o.DisposalPresent

/-- Context invariant: realization, per-owner well-formedness and distinct
capability identifiers. -/
def Ctx.WellFormed (C : Ctx) : Prop :=
  C.Realizes ∧ (∀ o ∈ C.owners, o.WellFormed C.D) ∧ C.ids.Nodup

/-- The three loan-readiness facts every command-level proof about the
delegation route needs: lender names distinct, every lender absent from the
context's live identifiers, and every lender historically issued. They are
clauses 1 (lender half), 6 and 3 of `World.BorrowOK`, stated above the command
dispatcher because `Cap/Borrow.lean` sits downstream of it. -/
def Ctx.LoansReady (C : Ctx) : Prop :=
  (C.loans.loans.map (·.lender)).Nodup
  ∧ (∀ l ∈ C.loans.loans, l.lender ∉ C.ids)
  ∧ (∀ l ∈ C.loans.loans, l.lender ∈ C.issued)

/-- A context with no outstanding loans is loan-ready. -/
theorem Ctx.loansReady_of_loans_nil {C : Ctx} (h : C.loans.loans = []) :
    C.LoansReady := by
  refine ⟨by simp [h], ?_, ?_⟩
  · intro l hl
    simp [h] at hl
  · intro l hl
    simp [h] at hl

/-! ### Supporting lemmas on trees -/

/-- An identifier that some leaf carries occurs in `Tree.ids`. -/
theorem Tree.mem_ids_of_exists_find? {t : Tree} {id : CapId}
    (h : ∃ c, t.find? id = some c) : id ∈ t.ids := by
  induction t with
  | leaf c' =>
    obtain ⟨c, hc⟩ := h
    by_cases hcc : c'.id = id
    · exact List.mem_singleton.mpr hcc.symm
    · simp [Tree.find?, hcc] at hc
  | frac i l r ihl ihr =>
    obtain ⟨c, hc⟩ := h
    cases hlx : l.find? id with
    | some d =>
      exact List.mem_append.mpr (Or.inl (ihl ⟨d, hlx⟩))
    | none =>
      have hr : r.find? id = some c := by simpa only [Tree.find?, hlx] using hc
      exact List.mem_append.mpr (Or.inr (ihr ⟨c, hr⟩))
  | spatial i l r ihl ihr =>
    obtain ⟨c, hc⟩ := h
    cases hlx : l.find? id with
    | some d =>
      exact List.mem_append.mpr (Or.inl (ihl ⟨d, hlx⟩))
    | none =>
      have hr : r.find? id = some c := by simpa only [Tree.find?, hlx] using hc
      exact List.mem_append.mpr (Or.inr (ihr ⟨c, hr⟩))

/-- A leaf identifier found by `Tree.find?` occurs in `Tree.ids`. -/
theorem Tree.find?_mem_ids {t : Tree} {id : CapId} {c : Leaf} (h : t.find? id = some c) :
    id ∈ t.ids :=
  Tree.mem_ids_of_exists_find? ⟨c, h⟩

/-- A list of capability identifiers with no occurrence of `id` is unchanged by
filtering `id` out. -/
private theorem filter_ne_self {l : List CapId} {id : CapId} (h : id ∉ l) :
    l.filter (· ≠ id) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx : ¬ x = id := fun hx' => h (hx' ▸ List.mem_cons_self)
    have hxs : id ∉ xs := fun h' => h (List.mem_cons_of_mem x h')
    have hp : decide (x ≠ id) = true := by simp [hx]
    rw [List.filter_cons, ite_eq_left hp, ih hxs]

/-- Replacing the first leaf found at `id` leaves `Tree.find?` at an `x ≠ id`
unchanged, provided the replacement introduces no `x`. -/
theorem Tree.find?_replace_eq {t : Tree} {id x : CapId} {f : Leaf → Tree}
    (hne : x ≠ id)
    (hf : ∀ c, t.find? id = some c → (f c).find? x = none) :
    (t.replace id f).find? x = t.find? x := by
  induction t with
  | leaf c =>
    by_cases hc : c.id = id
    · have hcx : ¬ c.id = x := fun h => hne (h.symm.trans hc)
      have hix : ¬ id = x := fun h => hne h.symm
      have hid : (Tree.leaf c).find? id = some c := by
        simp [Tree.find?, hc]
      have hnone : (f c).find? x = none := hf c hid
      simp [Tree.replace, Tree.find?, hc, hix, hnone]
    · simp [Tree.replace, Tree.find?, hc]
  | frac i l r ihl ihr =>
    cases hfl : l.find? id with
    | none =>
      have hfr : ∀ c, r.find? id = some c → (f c).find? x = none := by
        intro c hc
        exact hf c (by simp [Tree.find?, hfl, hc])
      simp only [Tree.replace, hfl, Tree.find?]
      rw [ihr hfr]
    | some c0 =>
      have hfl' : ∀ c, l.find? id = some c → (f c).find? x = none := by
        intro c hc
        exact hf c (by simp [Tree.find?, hc])
      simp only [Tree.replace, hfl, Tree.find?]
      rw [ihl hfl']
  | spatial i l r ihl ihr =>
    cases hfl : l.find? id with
    | none =>
      have hfr : ∀ c, r.find? id = some c → (f c).find? x = none := by
        intro c hc
        exact hf c (by simp [Tree.find?, hfl, hc])
      simp only [Tree.replace, hfl, Tree.find?]
      rw [ihr hfr]
    | some c0 =>
      have hfl' : ∀ c, l.find? id = some c → (f c).find? x = none := by
        intro c hc
        exact hf c (by simp [Tree.find?, hc])
      simp only [Tree.replace, hfl, Tree.find?]
      rw [ihl hfl']

/-- Every identifier of the replaced tree either occurred in the original tree
or occurs in the replacement of the first leaf found at `id`. -/
theorem Tree.mem_ids_replace {t : Tree} {id x : CapId} {f : Leaf → Tree}
    (h : x ∈ (t.replace id f).ids) :
    x ∈ t.ids ∨ ∃ c, t.find? id = some c ∧ x ∈ (f c).ids := by
  induction t with
  | leaf c =>
    by_cases hc : c.id = id
    · right
      refine ⟨c, by simp [Tree.find?, hc], ?_⟩
      simpa only [Tree.replace, hc, ite_true] using h
    · left
      have hx : x ∈ ([c.id] : List CapId) := by
        simpa only [Tree.replace, hc, ite_false, Tree.ids] using h
      simpa only [Tree.ids] using hx
  | frac i l r ihl ihr =>
    cases hfl : l.find? id with
    | some c0 =>
      have hh : x ∈ (l.replace id f).ids ++ r.ids := by
        simpa only [Tree.replace, hfl, Tree.ids] using h
      rcases List.mem_append.mp hh with hl | hr
      · rcases ihl hl with hm | ⟨c, hc, hfc⟩
        · exact Or.inl (by simp only [Tree.ids, List.mem_append]; exact Or.inl hm)
        · exact Or.inr ⟨c, by simp [Tree.find?, hc], hfc⟩
      · exact Or.inl (by simp only [Tree.ids, List.mem_append]; exact Or.inr hr)
    | none =>
      have hh : x ∈ l.ids ++ (r.replace id f).ids := by
        simpa only [Tree.replace, hfl, Tree.ids] using h
      rcases List.mem_append.mp hh with hl | hr
      · exact Or.inl (by simp only [Tree.ids, List.mem_append]; exact Or.inl hl)
      · rcases ihr hr with hm | ⟨c, hc, hfc⟩
        · exact Or.inl (by simp only [Tree.ids, List.mem_append]; exact Or.inr hm)
        · exact Or.inr ⟨c, by simp [Tree.find?, hfl, hc], hfc⟩
  | spatial i l r ihl ihr =>
    cases hfl : l.find? id with
    | some c0 =>
      have hh : x ∈ (l.replace id f).ids ++ r.ids := by
        simpa only [Tree.replace, hfl, Tree.ids] using h
      rcases List.mem_append.mp hh with hl | hr
      · rcases ihl hl with hm | ⟨c, hc, hfc⟩
        · exact Or.inl (by simp only [Tree.ids, List.mem_append]; exact Or.inl hm)
        · exact Or.inr ⟨c, by simp [Tree.find?, hc], hfc⟩
      · exact Or.inl (by simp only [Tree.ids, List.mem_append]; exact Or.inr hr)
    | none =>
      have hh : x ∈ l.ids ++ (r.replace id f).ids := by
        simpa only [Tree.replace, hfl, Tree.ids] using h
      rcases List.mem_append.mp hh with hl | hr
      · exact Or.inl (by simp only [Tree.ids, List.mem_append]; exact Or.inl hl)
      · rcases ihr hr with hm | ⟨c, hc, hfc⟩
        · exact Or.inl (by simp only [Tree.ids, List.mem_append]; exact Or.inr hm)
        · exact Or.inr ⟨c, by simp [Tree.find?, hfl, hc], hfc⟩

/-- Replacing the first leaf found at `id` turns the identifier list into the
original list without `id`, followed by the replacement's identifiers. This is
a permutation statement because the replacement sits where the leaf was. -/
theorem Tree.ids_replace_perm {t : Tree} {id : CapId} {f : Leaf → Tree}
    (hnd : t.ids.Nodup) :
    ∀ c, t.find? id = some c →
      (t.replace id f).ids.Perm (t.ids.filter (· ≠ id) ++ (f c).ids) := by
  induction t with
  | leaf c' =>
    intro c h
    by_cases hc : c'.id = id
    · have hcc : c' = c := by
        simpa [Tree.find?, hc] using h
      rw [← hcc]
      simp only [Tree.replace, Tree.ids, hc]
      rw [show ([id] : List CapId).filter (· ≠ id) = [] from by simp]
      rw [List.nil_append]
      exact List.Perm.refl _
    · simp [Tree.find?, hc] at h
  | frac i l r ihl ihr =>
    intro c h
    have hndt : (l.ids ++ r.ids).Nodup := hnd
    obtain ⟨hndl, hndr, hdisj⟩ := List.nodup_append.mp hndt
    cases hfl : l.find? id with
    | some c0 =>
      have hc0 : c = c0 := by
        have h' : (Tree.frac i l r).find? id = some c0 := by simp [Tree.find?, hfl]
        rw [h] at h'
        exact Option.some.inj h'
      rw [hc0]
      have hmem : id ∈ l.ids := Tree.find?_mem_ids hfl
      have hrid : id ∉ r.ids := fun hr => hdisj id hmem id hr rfl
      have hfilt : r.ids.filter (· ≠ id) = r.ids := filter_ne_self hrid
      have ih := ihl hndl c0 hfl
      simp only [Tree.replace, hfl, Tree.ids, List.filter_append, hfilt]
      refine List.Perm.trans (List.Perm.append ih (List.Perm.refl r.ids)) ?_
      have e1 : (l.ids.filter (· ≠ id) ++ (f c0).ids) ++ r.ids
          = l.ids.filter (· ≠ id) ++ ((f c0).ids ++ r.ids) := List.append_assoc ..
      have e2 : (l.ids.filter (· ≠ id) ++ r.ids) ++ (f c0).ids
          = l.ids.filter (· ≠ id) ++ (r.ids ++ (f c0).ids) := List.append_assoc ..
      rw [e1, e2]
      exact List.Perm.append_left _ List.perm_append_comm
    | none =>
      have hr : r.find? id = some c := by simpa only [Tree.find?, hfl] using h
      have hlid : id ∉ l.ids := by
        intro hl
        obtain ⟨d, hd⟩ := Tree.exists_find?_of_mem_ids hl
        rw [hfl] at hd
        cases hd
      have hfilt : l.ids.filter (· ≠ id) = l.ids := filter_ne_self hlid
      have ih := ihr hndr c hr
      simp only [Tree.replace, hfl, Tree.ids, List.filter_append, hfilt]
      refine List.Perm.trans (List.Perm.append_left l.ids ih) ?_
      rw [List.append_assoc]
  | spatial i l r ihl ihr =>
    intro c h
    have hndt : (l.ids ++ r.ids).Nodup := hnd
    obtain ⟨hndl, hndr, hdisj⟩ := List.nodup_append.mp hndt
    cases hfl : l.find? id with
    | some c0 =>
      have hc0 : c = c0 := by
        have h' : (Tree.spatial i l r).find? id = some c0 := by simp [Tree.find?, hfl]
        rw [h] at h'
        exact Option.some.inj h'
      rw [hc0]
      have hmem : id ∈ l.ids := Tree.find?_mem_ids hfl
      have hrid : id ∉ r.ids := fun hr => hdisj id hmem id hr rfl
      have hfilt : r.ids.filter (· ≠ id) = r.ids := filter_ne_self hrid
      have ih := ihl hndl c0 hfl
      simp only [Tree.replace, hfl, Tree.ids, List.filter_append, hfilt]
      refine List.Perm.trans (List.Perm.append ih (List.Perm.refl r.ids)) ?_
      have e1 : (l.ids.filter (· ≠ id) ++ (f c0).ids) ++ r.ids
          = l.ids.filter (· ≠ id) ++ ((f c0).ids ++ r.ids) := List.append_assoc ..
      have e2 : (l.ids.filter (· ≠ id) ++ r.ids) ++ (f c0).ids
          = l.ids.filter (· ≠ id) ++ (r.ids ++ (f c0).ids) := List.append_assoc ..
      rw [e1, e2]
      exact List.Perm.append_left _ List.perm_append_comm
    | none =>
      have hr : r.find? id = some c := by simpa only [Tree.find?, hfl] using h
      have hlid : id ∉ l.ids := by
        intro hl
        obtain ⟨d, hd⟩ := Tree.exists_find?_of_mem_ids hl
        rw [hfl] at hd
        cases hd
      have hfilt : l.ids.filter (· ≠ id) = l.ids := filter_ne_self hlid
      have ih := ihr hndr c hr
      simp only [Tree.replace, hfl, Tree.ids, List.filter_append, hfilt]
      refine List.Perm.trans (List.Perm.append_left l.ids ih) ?_
      rw [List.append_assoc]

/-- Leaves of a two-leaf fractional node are one of its children. -/
theorem Tree.frac_leaf_of_find? {id1 : CapId} {c1 c2 : Leaf} {x : CapId} {d : Leaf}
    (h : (Tree.frac id1 (.leaf c1) (.leaf c2)).find? x = some d) : d = c1 ∨ d = c2 := by
  by_cases hx : c1.id = x
  · left
    have hf : (Tree.frac id1 (.leaf c1) (.leaf c2)).find? x = some c1 := by
      simp [Tree.find?, hx]
    rw [hf] at h
    exact (Option.some.inj h).symm
  · right
    have hf : (Tree.frac id1 (.leaf c1) (.leaf c2)).find? x = (Tree.leaf c2).find? x := by
      simp [Tree.find?, hx]
    rw [hf] at h
    by_cases hx2 : c2.id = x
    · have h2 : (Tree.leaf c2).find? x = some c2 := by simp [Tree.find?, hx2]
      rw [h2] at h
      exact (Option.some.inj h).symm
    · simp [Tree.find?, hx2] at h

/-- Leaves of a two-leaf spatial node are one of its children. -/
theorem Tree.spatial_leaf_of_find? {id1 : CapId} {c1 c2 : Leaf} {x : CapId} {d : Leaf}
    (h : (Tree.spatial id1 (.leaf c1) (.leaf c2)).find? x = some d) : d = c1 ∨ d = c2 := by
  by_cases hx : c1.id = x
  · left
    have hf : (Tree.spatial id1 (.leaf c1) (.leaf c2)).find? x = some c1 := by
      simp [Tree.find?, hx]
    rw [hf] at h
    exact (Option.some.inj h).symm
  · right
    have hf : (Tree.spatial id1 (.leaf c1) (.leaf c2)).find? x = (Tree.leaf c2).find? x := by
      simp [Tree.find?, hx]
    rw [hf] at h
    by_cases hx2 : c2.id = x
    · have h2 : (Tree.leaf c2).find? x = some c2 := by simp [Tree.find?, hx2]
      rw [h2] at h
      exact (Option.some.inj h).symm
    · simp [Tree.find?, hx2] at h

/-- If every leaf found in `t` has `P`, and every leaf of the replacement of the
first leaf found at `id` has `P`, then every leaf found in the replaced tree has
`P`. Distinctness of `t`'s leaf identifiers is needed to know that a leaf found
in one child is not shadowed by a leaf of the other child. -/
theorem Tree.leaves_replace_nodup {t : Tree} {id : CapId} {f : Leaf → Tree}
    {P : Leaf → Prop}
    (hnd : t.ids.Nodup)
    (ht : ∀ x c, t.find? x = some c → P c)
    (hf : ∀ c, t.find? id = some c → ∀ x c', (f c).find? x = some c' → P c') :
    ∀ x c', (t.replace id f).find? x = some c' → P c' := by
  induction t with
  | leaf c =>
    intro x c' hx
    by_cases hc : c.id = id
    · simp only [Tree.replace, hc, ite_true] at hx
      exact hf c (by simp [Tree.find?, hc]) x c' hx
    · by_cases hcx : c.id = x
      · have hrep : (Tree.replace id f (Tree.leaf c)).find? x = (Tree.leaf c).find? x := by
          simp [Tree.replace, hc]
        rw [hrep] at hx
        have hc' : c = c' := by simpa [Tree.find?, hcx] using hx
        rw [← hc']
        exact ht x c (by simp [Tree.find?, hcx])
      · simp [Tree.replace, hc, Tree.find?, hcx] at hx
  | frac i l r ihl ihr =>
    intro x c' hx
    have hndt : (l.ids ++ r.ids).Nodup := hnd
    obtain ⟨hndl, hndr, hdisj⟩ := List.nodup_append.mp hndt
    have htl : ∀ x c, l.find? x = some c → P c := by
      intro x c hx'
      exact ht x c (by simp [Tree.find?, hx'])
    have htr : ∀ x c, r.find? x = some c → P c := by
      intro x c hx'
      have hlx : l.find? x = none := by
        cases h' : l.find? x with
        | none => rfl
        | some d =>
          have hd : x ∈ l.ids := Tree.find?_mem_ids h'
          have hd' : x ∈ r.ids := Tree.find?_mem_ids hx'
          exact absurd rfl (hdisj x hd x hd')
      exact ht x c (by simp [Tree.find?, hlx, hx'])
    cases hfl : l.find? id with
    | some c0 =>
      have hfl' : ∀ c, l.find? id = some c → ∀ x c', (f c).find? x = some c' → P c' := by
        intro c hc x c' hx'
        exact hf c (by simp [Tree.find?, hc]) x c' hx'
      have ih := ihl hndl htl hfl'
      cases hlx : (Tree.replace id f l).find? x with
      | some d =>
        have hcd : d = c' := by
          simpa only [Tree.replace, hfl, Tree.find?, hlx, Option.some.injEq] using hx
        rw [← hcd]
        exact ih x d hlx
      | none =>
        have hrx : r.find? x = some c' := by
          simpa only [Tree.replace, hfl, Tree.find?, hlx] using hx
        have hlx0 : l.find? x = none := by
          cases h' : l.find? x with
          | none => rfl
          | some d =>
            have hd : x ∈ l.ids := Tree.find?_mem_ids h'
            have hd' : x ∈ r.ids := Tree.find?_mem_ids hrx
            exact absurd rfl (hdisj x hd x hd')
        exact ht x c' (by simp [Tree.find?, hlx0, hrx])
    | none =>
      have hfr : ∀ c, r.find? id = some c → ∀ x c', (f c).find? x = some c' → P c' := by
        intro c hc x c' hx'
        exact hf c (by simp [Tree.find?, hfl, hc]) x c' hx'
      have ih := ihr hndr htr hfr
      cases hlx : l.find? x with
      | some d =>
        have hcd : d = c' := by
          simpa only [Tree.replace, hfl, Tree.find?, hlx, Option.some.injEq] using hx
        rw [← hcd]
        exact ht x d (by simp [Tree.find?, hlx])
      | none =>
        have hrx : (Tree.replace id f r).find? x = some c' := by
          simpa only [Tree.replace, hfl, Tree.find?, hlx] using hx
        exact ih x c' hrx
  | spatial i l r ihl ihr =>
    intro x c' hx
    have hndt : (l.ids ++ r.ids).Nodup := hnd
    obtain ⟨hndl, hndr, hdisj⟩ := List.nodup_append.mp hndt
    have htl : ∀ x c, l.find? x = some c → P c := by
      intro x c hx'
      exact ht x c (by simp [Tree.find?, hx'])
    have htr : ∀ x c, r.find? x = some c → P c := by
      intro x c hx'
      have hlx : l.find? x = none := by
        cases h' : l.find? x with
        | none => rfl
        | some d =>
          have hd : x ∈ l.ids := Tree.find?_mem_ids h'
          have hd' : x ∈ r.ids := Tree.find?_mem_ids hx'
          exact absurd rfl (hdisj x hd x hd')
      exact ht x c (by simp [Tree.find?, hlx, hx'])
    cases hfl : l.find? id with
    | some c0 =>
      have hfl' : ∀ c, l.find? id = some c → ∀ x c', (f c).find? x = some c' → P c' := by
        intro c hc x c' hx'
        exact hf c (by simp [Tree.find?, hc]) x c' hx'
      have ih := ihl hndl htl hfl'
      cases hlx : (Tree.replace id f l).find? x with
      | some d =>
        have hcd : d = c' := by
          simpa only [Tree.replace, hfl, Tree.find?, hlx, Option.some.injEq] using hx
        rw [← hcd]
        exact ih x d hlx
      | none =>
        have hrx : r.find? x = some c' := by
          simpa only [Tree.replace, hfl, Tree.find?, hlx] using hx
        have hlx0 : l.find? x = none := by
          cases h' : l.find? x with
          | none => rfl
          | some d =>
            have hd : x ∈ l.ids := Tree.find?_mem_ids h'
            have hd' : x ∈ r.ids := Tree.find?_mem_ids hrx
            exact absurd rfl (hdisj x hd x hd')
        exact ht x c' (by simp [Tree.find?, hlx0, hrx])
    | none =>
      have hfr : ∀ c, r.find? id = some c → ∀ x c', (f c).find? x = some c' → P c' := by
        intro c hc x c' hx'
        exact hf c (by simp [Tree.find?, hfl, hc]) x c' hx'
      have ih := ihr hndr htr hfr
      cases hlx : l.find? x with
      | some d =>
        have hcd : d = c' := by
          simpa only [Tree.replace, hfl, Tree.find?, hlx, Option.some.injEq] using hx
        rw [← hcd]
        exact ht x d (by simp [Tree.find?, hlx])
      | none =>
        have hrx : (Tree.replace id f r).find? x = some c' := by
          simpa only [Tree.replace, hfl, Tree.find?, hlx] using hx
        exact ih x c' hrx

/-- A leaf found inside the located fractional node is found in the whole tree,
provided the tree's identifiers are distinct (so no earlier leaf shadows it). -/
theorem Tree.find?_of_findFrac? {t u : Tree} {node x : CapId} {c : Leaf}
    (hnd : t.ids.Nodup) (hf : t.findFrac? node = some u)
    (hx : u.find? x = some c) : t.find? x = some c := by
  induction t with
  | leaf c' => simp [Tree.findFrac?] at hf
  | frac i l r ihl ihr =>
    by_cases hi : i = node
    · have h1 : Tree.findFrac? node (.frac i l r) = some (.frac i l r) := by
        simp [Tree.findFrac?, hi]
      rw [h1] at hf
      cases hf
      exact hx
    · have hndt : (l.ids ++ r.ids).Nodup := hnd
      obtain ⟨hndl, hndr, hdisj⟩ := List.nodup_append.mp hndt
      cases hfl : l.findFrac? node with
      | some w =>
        have huw : u = w := by
          have h' : Tree.findFrac? node (.frac i l r) = some w := by
            simp [Tree.findFrac?, hi, hfl]
          rw [h'] at hf
          exact (Option.some.inj hf).symm
        subst huw
        have hlf := ihl hndl hfl
        simp [Tree.find?, hlf]
      | none =>
        have hfr : r.findFrac? node = some u := by
          simpa [Tree.findFrac?, hi, hfl] using hf
        have hrf := ihr hndr hfr
        have hxr : x ∈ r.ids := Tree.find?_mem_ids hrf
        have hln : l.find? x = none := by
          cases h' : l.find? x with
          | none => rfl
          | some d =>
            have hxl : x ∈ l.ids := Tree.find?_mem_ids h'
            exact absurd rfl (hdisj x hxl x hxr)
        simp [Tree.find?, hln, hrf]
  | spatial i l r ihl ihr =>
    have hndt : (l.ids ++ r.ids).Nodup := hnd
    obtain ⟨hndl, hndr, hdisj⟩ := List.nodup_append.mp hndt
    cases hfl : l.findFrac? node with
    | some w =>
      have huw : u = w := by
        have h' : Tree.findFrac? node (.spatial i l r) = some w := by
          simp [Tree.findFrac?, hfl]
        rw [h'] at hf
        exact (Option.some.inj hf).symm
      subst huw
      have hlf := ihl hndl hfl
      simp [Tree.find?, hlf]
    | none =>
      have hfr : r.findFrac? node = some u := by
        simpa [Tree.findFrac?, hfl] using hf
      have hrf := ihr hndr hfr
      have hxr : x ∈ r.ids := Tree.find?_mem_ids hrf
      have hln : l.find? x = none := by
        cases h' : l.find? x with
        | none => rfl
        | some d =>
          have hxl : x ∈ l.ids := Tree.find?_mem_ids h'
          exact absurd rfl (hdisj x hxl x hxr)
      simp [Tree.find?, hln, hrf]

/-- If every leaf found in `t` has `P`, and every leaf of the replacement has
`P`, then every leaf found in the node-replaced tree has `P`. Distinctness of
`t`'s leaf identifiers is needed to know that a leaf found in one child is not
shadowed by a leaf of the other child. -/
theorem Tree.leaves_replaceNode_nodup {t : Tree} {node : CapId} {t' : Tree}
    {P : Leaf → Prop}
    (hnd : t.ids.Nodup)
    (ht : ∀ x c, t.find? x = some c → P c)
    (ht' : ∀ x c, t'.find? x = some c → P c) :
    ∀ x c', (Tree.replaceNode node t' t).find? x = some c' → P c' := by
  induction t with
  | leaf c =>
    intro x c' hx
    exact ht x c' hx
  | frac i l r ihl ihr =>
    have hndt : (l.ids ++ r.ids).Nodup := hnd
    obtain ⟨hndl, hndr, hdisj⟩ := List.nodup_append.mp hndt
    have htl : ∀ x c, l.find? x = some c → P c := by
      intro x c hx'
      exact ht x c (by simp [Tree.find?, hx'])
    have htr : ∀ x c, r.find? x = some c → P c := by
      intro x c hx'
      have hlx : l.find? x = none := by
        cases h' : l.find? x with
        | none => rfl
        | some d =>
          have hd : x ∈ l.ids := Tree.find?_mem_ids h'
          have hd' : x ∈ r.ids := Tree.find?_mem_ids hx'
          exact absurd rfl (hdisj x hd x hd')
      exact ht x c (by simp [Tree.find?, hlx, hx'])
    by_cases hi : i = node
    · intro x c' hx
      have hrep : Tree.replaceNode node t' (.frac i l r) = t' := by
        simp [Tree.replaceNode, hi]
      rw [hrep] at hx
      exact ht' x c' hx
    · cases hfl : l.findFrac? node with
      | some w =>
        intro x c' hx
        have hrep : Tree.replaceNode node t' (.frac i l r)
            = .frac i (Tree.replaceNode node t' l) r := by
          simp [Tree.replaceNode, hi, hfl]
        rw [hrep] at hx
        cases hlx : (Tree.replaceNode node t' l).find? x with
        | some d =>
          have hcd : d = c' := by
            simpa only [Tree.find?, hlx, Option.some.injEq] using hx
          rw [← hcd]
          exact ihl hndl htl x d hlx
        | none =>
          have hrx : r.find? x = some c' := by
            simpa only [Tree.find?, hlx] using hx
          exact htr x c' hrx
      | none =>
        intro x c' hx
        have hrep : Tree.replaceNode node t' (.frac i l r)
            = .frac i l (Tree.replaceNode node t' r) := by
          simp [Tree.replaceNode, hi, hfl]
        rw [hrep] at hx
        cases hlx : l.find? x with
        | some d =>
          have hcd : d = c' := by
            simpa only [Tree.find?, hlx, Option.some.injEq] using hx
          rw [← hcd]
          exact htl x d hlx
        | none =>
          have hrx : (Tree.replaceNode node t' r).find? x = some c' := by
            simpa only [Tree.find?, hlx] using hx
          exact ihr hndr htr x c' hrx
  | spatial i l r ihl ihr =>
    have hndt : (l.ids ++ r.ids).Nodup := hnd
    obtain ⟨hndl, hndr, hdisj⟩ := List.nodup_append.mp hndt
    have htl : ∀ x c, l.find? x = some c → P c := by
      intro x c hx'
      exact ht x c (by simp [Tree.find?, hx'])
    have htr : ∀ x c, r.find? x = some c → P c := by
      intro x c hx'
      have hlx : l.find? x = none := by
        cases h' : l.find? x with
        | none => rfl
        | some d =>
          have hd : x ∈ l.ids := Tree.find?_mem_ids h'
          have hd' : x ∈ r.ids := Tree.find?_mem_ids hx'
          exact absurd rfl (hdisj x hd x hd')
      exact ht x c (by simp [Tree.find?, hlx, hx'])
    cases hfl : l.findFrac? node with
    | some w =>
      intro x c' hx
      have hrep : Tree.replaceNode node t' (.spatial i l r)
          = .spatial i (Tree.replaceNode node t' l) r := by
        simp [Tree.replaceNode, hfl]
      rw [hrep] at hx
      cases hlx : (Tree.replaceNode node t' l).find? x with
      | some d =>
        have hcd : d = c' := by
          simpa only [Tree.find?, hlx, Option.some.injEq] using hx
        rw [← hcd]
        exact ihl hndl htl x d hlx
      | none =>
        have hrx : r.find? x = some c' := by
          simpa only [Tree.find?, hlx] using hx
        exact htr x c' hrx
    | none =>
      intro x c' hx
      have hrep : Tree.replaceNode node t' (.spatial i l r)
          = .spatial i l (Tree.replaceNode node t' r) := by
        simp [Tree.replaceNode, hfl]
      rw [hrep] at hx
      cases hlx : l.find? x with
      | some d =>
        have hcd : d = c' := by
          simpa only [Tree.find?, hlx, Option.some.injEq] using hx
        rw [← hcd]
        exact htl x d hlx
      | none =>
        have hrx : (Tree.replaceNode node t' r).find? x = some c' := by
          simpa only [Tree.find?, hlx] using hx
        exact ihr hndr htr x c' hrx

/-- Replacing the located fractional node leaves `Tree.find?` at an `x` that
does not occur under the located node unchanged, provided the replacement does
not introduce `x`. -/
theorem Tree.find?_replaceNode_eq {t : Tree} {node x : CapId} {t' : Tree}
    (hx : ∀ i l r, t.findFrac? node = some (.frac i l r) →
      x ∉ (Tree.frac i l r).ids)
    (hx' : t'.find? x = none) :
    (Tree.replaceNode node t' t).find? x = t.find? x := by
  induction t with
  | leaf c => rfl
  | frac i l r ihl ihr =>
    by_cases hi : i = node
    · have hrep : Tree.replaceNode node t' (.frac i l r) = t' := by
        simp [Tree.replaceNode, hi]
      have hfind : Tree.findFrac? node (.frac i l r) = some (.frac i l r) := by
        simp [Tree.findFrac?, hi]
      have hnot : x ∉ (Tree.frac i l r).ids := hx i l r hfind
      have hnone : (Tree.frac i l r).find? x = none := by
        cases h'' : (Tree.frac i l r).find? x with
        | none => rfl
        | some d => exact absurd (Tree.find?_mem_ids h'') hnot
      rw [hrep, hx', hnone]
    · cases hfl : l.findFrac? node with
      | some w =>
        have hxl : ∀ j l' r', l.findFrac? node = some (.frac j l' r') →
            x ∉ (Tree.frac j l' r').ids := by
          intro j l' r' hj'
          exact hx j l' r' (by simp [Tree.findFrac?, hi, hj'])
        have hrep : Tree.replaceNode node t' (.frac i l r)
            = .frac i (Tree.replaceNode node t' l) r := by
          simp [Tree.replaceNode, hi, hfl]
        rw [hrep]
        have ih := ihl hxl
        rw [show (Tree.frac i (Tree.replaceNode node t' l) r).find? x
            = match (Tree.replaceNode node t' l).find? x with
              | some c => some c | none => r.find? x from rfl]
        rw [show (Tree.frac i l r).find? x
            = match l.find? x with | some c => some c | none => r.find? x from rfl]
        rw [ih]
      | none =>
        have hxr : ∀ j l' r', r.findFrac? node = some (.frac j l' r') →
            x ∉ (Tree.frac j l' r').ids := by
          intro j l' r' hj'
          exact hx j l' r' (by simp [Tree.findFrac?, hi, hfl, hj'])
        have hrep : Tree.replaceNode node t' (.frac i l r)
            = .frac i l (Tree.replaceNode node t' r) := by
          simp [Tree.replaceNode, hi, hfl]
        rw [hrep]
        have ih := ihr hxr
        rw [show (Tree.frac i l (Tree.replaceNode node t' r)).find? x
            = match l.find? x with
              | some c => some c | none => (Tree.replaceNode node t' r).find? x from rfl]
        rw [show (Tree.frac i l r).find? x
            = match l.find? x with | some c => some c | none => r.find? x from rfl]
        rw [ih]
  | spatial i l r ihl ihr =>
    cases hfl : l.findFrac? node with
    | some w =>
      have hxl : ∀ j l' r', l.findFrac? node = some (.frac j l' r') →
          x ∉ (Tree.frac j l' r').ids := by
        intro j l' r' hj'
        exact hx j l' r' (by simp [Tree.findFrac?, hj'])
      have hrep : Tree.replaceNode node t' (.spatial i l r)
          = .spatial i (Tree.replaceNode node t' l) r := by
        simp [Tree.replaceNode, hfl]
      rw [hrep]
      have ih := ihl hxl
      rw [show (Tree.spatial i (Tree.replaceNode node t' l) r).find? x
          = match (Tree.replaceNode node t' l).find? x with
            | some c => some c | none => r.find? x from rfl]
      rw [show (Tree.spatial i l r).find? x
          = match l.find? x with | some c => some c | none => r.find? x from rfl]
      rw [ih]
    | none =>
      have hxr : ∀ j l' r', r.findFrac? node = some (.frac j l' r') →
          x ∉ (Tree.frac j l' r').ids := by
        intro j l' r' hj'
        exact hx j l' r' (by simp [Tree.findFrac?, hfl, hj'])
      have hrep : Tree.replaceNode node t' (.spatial i l r)
          = .spatial i l (Tree.replaceNode node t' r) := by
        simp [Tree.replaceNode, hfl]
      rw [hrep]
      have ih := ihr hxr
      rw [show (Tree.spatial i l (Tree.replaceNode node t' r)).find? x
          = match l.find? x with
            | some c => some c | none => (Tree.replaceNode node t' r).find? x from rfl]
      rw [show (Tree.spatial i l r).find? x
          = match l.find? x with | some c => some c | none => r.find? x from rfl]
      rw [ih]

/-! ### Establishment: allocation -/

/-- The tree produced by a successful fractional split is the two-leaf fractional
node. -/
theorem Leaf.splitFractionTree_some {c : Leaf} {id1 id2 : CapId} {q1 q2 : Nat}
    {p1 : 0 < q1} {p2 : 0 < q2} {t : Tree}
    (h : c.splitFractionTree id1 id2 q1 q2 p1 p2 = some t) :
    ∃ (_hq : q1 + q2 = c.q),
      t = .frac id1
        (.leaf { c with id := id1, q := q1, pos := p1 })
        (.leaf { c with id := id2, q := q2, pos := p2 }) := by
  unfold Leaf.splitFractionTree at h
  split at h
  · rename_i hq
    exact ⟨hq, by simpa using h.symm⟩
  · simp at h

/-- The identifiers of a successful fractional split are the two children. -/
theorem Leaf.splitFractionTree_ids {c : Leaf} {id1 id2 : CapId} {q1 q2 : Nat}
    {p1 : 0 < q1} {p2 : 0 < q2} {t : Tree}
    (h : c.splitFractionTree id1 id2 q1 q2 p1 p2 = some t) : t.ids = [id1, id2] := by
  obtain ⟨_, ht⟩ := Leaf.splitFractionTree_some h
  subst ht
  rfl

/-- The identifiers of a successful spatial split are the two children. -/
theorem Leaf.splitSpatial?_ids {c : Leaf} {id1 id2 : CapId} {k : Nat} {t : Tree}
    (h : c.splitSpatial? id1 id2 k = some t) : t.ids = [id1, id2] := by
  obtain ⟨_, _, ht⟩ := Leaf.splitSpatial?_some h
  subst ht
  rfl

/-- Allocation puts every leaf inside the owner's allocation and extent. -/
theorem Owner.init_leavesWithin (a : AllocId) (n D : Nat) (pos : 0 < D)
    (rootId disposal : CapId) :
    (Owner.init a n D pos rootId disposal).LeavesWithin := by
  intro id c h
  by_cases hc : rootId = id
  · simp [Owner.init, Tree.find?, hc] at h
    cases h
    exact ⟨rfl, Nat.le_refl n⟩
  · simp [Owner.init, Tree.find?, hc] at h

/-- The disposal capability is present after allocation: it either names the
single leaf (when it is the root identifier) or is not a leaf identifier at
all. -/
theorem Owner.init_disposalPresent (a : AllocId) (n D : Nat) (pos : 0 < D)
    (rootId disposal : CapId) :
    (Owner.init a n D pos rootId disposal).DisposalPresent := by
  by_cases h : disposal = rootId
  · left
    have hmem : rootId ∈ (Owner.init a n D pos rootId disposal).root.ids := by
      simp only [Owner.init, Tree.ids, List.mem_singleton]
    obtain ⟨c, hc⟩ := Tree.exists_find?_of_mem_ids hmem
    exact ⟨c, by rwa [h]⟩
  · right
    unfold Owner.init
    simp only [Tree.ids, List.mem_singleton]
    exact h

/-- Allocation establishes the owner invariant, for any root and disposal
identifier. -/
theorem Owner.init_wellFormed (a : AllocId) (n D : Nat) (pos : 0 < D)
    (rootId disposal : CapId) :
    (Owner.init a n D pos rootId disposal).WellFormed D :=
  ⟨Owner.init_covered a n D pos rootId disposal,
   Owner.init_leavesWithin a n D pos rootId disposal,
   Owner.init_disposalPresent a n D pos rootId disposal⟩

/-- Under the strict reading of `DisposalPresent` (the disposal names a leaf),
allocation establishes the invariant exactly when the disposal is the root
leaf's identifier. -/
theorem Owner.init_disposalPresent_of_eq (a : AllocId) (n D : Nat) (pos : 0 < D)
    (rootId disposal : CapId) (h : disposal = rootId) :
    ∃ c, (Owner.init a n D pos rootId disposal).root.find? disposal = some c := by
  have hmem : rootId ∈ (Owner.init a n D pos rootId disposal).root.ids := by
    simp only [Owner.init, Tree.ids, List.mem_singleton]
  obtain ⟨c, hc⟩ := Tree.exists_find?_of_mem_ids hmem
  exact ⟨c, by rwa [h]⟩

/-! ### Preservation: spatial split -/

/-- A spatial split keeps every leaf inside the owner's allocation and extent. -/
theorem Owner.splitAt?_leavesWithin {o o' : Owner} {id id1 id2 : CapId} {k : Nat}
    (hids : o.ids.Nodup) (hs : o.splitAt? id id1 id2 k = some o')
    (hw : o.LeavesWithin) : o'.LeavesWithin := by
  have hroot : o.root.ids.Nodup := (List.nodup_cons.mp hids).2
  unfold Owner.splitAt? at hs
  cases hf : o.root.find? id with
  | none => simp [hf] at hs
  | some c =>
    cases hsp : c.splitSpatial? id1 id2 k with
    | none => simp [hf, hsp] at hs
    | some t =>
      simp only [hf, hsp, Option.map_some, Option.some.injEq] at hs
      subst hs
      obtain ⟨h1, h2, ht⟩ := Leaf.splitSpatial?_some hsp
      have hcw : c.alloc = o.alloc ∧ c.hi ≤ o.len := hw id c hf
      have hspec : ∀ c0, o.root.find? id = some c0 →
          ∀ x c', ((fun _ => t) c0).find? x = some c' →
          c'.alloc = o.alloc ∧ c'.hi ≤ o.len := by
        intro c0 hc0 x c' hc'
        have hc0c : c0 = c := by rw [hf] at hc0; cases hc0; rfl
        subst hc0c
        rw [ht] at hc'
        rcases Tree.spatial_leaf_of_find? hc' with rfl | rfl
        · refine ⟨?_, ?_⟩
          · simpa using hcw.1
          · simp only; omega
        · exact ⟨by simpa using hcw.1, by simpa using hcw.2⟩
      exact Tree.leaves_replace_nodup (t := o.root) (id := id) (f := fun _ => t)
        hroot hw hspec

/-- A fractional split keeps every leaf inside the owner's allocation and
extent. -/
theorem Owner.splitFraction?_leavesWithin {o o' : Owner} {id id1 id2 : CapId}
    {q1 q2 : Nat} {p1 : 0 < q1} {p2 : 0 < q2}
    (hids : o.ids.Nodup) (hs : o.splitFraction? id id1 id2 q1 q2 p1 p2 = some o')
    (hw : o.LeavesWithin) : o'.LeavesWithin := by
  have hroot : o.root.ids.Nodup := (List.nodup_cons.mp hids).2
  unfold Owner.splitFraction? at hs
  cases hf : o.root.find? id with
  | none => simp [hf] at hs
  | some c =>
    cases hsp : c.splitFractionTree id1 id2 q1 q2 p1 p2 with
    | none => simp [hf, hsp] at hs
    | some t =>
      simp only [hf, hsp, Option.map_some, Option.some.injEq] at hs
      subst hs
      obtain ⟨_, ht⟩ := Leaf.splitFractionTree_some hsp
      have hcw : c.alloc = o.alloc ∧ c.hi ≤ o.len := hw id c hf
      have hspec : ∀ c0, o.root.find? id = some c0 →
          ∀ x c', ((fun _ => t) c0).find? x = some c' →
          c'.alloc = o.alloc ∧ c'.hi ≤ o.len := by
        intro c0 hc0 x c' hc'
        have hc0c : c0 = c := by rw [hf] at hc0; cases hc0; rfl
        subst hc0c
        rw [ht] at hc'
        rcases Tree.frac_leaf_of_find? hc' with rfl | rfl
        · exact ⟨by simpa using hcw.1, by simpa using hcw.2⟩
        · exact ⟨by simpa using hcw.1, by simpa using hcw.2⟩
      exact Tree.leaves_replace_nodup (t := o.root) (id := id) (f := fun _ => t)
        hroot hw hspec

/-- A spatial split preserves the disposal branch. -/
theorem Owner.splitAt?_disposalPresent {o o' : Owner} {id id1 id2 : CapId} {k : Nat}
    (hids : o.ids.Nodup) (hfids : o.FreshIds id1 id2)
    (hs : o.splitAt? id id1 id2 k = some o') (hd : o.DisposalPresent) :
    o'.DisposalPresent := by
  have hroot : o.root.ids.Nodup := (List.nodup_cons.mp hids).2
  have hdisp : o.disposal ∉ o.root.ids := (List.nodup_cons.mp hids).1
  obtain ⟨h1f, h2f, _⟩ := hfids
  unfold Owner.splitAt? at hs
  cases hf : o.root.find? id with
  | none => simp [hf] at hs
  | some c =>
    cases hsp : c.splitSpatial? id1 id2 k with
    | none => simp [hf, hsp] at hs
    | some t =>
      simp only [hf, hsp, Option.map_some, Option.some.injEq] at hs
      subst hs
      obtain ⟨h1, h2, ht⟩ := Leaf.splitSpatial?_some hsp
      have hmemid : id ∈ o.root.ids := Tree.find?_mem_ids hf
      have hmemdisp : o.disposal ∈ o.ids := List.mem_cons_self
      have hne : o.disposal ≠ id := fun h => hdisp (h ▸ hmemid)
      have hd1 : id1 ≠ o.disposal := fun h => h1f (h ▸ hmemdisp)
      have hd2 : id2 ≠ o.disposal := fun h => h2f (h ▸ hmemdisp)
      have htnone : t.find? o.disposal = none := by
        rw [ht]
        simp [Tree.find?, hd1, hd2]
      rcases hd with ⟨c', hc'⟩ | hnot
      · left
        refine ⟨c', ?_⟩
        rw [Tree.find?_replace_eq (t := o.root) (id := id) (x := o.disposal)
          (f := fun _ => t) hne (fun _ _ => htnone)]
        exact hc'
      · right
        intro hmem
        rcases Tree.mem_ids_replace (t := o.root) (id := id) (x := o.disposal)
          (f := fun _ => t) hmem with hold | ⟨c0, _, hnew⟩
        · exact hnot hold
        · have htids : t.ids = [id1, id2] := by rw [ht]; rfl
          have hmem' : o.disposal ∈ ([id1, id2] : List CapId) := by
            simpa only [htids] using hnew
          rcases List.mem_cons.mp hmem' with h | h
          · exact h1f (h ▸ hmemdisp)
          · have : o.disposal = id2 := by simpa using h
            exact h2f (this ▸ hmemdisp)

/-- A fractional split preserves the disposal branch. -/
theorem Owner.splitFraction?_disposalPresent {o o' : Owner} {id id1 id2 : CapId}
    {q1 q2 : Nat} {p1 : 0 < q1} {p2 : 0 < q2}
    (hids : o.ids.Nodup) (hfids : o.FreshIds id1 id2)
    (hs : o.splitFraction? id id1 id2 q1 q2 p1 p2 = some o')
    (hd : o.DisposalPresent) : o'.DisposalPresent := by
  have hroot : o.root.ids.Nodup := (List.nodup_cons.mp hids).2
  have hdisp : o.disposal ∉ o.root.ids := (List.nodup_cons.mp hids).1
  obtain ⟨h1f, h2f, _⟩ := hfids
  unfold Owner.splitFraction? at hs
  cases hf : o.root.find? id with
  | none => simp [hf] at hs
  | some c =>
    cases hsp : c.splitFractionTree id1 id2 q1 q2 p1 p2 with
    | none => simp [hf, hsp] at hs
    | some t =>
      simp only [hf, hsp, Option.map_some, Option.some.injEq] at hs
      subst hs
      obtain ⟨_, ht⟩ := Leaf.splitFractionTree_some hsp
      have hmemid : id ∈ o.root.ids := Tree.find?_mem_ids hf
      have hmemdisp : o.disposal ∈ o.ids := List.mem_cons_self
      have hne : o.disposal ≠ id := fun h => hdisp (h ▸ hmemid)
      have hd1 : id1 ≠ o.disposal := fun h => h1f (h ▸ hmemdisp)
      have hd2 : id2 ≠ o.disposal := fun h => h2f (h ▸ hmemdisp)
      have htnone : t.find? o.disposal = none := by
        rw [ht]
        simp [Tree.find?, hd1, hd2]
      rcases hd with ⟨c', hc'⟩ | hnot
      · left
        refine ⟨c', ?_⟩
        rw [Tree.find?_replace_eq (t := o.root) (id := id) (x := o.disposal)
          (f := fun _ => t) hne (fun _ _ => htnone)]
        exact hc'
      · right
        intro hmem
        rcases Tree.mem_ids_replace (t := o.root) (id := id) (x := o.disposal)
          (f := fun _ => t) hmem with hold | ⟨c0, _, hnew⟩
        · exact hnot hold
        · have htids : t.ids = [id1, id2] := by rw [ht]; rfl
          have hmem' : o.disposal ∈ ([id1, id2] : List CapId) := by
            simpa only [htids] using hnew
          rcases List.mem_cons.mp hmem' with h | h
          · exact h1f (h ▸ hmemdisp)
          · have : o.disposal = id2 := by simpa using h
            exact h2f (this ▸ hmemdisp)

/-- A spatial split preserves the owner invariant. -/
theorem Owner.splitAt?_wellFormed {o o' : Owner} {D : Nat} {id id1 id2 : CapId} {k : Nat}
    (hids : o.ids.Nodup) (hfids : o.FreshIds id1 id2)
    (hs : o.splitAt? id id1 id2 k = some o') (hwf : o.WellFormed D) :
    o'.WellFormed D :=
  ⟨Owner.splitAt_covered hs hwf.1,
   Owner.splitAt?_leavesWithin hids hs hwf.2.1,
   Owner.splitAt?_disposalPresent hids hfids hs hwf.2.2⟩

/-- A fractional split preserves the owner invariant. -/
theorem Owner.splitFraction?_wellFormed {o o' : Owner} {D : Nat} {id id1 id2 : CapId}
    {q1 q2 : Nat} {p1 : 0 < q1} {p2 : 0 < q2}
    (hids : o.ids.Nodup) (hfids : o.FreshIds id1 id2)
    (hs : o.splitFraction? id id1 id2 q1 q2 p1 p2 = some o')
    (hwf : o.WellFormed D) : o'.WellFormed D :=
  ⟨Owner.splitFraction_covered hs hwf.1,
   Owner.splitFraction?_leavesWithin hids hs hwf.2.1,
   Owner.splitFraction?_disposalPresent hids hfids hs hwf.2.2⟩

/-! ### Preservation: fractional join -/

/-- A fractional join keeps every leaf inside the owner's allocation and
extent: the new leaf inherits its allocation and footprint from the joined
left child. -/
theorem Owner.joinFraction?_leavesWithin {o o' : Owner} {node newId : CapId}
    (hids : o.ids.Nodup) (hs : o.joinFraction? node newId = some o')
    (hw : o.LeavesWithin) : o'.LeavesWithin := by
  have hroot : o.root.ids.Nodup := (List.nodup_cons.mp hids).2
  unfold Owner.joinFraction? at hs
  cases hf : o.root.findFrac? node with
  | none => simp [hf] at hs
  | some tn =>
    cases hj : tn.joinChildren? newId with
    | none => simp [hf, hj] at hs
    | some t' =>
      simp only [hf, hj, Option.some.injEq] at hs
      subst hs
      obtain ⟨i, c1, c2, htn, -, -, ht'find⟩ := Tree.joinChildren?_some hj
      subst htn
      have hc1find : o.root.find? c1.id = some c1 :=
        Tree.find?_of_findFrac? hroot hf (by simp [Tree.find?])
      have hc1w := hw c1.id c1 hc1find
      intro x c' hx
      exact Tree.leaves_replaceNode_nodup (t := o.root) (node := node) (t' := t')
        hroot hw
        (fun y c hy => by
          obtain ⟨-, ha, hh⟩ := ht'find y c hy
          exact ⟨ha.trans hc1w.1, by rw [hh]; exact hc1w.2⟩)
        x c' hx

/-- A fractional join preserves the disposal branch when the new identifier is
fresh. -/
theorem Owner.joinFraction?_disposalPresent {o o' : Owner} {node newId : CapId}
    (hids : o.ids.Nodup) (hfresh : newId ∉ o.ids)
    (hs : o.joinFraction? node newId = some o') (hd : o.DisposalPresent) :
    o'.DisposalPresent := by
  have hdisp : o.disposal ∉ o.root.ids := (List.nodup_cons.mp hids).1
  unfold Owner.joinFraction? at hs
  cases hf : o.root.findFrac? node with
  | none => simp [hf] at hs
  | some tn =>
    cases hj : tn.joinChildren? newId with
    | none => simp [hf, hj] at hs
    | some t' =>
      simp only [hf, hj, Option.some.injEq] at hs
      subst hs
      obtain ⟨i, c1, c2, htn, -, ht'ids, ht'find⟩ := Tree.joinChildren?_some hj
      subst htn
      have hmemdisp : o.disposal ∈ o.ids := List.mem_cons_self
      have hdnew : o.disposal ≠ newId := fun hEq => hfresh (hEq ▸ hmemdisp)
      have hc1mem : c1.id ∈ o.root.ids := Tree.findFrac?_ids_sub hf (by simp [Tree.ids])
      have hc2mem : c2.id ∈ o.root.ids := Tree.findFrac?_ids_sub hf (by simp [Tree.ids])
      have hd1 : o.disposal ≠ c1.id := fun hEq => hdisp (hEq ▸ hc1mem)
      have hd2 : o.disposal ≠ c2.id := fun hEq => hdisp (hEq ▸ hc2mem)
      have htnone : t'.find? o.disposal = none := by
        cases htf : t'.find? o.disposal with
        | none => rfl
        | some d =>
          obtain ⟨hxd, -, -⟩ := ht'find o.disposal d htf
          exact absurd hxd hdnew
      rcases hd with ⟨c', hc'⟩ | hnot
      · left
        refine ⟨c', ?_⟩
        rw [Tree.find?_replaceNode_eq (t := o.root) (node := node) (t' := t')
          (x := o.disposal) ?_ htnone]
        exact hc'
        intro j l r hfind
        rw [hf] at hfind
        cases hfind
        simp only [Tree.ids, List.mem_append, List.mem_singleton]
        rintro (h | h)
        · exact hd1 h
        · exact hd2 h
      · right
        intro hmem
        rcases Tree.mem_ids_replaceNode hmem with hold | hnew
        · exact hnot hold
        · rw [ht'ids] at hnew
          exact hfresh ((List.mem_singleton.mp hnew) ▸ hmemdisp)

/-- A fractional join preserves the owner invariant. -/
theorem Owner.joinFraction?_wellFormed {o o' : Owner} {D : Nat} {node newId : CapId}
    (hids : o.ids.Nodup) (hfresh : newId ∉ o.ids)
    (hs : o.joinFraction? node newId = some o') (hwf : o.WellFormed D) :
    o'.WellFormed D :=
  ⟨Owner.joinFraction_covered hs hwf.1,
   Owner.joinFraction?_leavesWithin hids hs hwf.2.1,
   Owner.joinFraction?_disposalPresent hids hfresh hs hwf.2.2⟩

/-! ### Identifier lists after a split -/

/-- A spatial split turns the owner's identifier list into the old list without
the split leaf, followed by the two children. -/
theorem Owner.splitAt?_ids_perm {o o' : Owner} {id id1 id2 : CapId} {k : Nat}
    (hids : o.ids.Nodup) (hs : o.splitAt? id id1 id2 k = some o') :
    o'.ids.Perm (o.ids.filter (· ≠ id) ++ [id1, id2]) := by
  have hroot : o.root.ids.Nodup := (List.nodup_cons.mp hids).2
  have hdisp : o.disposal ∉ o.root.ids := (List.nodup_cons.mp hids).1
  unfold Owner.splitAt? at hs
  cases hf : o.root.find? id with
  | none => simp [hf] at hs
  | some c =>
    cases hsp : c.splitSpatial? id1 id2 k with
    | none => simp [hf, hsp] at hs
    | some t =>
      simp only [hf, hsp, Option.map_some, Option.some.injEq] at hs
      subst hs
      have hperm := Tree.ids_replace_perm (t := o.root) (id := id) (f := fun _ => t) hroot c hf
      have htids : t.ids = [id1, id2] := Leaf.splitSpatial?_ids hsp
      have hne : o.disposal ≠ id := fun hEq => hdisp (hEq ▸ Tree.find?_mem_ids hf)
      have hfilt : (o.disposal :: o.root.ids).filter (· ≠ id)
          = o.disposal :: o.root.ids.filter (· ≠ id) := by
        rw [List.filter_cons, ite_eq_left (by simp [hne])]
      simp only [Owner.ids]
      rw [hfilt]
      exact List.Perm.cons o.disposal (by simpa [htids] using hperm)

/-- A fractional split turns the owner's identifier list into the old list
without the split leaf, followed by the two children. -/
theorem Owner.splitFraction?_ids_perm {o o' : Owner} {id id1 id2 : CapId}
    {q1 q2 : Nat} {p1 : 0 < q1} {p2 : 0 < q2}
    (hids : o.ids.Nodup) (hs : o.splitFraction? id id1 id2 q1 q2 p1 p2 = some o') :
    o'.ids.Perm (o.ids.filter (· ≠ id) ++ [id1, id2]) := by
  have hroot : o.root.ids.Nodup := (List.nodup_cons.mp hids).2
  have hdisp : o.disposal ∉ o.root.ids := (List.nodup_cons.mp hids).1
  unfold Owner.splitFraction? at hs
  cases hf : o.root.find? id with
  | none => simp [hf] at hs
  | some c =>
    cases hsp : c.splitFractionTree id1 id2 q1 q2 p1 p2 with
    | none => simp [hf, hsp] at hs
    | some t =>
      simp only [hf, hsp, Option.map_some, Option.some.injEq] at hs
      subst hs
      have hperm := Tree.ids_replace_perm (t := o.root) (id := id) (f := fun _ => t) hroot c hf
      have htids : t.ids = [id1, id2] := Leaf.splitFractionTree_ids hsp
      have hne : o.disposal ≠ id := fun hEq => hdisp (hEq ▸ Tree.find?_mem_ids hf)
      have hfilt : (o.disposal :: o.root.ids).filter (· ≠ id)
          = o.disposal :: o.root.ids.filter (· ≠ id) := by
        rw [List.filter_cons, ite_eq_left (by simp [hne])]
      simp only [Owner.ids]
      rw [hfilt]
      exact List.Perm.cons o.disposal (by simpa [htids] using hperm)

/-- A successful spatial split's leaf identifier occurs in the owner's
identifiers. -/
theorem Owner.splitAt?_mem_ids {o o' : Owner} {id id1 id2 : CapId} {k : Nat}
    (hs : o.splitAt? id id1 id2 k = some o') : id ∈ o.ids := by
  unfold Owner.splitAt? at hs
  cases hf : o.root.find? id with
  | none => simp [hf] at hs
  | some c => exact List.mem_cons_of_mem o.disposal (Tree.find?_mem_ids hf)

/-- A successful fractional split's leaf identifier occurs in the owner's
identifiers. -/
theorem Owner.splitFraction?_mem_ids {o o' : Owner} {id id1 id2 : CapId}
    {q1 q2 : Nat} {p1 : 0 < q1} {p2 : 0 < q2}
    (hs : o.splitFraction? id id1 id2 q1 q2 p1 p2 = some o') : id ∈ o.ids := by
  unfold Owner.splitFraction? at hs
  cases hf : o.root.find? id with
  | none => simp [hf] at hs
  | some c => exact List.mem_cons_of_mem o.disposal (Tree.find?_mem_ids hf)

/-! ### Context-level preservation -/

/-- Every owner's identifier list is duplicate-free in a context with
duplicate-free identifiers. -/
theorem flatMap_nodup_of_mem {l : List Owner} {f : Owner → List CapId} {o : Owner}
    (hnd : (l.flatMap f).Nodup) (hmem : o ∈ l) : (f o).Nodup := by
  induction l with
  | nil => simp at hmem
  | cons x xs ih =>
    rw [List.flatMap_cons] at hnd
    obtain ⟨hx, hxs, _⟩ := List.nodup_append.mp hnd
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · exact hx
    · exact ih hxs hmem'

/-- Owners of a list with duplicate-free identifier lists are identifier-disjoint:
one identifier cannot occur in two distinct owners. -/
theorem flatMap_disjoint_of_nodup {l : List Owner} {f : Owner → List CapId}
    (hnd : (l.flatMap f).Nodup) {x y : Owner} (hx : x ∈ l) (hy : y ∈ l)
    (hne : x ≠ y) : ∀ id, id ∈ f x → id ∈ f y → False := by
  induction l with
  | nil => simp at hx
  | cons z zs ih =>
    rw [List.flatMap_cons] at hnd
    obtain ⟨hz, hzs, hdisj⟩ := List.nodup_append.mp hnd
    rcases List.mem_cons.mp hx with rfl | hx'
    · rcases List.mem_cons.mp hy with rfl | hy'
      · exact absurd rfl hne
      · intro id hidx hidy
        exact absurd rfl (hdisj id hidx id (List.mem_flatMap.mpr ⟨y, hy', hidy⟩))
    · rcases List.mem_cons.mp hy with rfl | hy'
      · intro id hidx hidy
        exact absurd rfl (hdisj id hidy id (List.mem_flatMap.mpr ⟨x, hx', hidx⟩))
      · exact ih hzs hx' hy'

/-- Distinct owners of a well-formed context share no capability identifier. -/
theorem Ctx.ids_disjoint_of_ne {C : Ctx} (hnd : C.ids.Nodup) {o o' : Owner}
    (ho : o ∈ C.owners) (ho' : o' ∈ C.owners) (hne : o ≠ o') :
    ∀ id, id ∈ o.ids → id ∈ o'.ids → False :=
  flatMap_disjoint_of_nodup (l := C.owners) (f := Owner.ids) hnd ho ho' hne

/-- An owner's identifiers are duplicate-free in a well-formed context. -/
theorem Ctx.owner_ids_nodup {C : Ctx} {o : Owner} (hnd : C.ids.Nodup)
    (hmem : o ∈ C.owners) : o.ids.Nodup :=
  flatMap_nodup_of_mem (l := C.owners) (f := Owner.ids) hnd hmem

/-- Owners with equal allocation identifiers are equal, when the allocation
identifiers of a list of owners are distinct. -/
theorem alloc_eq_of_mem {l : List Owner} {x y : Owner}
    (hnd : (l.map (·.alloc)).Nodup) (hx : x ∈ l) (hy : y ∈ l)
    (ha : x.alloc = y.alloc) : x = y := by
  induction l with
  | nil => simp at hx
  | cons z zs ih =>
    obtain ⟨hznd, hzsnd⟩ := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp hx with hxz | hx'
    · rcases List.mem_cons.mp hy with hyz | hy'
      · rw [hxz, hyz]
      · have hmem : y.alloc ∈ zs.map (·.alloc) := by
          rw [List.mem_map]
          exact ⟨y, hy', rfl⟩
        have hzy : z.alloc = y.alloc := by rw [← hxz]; exact ha
        have hmem' : z.alloc ∈ zs.map (·.alloc) := by
          have h2 := hmem
          rw [← hzy] at h2
          exact h2
        exact absurd hmem' hznd
    · rcases List.mem_cons.mp hy with hyz | hy'
      · have hmem : x.alloc ∈ zs.map (·.alloc) := by
          rw [List.mem_map]
          exact ⟨x, hx', rfl⟩
        have hxz : x.alloc = z.alloc := by rw [hyz] at ha; exact ha
        have hmem' : z.alloc ∈ zs.map (·.alloc) := by
          have h2 := hmem
          rw [hxz] at h2
          exact h2
        exact absurd hmem' hznd
      · exact ih hzsnd hx' hy'

/-- Updating the owner for one allocation changes the context identifier list
into the old list without the split leaf, followed by the two children. -/
theorem flatMap_update_perm {l : List Owner} {a : AllocId} {o o' : Owner}
    {id id1 id2 : CapId}
    (hndAlloc : (l.map (·.alloc)).Nodup)
    (hidsnd : (l.flatMap Owner.ids).Nodup)
    (hmem : o ∈ l) (hoa : o.alloc = a)
    (hidmem : id ∈ o.ids)
    (hperm : o'.ids.Perm (o.ids.filter (· ≠ id) ++ [id1, id2])) :
    ((l.map (fun x => if x.alloc = a then o' else x)).flatMap Owner.ids).Perm
      ((l.flatMap Owner.ids).filter (· ≠ id) ++ [id1, id2]) := by
  induction l with
  | nil => simp at hmem
  | cons x xs ih =>
    have hndx : (xs.map (·.alloc)).Nodup := (List.nodup_cons.mp hndAlloc).2
    have hnxt : (xs.flatMap Owner.ids).Nodup := (List.nodup_append.mp hidsnd).2.1
    by_cases hxa : x.alloc = a
    · have hxo : x = o :=
        alloc_eq_of_mem hndAlloc List.mem_cons_self hmem (by rw [hxa, hoa])
      rw [hxo] at ⊢
      have hoa' : o.alloc = a := hxo ▸ hxa
      have hoxs : o ∉ xs := by
        intro ho'
        have hmemmap : a ∈ xs.map (·.alloc) := by
          rw [List.mem_map]
          exact ⟨o, ho', hoa⟩
        have hmemmap' : x.alloc ∈ xs.map (·.alloc) := by
          have h2 := hmemmap
          rw [← hxa] at h2
          exact h2
        exact (List.nodup_cons.mp hndAlloc).1 hmemmap' 
      have hxsmap : xs.map (fun y => if y.alloc = a then o' else y) = xs := by
        have h := List.map_congr_left (l := xs)
          (f := fun y => if y.alloc = a then o' else y) (g := fun y => y)
          (fun y hy => by
            have hya : y.alloc ≠ a := by
              intro hya
              have hyo : y = o :=
                alloc_eq_of_mem (l := x :: xs) (x := y) (y := o) hndAlloc
                  (List.mem_cons_of_mem x hy) hmem (by rw [hya, hoa])
              exact hoxs (hyo ▸ hy)
            simp [hya])
        simpa using h
      have hidxs : id ∉ xs.flatMap Owner.ids := by
        have hdisj := (List.nodup_append.mp hidsnd).2.2
        have hidx : id ∈ x.ids := hxo.symm ▸ hidmem
        exact fun hmem' => hdisj id hidx id hmem' rfl
      rw [List.map_cons, ite_eq_left hoa', List.flatMap_cons, List.flatMap_cons, hxsmap,
        List.filter_append, filter_ne_self hidxs]
      refine List.Perm.trans
        (List.Perm.append hperm (List.Perm.refl (xs.flatMap Owner.ids))) ?_
      rw [List.append_assoc, List.append_assoc]
      exact List.Perm.append_left _ List.perm_append_comm
    · have hxo : x ≠ o := fun hEq => hxa (by rw [hEq]; exact hoa)
      have hmem' : o ∈ xs := by
        rcases List.mem_cons.mp hmem with h | h
        · exact (hxo h.symm).elim
        · exact h
      have hidx : id ∉ x.ids := by
        have hdisj := (List.nodup_append.mp hidsnd).2.2
        have hxsid : id ∈ xs.flatMap Owner.ids := by
          rw [List.mem_flatMap]
          exact ⟨o, hmem', hidmem⟩
        exact fun hid => hdisj id hid id hxsid rfl
      have ihxs := ih hndx hnxt hmem'
      rw [List.map_cons, ite_eq_right hxa, List.flatMap_cons, List.flatMap_cons,
        List.filter_append, filter_ne_self hidx]
      refine List.Perm.trans (List.Perm.append_left x.ids ihxs) ?_
      rw [List.append_assoc]

/-- A context update preserves identifier distinctness when the replacement's
identifiers are the old owner's list without the split leaf followed by fresh,
distinct children. -/
theorem Ctx.update_ids_nodup {C : Ctx} {a : AllocId} {o o' : Owner} {id id1 id2 : CapId}
    (hreal : C.Realizes) (hmem : o ∈ C.owners) (halloc : o.alloc = a)
    (hnd : C.ids.Nodup) (hidmem : id ∈ o.ids)
    (hperm : o'.ids.Perm (o.ids.filter (· ≠ id) ++ [id1, id2]))
    (h1 : id1 ∉ C.ids) (h2 : id2 ∉ C.ids) (hne : id1 ≠ id2) :
    (C.update a o').ids.Nodup := by
  have hpermNew := flatMap_update_perm (l := C.owners) (a := a) (o := o) (o' := o')
    (id := id) (id1 := id1) (id2 := id2) hreal.2 hnd hmem halloc hidmem hperm
  have hfilter : (C.ids.filter (· ≠ id)).Nodup :=
    List.Nodup.sublist List.filter_sublist hnd
  have hsingle : ([id1, id2] : List CapId).Nodup := by simp [hne]
  have hdisj : ∀ x ∈ C.ids.filter (· ≠ id), ∀ y ∈ ([id1, id2] : List CapId), x ≠ y := by
    intro x hx y hy
    have hxC : x ∈ C.ids := List.filter_sublist.subset hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact fun h => h1 (h ▸ hxC)
    · exact fun h => h2 (h ▸ hxC)
  have hnodup : ((C.ids.filter (· ≠ id)) ++ [id1, id2]).Nodup :=
    List.nodup_append.mpr ⟨hfilter, hsingle, hdisj⟩
  exact (hpermNew.nodup_iff).mpr hnodup

/-- Updating the owner for one allocation keeps the context identifier list
duplicate-free when the replacement's identifiers are duplicate-free, are drawn
from the old owner's identifiers or a single new identifier, and the new
identifier is fresh for the whole list. The conjunction also records that the
updated list introduces nothing beyond the old list and the new identifier,
which the induction needs for the disjointness side condition. -/
theorem flatMap_update_ids_nodup_of_sub (l : List Owner) (a : AllocId) (o o' : Owner)
    (newId : CapId)
    (hndAlloc : (l.map (·.alloc)).Nodup)
    (hidsnd : (l.flatMap Owner.ids).Nodup)
    (hmem : o ∈ l) (hoa : o.alloc = a)
    (ho'nd : o'.ids.Nodup)
    (hsub : ∀ x ∈ o'.ids, x ∈ o.ids ∨ x = newId)
    (hfresh : newId ∉ l.flatMap Owner.ids) :
    ((l.map (fun x => if x.alloc = a then o' else x)).flatMap Owner.ids).Nodup ∧
    ∀ x ∈ (l.map (fun x => if x.alloc = a then o' else x)).flatMap Owner.ids,
      x ∈ l.flatMap Owner.ids ∨ x = newId := by
  induction l with
  | nil => simp at hmem
  | cons x xs ih =>
    have hndx : (xs.map (·.alloc)).Nodup := (List.nodup_cons.mp hndAlloc).2
    have hidsxs : (xs.flatMap Owner.ids).Nodup := (List.nodup_append.mp hidsnd).2.1
    have hxsnd : x.ids.Nodup := (List.nodup_append.mp hidsnd).1
    have hdisj : ∀ y ∈ x.ids, ∀ z ∈ xs.flatMap Owner.ids, y ≠ z :=
      (List.nodup_append.mp hidsnd).2.2
    have hxfresh : newId ∉ x.ids := fun h => hfresh (List.mem_append_left _ h)
    have hfreshxs : newId ∉ xs.flatMap Owner.ids :=
      fun h => hfresh (List.mem_append_right _ h)
    by_cases hxa : x.alloc = a
    · have hxo : x = o :=
        alloc_eq_of_mem hndAlloc List.mem_cons_self hmem (by rw [hxa, hoa])
      subst x
      have hoxs : o ∉ xs := by
        intro ho'
        have h1 : o.alloc ∈ xs.map (·.alloc) := by
          rw [List.mem_map]
          exact ⟨o, ho', rfl⟩
        exact (List.nodup_cons.mp hndAlloc).1 h1
      have hxsmap : xs.map (fun y => if y.alloc = a then o' else y) = xs := by
        have h := List.map_congr_left (l := xs)
          (f := fun y => if y.alloc = a then o' else y) (g := fun y => y)
          (fun y hy => by
            have hya : y.alloc ≠ a := by
              intro hya
              have hyo : y = o :=
                alloc_eq_of_mem (l := o :: xs) (x := y) (y := o) hndAlloc
                  (List.mem_cons_of_mem o hy) List.mem_cons_self (by rw [hya, hoa])
              exact hoxs (hyo ▸ hy)
            simp [hya])
        simpa using h
      rw [List.map_cons, ite_eq_left hoa, List.flatMap_cons, hxsmap]
      refine ⟨List.nodup_append.mpr ⟨ho'nd, hidsxs, ?_⟩, ?_⟩
      · intro y hy z hz
        rcases hsub y hy with hyo | rfl
        · exact hdisj y hyo z hz
        · exact fun h => hfreshxs (h ▸ hz)
      · intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · rcases hsub w hw with hwo | rfl
          · exact Or.inl (List.mem_append_left _ hwo)
          · exact Or.inr rfl
        · exact Or.inl (List.mem_append_right _ hw)
    · have hxo : x ≠ o := fun hEq => hxa (by rw [hEq]; exact hoa)
      have hmem' : o ∈ xs := by
        rcases List.mem_cons.mp hmem with h | h
        · exact (hxo h.symm).elim
        · exact h
      have ih := ih hndx hidsxs hmem' hfreshxs
      rw [List.map_cons, ite_eq_right hxa, List.flatMap_cons]
      refine ⟨List.nodup_append.mpr ⟨hxsnd, ih.1, ?_⟩, ?_⟩
      · intro y hy z hz
        rcases ih.2 z hz with hzo | rfl
        · exact hdisj y hy z hzo
        · exact fun h => hxfresh (h ▸ hy)
      · intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · exact Or.inl (List.mem_append_left _ hw)
        · rcases ih.2 w hw with hwo | rfl
          · exact Or.inl (List.mem_append_right _ hwo)
          · exact Or.inr rfl

/-- A context update preserves identifier distinctness when the replacement's
identifiers are duplicate-free, each of them is an old identifier of the
replaced owner or the single new identifier, and the new identifier is fresh
for the whole context. This is the join-shaped counterpart of
`Ctx.update_ids_nodup`. -/
theorem Ctx.update_ids_nodup_of_sub {C : Ctx} {a : AllocId} {o o' : Owner}
    {newId : CapId}
    (hreal : C.Realizes) (hmem : o ∈ C.owners) (halloc : o.alloc = a)
    (hnd : C.ids.Nodup) (ho'nd : o'.ids.Nodup)
    (hsub : ∀ x ∈ o'.ids, x ∈ o.ids ∨ x = newId) (hfresh : newId ∉ C.ids) :
    (C.update a o').ids.Nodup :=
  (flatMap_update_ids_nodup_of_sub C.owners a o o' newId hreal.2 hnd hmem halloc
    ho'nd hsub hfresh).1

/-- Owners other than the updated allocation keep their well-formedness. -/
theorem Ctx.update_wellFormed_owners {C : Ctx} {a : AllocId} {o' : Owner}
    (ho' : o'.WellFormed C.D)
    (hothers : ∀ o ∈ C.owners, o.alloc ≠ a → o.WellFormed C.D) :
    ∀ o ∈ (C.update a o').owners, o.WellFormed C.D := by
  intro o ho
  simp only [Ctx.update] at ho
  rw [List.mem_map] at ho
  obtain ⟨x, hx, rfl⟩ := ho
  by_cases hxa : x.alloc = a
  · rw [ite_eq_left hxa]
    exact ho'
  · rw [ite_eq_right hxa]
    exact hothers x hx hxa

/-- Allocation preserves the context invariant. -/
theorem Ctx.alloc_wellFormed {C : Ctx} {a : AllocId} {n : Nat} {pos : 0 < C.D}
    {rootId disposal : CapId} {hfresh : a ∉ C.owners.map (·.alloc)}
    (hwf : C.WellFormed) (hroot : rootId ∉ C.ids) (hdisp : disposal ∉ C.ids)
    (hne : rootId ≠ disposal) :
    (C.alloc a n pos rootId disposal hfresh).WellFormed := by
  refine ⟨Ctx.alloc_realizes hwf.1, ?_, Ctx.alloc_ids_nodup hroot hdisp hne hwf.2.2⟩
  intro o ho
  simp only [Ctx.alloc, List.mem_cons] at ho
  rcases ho with rfl | ho
  · exact Owner.init_wellFormed a n C.D pos rootId disposal
  · exact hwf.2.1 o ho

/-- Unconditional disposal preserves the context invariant. -/
theorem Ctx.free_wellFormed {C : Ctx} {a : AllocId} (hwf : C.WellFormed) :
    (C.free a).WellFormed := by
  refine ⟨Ctx.free_realizes hwf.1, ?_, Ctx.free_ids_nodup hwf.2.2⟩
  intro o ho
  exact hwf.2.1 o (List.mem_filter.mp ho).1

/-- Disposal guarded by the owner's disposal capability preserves the context
invariant. -/
theorem Ctx.freeWith?_wellFormed {C C' : Ctx} {a : AllocId} {d : CapId}
    (hwf : C.WellFormed) (h : C.freeWith? a d = some C') : C'.WellFormed := by
  unfold Ctx.freeWith? at h
  cases hf : C.findOwner? a with
  | none => simp [hf] at h
  | some o =>
    by_cases hd : o.disposal = d
    · simp only [hf] at h
      rw [ite_eq_left hd] at h
      cases h
      exact Ctx.free_wellFormed hwf
    · simp [hf, hd] at h

/-- A spatial split dispatched to its owner preserves the context invariant,
provided the children are fresh for the whole context. -/
theorem Ctx.splitAtOwner_wellFormed {C C' : Ctx} {o : Owner} {id id1 id2 : CapId}
    {k : Nat} (hwf : C.WellFormed) (hmem : o ∈ C.owners) (hfids : o.FreshIds id1 id2)
    (hfresh1 : id1 ∉ C.ids) (hfresh2 : id2 ∉ C.ids)
    (hs : C.splitAtOwner? o id id1 id2 k = some C') : C'.WellFormed := by
  have hreal := Ctx.splitAtOwner_realizes hmem hs hwf.1
  have hoids : o.ids.Nodup := Ctx.owner_ids_nodup hwf.2.2 hmem
  unfold Ctx.splitAtOwner? at hs
  cases ho : o.splitAt? id id1 id2 k with
  | none => simp [ho] at hs
  | some o' =>
    simp only [ho, Option.map_some, Option.some.injEq] at hs
    subst hs
    have hown : o.WellFormed C.D := hwf.2.1 o hmem
    have ho' : o'.WellFormed C.D := Owner.splitAt?_wellFormed hoids hfids ho hown
    have hidmem : id ∈ o.ids := Owner.splitAt?_mem_ids ho
    have hperm := Owner.splitAt?_ids_perm hoids ho
    refine ⟨hreal, ?_, ?_⟩
    · exact Ctx.update_wellFormed_owners ho' (fun x hx _ => hwf.2.1 x hx)
    · exact Ctx.update_ids_nodup hwf.1 hmem rfl hwf.2.2 hidmem
        hperm hfresh1 hfresh2 hfids.2.2

/-- A fractional split dispatched to its owner preserves the context invariant,
provided the children are fresh for the whole context. -/
theorem Ctx.splitFractionOwner_wellFormed {C C' : Ctx} {o : Owner}
    {id id1 id2 : CapId} {q1 q2 : Nat} {p1 : 0 < q1} {p2 : 0 < q2}
    (hwf : C.WellFormed) (hmem : o ∈ C.owners) (hfids : o.FreshIds id1 id2)
    (hfresh1 : id1 ∉ C.ids) (hfresh2 : id2 ∉ C.ids)
    (hs : C.splitFractionOwner? o id id1 id2 q1 q2 p1 p2 = some C') :
    C'.WellFormed := by
  have hreal := Ctx.splitFractionOwner_realizes hmem hs hwf.1
  have hoids : o.ids.Nodup := Ctx.owner_ids_nodup hwf.2.2 hmem
  unfold Ctx.splitFractionOwner? at hs
  cases ho : o.splitFraction? id id1 id2 q1 q2 p1 p2 with
  | none => simp [ho] at hs
  | some o' =>
    simp only [ho, Option.map_some, Option.some.injEq] at hs
    subst hs
    have hown : o.WellFormed C.D := hwf.2.1 o hmem
    have ho' : o'.WellFormed C.D := Owner.splitFraction?_wellFormed hoids hfids ho hown
    have hidmem : id ∈ o.ids := Owner.splitFraction?_mem_ids ho
    have hperm := Owner.splitFraction?_ids_perm hoids ho
    refine ⟨hreal, ?_, ?_⟩
    · exact Ctx.update_wellFormed_owners ho' (fun x hx _ => hwf.2.1 x hx)
    · exact Ctx.update_ids_nodup hwf.1 hmem rfl hwf.2.2 hidmem
        hperm hfresh1 hfresh2 hfids.2.2

/-- A fractional join dispatched to its owner preserves the context invariant,
provided the new leaf's identifier is fresh for the whole context. -/
theorem Ctx.joinFractionOwner_wellFormed {C C' : Ctx} {o : Owner} {node newId : CapId}
    (hwf : C.WellFormed) (hmem : o ∈ C.owners) (hfresh : newId ∉ C.ids)
    (hs : C.joinFractionOwner? o node newId = some C') : C'.WellFormed := by
  have hreal := Ctx.joinFractionOwner_realizes hmem hs hwf.1
  have hoids : o.ids.Nodup := Ctx.owner_ids_nodup hwf.2.2 hmem
  have hofresh : newId ∉ o.ids :=
    fun h => hfresh (List.mem_flatMap.mpr ⟨o, hmem, h⟩)
  unfold Ctx.joinFractionOwner? at hs
  cases ho : o.joinFraction? node newId with
  | none => simp [ho] at hs
  | some o' =>
    simp only [ho, Option.map_some, Option.some.injEq] at hs
    subst hs
    have hown : o.WellFormed C.D := hwf.2.1 o hmem
    have ho' : o'.WellFormed C.D := Owner.joinFraction?_wellFormed hoids hofresh ho hown
    have ho'nd : o'.ids.Nodup := Owner.joinFraction?_ids_nodup hoids hofresh ho
    have hsub : ∀ x ∈ o'.ids, x ∈ o.ids ∨ x = newId :=
      fun x hx => (Owner.joinFraction?_ids_sub ho hx).symm
    refine ⟨hreal, ?_, ?_⟩
    · exact Ctx.update_wellFormed_owners ho' (fun x hx _ => hwf.2.1 x hx)
    · exact Ctx.update_ids_nodup_of_sub hwf.1 hmem rfl hwf.2.2 ho'nd hsub hfresh

/-! ### Positive instances -/

namespace InvariantExamples

/-- The 64-byte owner: allocation `0`, one whole-share read--write leaf, root
identifier `0` and disposal identifier `1`. The disposal names no leaf, so the
`DisposalPresent` second branch is what holds. -/
def owner64 : Owner :=
  Owner.init ⟨0⟩ 64 64 (by decide) ⟨0⟩ ⟨1⟩

example : owner64.WellFormed 64 :=
  Owner.init_wellFormed ⟨0⟩ 64 64 (by decide) ⟨0⟩ ⟨1⟩

/-- The same 64-byte owner with the disposal capability on the root leaf. -/
def owner64Same : Owner :=
  Owner.init ⟨0⟩ 64 64 (by decide) ⟨0⟩ ⟨0⟩

example : owner64Same.WellFormed 64 :=
  Owner.init_wellFormed ⟨0⟩ 64 64 (by decide) ⟨0⟩ ⟨0⟩

example : ∃ c, owner64Same.root.find? ⟨0⟩ = some c :=
  Owner.init_disposalPresent_of_eq ⟨0⟩ 64 64 (by decide) ⟨0⟩ ⟨0⟩ rfl

/-- A one-allocation 64-byte context. -/
def ctx64 : Ctx :=
  { owners := [owner64], D := 64, nextAlloc := 1, issued := [⟨1⟩, ⟨0⟩], loans := .rootOnly }

example : ctx64.WellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro o ho
      have ho' : o = owner64 := by simpa [ctx64] using ho
      rw [ho']
      exact Owner.init_covered ⟨0⟩ 64 64 (by decide) ⟨0⟩ ⟨1⟩
    · simp [ctx64, owner64, Owner.init]
  · intro o ho
    have ho' : o = owner64 := by simpa [ctx64] using ho
    rw [ho']
    exact Owner.init_wellFormed ⟨0⟩ 64 64 (by decide) ⟨0⟩ ⟨1⟩
  · simp [Ctx.ids, ctx64, owner64, Owner.init, Owner.ids, Tree.ids]

end InvariantExamples

/-- The retag preserves the found leaves' allocation and extent. -/
theorem Owner.retagLeaf?_leavesWithin {o o' : Owner} {old new : CapId}
    (h : o.retagLeaf? old new = some o') (hlw : o.LeavesWithin) : o'.LeavesWithin := by
  rw [Owner.retagLeaf?_eq h]
  intro x c hc
  exact Tree.retag_leavesWithin (Owner.retagLeaf?_fresh h) (fun y c hy => hlw y c hy) x c hc

/-- The retag preserves the disposal entitlement. -/
theorem Owner.retagLeaf?_disposalPresent {o o' : Owner} {old new : CapId}
    (h : o.retagLeaf? old new = some o') (hd : o.DisposalPresent) :
    o'.DisposalPresent := by
  rw [Owner.retagLeaf?_eq h]
  have hnew := Owner.retagLeaf?_fresh h
  rcases hd with ⟨c, hc⟩ | hd
  · by_cases hdo : o.disposal = old
    · right
      show o.disposal ∉ (o.root.retag old new).ids
      rw [hdo]
      exact Tree.not_mem_ids_retag_old hnew
    · left
      refine ⟨c, ?_⟩
      have hdn : o.disposal ≠ new := by
        intro hid
        exact hnew (hid ▸ Tree.mem_ids_of_find? hc)
      rw [Tree.find?_retag_of_ne hdo hdn]
      exact hc
  · by_cases hdn : o.disposal = new
    · left
      obtain ⟨c0, hc0, _hact⟩ := Owner.retagLeaf?_active h
      refine ⟨{ c0 with id := new }, ?_⟩
      rw [hdn]
      exact Tree.find?_retag_new hc0 hnew
    · right
      show o.disposal ∉ (o.root.retag old new).ids
      rw [Tree.retag_ids_map]
      intro hmem
      rcases List.mem_map.mp hmem with ⟨x, hx, hfx⟩
      by_cases hxo : x = old
      · rw [if_pos hxo] at hfx
        exact hdn hfx.symm
      · rw [if_neg hxo] at hfx
        exact hd (hfx ▸ hx)

/-- The retag preserves the owner invariant. -/
theorem Owner.retagLeaf?_wellFormed {o o' : Owner} {D : Nat} {old new : CapId}
    (h : o.retagLeaf? old new = some o') (hwf : o.WellFormed D) : o'.WellFormed D :=
  ⟨(Owner.retagLeaf?_covered h).mpr hwf.1, Owner.retagLeaf?_leavesWithin h hwf.2.1,
    Owner.retagLeaf?_disposalPresent h hwf.2.2⟩

/-- An identifier of the replaced owner that the replacement drops is absent
from the updated context's identifiers. -/
theorem flatMap_update_ids_not_mem_of_owner (l : List Owner) (a : AllocId)
    (o o' : Owner) (x : CapId)
    (hndAlloc : (l.map (·.alloc)).Nodup) (hidsnd : (l.flatMap Owner.ids).Nodup)
    (hmem : o ∈ l) (hoa : o.alloc = a) (hx : x ∈ o.ids) (ho' : x ∉ o'.ids) :
    x ∉ (l.map (fun y => if y.alloc = a then o' else y)).flatMap Owner.ids := by
  induction l with
  | nil => simp at hmem
  | cons y ys ih =>
    have hndy : y.ids.Nodup := (List.nodup_append.mp hidsnd).1
    have hndys : (ys.flatMap Owner.ids).Nodup := (List.nodup_append.mp hidsnd).2.1
    have hdisj : ∀ u ∈ y.ids, ∀ v ∈ ys.flatMap Owner.ids, u ≠ v :=
      (List.nodup_append.mp hidsnd).2.2
    have hndAlloc' : (ys.map (·.alloc)).Nodup := (List.nodup_cons.mp hndAlloc).2
    by_cases hya : y.alloc = a
    · have hyo : y = o :=
        alloc_eq_of_mem hndAlloc List.mem_cons_self hmem (by rw [hya, hoa])
      have hnotalloc : a ∉ ys.map (·.alloc) := by
        simpa [hya] using (List.nodup_cons.mp hndAlloc).1
      have hysmap : ys.map (fun z => if z.alloc = a then o' else z) = ys := by
        have hmap := List.map_congr_left (l := ys)
          (f := fun z => if z.alloc = a then o' else z) (g := fun z => z)
          (fun z hz => by
            have hza : z.alloc ≠ a := fun h => hnotalloc (List.mem_map.mpr ⟨z, hz, h⟩)
            simp [hza])
        simpa using hmap
      rw [List.map_cons, ite_eq_left hya, List.flatMap_cons, hysmap]
      intro hmemx
      rcases List.mem_append.mp hmemx with h | h
      · exact ho' h
      · have hx' : x ∈ y.ids := by rw [hyo]; exact hx
        exact hdisj x hx' x h rfl
    · have hmem' : o ∈ ys := by
        rcases List.mem_cons.mp hmem with h | h
        · exact absurd (h ▸ hoa) hya
        · exact h
      rw [List.map_cons, ite_eq_right hya, List.flatMap_cons]
      intro hmemx
      rcases List.mem_append.mp hmemx with h | h
      · have hxo : x ∈ ys.flatMap Owner.ids := List.mem_flatMap.mpr ⟨o, hmem', hx⟩
        exact hdisj x h x hxo rfl
      · exact ih hndAlloc' hndys hmem' h

/-- A context update whose replacement drops an identifier of the replaced
owner omits that identifier. -/
theorem Ctx.not_mem_ids_update_of_owner {C : Ctx} {a : AllocId} {o o' : Owner}
    {x : CapId} (hreal : C.Realizes) (hnd : C.ids.Nodup) (hmem : o ∈ C.owners)
    (hoa : o.alloc = a) (hx : x ∈ o.ids) (ho' : x ∉ o'.ids) :
    x ∉ (C.update a o').ids :=
  flatMap_update_ids_not_mem_of_owner C.owners a o o' x hreal.2 hnd hmem hoa hx ho'

end Cap
