/-
Capability retagging for the live-borrower accounting model.

A borrow does not add a second whole-share leaf. The lender's active leaf is
retagged to the borrower identity, so the decomposition continues to carry the
allocation's share exactly once. The loan record stores the original lender
identity for restoration. Retagging changes only leaf identifiers, not
footprints, shares, states or ceilings, so the byte budget and coverage are
unchanged.
-/
import Cap.Ledger

namespace Cap

/-- Rename every occurrence of `old` to `new`; the leaf's other fields are kept. -/
def Tree.retag (old new : CapId) : Tree → Tree
  | .leaf c => .leaf (if c.id = old then { c with id := new } else c)
  | .frac i l r => .frac i (l.retag old new) (r.retag old new)
  | .spatial i l r => .spatial i (l.retag old new) (r.retag old new)

/-- Retagging preserves the byte budget: the budget reads footprints, shares and
    states, never identifiers. -/
theorem Tree.retag_budget (t : Tree) (old new : CapId) (x : Nat) :
    (t.retag old new).budget x = t.budget x := by
  induction t with
  | leaf c => by_cases h : c.id = old <;>
      simp [Tree.retag, Tree.budget, Leaf.budget, h]
  | frac i l r ihl ihr => simp [Tree.retag, Tree.budget, ihl, ihr]
  | spatial i l r ihl ihr => simp [Tree.retag, Tree.budget, ihl, ihr]

/-- Retag an active leaf to a fresh identifier. -/
def Owner.retagLeaf? (o : Owner) (old new : CapId) : Option Owner :=
  match o.root.find? old with
  | none => none
  | some c =>
    if c.state = .active then
      if new ∉ o.root.ids then
        some { o with root := o.root.retag old new }
      else none
    else none

/-- The retag predicate together with the leaf it renamed: the first component
is exactly `retagLeaf?`, the second the active leaf found at the old name. -/
def Owner.retagLeafFind? (o : Owner) (old new : CapId) : Option (Owner × Leaf) :=
  match o.root.find? old with
  | none => none
  | some c =>
    if c.state = .active then
      if new ∉ o.root.ids then
        some ({ o with root := o.root.retag old new }, c)
      else none
    else none

/-- The first component of `retagLeafFind?` is the base `retagLeaf?` predicate. -/
theorem Owner.retagLeafFind?_fst {o o' : Owner} {old new : CapId} {c : Leaf}
    (h : o.retagLeafFind? old new = some (o', c)) :
    o.retagLeaf? old new = some o' := by
  unfold Owner.retagLeafFind? at h
  unfold Owner.retagLeaf?
  cases hf : o.root.find? old with
  | none => simp [hf] at h
  | some d =>
    simp only [hf] at h
    by_cases hstate : d.state = .active
    · by_cases hfresh : new ∉ o.root.ids
      · simp [hstate, hfresh] at h ⊢
        exact h.1
      · simp [hstate, hfresh] at h
    · simp [hstate] at h

/-- A successful `retagLeafFind?` finds the renamed leaf. -/
theorem Owner.retagLeafFind?_leaf {o o' : Owner} {old new : CapId} {c : Leaf}
    (h : o.retagLeafFind? old new = some (o', c)) :
    o.root.find? old = some c ∧ c.state = .active ∧ new ∉ o.root.ids := by
  unfold Owner.retagLeafFind? at h
  cases hf : o.root.find? old with
  | none => simp [hf] at h
  | some d =>
    simp only [hf] at h
    by_cases hstate : d.state = .active
    · by_cases hfresh : new ∉ o.root.ids
      · simp [hstate, hfresh] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, hstate, hfresh⟩
      · simp [hstate, hfresh] at h
    · simp [hstate] at h

/-- A tree identifier found by traversal is some leaf's identifier. -/
theorem Tree.exists_find?_of_mem_ids {t : Tree} {id : CapId} (h : id ∈ t.ids) :
    ∃ c, t.find? id = some c := by
  induction t with
  | leaf c =>
    simp only [Tree.ids, List.mem_singleton] at h
    subst h
    exact ⟨c, by simp [Tree.find?]⟩
  | frac i l r ihl ihr =>
    simp only [Tree.ids, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨c, hc⟩ := ihl h
      exact ⟨c, by simp [Tree.find?, hc]⟩
    · cases hl : l.find? id with
      | some d => exact ⟨d, by simp [Tree.find?, hl]⟩
      | none =>
        obtain ⟨c, hc⟩ := ihr h
        exact ⟨c, by simp [Tree.find?, hl, hc]⟩
  | spatial i l r ihl ihr =>
    simp only [Tree.ids, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨c, hc⟩ := ihl h
      exact ⟨c, by simp [Tree.find?, hc]⟩
    · cases hl : l.find? id with
      | some d => exact ⟨d, by simp [Tree.find?, hl]⟩
      | none =>
        obtain ⟨c, hc⟩ := ihr h
        exact ⟨c, by simp [Tree.find?, hl, hc]⟩

/-- A tree with no leaf at an identifier does not list it. -/
theorem Tree.not_mem_ids_of_find?_eq_none {t : Tree} {id : CapId}
    (h : t.find? id = none) : id ∉ t.ids := by
  intro hmem
  obtain ⟨c, hc⟩ := Tree.exists_find?_of_mem_ids hmem
  rw [h] at hc
  nomatch hc

/-- A leaf found by traversal is listed. -/
theorem Tree.mem_ids_of_find? {t : Tree} {id : CapId} {c : Leaf}
    (h : t.find? id = some c) : id ∈ t.ids := by
  induction t with
  | leaf d =>
    simp only [Tree.find?] at h
    by_cases hd : d.id = id
    · simp [Tree.ids, hd]
    · simp [hd] at h
  | frac i l r ihl ihr =>
    simp only [Tree.find?] at h
    cases hl : l.find? id with
    | some d =>
      have hd : d = c := by
        have hh := h
        rw [hl] at hh
        exact Option.some.inj hh
      subst hd
      simp [Tree.ids, ihl hl]
    | none => simp [Tree.ids, ihr (by simpa [hl] using h)]
  | spatial i l r ihl ihr =>
    simp only [Tree.find?] at h
    cases hl : l.find? id with
    | some d =>
      have hd : d = c := by
        have hh := h
        rw [hl] at hh
        exact Option.some.inj hh
      subst hd
      simp [Tree.ids, ihl hl]
    | none => simp [Tree.ids, ihr (by simpa [hl] using h)]

/-- A tree with no listed occurrence has no found leaf. -/
theorem Tree.find?_eq_none_of_not_mem_ids {t : Tree} {id : CapId}
    (h : id ∉ t.ids) : t.find? id = none := by
  cases hf : t.find? id with
  | none => rfl
  | some c => exact absurd (Tree.mem_ids_of_find? hf) h

/-- Retagging any tree: `new` occurs in the identifier list exactly when `old`
does, and every other identifier is unchanged. -/
theorem Tree.mem_ids_retag {t : Tree} {old new x : CapId}
    (hnew : new ∉ t.ids) :
    x ∈ (t.retag old new).ids ↔ (x ∈ t.ids ∧ x ≠ old) ∨ (x = new ∧ old ∈ t.ids) := by
  induction t with
  | leaf c =>
    have hnew' : new ≠ c.id := by simpa [Tree.ids] using hnew
    by_cases hc : c.id = old
    · subst hc
      simp [Tree.retag, Tree.ids, hnew', Ne.symm hnew']
    · simp only [Tree.retag, Tree.ids, if_neg hc, List.mem_singleton]
      constructor
      · intro hx
        exact Or.inl ⟨hx, fun hxo => hc (hx ▸ hxo)⟩
      · rintro (⟨hx, -⟩ | ⟨-, hold⟩)
        · exact hx
        · exact absurd hold.symm hc
  | frac i l r ihl ihr =>
    simp only [Tree.retag, Tree.ids, List.mem_append] at hnew ⊢
    have hl := ihl (by intro h; exact hnew (Or.inl h))
    have hr := ihr (by intro h; exact hnew (Or.inr h))
    constructor
    · intro hx
      rcases hx with hx | hx
      · rcases hl.mp hx with ⟨hm, hne⟩ | ⟨hne, hold⟩
        · exact Or.inl ⟨Or.inl hm, hne⟩
        · exact Or.inr ⟨hne, Or.inl hold⟩
      · rcases hr.mp hx with ⟨hm, hne⟩ | ⟨hne, hold⟩
        · exact Or.inl ⟨Or.inr hm, hne⟩
        · exact Or.inr ⟨hne, Or.inr hold⟩
    · intro hx
      rcases hx with ⟨hm, hne⟩ | ⟨hne, hold⟩
      · rcases hm with hm | hm
        · exact Or.inl (hl.mpr (Or.inl ⟨hm, hne⟩))
        · exact Or.inr (hr.mpr (Or.inl ⟨hm, hne⟩))
      · rcases hold with hold | hold
        · exact Or.inl (hl.mpr (Or.inr ⟨hne, hold⟩))
        · exact Or.inr (hr.mpr (Or.inr ⟨hne, hold⟩))
  | spatial i l r ihl ihr =>
    simp only [Tree.retag, Tree.ids, List.mem_append] at hnew ⊢
    have hl := ihl (by intro h; exact hnew (Or.inl h))
    have hr := ihr (by intro h; exact hnew (Or.inr h))
    constructor
    · intro hx
      rcases hx with hx | hx
      · rcases hl.mp hx with ⟨hm, hne⟩ | ⟨hne, hold⟩
        · exact Or.inl ⟨Or.inl hm, hne⟩
        · exact Or.inr ⟨hne, Or.inl hold⟩
      · rcases hr.mp hx with ⟨hm, hne⟩ | ⟨hne, hold⟩
        · exact Or.inl ⟨Or.inr hm, hne⟩
        · exact Or.inr ⟨hne, Or.inr hold⟩
    · intro hx
      rcases hx with ⟨hm, hne⟩ | ⟨hne, hold⟩
      · rcases hm with hm | hm
        · exact Or.inl (hl.mpr (Or.inl ⟨hm, hne⟩))
        · exact Or.inr (hr.mpr (Or.inl ⟨hm, hne⟩))
      · rcases hold with hold | hold
        · exact Or.inl (hl.mpr (Or.inr ⟨hne, hold⟩))
        · exact Or.inr (hr.mpr (Or.inr ⟨hne, hold⟩))

/-- An identifier neither renamed nor introduced is unaffected by the retag. -/
theorem Tree.mem_ids_retag_of_ne {t : Tree} {old new x : CapId}
    (hnew : new ∉ t.ids) (hxold : x ≠ old) (hxnew : x ≠ new) :
    x ∈ (t.retag old new).ids ↔ x ∈ t.ids := by
  rw [Tree.mem_ids_retag hnew]
  constructor
  · rintro (⟨hm, -⟩ | ⟨hxeq, -⟩)
    · exact hm
    · exact absurd hxeq hxnew
  · intro hm
    exact Or.inl ⟨hm, hxold⟩

/-- The old name is absent after a retag. -/
theorem Tree.not_mem_ids_retag_old {t : Tree} {old new : CapId}
    (hnew : new ∉ t.ids) : old ∉ (t.retag old new).ids := by
  intro hmem
  rcases (Tree.mem_ids_retag hnew).mp hmem with ⟨-, hne⟩ | ⟨hne, hold⟩
  · exact hne rfl
  · rw [hne] at hold
    exact hnew hold

/-- The new name occurs after a retag exactly when the old name did. -/
theorem Tree.mem_ids_retag_new {t : Tree} {old new : CapId}
    (hnew : new ∉ t.ids) : new ∈ (t.retag old new).ids ↔ old ∈ t.ids := by
  constructor
  · intro hmem
    rcases (Tree.mem_ids_retag hnew).mp hmem with ⟨hm, -⟩ | ⟨-, hold⟩
    · exact absurd hm hnew
    · exact hold
  · intro hold
    exact (Tree.mem_ids_retag hnew).mpr (Or.inr ⟨rfl, hold⟩)

/-- Retagging a tree whose old name is found returns that leaf under the new
name. -/
theorem Tree.find?_retag_new {t : Tree} {old new : CapId} {c : Leaf}
    (hc : t.find? old = some c) (hnew : new ∉ t.ids) :
    (t.retag old new).find? new = some { c with id := new } := by
  induction t with
  | leaf d =>
    have hnd : new ≠ d.id := by simpa [Tree.ids] using hnew
    simp only [Tree.find?] at hc
    by_cases hd : d.id = old
    · simp only [if_pos hd] at hc
      cases hc
      simp [Tree.retag, Tree.find?, hd]
    · simp [Tree.find?, hd] at hc
  | frac i l r ihl ihr =>
    simp only [Tree.ids, List.mem_append, not_or] at hnew
    simp only [Tree.retag, Tree.find?]
    cases hl : l.find? old with
    | some d =>
      have hcd : d = c := by
        have hh := hc
        simp only [Tree.find?, hl] at hh
        exact Option.some.inj hh
      subst hcd
      rw [ihl hl hnew.1]
    | none =>
      have hr : r.find? old = some c := by
        have hh := hc
        simp only [Tree.find?, hl] at hh
        exact hh
      have hnot : old ∉ l.ids := Tree.not_mem_ids_of_find?_eq_none hl
      have hnewl : new ∉ (l.retag old new).ids := by
        rw [Tree.mem_ids_retag_new (t := l) hnew.1]
        exact hnot
      rw [Tree.find?_eq_none_of_not_mem_ids hnewl]
      exact ihr hr hnew.2
  | spatial i l r ihl ihr =>
    simp only [Tree.ids, List.mem_append, not_or] at hnew
    simp only [Tree.retag, Tree.find?]
    cases hl : l.find? old with
    | some d =>
      have hcd : d = c := by
        have hh := hc
        simp only [Tree.find?, hl] at hh
        exact Option.some.inj hh
      subst hcd
      rw [ihl hl hnew.1]
    | none =>
      have hr : r.find? old = some c := by
        have hh := hc
        simp only [Tree.find?, hl] at hh
        exact hh
      have hnot : old ∉ l.ids := Tree.not_mem_ids_of_find?_eq_none hl
      have hnewl : new ∉ (l.retag old new).ids := by
        rw [Tree.mem_ids_retag_new (t := l) hnew.1]
        exact hnot
      rw [Tree.find?_eq_none_of_not_mem_ids hnewl]
      exact ihr hr hnew.2

/-- A successful retag preserves the byte budget everywhere. -/
theorem Owner.retagLeaf?_budget {o o' : Owner} {old new : CapId} {x : Nat}
    (h : o.retagLeaf? old new = some o') :
    o'.root.budget x = o.root.budget x := by
  unfold Owner.retagLeaf? at h
  cases hf : o.root.find? old with
  | none => simp [hf] at h
  | some c =>
    simp only [hf] at h
    by_cases hstate : c.state = .active
    · by_cases hfresh : new ∉ o.root.ids
      · simp [hstate, hfresh] at h
        cases h
        exact Tree.retag_budget o.root old new x
      · simp [hstate, hfresh] at h
    · simp [hstate] at h

/-- A successful retag leaves the owner length unchanged. -/
theorem Owner.retagLeaf?_len {o o' : Owner} {old new : CapId}
    (h : o.retagLeaf? old new = some o') : o'.len = o.len := by
  unfold Owner.retagLeaf? at h
  cases hf : o.root.find? old with
  | none => simp [hf] at h
  | some c =>
    simp only [hf] at h
    by_cases hstate : c.state = .active
    · by_cases hfresh : new ∉ o.root.ids
      · simp [hstate, hfresh] at h
        cases h
        rfl
      · simp [hstate, hfresh] at h
    · simp [hstate] at h

/-- A successful retag preserves coverage at the same denominator. -/
theorem Owner.retagLeaf?_covered {o o' : Owner} {old new : CapId} {D : Nat}
    (h : o.retagLeaf? old new = some o') :
    o'.Covered D ↔ o.Covered D := by
  unfold Owner.Covered
  constructor
  · intro hc x hx
    rw [← Owner.retagLeaf?_budget h]
    exact hc x (by simpa [Owner.retagLeaf?_len h] using hx)
  · intro hc x hx
    rw [Owner.retagLeaf?_budget h]
    exact hc x (by simpa [Owner.retagLeaf?_len h] using hx)

/-- A successful retag starts from an active leaf. -/
theorem Owner.retagLeaf?_active {o o' : Owner} {old new : CapId}
    (h : o.retagLeaf? old new = some o') :
    ∃ c, o.root.find? old = some c ∧ c.state = .active := by
  unfold Owner.retagLeaf? at h
  cases hf : o.root.find? old with
  | none => simp [hf] at h
  | some c =>
    simp only [hf] at h
    by_cases hstate : c.state = .active
    · by_cases hfresh : new ∉ o.root.ids
      · simp [hstate, hfresh] at h
        exact ⟨c, rfl, hstate⟩
      · simp [hstate, hfresh] at h
    · simp [hstate] at h

/-- A successful retag targets a fresh identifier in the owner's current tree. -/
theorem Owner.retagLeaf?_fresh {o o' : Owner} {old new : CapId}
    (h : o.retagLeaf? old new = some o') :
    new ∉ o.root.ids := by
  unfold Owner.retagLeaf? at h
  cases hf : o.root.find? old with
  | none => simp [hf] at h
  | some c =>
    simp only [hf] at h
    by_cases hstate : c.state = .active
    · by_cases hfresh : new ∉ o.root.ids
      · simp [hstate, hfresh] at h
        exact hfresh
      · simp [hstate, hfresh] at h
    · simp [hstate] at h

/-- A successful retag is the owner with its tree retagged. -/
theorem Owner.retagLeaf?_eq {o o' : Owner} {old new : CapId}
    (h : o.retagLeaf? old new = some o') :
    o' = { o with root := o.root.retag old new } := by
  unfold Owner.retagLeaf? at h
  cases hf : o.root.find? old with
  | none => simp [hf] at h
  | some c =>
    simp only [hf] at h
    by_cases hstate : c.state = .active
    · by_cases hfresh : new ∉ o.root.ids
      · simp [hstate, hfresh] at h
        exact h.symm
      · simp [hstate, hfresh] at h
    · simp [hstate] at h

/-- A successful `retagLeafFind?` is the owner with its tree retagged. -/
theorem Owner.retagLeafFind?_eq {o o' : Owner} {old new : CapId} {c : Leaf}
    (h : o.retagLeafFind? old new = some (o', c)) :
    o' = { o with root := o.root.retag old new } := by
  unfold Owner.retagLeafFind? at h
  cases hf : o.root.find? old with
  | none => simp [hf] at h
  | some d =>
    simp only [hf] at h
    by_cases hstate : d.state = .active
    · by_cases hfresh : new ∉ o.root.ids
      · simp [hstate, hfresh] at h
        exact h.1.symm
      · simp [hstate, hfresh] at h
    · simp [hstate] at h

/-- A successful retag keeps the owner's allocation. -/
theorem Owner.retagLeaf?_alloc {o o' : Owner} {old new : CapId}
    (h : o.retagLeaf? old new = some o') : o'.alloc = o.alloc := by
  rw [Owner.retagLeaf?_eq h]

/-- Every identifier of a retagged owner is an old identifier or the new name. -/
theorem Owner.retagLeaf?_ids_sub {o o' : Owner} {old new : CapId}
    (h : o.retagLeaf? old new = some o') :
    ∀ x ∈ o'.ids, x ∈ o.ids ∨ x = new := by
  rw [Owner.retagLeaf?_eq h]
  intro x hx
  simp only [Owner.ids] at hx ⊢
  rcases List.mem_cons.mp hx with rfl | hx
  · exact Or.inl (List.mem_cons_self ..)
  · rcases (Tree.mem_ids_retag (Owner.retagLeaf?_fresh h)).mp hx with
      ⟨hm, -⟩ | ⟨hnew, -⟩
    · exact Or.inl (List.mem_cons_of_mem _ hm)
    · exact Or.inr hnew

/-- The retagged-away name is absent from the owner's identifiers, provided the
owner's identifiers are distinct. -/
theorem Owner.retagLeaf?_detached {o o' : Owner} {old new : CapId}
    (h : o.retagLeaf? old new = some o') (hnd : o.ids.Nodup) :
    old ∉ o'.ids := by
  obtain ⟨c, hc, _hact⟩ := Owner.retagLeaf?_active h
  have hold : old ∈ o.root.ids := Tree.mem_ids_of_find? hc
  have hmem : o.disposal ∈ o.ids := by simp [Owner.ids]
  have hnotdisp : old ≠ o.disposal := by
    intro hEq
    have hdisp : o.disposal ∈ o.root.ids := hEq ▸ hold
    exact (List.nodup_cons.mp hnd).1 hdisp
  rw [Owner.retagLeaf?_eq h]
  simp only [Owner.ids]
  intro hx
  rcases List.mem_cons.mp hx with hx | hx
  · exact hnotdisp hx
  · exact Tree.not_mem_ids_retag_old (Owner.retagLeaf?_fresh h) hx

/-- The retag preserves the found leaf's allocation and resource description,
under the new name. -/
theorem Tree.retag_leaf_description {t : Tree} {old new : CapId} {c : Leaf}
    (hc : t.find? old = some c) (hnew : new ∉ t.ids) :
    ∃ c', (t.retag old new).find? new = some c' ∧ c'.id = new ∧
      c'.alloc = c.alloc ∧ c'.lo = c.lo ∧ c'.hi = c.hi ∧ c'.q = c.q ∧
      c'.ceiling = c.ceiling ∧ c'.state = c.state :=
  ⟨{ c with id := new }, Tree.find?_retag_new hc hnew, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A map of a duplicate-free list is duplicate-free when the function is
injective on the list. -/
theorem List.nodup_map_of_inj {α β : Type} {f : α → β} {l : List α}
    (h : l.Nodup) (hinj : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) :
    (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons] at h ⊢
    refine ⟨?_, ih h.2 ?_⟩
    · intro hx
      rcases List.mem_map.mp hx with ⟨y, hy, hfy⟩
      have hxy : x = y := hinj x (by simp) y (List.mem_cons_of_mem _ hy) hfy.symm
      subst hxy
      exact h.1 hy
    · intro a ha b hb heq
      exact hinj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) heq

/-- Retagging rewrites the identifier list by replacing the old name. -/
theorem Tree.retag_ids_map (t : Tree) (old new : CapId) :
    (t.retag old new).ids = t.ids.map (fun x => if x = old then new else x) := by
  induction t with
  | leaf c =>
    by_cases hc : c.id = old <;> simp [Tree.retag, Tree.ids, hc]
  | frac i l r ihl ihr =>
    simp [Tree.retag, Tree.ids, ihl, ihr, List.map_append]
  | spatial i l r ihl ihr =>
    simp [Tree.retag, Tree.ids, ihl, ihr, List.map_append]

/-- Retagging does not change the found leaf's identifier except by the rename. -/
theorem Tree.find?_retag_of_ne {t : Tree} {old new x : CapId}
    (hxold : x ≠ old) (hxnew : x ≠ new) :
    (t.retag old new).find? x = t.find? x := by
  induction t with
  | leaf c =>
    by_cases hc : c.id = old
    · have hox : old ≠ x := fun h => hxold h.symm
      have hnx : new ≠ x := fun h => hxnew h.symm
      simp [Tree.retag, Tree.find?, hc, hox, hnx]
    · simp [Tree.retag, Tree.find?, hc]
  | frac i l r ihl ihr =>
    simp only [Tree.retag, Tree.find?]
    rw [ihl, ihr]
  | spatial i l r ihl ihr =>
    simp only [Tree.retag, Tree.find?]
    rw [ihl, ihr]

/-- The retag preserves every found leaf's allocation and extent. -/
theorem Tree.retag_leavesWithin {t : Tree} {old new : CapId} {alloc : AllocId}
    {len : Nat} (hnew : new ∉ t.ids)
    (h : ∀ x c, t.find? x = some c → c.alloc = alloc ∧ c.hi ≤ len) :
    ∀ x c, (t.retag old new).find? x = some c → c.alloc = alloc ∧ c.hi ≤ len := by
  intro x c hc
  by_cases hxnew : x = new
  · subst x
    cases hfold : t.find? old with
    | none =>
      have hnot : new ∉ (t.retag old new).ids := by
        rw [Tree.mem_ids_retag_new hnew]
        exact Tree.not_mem_ids_of_find?_eq_none hfold
      exact absurd (Tree.mem_ids_of_find? hc) hnot
    | some d =>
      have hret := Tree.find?_retag_new hfold hnew
      rw [hret] at hc
      have hcd : c = { d with id := new } := (Option.some.inj hc).symm
      rw [hcd]
      exact h old d hfold
  · by_cases hxold : x = old
    · subst x
      cases hret : (t.retag old new).find? old with
      | none => rw [hret] at hc; nomatch hc
      | some d =>
        exact absurd (Tree.mem_ids_of_find? hret) (Tree.not_mem_ids_retag_old hnew)
    · rw [Tree.find?_retag_of_ne hxold hxnew] at hc
      exact h x c hc

/-- The retag keeps the owner's identifier list duplicate-free, provided the new
name is distinct from the disposal capability (which is listed separately). -/
theorem Owner.retagLeaf?_ids_nodup {o o' : Owner} {old new : CapId}
    (h : o.retagLeaf? old new = some o') (hnd : o.ids.Nodup)
    (hdisp : new ≠ o.disposal) : o'.ids.Nodup := by
  rw [Owner.retagLeaf?_eq h]
  simp only [Owner.ids, List.nodup_cons]
  have hrold : o.root.ids.Nodup := (List.nodup_cons.mp hnd).2
  have hnew := Owner.retagLeaf?_fresh h
  refine ⟨?_, ?_⟩
  · intro hmem
    rw [Tree.retag_ids_map] at hmem
    rcases List.mem_map.mp hmem with ⟨x, hx, hfx⟩
    by_cases hxo : x = old
    · rw [if_pos hxo] at hfx
      exact hdisp hfx
    · rw [if_neg hxo] at hfx
      exact (List.nodup_cons.mp hnd).1 (hfx ▸ hx)
  · rw [Tree.retag_ids_map]
    apply List.nodup_map_of_inj hrold
    intro a ha b hb heq
    by_cases hao : a = old <;> by_cases hbo : b = old
    · exact hao.trans hbo.symm
    · rw [if_pos hao, if_neg hbo] at heq
      exact absurd (heq ▸ hb) hnew
    · rw [if_neg hao, if_pos hbo] at heq
      exact absurd (heq ▸ ha) hnew
    · rw [if_neg hao, if_neg hbo] at heq
      exact heq

end Cap
