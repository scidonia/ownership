/-
Suspension and resumption of a capability leaf.

A loan suspends the lender's leaf: its state moves from `active` to `retired`,
so the write guard (`Owner.writableB`, `Cap.Core`) refuses through it while the
loan is outstanding. Ending the loan restores `active`. Both transitions keep
the leaf's footprint, share and ceiling, so the byte budget, the owner's
identifier list, its allocation and its length are unchanged, and resuming a
just-suspended leaf returns the original owner.

The world-level dispatch (`World.suspendChecked`, `World.resumeChecked`) and
the loan commands live in `Cap.WorldInvariant` and `Cap.Unified`.
-/
import Cap.Core

namespace Cap

/-- Find after an id-preserving leaf update: the queried identifier finds the
updated leaf when it names the replaced one, and is untouched otherwise. -/
theorem Tree.find?_replace_leaf (t : Tree) (id id' : CapId) (g : Leaf → Leaf)
    (hg : ∀ c, (g c).id = c.id) :
    (t.replace id (fun c => .leaf (g c))).find? id' =
      if id' = id then (t.find? id).map g else t.find? id' := by
  induction t with
  | leaf c =>
    by_cases hc : c.id = id
    · by_cases h' : id' = id
      · subst h'
        simp [Tree.replace, Tree.find?, hc, hg]
      · simp [Tree.replace, Tree.find?, hc, hg, h', Ne.symm h']
    · by_cases h' : id' = id
      · subst h'
        simp [Tree.replace, Tree.find?, hc]
      · simp [Tree.replace, Tree.find?, hc, h']
  | frac i l r ihl ihr =>
    cases hfl : l.find? id with
    | some c =>
      by_cases h' : id' = id
      · subst h'
        simp [Tree.replace, Tree.find?, hfl, ihl]
      · simp [Tree.replace, Tree.find?, hfl, h', ihl]
    | none =>
      by_cases h' : id' = id
      · subst h'
        simp [Tree.replace, Tree.find?, hfl, ihl, ihr]
      · simp [Tree.replace, Tree.find?, hfl, h', ihl, ihr]
  | spatial i l r ihl ihr =>
    cases hfl : l.find? id with
    | some c =>
      by_cases h' : id' = id
      · subst h'
        simp [Tree.replace, Tree.find?, hfl, ihl]
      · simp [Tree.replace, Tree.find?, hfl, h', ihl]
    | none =>
      by_cases h' : id' = id
      · subst h'
        simp [Tree.replace, Tree.find?, hfl, ihl, ihr]
      · simp [Tree.replace, Tree.find?, hfl, h', ihl, ihr]

/-- The replaced leaf itself is found, updated. -/
theorem Tree.find?_replace_leaf_eq (t : Tree) (id : CapId) (g : Leaf → Leaf)
    (hg : ∀ c, (g c).id = c.id) :
    (t.replace id (fun c => .leaf (g c))).find? id = (t.find? id).map g := by
  rw [Tree.find?_replace_leaf t id id g hg]
  simp

/-- An identifier other than the replaced one is found unchanged. -/
theorem Tree.find?_replace_leaf_ne (t : Tree) (id id' : CapId) (g : Leaf → Leaf)
    (hg : ∀ c, (g c).id = c.id) (hne : id' ≠ id) :
    (t.replace id (fun c => .leaf (g c))).find? id' = t.find? id' := by
  rw [Tree.find?_replace_leaf t id id' g hg]
  simp [hne]

/-- An id-preserving leaf update keeps the tree's identifier list. -/
theorem Tree.ids_replace_leaf (t : Tree) (id : CapId) (g : Leaf → Leaf)
    (hg : ∀ c, (g c).id = c.id) :
    (t.replace id (fun c => .leaf (g c))).ids = t.ids := by
  induction t with
  | leaf c =>
    by_cases hc : c.id = id
    · simp [Tree.replace, Tree.ids, hc, hg]
    · simp [Tree.replace, Tree.ids, hc]
  | frac i l r ihl ihr =>
    cases hf : l.find? id with
    | some c =>
      simp only [Tree.replace, Tree.ids, hf]
      rw [ihl]
    | none =>
      simp only [Tree.replace, Tree.ids, hf]
      rw [ihr]
  | spatial i l r ihl ihr =>
    cases hf : l.find? id with
    | some c =>
      simp only [Tree.replace, Tree.ids, hf]
      rw [ihl]
    | none =>
      simp only [Tree.replace, Tree.ids, hf]
      rw [ihr]

/-- Suspending then resuming the found leaf restores the tree, provided the
found leaf was active. -/
theorem Tree.replace_replace_leaf (t : Tree) (id : CapId)
    (h : ∀ c, t.find? id = some c → c.state = .active) :
    (t.replace id (fun c => .leaf { c with state := .retired })).replace id
      (fun c => .leaf { c with state := .active }) = t := by
  induction t with
  | leaf c =>
    by_cases hc : c.id = id
    · have hstate : c.state = .active := h c (by simp [Tree.find?, hc])
      simp only [Tree.replace, hc, ite_true]
      cases c
      simp_all
    · simp [Tree.replace, hc]
  | frac i l r ihl ihr =>
    cases hfl : l.find? id with
    | some c =>
      have hl : ∀ c', l.find? id = some c' → c'.state = .active :=
        fun c' hc' => h c' (by simp [Tree.find?, hc'])
      have hf1 : (l.replace id (fun c => .leaf { c with state := .retired })).find? id
          = some { c with state := .retired } := by
        rw [Tree.find?_replace_leaf_eq l id (fun c => { c with state := .retired })
          (fun _ => rfl), hfl]
        rfl
      simp only [Tree.replace, hfl, hf1]
      rw [ihl hl]
    | none =>
      have hr : ∀ c', r.find? id = some c' → c'.state = .active :=
        fun c' hc' => h c' (by simp [Tree.find?, hfl, hc'])
      simp only [Tree.replace, hfl]
      rw [ihr hr]
  | spatial i l r ihl ihr =>
    cases hfl : l.find? id with
    | some c =>
      have hl : ∀ c', l.find? id = some c' → c'.state = .active :=
        fun c' hc' => h c' (by simp [Tree.find?, hc'])
      have hf1 : (l.replace id (fun c => .leaf { c with state := .retired })).find? id
          = some { c with state := .retired } := by
        rw [Tree.find?_replace_leaf_eq l id (fun c => { c with state := .retired })
          (fun _ => rfl), hfl]
        rfl
      simp only [Tree.replace, hfl, hf1]
      rw [ihl hl]
    | none =>
      have hr : ∀ c', r.find? id = some c' → c'.state = .active :=
        fun c' hc' => h c' (by simp [Tree.find?, hfl, hc'])
      simp only [Tree.replace, hfl]
      rw [ihr hr]

/-- Retire the leaf `id`, provided it is active. The write guard refuses a
retired leaf, so the lender is suspended while the loan is outstanding. -/
def Owner.suspendLeaf? (o : Owner) (id : CapId) : Option Owner :=
  match o.root.find? id with
  | some c =>
    if c.state = .active then
      some { o with root := o.root.replace id (fun c => .leaf { c with state := .retired }) }
    else none
  | none => none

/-- Restore the leaf `id` to active, provided it is retired. -/
def Owner.resumeLeaf? (o : Owner) (id : CapId) : Option Owner :=
  match o.root.find? id with
  | some c =>
    if c.state = .retired then
      some { o with root := o.root.replace id (fun c => .leaf { c with state := .active }) }
    else none
  | none => none

/-- A successful suspension names the active leaf and the replaced root. -/
theorem Owner.suspendLeaf?_eq {o o' : Owner} {id : CapId}
    (h : o.suspendLeaf? id = some o') :
    ∃ c, o.root.find? id = some c ∧ c.state = .active ∧
      o' = { o with root := o.root.replace id (fun c => .leaf { c with state := .retired }) } := by
  unfold Owner.suspendLeaf? at h
  cases hf : o.root.find? id with
  | none => simp [hf] at h
  | some c =>
    by_cases hst : c.state = .active
    · simp [hf, hst] at h
      subst h
      exact ⟨c, rfl, hst, rfl⟩
    · simp [hf, hst] at h

/-- A successful resumption names the retired leaf and the replaced root. -/
theorem Owner.resumeLeaf?_eq {o o' : Owner} {id : CapId}
    (h : o.resumeLeaf? id = some o') :
    ∃ c, o.root.find? id = some c ∧ c.state = .retired ∧
      o' = { o with root := o.root.replace id (fun c => .leaf { c with state := .active }) } := by
  unfold Owner.resumeLeaf? at h
  cases hf : o.root.find? id with
  | none => simp [hf] at h
  | some c =>
    by_cases hst : c.state = .retired
    · simp [hf, hst] at h
      subst h
      exact ⟨c, rfl, hst, rfl⟩
    · simp [hf, hst] at h

/-- Suspension keeps the owner's allocation identifier. -/
theorem Owner.suspendLeaf?_alloc {o o' : Owner} {id : CapId}
    (h : o.suspendLeaf? id = some o') : o'.alloc = o.alloc := by
  obtain ⟨_, _, _, rfl⟩ := suspendLeaf?_eq h
  rfl

/-- Resumption keeps the owner's allocation identifier. -/
theorem Owner.resumeLeaf?_alloc {o o' : Owner} {id : CapId}
    (h : o.resumeLeaf? id = some o') : o'.alloc = o.alloc := by
  obtain ⟨_, _, _, rfl⟩ := resumeLeaf?_eq h
  rfl

/-- Suspension keeps the owner's length. -/
theorem Owner.suspendLeaf?_len {o o' : Owner} {id : CapId}
    (h : o.suspendLeaf? id = some o') : o'.len = o.len := by
  obtain ⟨_, _, _, rfl⟩ := suspendLeaf?_eq h
  rfl

/-- Resumption keeps the owner's length. -/
theorem Owner.resumeLeaf?_len {o o' : Owner} {id : CapId}
    (h : o.resumeLeaf? id = some o') : o'.len = o.len := by
  obtain ⟨_, _, _, rfl⟩ := resumeLeaf?_eq h
  rfl

/-- Suspension keeps the owner's identifier list. -/
theorem Owner.suspendLeaf?_ids {o o' : Owner} {id : CapId}
    (h : o.suspendLeaf? id = some o') : o'.ids = o.ids := by
  obtain ⟨_, _, _, rfl⟩ := suspendLeaf?_eq h
  simp [Owner.ids, Tree.ids_replace_leaf o.root id (fun c => { c with state := .retired })
    (fun _ => rfl)]

/-- Resumption keeps the owner's identifier list. -/
theorem Owner.resumeLeaf?_ids {o o' : Owner} {id : CapId}
    (h : o.resumeLeaf? id = some o') : o'.ids = o.ids := by
  obtain ⟨_, _, _, rfl⟩ := resumeLeaf?_eq h
  simp [Owner.ids, Tree.ids_replace_leaf o.root id (fun c => { c with state := .active })
    (fun _ => rfl)]

/-- Suspension keeps the budget at every byte: only a consumed leaf has a zero
budget, and the retired leaf keeps its footprint and share. -/
theorem Owner.suspendLeaf?_budget {o o' : Owner} {id : CapId}
    (h : o.suspendLeaf? id = some o') (x : Nat) :
    o'.root.budget x = o.root.budget x := by
  obtain ⟨c, hf, hst, rfl⟩ := suspendLeaf?_eq h
  apply Tree.budget_replace
  intro c' hc'
  have hcc' : c' = c := by
    rw [hf] at hc'
    exact (Option.some.inj hc').symm
  subst hcc'
  simp [Tree.budget, Leaf.budget, hst]

/-- Resumption keeps the budget at every byte. -/
theorem Owner.resumeLeaf?_budget {o o' : Owner} {id : CapId}
    (h : o.resumeLeaf? id = some o') (x : Nat) :
    o'.root.budget x = o.root.budget x := by
  obtain ⟨c, hf, hst, rfl⟩ := resumeLeaf?_eq h
  apply Tree.budget_replace
  intro c' hc'
  have hcc' : c' = c := by
    rw [hf] at hc'
    exact (Option.some.inj hc').symm
  subst hcc'
  simp [Tree.budget, Leaf.budget, hst]

/-- The suspended leaf is found retired in the new owner. -/
theorem Owner.suspendLeaf?_find? {o o' : Owner} {id : CapId}
    (h : o.suspendLeaf? id = some o') :
    ∃ c, o.root.find? id = some c ∧ c.state = .active ∧
      o'.root.find? id = some { c with state := .retired } := by
  obtain ⟨c, hf, hst, rfl⟩ := suspendLeaf?_eq h
  refine ⟨c, hf, hst, ?_⟩
  show (o.root.replace id (fun c => .leaf { c with state := .retired })).find? id
      = some { c with state := .retired }
  rw [Tree.find?_replace_leaf_eq _ _ (fun c => { c with state := .retired }) (fun _ => rfl), hf]
  rfl

/-- The resumed leaf is found active in the new owner. -/
theorem Owner.resumeLeaf?_find? {o o' : Owner} {id : CapId}
    (h : o.resumeLeaf? id = some o') :
    ∃ c, o.root.find? id = some c ∧ c.state = .retired ∧
      o'.root.find? id = some { c with state := .active } := by
  obtain ⟨c, hf, hst, rfl⟩ := resumeLeaf?_eq h
  refine ⟨c, hf, hst, ?_⟩
  show (o.root.replace id (fun c => .leaf { c with state := .active })).find? id
      = some { c with state := .active }
  rw [Tree.find?_replace_leaf_eq _ _ (fun c => { c with state := .active }) (fun _ => rfl), hf]
  rfl

/-- A suspended leaf is not writable at any index: the state check fails. -/
theorem Owner.suspendLeaf?_not_writable {o o' : Owner} {D : Nat} {id : CapId}
    (h : o.suspendLeaf? id = some o') (i : Nat) : o'.writableB D id i = false := by
  obtain ⟨_, _, _, hfind⟩ := suspendLeaf?_find? h
  simp [Owner.writableB, hfind]

/-- Resuming a just-suspended leaf returns the original owner. -/
theorem Owner.resumeLeaf?_of_suspendLeaf? {o o' o'' : Owner} {id : CapId}
    (hs : o.suspendLeaf? id = some o') (hr : o'.resumeLeaf? id = some o'') :
    o'' = o := by
  obtain ⟨c, hf, hst, rfl⟩ := suspendLeaf?_eq hs
  obtain ⟨c2, hf2, _, ho''⟩ := resumeLeaf?_eq hr
  rw [Tree.find?_replace_leaf_eq _ _ (fun c => { c with state := .retired }) (fun _ => rfl), hf] at hf2
  have hc2 : c2 = { c with state := .retired } := (Option.some.inj hf2).symm
  subst hc2
  rw [ho'']
  have hrt : (o.root.replace id (fun c => .leaf { c with state := .retired })).replace id
        (fun c => .leaf { c with state := .active }) = o.root :=
    Tree.replace_replace_leaf o.root id (fun c' hc' => by
      rw [hf] at hc'
      cases hc'
      exact hst)
  rw [hrt]

/-- After resume the original writability returns. -/
theorem Owner.resumeLeaf?_writable {o o' o'' : Owner} {D : Nat} {id : CapId} {i : Nat}
    (hs : o.suspendLeaf? id = some o') (hr : o'.resumeLeaf? id = some o'') :
    o''.writableB D id i = o.writableB D id i := by
  rw [resumeLeaf?_of_suspendLeaf? hs hr]

end Cap
