/-
Sibling-only fractional join.

A fractional split replaces one leaf by two leaves whose shares add to it. The
join implemented here is the exact inverse, and only that: a `frac` node is
located by its identifier, its two children must both be leaves, and those leaves
must agree on allocation, footprint (`lo`, `hi`), ceiling and state. The two
children are then replaced by a single leaf whose share is their sum and whose
other fields are inherited from the left child. A join of the two children's own
identifiers is refused: the children must carry distinct capability identifiers,
so a node that stores the same capability twice cannot silently be collapsed to
one leaf.

Theorems:
* `Tree.joinChildren?_budget` — the joined tree has the original `frac` node's
  budget at every byte, provided the children are siblings as described.
* `Tree.budget_replaceNode` — replacing the located node by any tree with the same
  budget at every byte preserves the whole tree's budget.
* `Owner.joinFraction_covered` — a successful join preserves `Owner.Covered`.
* `Owner.joinFraction_alloc` — a successful join keeps the allocation identifier.
* `Tree.joinChildren?_alias_none` and `Owner.joinFraction_alias_none` — a join of
  two children carrying the same capability identifier is refused.
* `Tree.findFrac?_isFrac` — the located node is always a `frac` node.
* `Owner.joinFraction?_len` — a join keeps the owner's length.
* `Tree.ids_replaceNode_perm` and `Owner.joinFraction?_ids_perm` — a join turns
  the identifier list into the old list without the two joined children,
  followed by the new leaf's identifier.
* `Owner.joinFraction?_ids_sub` and `Owner.joinFraction?_ids_nodup` — every
  identifier of the joined owner is the new identifier or an old one, and
  distinctness is preserved when the new identifier is fresh.

What is not proved / not implemented:
* The join is sibling-only: it combines exactly the two leaf children of one
  `frac` node, and only when they already agree on allocation, footprint, ceiling
  and state. Arbitrary recombination of two leaves over the same resource is not
  implemented, and no theorem claims it.
* The common-partition normaliser (re-associating and regrouping fractional splits
  so that equal partitions present the same tree) is not implemented.
* Provenance beyond the shape of the node is not tracked: the module records the
  new leaf's share and inherited fields, not the history of the capabilities that
  were merged, nor any loan or lifetime information.
* `findFrac?` and `replaceNode` act on the first matching node, like `Tree.find?`
  and `Tree.replace`; the join is defined for one node and is not iterated.
-/
import Cap.Ledger

namespace Cap

namespace Tree

/-- Find the first fractional node with the given identifier. A `spatial` node
with the identifier is not returned, and a `frac` node's own identifier is
preferred over any match in its children. -/
def findFrac? (id : CapId) : Tree → Option Tree
  | .leaf _ => none
  | .frac i l r =>
    if i = id then some (.frac i l r)
    else
      match l.findFrac? id with
      | some t => some t
      | none => r.findFrac? id
  | .spatial _ l r =>
    match l.findFrac? id with
    | some t => some t
    | none => r.findFrac? id

/-- Replace the first fractional node with the given identifier by `t'`. Leaves
are untouched, and `spatial` nodes are never themselves replaced. -/
def replaceNode (id : CapId) (t' : Tree) : Tree → Tree
  | .leaf c => .leaf c
  | .frac i l r =>
    if i = id then t'
    else
      match l.findFrac? id with
      | some _ => .frac i (replaceNode id t' l) r
      | none => .frac i l (replaceNode id t' r)
  | .spatial i l r =>
    match l.findFrac? id with
    | some _ => .spatial i (replaceNode id t' l) r
    | none => .spatial i l (replaceNode id t' r)

/-- Replacing the located fractional node by a tree with the same budget at every
byte preserves the budget of the whole tree at every byte. -/
theorem budget_replaceNode (t : Tree) (id : CapId) (t' : Tree)
    (h : ∀ x i l r, t.findFrac? id = some (.frac i l r) →
      t'.budget x = (Tree.frac i l r).budget x) :
    ∀ x, (Tree.replaceNode id t' t).budget x = t.budget x := by
  induction t with
  | leaf c =>
    intro x
    show (Tree.leaf c).budget x = (Tree.leaf c).budget x
    rfl
  | frac i l r ihl ihr =>
    intro x
    by_cases hi : i = id
    · have hfind : Tree.findFrac? id (.frac i l r) = some (.frac i l r) := by
        simp [findFrac?, hi]
      have hrep : Tree.replaceNode id t' (.frac i l r) = t' := by
        simp [replaceNode, hi]
      rw [hrep]
      exact h x i l r hfind
    · cases hf : l.findFrac? id with
      | some c =>
        have hl : ∀ x' i' l' r', l.findFrac? id = some (.frac i' l' r') →
            t'.budget x' = (Tree.frac i' l' r').budget x' := by
          intro x' i' l' r' hc'
          exact h x' i' l' r' (by simp [findFrac?, hi, hc'])
        have hrep : Tree.replaceNode id t' (.frac i l r)
            = .frac i (Tree.replaceNode id t' l) r := by
          simp [replaceNode, hi, hf]
        rw [hrep]
        calc
          (Tree.frac i (Tree.replaceNode id t' l) r).budget x
              = (Tree.replaceNode id t' l).budget x + r.budget x := rfl
          _ = l.budget x + r.budget x := by rw [ihl hl x]
          _ = (Tree.frac i l r).budget x := rfl
      | none =>
        have hr : ∀ x' i' l' r', r.findFrac? id = some (.frac i' l' r') →
            t'.budget x' = (Tree.frac i' l' r').budget x' := by
          intro x' i' l' r' hc'
          exact h x' i' l' r' (by simp [findFrac?, hi, hf, hc'])
        have hrep : Tree.replaceNode id t' (.frac i l r)
            = .frac i l (Tree.replaceNode id t' r) := by
          simp [replaceNode, hi, hf]
        rw [hrep]
        calc
          (Tree.frac i l (Tree.replaceNode id t' r)).budget x
              = l.budget x + (Tree.replaceNode id t' r).budget x := rfl
          _ = l.budget x + r.budget x := by rw [ihr hr x]
          _ = (Tree.frac i l r).budget x := rfl
  | spatial i l r ihl ihr =>
    intro x
    cases hf : l.findFrac? id with
    | some c =>
      have hl : ∀ x' i' l' r', l.findFrac? id = some (.frac i' l' r') →
          t'.budget x' = (Tree.frac i' l' r').budget x' := by
        intro x' i' l' r' hc'
        exact h x' i' l' r' (by simp [findFrac?, hc'])
      have hrep : Tree.replaceNode id t' (.spatial i l r)
          = .spatial i (Tree.replaceNode id t' l) r := by
        simp [replaceNode, hf]
      rw [hrep]
      calc
        (Tree.spatial i (Tree.replaceNode id t' l) r).budget x
            = (Tree.replaceNode id t' l).budget x + r.budget x := rfl
        _ = l.budget x + r.budget x := by rw [ihl hl x]
        _ = (Tree.spatial i l r).budget x := rfl
    | none =>
      have hr : ∀ x' i' l' r', r.findFrac? id = some (.frac i' l' r') →
          t'.budget x' = (Tree.frac i' l' r').budget x' := by
        intro x' i' l' r' hc'
        exact h x' i' l' r' (by simp [findFrac?, hf, hc'])
      have hrep : Tree.replaceNode id t' (.spatial i l r)
          = .spatial i l (Tree.replaceNode id t' r) := by
        simp [replaceNode, hf]
      rw [hrep]
      calc
        (Tree.spatial i l (Tree.replaceNode id t' r)).budget x
            = l.budget x + (Tree.replaceNode id t' r).budget x := rfl
        _ = l.budget x + r.budget x := by rw [ihr hr x]
        _ = (Tree.spatial i l r).budget x := rfl

/-- The located node is a fractional node. -/
theorem findFrac?_isFrac (id : CapId) :
    ∀ (t u : Tree), t.findFrac? id = some u → ∃ i l r, u = Tree.frac i l r := by
  intro t
  induction t with
  | leaf c =>
    intro u h
    simp [findFrac?] at h
  | frac i l r ihl ihr =>
    intro u h
    by_cases hi : i = id
    · have h1 : Tree.findFrac? id (.frac i l r) = some (.frac i l r) := by
        simp [findFrac?, hi]
      rw [h1] at h
      cases h
      exact ⟨i, l, r, rfl⟩
    · cases hf : l.findFrac? id with
      | some c =>
        have hcu : c = u := by
          rw [findFrac?] at h
          simp [hi, hf] at h
          exact h
        subst hcu
        exact ihl c hf
      | none =>
        have hru : r.findFrac? id = some u := by
          rw [findFrac?] at h
          simpa [hi, hf] using h
        exact ihr u hru
  | spatial i l r ihl ihr =>
    intro u h
    cases hf : l.findFrac? id with
    | some c =>
      have hcu : c = u := by
        rw [findFrac?] at h
        simp [hf] at h
        exact h
      subst hcu
      exact ihl c hf
    | none =>
      have hru : r.findFrac? id = some u := by
        rw [findFrac?] at h
        simpa [hf] using h
      exact ihr u hru

/-- The sibling join's budget statement for an arbitrary `frac` identifier (the
budget of a `frac` node does not depend on its own identifier). -/
theorem frac_join_budget_any_id {i : CapId} {c c1 c2 : Leaf} {x : Nat}
    (hstate1 : c1.state = c.state) (hstate2 : c2.state = c.state)
    (hlo1 : c1.lo = c.lo) (hhi1 : c1.hi = c.hi)
    (hlo2 : c2.lo = c.lo) (hhi2 : c2.hi = c.hi)
    (hq : c.q = c1.q + c2.q) :
    (Tree.leaf c).budget x = (Tree.frac i (.leaf c1) (.leaf c2)).budget x := by
  simpa [Tree.budget] using
    frac_join_budget (c := c) (c1 := c1) (c2 := c2)
      hstate1 hstate2 hlo1 hhi1 hlo2 hhi2 hq

/-- Join the two leaf children of a fractional node into one leaf, provided the
children are distinct capabilities with the same allocation, footprint, ceiling
and state. The new leaf is named `newId`, has the children's summed share and
inherits the other fields from the left child. -/
def joinChildren? (newId : CapId) : Tree → Option Tree
  | .frac _ (.leaf c1) (.leaf c2) =>
    if c1.id = c2.id then none
    else if c1.alloc = c2.alloc ∧ c1.lo = c2.lo ∧ c1.hi = c2.hi ∧
            c1.ceiling = c2.ceiling ∧ c1.state = c2.state ∧
            c1.state = .active then
      some (.leaf
        { id := newId, alloc := c1.alloc, lo := c1.lo, hi := c1.hi,
          ordered := c1.ordered, q := c1.q + c2.q,
          pos := by have h1 := c1.pos; have h2 := c2.pos; omega,
          ceiling := c1.ceiling, state := c1.state })
    else none
  | _ => none

/-- A successful join under the same resource is a same-budget replacement. -/
theorem joinChildren?_budget (node : Tree) (newId : CapId) (t' : Tree)
    (h : node.joinChildren? newId = some t') :
    ∀ x, t'.budget x = node.budget x := by
  intro x
  cases node with
  | leaf c => simp [joinChildren?] at h
  | spatial i l r => simp [joinChildren?] at h
  | frac i l r =>
    cases l with
    | leaf c1 =>
      cases r with
      | leaf c2 =>
        by_cases hid : c1.id = c2.id
        · simp [joinChildren?, hid] at h
        · by_cases hg : c1.alloc = c2.alloc ∧ c1.lo = c2.lo ∧ c1.hi = c2.hi ∧
              c1.ceiling = c2.ceiling ∧ c1.state = c2.state ∧
              c1.state = .active
          · have hu : t' = .leaf
                { id := newId, alloc := c1.alloc, lo := c1.lo, hi := c1.hi,
                  ordered := c1.ordered, q := c1.q + c2.q,
                  pos := by have h1 := c1.pos; have h2 := c2.pos; omega,
                  ceiling := c1.ceiling, state := c1.state } := by
              rw [joinChildren?] at h
              rw [if_neg hid, if_pos hg] at h
              exact (Option.some.inj h).symm
            rw [hu]
            obtain ⟨hl, hlo, hhi, hc, hs, hact⟩ := hg
            exact frac_join_budget_any_id (i := i)
              rfl hs.symm rfl rfl hlo.symm hhi.symm rfl
          · simp [joinChildren?, hid, hg] at h
      | frac j l' r' => simp [joinChildren?] at h
      | spatial j l' r' => simp [joinChildren?] at h
    | frac j l' r' => simp [joinChildren?] at h
    | spatial j l' r' => simp [joinChildren?] at h

/-- A join of a retired (suspended or consumed) child is refused, so a lender's
leaf cannot be merged away while its loan exists. -/
theorem joinChildren?_retired_none {i newId : CapId} {c1 c2 : Leaf}
    (hs : c1.state ≠ .active) :
    joinChildren? newId (.frac i (.leaf c1) (.leaf c2)) = none := by
  simp only [joinChildren?]
  by_cases hid : c1.id = c2.id
  · simp [hid]
  · rw [if_neg hid]
    by_cases hg : c1.alloc = c2.alloc ∧ c1.lo = c2.lo ∧ c1.hi = c2.hi ∧
        c1.ceiling = c2.ceiling ∧ c1.state = c2.state ∧ c1.state = .active
    · rw [if_pos hg]
      exact absurd hg.2.2.2.2.2 hs
    · rw [if_neg hg]

/-- Two children carrying the same capability identifier are never joined. -/
theorem joinChildren?_alias_none (i newId : CapId) (c1 c2 : Leaf)
    (h : c1.id = c2.id) :
    joinChildren? newId (.frac i (.leaf c1) (.leaf c2)) = none := by
  simp [joinChildren?, h]

end Tree

/-- Sibling-only fractional join: find the fractional node `node`, join its two
leaf children into a single leaf named `newId`, and replace the node by that leaf.
The join is refused when the node is absent, when either child is not a leaf, when
the children disagree on allocation, footprint, ceiling or state, or when the
children carry the same capability identifier. -/
def Owner.joinFraction? (o : Owner) (node newId : CapId) : Option Owner :=
  match o.root.findFrac? node with
  | none => none
  | some t =>
    match t.joinChildren? newId with
    | none => none
    | some t' => some { o with root := Tree.replaceNode node t' o.root }

/-- A sibling-only fractional join preserves coverage: the joined leaf has the
`frac` node's budget at every byte. -/
theorem Owner.joinFraction_covered {o o' : Owner} {D : Nat} {node newId : CapId}
    (h : o.joinFraction? node newId = some o') (hcov : o.Covered D) :
    o'.Covered D := by
  unfold Owner.joinFraction? at h
  cases hf : o.root.findFrac? node with
  | none => simp [hf] at h
  | some tn =>
    cases hj : tn.joinChildren? newId with
    | none => simp [hf, hj] at h
    | some t' =>
      simp only [hf, hj, Option.some.injEq] at h
      subst h
      intro x hx
      rw [Tree.budget_replaceNode o.root node t']
      · exact hcov x hx
      · intro x' i l r hff
        have ht : tn = .frac i l r := by
          rw [hf] at hff
          cases hff
          rfl
        rw [← ht]
        exact Tree.joinChildren?_budget tn newId t' hj x'

/-- A sibling-only fractional join keeps the owner's allocation identifier. -/
theorem Owner.joinFraction_alloc {o o' : Owner} {node newId : CapId}
    (h : o.joinFraction? node newId = some o') : o'.alloc = o.alloc := by
  unfold Owner.joinFraction? at h
  cases hf : o.root.findFrac? node with
  | none => simp [hf] at h
  | some tn =>
    cases hj : tn.joinChildren? newId with
    | none => simp [hf, hj] at h
    | some t' =>
      simp only [hf, hj, Option.some.injEq] at h
      subst h
      rfl

/-- An alias join — the located node is a `frac` node whose children are leaves
with the same capability identifier — is refused. -/
theorem Owner.joinFraction_alias_none (o : Owner) (node newId i : CapId)
    (c1 c2 : Leaf)
    (hf : o.root.findFrac? node = some (.frac i (.leaf c1) (.leaf c2)))
    (h : c1.id = c2.id) : o.joinFraction? node newId = none := by
  simp [Owner.joinFraction?, hf, Tree.joinChildren?_alias_none i newId c1 c2 h]

/-! ### Identifier lists after a join -/

/-- The identifiers of a located fractional node occur in the tree's identifier
list. -/
theorem Tree.findFrac?_ids_sub {t u : Tree} {id x : CapId}
    (h : t.findFrac? id = some u) (hx : x ∈ u.ids) : x ∈ t.ids := by
  induction t with
  | leaf c => simp [findFrac?] at h
  | frac i l r ihl ihr =>
    by_cases hi : i = id
    · have h1 : Tree.findFrac? id (.frac i l r) = some (.frac i l r) := by
        simp [findFrac?, hi]
      rw [h1] at h
      cases h
      exact hx
    · cases hf : l.findFrac? id with
      | some w =>
        have huw : u = w := by
          have h' : Tree.findFrac? id (.frac i l r) = some w := by
            simp [findFrac?, hi, hf]
          rw [h'] at h
          exact (Option.some.inj h).symm
        subst huw
        exact List.mem_append.mpr (Or.inl (ihl hf))
      | none =>
        have hur : r.findFrac? id = some u := by simpa [findFrac?, hi, hf] using h
        exact List.mem_append.mpr (Or.inr (ihr hur))
  | spatial i l r ihl ihr =>
    cases hf : l.findFrac? id with
    | some w =>
      have huw : u = w := by
        have h' : Tree.findFrac? id (.spatial i l r) = some w := by
          simp [findFrac?, hf]
        rw [h'] at h
        exact (Option.some.inj h).symm
      subst huw
      exact List.mem_append.mpr (Or.inl (ihl hf))
    | none =>
      have hur : r.findFrac? id = some u := by simpa [findFrac?, hf] using h
      exact List.mem_append.mpr (Or.inr (ihr hur))

/-- A successful sibling join names a two-leaf fractional node with distinct
children identifiers; the joined leaf carries `newId` and inherits its
allocation and footprint from the left child. -/
theorem Tree.joinChildren?_some {node : Tree} {newId : CapId} {t' : Tree}
    (h : node.joinChildren? newId = some t') :
    ∃ i c1 c2, node = .frac i (.leaf c1) (.leaf c2) ∧ c1.id ≠ c2.id ∧
      t'.ids = [newId] ∧
      ∀ x c, t'.find? x = some c → x = newId ∧ c.alloc = c1.alloc ∧ c.hi = c1.hi := by
  cases node with
  | leaf c => simp [joinChildren?] at h
  | spatial i l r => simp [joinChildren?] at h
  | frac i l r =>
    cases l with
    | leaf c1 =>
      cases r with
      | leaf c2 =>
        by_cases hid : c1.id = c2.id
        · simp [joinChildren?, hid] at h
        · by_cases hg : c1.alloc = c2.alloc ∧ c1.lo = c2.lo ∧ c1.hi = c2.hi ∧
              c1.ceiling = c2.ceiling ∧ c1.state = c2.state ∧
              c1.state = .active
          · have hu : t' = .leaf
                { id := newId, alloc := c1.alloc, lo := c1.lo, hi := c1.hi,
                  ordered := c1.ordered, q := c1.q + c2.q,
                  pos := by have h1 := c1.pos; have h2 := c2.pos; omega,
                  ceiling := c1.ceiling, state := c1.state } := by
              rw [joinChildren?] at h
              rw [if_neg hid, if_pos hg] at h
              exact (Option.some.inj h).symm
            refine ⟨i, c1, c2, rfl, hid, by rw [hu]; rfl, ?_⟩
            intro x c hx
            rw [hu] at hx
            by_cases hx2 : newId = x
            · subst hx2
              simp [Tree.find?] at hx
              cases hx
              exact ⟨rfl, rfl, rfl⟩
            · simp [Tree.find?, hx2] at hx
          · simp [joinChildren?, hid, hg] at h
      | frac j l' r' => simp [joinChildren?] at h
      | spatial j l' r' => simp [joinChildren?] at h
    | frac j l' r' => simp [joinChildren?] at h
    | spatial j l' r' => simp [joinChildren?] at h

/-- Every identifier of the node-replaced tree either occurred in the original
tree or occurs in the replacement. -/
theorem Tree.mem_ids_replaceNode {t : Tree} {node x : CapId} {t' : Tree}
    (h : x ∈ (Tree.replaceNode node t' t).ids) : x ∈ t.ids ∨ x ∈ t'.ids := by
  induction t with
  | leaf c => exact Or.inl h
  | frac i l r ihl ihr =>
    by_cases hi : i = node
    · have hrep : Tree.replaceNode node t' (.frac i l r) = t' := by
        simp [replaceNode, hi]
      rw [hrep] at h
      exact Or.inr h
    · cases hf : l.findFrac? node with
      | some w =>
        have hrep : Tree.replaceNode node t' (.frac i l r)
            = .frac i (Tree.replaceNode node t' l) r := by
          simp [replaceNode, hi, hf]
        rw [hrep] at h
        have hh : x ∈ (Tree.replaceNode node t' l).ids ++ r.ids := h
        rcases List.mem_append.mp hh with hl | hr
        · rcases ihl hl with hm | hm
          · exact Or.inl (List.mem_append.mpr (Or.inl hm))
          · exact Or.inr hm
        · exact Or.inl (List.mem_append.mpr (Or.inr hr))
      | none =>
        have hrep : Tree.replaceNode node t' (.frac i l r)
            = .frac i l (Tree.replaceNode node t' r) := by
          simp [replaceNode, hi, hf]
        rw [hrep] at h
        have hh : x ∈ l.ids ++ (Tree.replaceNode node t' r).ids := h
        rcases List.mem_append.mp hh with hl | hr
        · exact Or.inl (List.mem_append.mpr (Or.inl hl))
        · rcases ihr hr with hm | hm
          · exact Or.inl (List.mem_append.mpr (Or.inr hm))
          · exact Or.inr hm
  | spatial i l r ihl ihr =>
    cases hf : l.findFrac? node with
    | some w =>
      have hrep : Tree.replaceNode node t' (.spatial i l r)
          = .spatial i (Tree.replaceNode node t' l) r := by
        simp [replaceNode, hf]
      rw [hrep] at h
      have hh : x ∈ (Tree.replaceNode node t' l).ids ++ r.ids := h
      rcases List.mem_append.mp hh with hl | hr
      · rcases ihl hl with hm | hm
        · exact Or.inl (List.mem_append.mpr (Or.inl hm))
        · exact Or.inr hm
      · exact Or.inl (List.mem_append.mpr (Or.inr hr))
    | none =>
      have hrep : Tree.replaceNode node t' (.spatial i l r)
          = .spatial i l (Tree.replaceNode node t' r) := by
        simp [replaceNode, hf]
      rw [hrep] at h
      have hh : x ∈ l.ids ++ (Tree.replaceNode node t' r).ids := h
      rcases List.mem_append.mp hh with hl | hr
      · exact Or.inl (List.mem_append.mpr (Or.inl hl))
      · rcases ihr hr with hm | hm
        · exact Or.inl (List.mem_append.mpr (Or.inr hm))
        · exact Or.inr hm

/-- Filtering two absent identifiers out of a list leaves it unchanged. -/
private theorem filter_not_mem₂_self {l : List CapId} {a b : CapId}
    (ha : a ∉ l) (hb : b ∉ l) :
    l.filter (fun x => x ≠ a ∧ x ≠ b) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hxa : ¬ x = a := fun hx' => ha (hx' ▸ List.mem_cons_self)
    have hxb : ¬ x = b := fun hx' => hb (hx' ▸ List.mem_cons_self)
    have hxs_a : a ∉ xs := fun h' => ha (List.mem_cons_of_mem x h')
    have hxs_b : b ∉ xs := fun h' => hb (List.mem_cons_of_mem x h')
    have hp : decide (x ≠ a ∧ x ≠ b) = true := by simp [hxa, hxb]
    rw [List.filter_cons, ite_eq_left hp, ih hxs_a hxs_b]

/-- Replacing the located two-leaf fractional node by a leaf turns the
identifier list into the original list without the two children's identifiers,
followed by the new leaf's identifier. This is a permutation statement because
the replacement sits where the node was. -/
theorem Tree.ids_replaceNode_perm {t : Tree} {node newId : CapId} {t' : Tree}
    {i : CapId} {c1 c2 : Leaf}
    (hnd : t.ids.Nodup)
    (hf : t.findFrac? node = some (.frac i (.leaf c1) (.leaf c2)))
    (ht' : t'.ids = [newId]) :
    (Tree.replaceNode node t' t).ids.Perm
      (t.ids.filter (fun x => x ≠ c1.id ∧ x ≠ c2.id) ++ [newId]) := by
  induction t with
  | leaf c => simp [findFrac?] at hf
  | frac j l r ihl ihr =>
    by_cases hj : j = node
    · have hfind : Tree.findFrac? node (.frac j l r) = some (.frac j l r) := by
        simp [findFrac?, hj]
      rw [hfind] at hf
      cases hf
      have hrep : Tree.replaceNode node t' (.frac i (.leaf c1) (.leaf c2)) = t' := by
        simp [replaceNode, hj]
      rw [hrep, ht']
      show [newId].Perm (([c1.id, c2.id] : List CapId).filter _ ++ [newId])
      have hfilt : ([c1.id, c2.id] : List CapId).filter (fun x => x ≠ c1.id ∧ x ≠ c2.id)
          = [] := by
        simp [List.filter_cons]
      rw [hfilt]
      exact List.Perm.refl _
    · cases hfl : l.findFrac? node with
      | some u =>
        have hu : u = .frac i (.leaf c1) (.leaf c2) := by
          have h' : Tree.findFrac? node (.frac j l r) = some u := by
            simp [findFrac?, hj, hfl]
          rw [h'] at hf
          exact Option.some.inj hf
        subst hu
        have hc1 : c1.id ∈ l.ids := Tree.findFrac?_ids_sub hfl (by simp [Tree.ids])
        have hc2 : c2.id ∈ l.ids := Tree.findFrac?_ids_sub hfl (by simp [Tree.ids])
        have hndt : (l.ids ++ r.ids).Nodup := hnd
        obtain ⟨hndl, hndr, hdisj⟩ := List.nodup_append.mp hndt
        have hr1 : c1.id ∉ r.ids := fun hr => hdisj _ hc1 _ hr rfl
        have hr2 : c2.id ∉ r.ids := fun hr => hdisj _ hc2 _ hr rfl
        have hfiltr : r.ids.filter (fun x => x ≠ c1.id ∧ x ≠ c2.id) = r.ids :=
          filter_not_mem₂_self hr1 hr2
        have ih := ihl hndl hfl
        have hrep : Tree.replaceNode node t' (.frac j l r)
            = .frac j (Tree.replaceNode node t' l) r := by
          simp [replaceNode, hj, hfl]
        rw [hrep]
        show ((Tree.replaceNode node t' l).ids ++ r.ids).Perm
          ((l.ids ++ r.ids).filter (fun x => x ≠ c1.id ∧ x ≠ c2.id) ++ [newId])
        rw [List.filter_append, hfiltr]
        refine List.Perm.trans (List.Perm.append ih (List.Perm.refl r.ids)) ?_
        have e1 : (l.ids.filter (fun x => x ≠ c1.id ∧ x ≠ c2.id) ++ [newId]) ++ r.ids
            = l.ids.filter (fun x => x ≠ c1.id ∧ x ≠ c2.id) ++ ([newId] ++ r.ids) :=
          List.append_assoc ..
        have e2 : (l.ids.filter (fun x => x ≠ c1.id ∧ x ≠ c2.id) ++ r.ids) ++ [newId]
            = l.ids.filter (fun x => x ≠ c1.id ∧ x ≠ c2.id) ++ (r.ids ++ [newId]) :=
          List.append_assoc ..
        rw [e1, e2]
        exact List.Perm.append_left _ List.perm_append_comm
      | none =>
        have hfr : r.findFrac? node = some (.frac i (.leaf c1) (.leaf c2)) := by
          simpa [findFrac?, hj, hfl] using hf
        have hc1 : c1.id ∈ r.ids := Tree.findFrac?_ids_sub hfr (by simp [Tree.ids])
        have hc2 : c2.id ∈ r.ids := Tree.findFrac?_ids_sub hfr (by simp [Tree.ids])
        have hndt : (l.ids ++ r.ids).Nodup := hnd
        obtain ⟨hndl, hndr, hdisj⟩ := List.nodup_append.mp hndt
        have hl1 : c1.id ∉ l.ids := fun hl => hdisj _ hl _ hc1 rfl
        have hl2 : c2.id ∉ l.ids := fun hl => hdisj _ hl _ hc2 rfl
        have hfiltl : l.ids.filter (fun x => x ≠ c1.id ∧ x ≠ c2.id) = l.ids :=
          filter_not_mem₂_self hl1 hl2
        have ih := ihr hndr hfr
        have hrep : Tree.replaceNode node t' (.frac j l r)
            = .frac j l (Tree.replaceNode node t' r) := by
          simp [replaceNode, hj, hfl]
        rw [hrep]
        show (l.ids ++ (Tree.replaceNode node t' r).ids).Perm
          ((l.ids ++ r.ids).filter (fun x => x ≠ c1.id ∧ x ≠ c2.id) ++ [newId])
        rw [List.filter_append, hfiltl]
        refine List.Perm.trans (List.Perm.append_left l.ids ih) ?_
        rw [List.append_assoc]
  | spatial j l r ihl ihr =>
    cases hfl : l.findFrac? node with
    | some u =>
      have hu : u = .frac i (.leaf c1) (.leaf c2) := by
        have h' : Tree.findFrac? node (.spatial j l r) = some u := by
          simp [findFrac?, hfl]
        rw [h'] at hf
        exact Option.some.inj hf
      subst hu
      have hc1 : c1.id ∈ l.ids := Tree.findFrac?_ids_sub hfl (by simp [Tree.ids])
      have hc2 : c2.id ∈ l.ids := Tree.findFrac?_ids_sub hfl (by simp [Tree.ids])
      have hndt : (l.ids ++ r.ids).Nodup := hnd
      obtain ⟨hndl, hndr, hdisj⟩ := List.nodup_append.mp hndt
      have hr1 : c1.id ∉ r.ids := fun hr => hdisj _ hc1 _ hr rfl
      have hr2 : c2.id ∉ r.ids := fun hr => hdisj _ hc2 _ hr rfl
      have hfiltr : r.ids.filter (fun x => x ≠ c1.id ∧ x ≠ c2.id) = r.ids :=
        filter_not_mem₂_self hr1 hr2
      have ih := ihl hndl hfl
      have hrep : Tree.replaceNode node t' (.spatial j l r)
          = .spatial j (Tree.replaceNode node t' l) r := by
        simp [replaceNode, hfl]
      rw [hrep]
      show ((Tree.replaceNode node t' l).ids ++ r.ids).Perm
        ((l.ids ++ r.ids).filter (fun x => x ≠ c1.id ∧ x ≠ c2.id) ++ [newId])
      rw [List.filter_append, hfiltr]
      refine List.Perm.trans (List.Perm.append ih (List.Perm.refl r.ids)) ?_
      have e1 : (l.ids.filter (fun x => x ≠ c1.id ∧ x ≠ c2.id) ++ [newId]) ++ r.ids
          = l.ids.filter (fun x => x ≠ c1.id ∧ x ≠ c2.id) ++ ([newId] ++ r.ids) :=
        List.append_assoc ..
      have e2 : (l.ids.filter (fun x => x ≠ c1.id ∧ x ≠ c2.id) ++ r.ids) ++ [newId]
          = l.ids.filter (fun x => x ≠ c1.id ∧ x ≠ c2.id) ++ (r.ids ++ [newId]) :=
        List.append_assoc ..
      rw [e1, e2]
      exact List.Perm.append_left _ List.perm_append_comm
    | none =>
      have hfr : r.findFrac? node = some (.frac i (.leaf c1) (.leaf c2)) := by
        simpa [findFrac?, hfl] using hf
      have hc1 : c1.id ∈ r.ids := Tree.findFrac?_ids_sub hfr (by simp [Tree.ids])
      have hc2 : c2.id ∈ r.ids := Tree.findFrac?_ids_sub hfr (by simp [Tree.ids])
      have hndt : (l.ids ++ r.ids).Nodup := hnd
      obtain ⟨hndl, hndr, hdisj⟩ := List.nodup_append.mp hndt
      have hl1 : c1.id ∉ l.ids := fun hl => hdisj _ hl _ hc1 rfl
      have hl2 : c2.id ∉ l.ids := fun hl => hdisj _ hl _ hc2 rfl
      have hfiltl : l.ids.filter (fun x => x ≠ c1.id ∧ x ≠ c2.id) = l.ids :=
        filter_not_mem₂_self hl1 hl2
      have ih := ihr hndr hfr
      have hrep : Tree.replaceNode node t' (.spatial j l r)
          = .spatial j l (Tree.replaceNode node t' r) := by
        simp [replaceNode, hfl]
      rw [hrep]
      show (l.ids ++ (Tree.replaceNode node t' r).ids).Perm
        ((l.ids ++ r.ids).filter (fun x => x ≠ c1.id ∧ x ≠ c2.id) ++ [newId])
      rw [List.filter_append, hfiltl]
      refine List.Perm.trans (List.Perm.append_left l.ids ih) ?_
      rw [List.append_assoc]

/-- A fractional join keeps the owner's length. -/
theorem Owner.joinFraction?_len {o o' : Owner} {node newId : CapId}
    (h : o.joinFraction? node newId = some o') : o'.len = o.len := by
  unfold Owner.joinFraction? at h
  cases hf : o.root.findFrac? node with
  | none => simp [hf] at h
  | some tn =>
    cases hj : tn.joinChildren? newId with
    | none => simp [hf, hj] at h
    | some t' =>
      simp only [hf, hj, Option.some.injEq] at h
      subst h
      rfl

/-- A successful fractional join turns the owner's identifier list into the old
list without the two joined children, followed by the new leaf's identifier.
The existential packages the children, so the statement supports nodup
preservation: the filtered list is duplicate-free and the new identifier only
needs to be fresh. -/
theorem Owner.joinFraction?_ids_perm {o o' : Owner} {node newId : CapId}
    (hids : o.ids.Nodup) (h : o.joinFraction? node newId = some o') :
    ∃ c1 c2 : Leaf, c1.id ∈ o.ids ∧ c2.id ∈ o.ids ∧ c1.id ≠ c2.id ∧
      o'.ids.Perm (o.ids.filter (fun x => x ≠ c1.id ∧ x ≠ c2.id) ++ [newId]) := by
  have hroot : o.root.ids.Nodup := (List.nodup_cons.mp hids).2
  have hdisp : o.disposal ∉ o.root.ids := (List.nodup_cons.mp hids).1
  unfold Owner.joinFraction? at h
  cases hf : o.root.findFrac? node with
  | none => simp [hf] at h
  | some tn =>
    cases hj : tn.joinChildren? newId with
    | none => simp [hf, hj] at h
    | some t' =>
      simp only [hf, hj, Option.some.injEq] at h
      subst h
      obtain ⟨i, c1, c2, htn, h12, ht'ids, -⟩ := Tree.joinChildren?_some hj
      subst htn
      have hc1mem : c1.id ∈ o.root.ids := Tree.findFrac?_ids_sub hf (by simp [Tree.ids])
      have hc2mem : c2.id ∈ o.root.ids := Tree.findFrac?_ids_sub hf (by simp [Tree.ids])
      refine ⟨c1, c2, List.mem_cons_of_mem _ hc1mem, List.mem_cons_of_mem _ hc2mem,
        h12, ?_⟩
      have hperm := Tree.ids_replaceNode_perm (t := o.root) (node := node) (t' := t')
        (i := i) (c1 := c1) (c2 := c2) hroot hf ht'ids
      have hd1 : o.disposal ≠ c1.id := fun hEq => hdisp (hEq ▸ hc1mem)
      have hd2 : o.disposal ≠ c2.id := fun hEq => hdisp (hEq ▸ hc2mem)
      have hfilt : (o.disposal :: o.root.ids).filter (fun x => x ≠ c1.id ∧ x ≠ c2.id)
          = o.disposal :: o.root.ids.filter (fun x => x ≠ c1.id ∧ x ≠ c2.id) := by
        rw [List.filter_cons, ite_eq_left (by simp [hd1, hd2])]
      simp only [Owner.ids]
      rw [hfilt]
      exact List.Perm.cons o.disposal hperm

/-- Every identifier of the joined owner is the new leaf's identifier or an
identifier of the original owner. -/
theorem Owner.joinFraction?_ids_sub {o o' : Owner} {node newId x : CapId}
    (h : o.joinFraction? node newId = some o') (hx : x ∈ o'.ids) :
    x = newId ∨ x ∈ o.ids := by
  unfold Owner.joinFraction? at h
  cases hf : o.root.findFrac? node with
  | none => simp [hf] at h
  | some tn =>
    cases hj : tn.joinChildren? newId with
    | none => simp [hf, hj] at h
    | some t' =>
      simp only [hf, hj, Option.some.injEq] at h
      subst h
      obtain ⟨-, -, -, -, -, ht'ids, -⟩ := Tree.joinChildren?_some hj
      rcases List.mem_cons.mp hx with rfl | hxroot
      · exact Or.inr List.mem_cons_self
      · rcases Tree.mem_ids_replaceNode hxroot with hold | hnew
        · exact Or.inr (List.mem_cons_of_mem _ hold)
        · rw [ht'ids] at hnew
          exact Or.inl (List.mem_singleton.mp hnew)

/-- A fractional join keeps the owner's identifiers distinct when the new
identifier is fresh. -/
theorem Owner.joinFraction?_ids_nodup {o o' : Owner} {node newId : CapId}
    (hids : o.ids.Nodup) (hfresh : newId ∉ o.ids)
    (h : o.joinFraction? node newId = some o') : o'.ids.Nodup := by
  obtain ⟨c1, c2, -, -, -, hperm⟩ := Owner.joinFraction?_ids_perm hids h
  apply (hperm.nodup_iff).mpr
  refine List.nodup_append.mpr ⟨?_, by simp, ?_⟩
  · exact List.Nodup.sublist List.filter_sublist hids
  · intro y hy z hz
    have hz' : z = newId := List.mem_singleton.mp hz
    have hyC : y ∈ o.ids := List.filter_sublist.subset hy
    exact fun hyz => hfresh (hz' ▸ hyz ▸ hyC)

end Cap
