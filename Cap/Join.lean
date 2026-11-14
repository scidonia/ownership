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
            c1.ceiling = c2.ceiling ∧ c1.state = c2.state then
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
              c1.ceiling = c2.ceiling ∧ c1.state = c2.state
          · have hu : t' = .leaf
                { id := newId, alloc := c2.alloc, lo := c2.lo, hi := c2.hi,
                  ordered := c2.ordered, q := c1.q + c2.q,
                  pos := by have h1 := c1.pos; have h2 := c2.pos; omega,
                  ceiling := c2.ceiling, state := c2.state } := by
              rw [joinChildren?] at h
              simp [hid, hg] at h
              exact h.symm
            rw [hu]
            obtain ⟨_, hl, hh, _, hs⟩ := hg
            exact frac_join_budget_any_id (i := i)
              hs rfl hl hh rfl rfl rfl
          · simp [joinChildren?, hid, hg] at h
      | frac j l' r' => simp [joinChildren?] at h
      | spatial j l' r' => simp [joinChildren?] at h
    | frac j l' r' => simp [joinChildren?] at h
    | spatial j l' r' => simp [joinChildren?] at h

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

end Cap
