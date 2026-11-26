/-
Borrowed subdivision with reconstruction obligations.

A borrowed resource may be subdivided while the loan is outstanding. The
subdivision is not a second arithmetic model: each node records the checked
spatial or fractional rule of `Cap.Ledger`, and the node's budget is the sum of
its current children's budgets. A node stays in the forest until both children
have been reconstructed to the fragments the rule names, at which point the
parent fragment is restored and the children's access names are retired.

The lifecycle is the worked 64-byte example:

  own `a : [0,64), D`
  borrow `b : [0,64), D`            (restore `a` when `b` returns)
  split `left : [0,32), D`, `right : [32,64), D`
                                   (reconstruct the borrowed resource)
  process the two footprints
  reconstruct `[0,64), D`          (retire `left` and `right`)
  return `a : [0,64), D`           (retire `b`)

The checked operations refuse a subdivision whose children overlap or leave a
gap, a fractional subdivision whose shares do not sum to the parent, a
reconstruction while a child has been subdivided or lent further, a reuse of a
retired name, and a return before the borrowed resource has been reconstructed.

`Cap.World` still guards split and join by the allocation-wide test `no loan on
the allocation`. That test is what prevents a split of an independent sibling
while another range is borrowed, so the frame property is stated on the
reconstruction model below and `World.splitAtChecked_refuses_with_loan` records
the current guard. The exact core change is: delete the allocation-wide loan
test from `World.splitAtChecked`, `World.splitFractionChecked` and
`World.joinChecked` (leave it in `World.freeChecked`), and have those operations
consult the reconstruction forest instead: split or join a current live
fragment, record or discharge its reconstruction obligation, and require
reconstruction in `World.endBorrowChecked`. Loan exclusion is a property of the
authority an operation consumes, not of the allocation's footprint.
-/
import Cap.Ledger
import Cap.WorldInvariant

namespace Cap

/-- Two leaves carry the same access name and resource description. -/
def Leaf.Agrees (a b : Leaf) : Prop :=
  a.id = b.id ∧ a.alloc = b.alloc ∧ a.lo = b.lo ∧ a.hi = b.hi ∧ a.q = b.q ∧
  a.ceiling = b.ceiling ∧ a.state = b.state

instance (a b : Leaf) : Decidable (a.Agrees b) := by
  unfold Leaf.Agrees
  infer_instance

/-- Two leaves describe the same allocation, footprint, share and ceiling. The
access identity is deliberately excluded: this is the resource agreement that a
retagging preserves. -/
def Leaf.SameResource (a b : Leaf) : Prop :=
  a.alloc = b.alloc ∧ a.lo = b.lo ∧ a.hi = b.hi ∧ a.q = b.q ∧
  a.ceiling = b.ceiling

instance (a b : Leaf) : Decidable (a.SameResource b) := by
  unfold Leaf.SameResource
  infer_instance

namespace Reconstruction

/-- The two checked subdivision rules. -/
inductive RuleKind where
  | spatial
  | fractional
deriving DecidableEq, Repr

/-- A recorded return obligation: the dormant lender capability that is restored
when the borrower returns the borrowed resource. -/
structure Restore where
  lender : CapId
  borrower : CapId
  alloc : AllocId
  lo : Nat
  hi : Nat
  q : Nat
  ceiling : Ceiling
deriving DecidableEq, Repr

/-- A return obligation agrees with the resource of a leaf. -/
def Restore.Agrees (r : Restore) (c : Leaf) : Prop :=
  r.alloc = c.alloc ∧ r.lo = c.lo ∧ r.hi = c.hi ∧ r.q = c.q ∧
  r.ceiling = c.ceiling

/-- Two return obligations agree on the resource of a leaf. -/
def Restore.SameResource (r r' : Restore) : Prop :=
  r.alloc = r'.alloc ∧ r.lo = r'.lo ∧ r.hi = r'.hi ∧ r.q = r'.q ∧
  r.ceiling = r'.ceiling

/-- Resource agreement is symmetric. -/
theorem Restore.SameResource.symm {r r' : Restore} (h : r.SameResource r') :
    r'.SameResource r :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.symm⟩

/-- Leaf agreement entails resource agreement. -/
theorem Leaf.Agrees.sameResource {a b : Leaf} (h : a.Agrees b) : a.SameResource b :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

/-- An obligation with a resource equal to another agrees with whatever the
first agrees with. -/
theorem Restore.Agrees.of_sameResource {r r' : Restore} {c : Leaf}
    (hs : r.SameResource r') (ha : r.Agrees c) : r'.Agrees c :=
  ⟨hs.1.symm.trans ha.1, hs.2.1.symm.trans ha.2.1, hs.2.2.1.symm.trans ha.2.2.1,
   hs.2.2.2.1.symm.trans ha.2.2.2.1, hs.2.2.2.2.symm.trans ha.2.2.2.2⟩

instance (r : Restore) (c : Leaf) : Decidable (r.Agrees c) := by
  unfold Restore.Agrees
  infer_instance

instance (r r' : Restore) : Decidable (r.SameResource r') := by
  unfold Restore.SameResource
  infer_instance

/-- A plain-data description of a current fragment: allocation, interval, share,
ceiling and state. This is the exported view of a leaf; the proof fields stay
inside the reconstruction model. -/
structure Fragment where
  alloc : AllocId
  lo : Nat
  hi : Nat
  q : Nat
  ceiling : Ceiling
  state : CapState
deriving DecidableEq, Repr

/-- A checked reconstruction rule. The parent fragment is suspended and the two
rule fragments are the fragments the children must be reconstructed to. -/
def RuleValid (kind : RuleKind) (parent left right : Leaf) : Prop :=
  parent.state = .active ∧
  left.alloc = parent.alloc ∧ right.alloc = parent.alloc ∧
  left.ceiling = parent.ceiling ∧ right.ceiling = parent.ceiling ∧
  left.state = .active ∧ right.state = .active ∧
  left.id ≠ right.id ∧ left.id ≠ parent.id ∧ right.id ≠ parent.id ∧
  (match kind with
   | .spatial =>
       left.lo = parent.lo ∧ left.hi = right.lo ∧ right.hi = parent.hi ∧
       left.q = parent.q ∧ right.q = parent.q
   | .fractional =>
       left.lo = parent.lo ∧ left.hi = parent.hi ∧
       right.lo = parent.lo ∧ right.hi = parent.hi ∧
       0 < left.q ∧ 0 < right.q ∧ left.q + right.q = parent.q)

instance (kind : RuleKind) (parent left right : Leaf) :
    Decidable (RuleValid kind parent left right) := by
  unfold RuleValid
  cases kind <;> infer_instance

/-- A reconstruction forest. A `leaf` is a current fragment; a `split` records a
suspended parent, the two fragments the rule names, and the current subtrees of
those fragments. A child subtree is either the original fragment leaf or a
further subdivision rooted at it. -/
inductive Forest where
  | leaf (c : Leaf)
  | split (kind : RuleKind) (parent leftRule rightRule : Leaf)
      (left right : Forest)

namespace Forest

/-- The byte budget of the current frontier. A split node contributes its
children's budgets; the suspended parent and its rule contribute nothing. -/
def budget (x : Nat) : Forest → Nat
  | .leaf c => c.budget x
  | .split _ _ _ _ l r => l.budget x + r.budget x

/-- The ledger tree of the current frontier. The suspended rule fragments are
not current leaves. -/
def toTree : Forest → Tree
  | .leaf c => .leaf c
  | .split k p _ _ l r =>
      match k with
      | .spatial => .spatial p.id l.toTree r.toTree
      | .fractional => .frac p.id l.toTree r.toTree

/-- The frontier budget is the ledger tree budget. -/
theorem budget_eq_toTree (f : Forest) (x : Nat) : f.budget x = f.toTree.budget x := by
  induction f with
  | leaf c => rfl
  | split k p lr rr l r ihl ihr =>
      cases k <;> simp [Forest.budget, Forest.toTree, Tree.budget, ihl, ihr]

/-- Every split node records a valid rule; both current subtrees are valid. -/
def Valid : Forest → Prop
  | .leaf _ => True
  | .split k p lr rr l r => RuleValid k p lr rr ∧ l.Valid ∧ r.Valid

/-- A spatial split preserves the parent's budget at every byte. -/
theorem spatial_split_budget {p l r : Leaf} {x : Nat}
    (hsl : l.state = p.state) (hsr : r.state = p.state)
    (hlo : l.lo = p.lo) (hhi : l.hi = r.lo) (hrhi : r.hi = p.hi)
    (hql : l.q = p.q) (hqr : r.q = p.q)
    (hk1 : p.lo ≤ r.lo) (hk2 : r.lo ≤ p.hi) :
    (Forest.split .spatial p l r (.leaf l) (.leaf r)).budget x =
      (Forest.leaf p).budget x := by
  have hstateL : l.state = p.state := hsl
  have hstateR : r.state = p.state := hsr
  calc
    (Forest.split .spatial p l r (.leaf l) (.leaf r)).budget x
        = (Forest.split .spatial p l r (.leaf l) (.leaf r)).toTree.budget x :=
            budget_eq_toTree _ _
    _ = (Tree.spatial p.id (.leaf l) (.leaf r)).budget x := by
          simp [Forest.toTree, Tree.budget]
    _ = (Tree.leaf p).budget x :=
          Cap.spatial_split_budget hstateL hstateR hlo hhi rfl hrhi hql hqr hk1 hk2
    _ = (Forest.leaf p).budget x := (budget_eq_toTree (Forest.leaf p) x).symm

/-- A fractional split preserves the parent's budget at every byte. -/
theorem fractional_split_budget {p l r : Leaf} {x : Nat}
    (hsl : l.state = p.state) (hsr : r.state = p.state)
    (hlo1 : l.lo = p.lo) (hhi1 : l.hi = p.hi)
    (hlo2 : r.lo = p.lo) (hhi2 : r.hi = p.hi)
    (hsum : l.q + r.q = p.q) :
    (Forest.split .fractional p l r (.leaf l) (.leaf r)).budget x =
      (Forest.leaf p).budget x := by
  calc
    (Forest.split .fractional p l r (.leaf l) (.leaf r)).budget x
        = (Forest.split .fractional p l r (.leaf l) (.leaf r)).toTree.budget x :=
            budget_eq_toTree _ _
    _ = (Tree.frac p.id (.leaf l) (.leaf r)).budget x := by
          simp [Forest.toTree, Tree.budget]
    _ = (Tree.leaf p).budget x :=
          Cap.frac_split_budget hsl hsr hlo1 hhi1 hlo2 hhi2 hsum
    _ = (Forest.leaf p).budget x := (budget_eq_toTree (Forest.leaf p) x).symm

/-- Reconstructing a spatial subdivision restores the parent's budget. -/
theorem spatial_join_budget {p l r : Leaf} {x : Nat}
    (hsl : l.state = p.state) (hsr : r.state = p.state)
    (hlo : l.lo = p.lo) (hhi : l.hi = r.lo) (hrhi : r.hi = p.hi)
    (hql : l.q = p.q) (hqr : r.q = p.q)
    (hk1 : p.lo ≤ r.lo) (hk2 : r.lo ≤ p.hi) :
    (Forest.leaf p).budget x =
      (Forest.split .spatial p l r (.leaf l) (.leaf r)).budget x :=
  (spatial_split_budget (p := p) (l := l) (r := r) (x := x)
    hsl hsr hlo hhi hrhi hql hqr hk1 hk2).symm

/-- Reconstructing a fractional subdivision restores the parent's budget. -/
theorem fractional_join_budget {p l r : Leaf} {x : Nat}
    (hsl : l.state = p.state) (hsr : r.state = p.state)
    (hlo1 : l.lo = p.lo) (hhi1 : l.hi = p.hi)
    (hlo2 : r.lo = p.lo) (hhi2 : r.hi = p.hi)
    (hsum : l.q + r.q = p.q) :
    (Forest.leaf p).budget x =
      (Forest.split .fractional p l r (.leaf l) (.leaf r)).budget x :=
  (fractional_split_budget (p := p) (l := l) (r := r) (x := x)
    hsl hsr hlo1 hhi1 hlo2 hhi2 hsum).symm

/-- Two agreeing leaves have the same budget at every byte. -/
theorem Leaf.budget_congr {a b : Leaf} (h : a.Agrees b) (x : Nat) :
    a.budget x = b.budget x := by
  obtain ⟨_, _, hlo, hhi, hq, _, hstate⟩ := h
  simp [Leaf.budget, hlo, hhi, hq, hstate]

/-- Find the current leaf with the given access name. -/
def findLeaf? (id : CapId) : Forest → Option Leaf
  | .leaf c => if c.id = id then some c else none
  | .split _ _ _ _ l r =>
      match l.findLeaf? id with
      | some c => some c
      | none => r.findLeaf? id

/-- The current frontier fragments. -/
def leaves : Forest → List Leaf
  | .leaf c => [c]
  | .split _ _ _ _ l r => l.leaves ++ r.leaves

/-- Every access name the forest mentions: current leaves and the parent and rule
fragments of every suspension. -/
def ids : Forest → List CapId
  | .leaf c => [c.id]
  | .split _ p lr rr l r =>
      p.id :: lr.id :: rr.id :: (l.ids ++ r.ids)

/-- The fragments that carry a current access identity: the current leaves and
the suspended parent of every split. A rule fragment is a template that records
where reconstruction must place its children; it is not current authority. -/
def nodes : Forest → List Leaf
  | .leaf c => [c]
  | .split _ p _ _ l r => p :: (l.nodes ++ r.nodes)

/-- The rule fragments of every suspension. These are the child identities that a
reconstruction must recover before it may restore the suspended parent. -/
def ruleIds : Forest → List CapId
  | .leaf _ => []
  | .split _ _ lr rr l r => lr.id :: rr.id :: (l.ruleIds ++ r.ruleIds)

/-- A current leaf is an authority-carrying node. -/
theorem mem_nodes_of_mem_leaves {f : Forest} {c : Leaf} (h : c ∈ f.leaves) :
    c ∈ f.nodes := by
  induction f with
  | leaf d =>
      simp only [Forest.leaves, List.mem_singleton] at h
      subst h
      simp [Forest.nodes]
  | split k p lr rr l r ihl ihr =>
      simp only [Forest.leaves, List.mem_append] at h
      simp only [Forest.nodes, List.mem_cons]
      rcases h with h | h
      · exact Or.inr (List.mem_append.mpr (Or.inl (ihl h)))
      · exact Or.inr (List.mem_append.mpr (Or.inr (ihr h)))

/-- Every node identity is mentioned by the forest's identity list. -/
theorem node_id_mem_ids {f : Forest} {c : Leaf} (h : c ∈ f.nodes) :
    c.id ∈ f.ids := by
  induction f with
  | leaf d =>
      simp only [Forest.nodes, List.mem_singleton] at h
      subst h
      simp [Forest.ids]
  | split k p lr rr l r ihl ihr =>
      simp only [Forest.nodes, List.mem_cons, List.mem_append] at h
      simp only [Forest.ids]
      rcases h with rfl | h | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_append.mpr (Or.inl (ihl h)))))
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_append.mpr (Or.inr (ihr h)))))

/-- Every current leaf is an authority-carrying node, and the leaf list is a
sublist of the node list. -/
theorem leaves_sublist_nodes (f : Forest) : List.Sublist f.leaves f.nodes := by
  induction f with
  | leaf c => exact List.Sublist.refl _
  | split k p lr rr l r ihl ihr =>
      exact List.Sublist.cons p (List.Sublist.append ihl ihr)

/-- A list disjoint from another in pointwise form. -/
theorem not_mem_of_disjoint {l r : List CapId}
    (h : ∀ a ∈ l, ∀ b ∈ r, a ≠ b) {x : CapId} (hx : x ∈ l) : x ∉ r := by
  intro hy
  exact (h x hx x hy) rfl

/-- Convert pointwise non-membership into the relation `List.nodup_append`
expects. -/
theorem disjoint_of_not_mem {l r : List CapId}
    (h : ∀ x ∈ l, x ∉ r) : ∀ a ∈ l, ∀ b ∈ r, a ≠ b := by
  intro a ha b hb heq
  exact h a ha (heq ▸ hb)

/-- Every rule fragment identity is mentioned by the forest's identity list. -/
theorem rule_id_mem_ids {f : Forest} {x : CapId} (h : x ∈ f.ruleIds) :
    x ∈ f.ids := by
  induction f with
  | leaf c => simp [Forest.ruleIds] at h
  | split k p lr rr l r ihl ihr =>
      simp only [Forest.ruleIds, List.mem_cons, List.mem_append] at h
      simp only [Forest.ids]
      rcases h with rfl | rfl | h | h
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_append.mpr (Or.inl (ihl h)))))
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_append.mpr (Or.inr (ihr h)))))

/-- Modify the first current leaf with the given name. Returns the updated forest
and the leaf that was replaced. -/
def modifyLeafAt (id : CapId) (g : Leaf → Option (Forest × Leaf)) :
    Forest → Option (Forest × Leaf)
  | .leaf c => if c.id = id then g c else none
  | .split k p lr rr l r =>
      match modifyLeafAt id g l with
      | some (l', c) => some (.split k p lr rr l' r, c)
      | none =>
          match modifyLeafAt id g r with
          | some (r', c) => some (.split k p lr rr l r', c)
          | none => none

/-- Recovering a leaf by modification preserves the frontier budget. -/
theorem budget_modifyLeafAt {f f' : Forest} {id : CapId}
    {g : Leaf → Option (Forest × Leaf)} {c : Leaf}
    (h : f.modifyLeafAt id g = some (f', c))
    (hlocal : ∀ (d : Leaf) (x : Forest) (d' : Leaf),
      g d = some (x, d') → ∀ b, x.budget b = (Forest.leaf d).budget b) :
    ∀ b, f'.budget b = f.budget b := by
  induction f generalizing f' c with
  | leaf c0 =>
      simp only [Forest.modifyLeafAt] at h
      by_cases hc : c0.id = id
      · rw [if_pos hc] at h
        exact hlocal c0 f' c h
      · rw [if_neg hc] at h
        cases h
  | split k p lr rr l r ihl ihr =>
      simp only [Forest.modifyLeafAt] at h
      split at h
      · rename_i l' c' hl
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        intro b
        simp only [Forest.budget]
        rw [ihl hl b]
      · rename_i hl
        split at h
        · rename_i r' c' hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          intro b
          simp only [Forest.budget]
          rw [ihr hr b]
        · cases h

/-- Modifying a leaf preserves validity when the modification does. -/
theorem valid_modifyLeafAt {f f' : Forest} {id : CapId}
    {g : Leaf → Option (Forest × Leaf)} {c : Leaf}
    (h : f.modifyLeafAt id g = some (f', c))
    (hv : f.Valid)
    (hg : ∀ (d : Leaf) (x : Forest) (d' : Leaf), g d = some (x, d') → x.Valid) :
    f'.Valid := by
  induction f generalizing f' c with
  | leaf c0 =>
      simp only [Forest.modifyLeafAt] at h
      by_cases hc : c0.id = id
      · rw [if_pos hc] at h
        exact hg c0 f' c h
      · rw [if_neg hc] at h
        cases h
  | split k p lr rr l r ihl ihr =>
      simp only [Forest.Valid] at hv
      obtain ⟨hrule, hvl, hvr⟩ := hv
      simp only [Forest.modifyLeafAt] at h
      split at h
      · rename_i l' c' hl
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hrule, ihl hl hvl, hvr⟩
      · rename_i hl
        split at h
        · rename_i r' c' hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨hrule, hvl, ihr hr hvr⟩
        · cases h

/-- A split-shaped leaf modification keeps every old authority node. -/
theorem modifyLeafAt_nodes_old {f f' : Forest} {id : CapId}
    {g : Leaf → Option (Forest × Leaf)} {c : Leaf} {c1 c2 : CapId}
    (h : f.modifyLeafAt id g = some (f', c))
    (hlocal : ∀ (d : Leaf) (x : Forest) (d' : Leaf),
      g d = some (x, d') → x.nodes.map Leaf.id = d.id :: c1 :: c2 :: [])
    {y : CapId} (hy : y ∈ f.nodes.map Leaf.id) :
    y ∈ f'.nodes.map Leaf.id := by
  induction f generalizing f' c with
  | leaf c0 =>
      simp only [Forest.modifyLeafAt] at h
      by_cases hc : c0.id = id
      · rw [if_pos hc] at h
        have hlist := hlocal c0 f' c h
        simp only [Forest.nodes, List.map_cons, List.map_nil] at hy
        rw [hlist]
        simp only [List.mem_cons]
        left
        simpa using hy
      · rw [if_neg hc] at h
        cases h
  | split k p lr rr l r ihl ihr =>
      simp only [Forest.nodes, List.map_cons, List.map_append] at hy
      simp only [Forest.modifyLeafAt] at h
      split at h
      · rename_i l' c' hl
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Forest.nodes, List.map_cons, List.map_append]
        rcases List.mem_cons.mp hy with rfl | hy
        · exact List.mem_cons_self
        · rcases List.mem_append.mp hy with hy | hy
          · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl (ihl hl hy)))
          · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr hy))
      · rename_i hl
        split at h
        · rename_i r' c' hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [Forest.nodes, List.map_cons, List.map_append]
          rcases List.mem_cons.mp hy with rfl | hy
          · exact List.mem_cons_self
          · rcases List.mem_append.mp hy with hy | hy
            · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl hy))
            · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr (ihr hr hy)))
        · cases h

/-- A split-shaped leaf modification introduces only the two fresh child names. -/
theorem modifyLeafAt_nodes_mem {f f' : Forest} {id : CapId}
    {g : Leaf → Option (Forest × Leaf)} {c : Leaf} {c1 c2 : CapId}
    (h : f.modifyLeafAt id g = some (f', c))
    (hlocal : ∀ (d : Leaf) (x : Forest) (d' : Leaf),
      g d = some (x, d') → x.nodes.map Leaf.id = d.id :: c1 :: c2 :: [])
    {y : CapId} (hy : y ∈ f'.nodes.map Leaf.id) :
    y ∈ f.nodes.map Leaf.id ∨ y = c1 ∨ y = c2 := by
  induction f generalizing f' c with
  | leaf c0 =>
      simp only [Forest.modifyLeafAt] at h
      by_cases hc : c0.id = id
      · rw [if_pos hc] at h
        have hlist := hlocal c0 f' c h
        rw [hlist] at hy
        simp only [Forest.nodes, List.map_cons, List.map_nil]
        simpa using hy
      · rw [if_neg hc] at h
        cases h
  | split k p lr rr l r ihl ihr =>
      simp only [Forest.modifyLeafAt] at h
      split at h
      · rename_i l' c' hl
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Forest.nodes, List.map_cons, List.map_append] at hy ⊢
        rcases List.mem_cons.mp hy with rfl | hy
        · exact Or.inl List.mem_cons_self
        · rcases List.mem_append.mp hy with hy | hy
          · rcases ihl hl hy with hy | hy | hy
            · exact Or.inl (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl hy)))
            · exact Or.inr (Or.inl hy)
            · exact Or.inr (Or.inr hy)
          · exact Or.inl (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr hy)))
      · rename_i hl
        split at h
        · rename_i r' c' hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [Forest.nodes, List.map_cons, List.map_append] at hy ⊢
          rcases List.mem_cons.mp hy with rfl | hy
          · exact Or.inl List.mem_cons_self
          · rcases List.mem_append.mp hy with hy | hy
            · exact Or.inl (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl hy)))
            · rcases ihr hr hy with hy | hy | hy
              · exact Or.inl (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr hy)))
              · exact Or.inr (Or.inl hy)
              · exact Or.inr (Or.inr hy)
        · cases h

/-- A split-shaped leaf modification preserves distinct authority identities when
both child names are fresh. -/
theorem modifyLeafAt_nodes_nodup {f f' : Forest} {id : CapId}
    {g : Leaf → Option (Forest × Leaf)} {c : Leaf} {c1 c2 : CapId}
    (h : f.modifyLeafAt id g = some (f', c))
    (hn : (f.nodes.map Leaf.id).Nodup)
    (hlocal : ∀ (d : Leaf) (x : Forest) (d' : Leaf),
      g d = some (x, d') → x.nodes.map Leaf.id = d.id :: c1 :: c2 :: [])
    (h1 : c1 ∉ f.nodes.map Leaf.id) (h2 : c2 ∉ f.nodes.map Leaf.id)
    (hne : c1 ≠ c2) :
    (f'.nodes.map Leaf.id).Nodup := by
  induction f generalizing f' c with
  | leaf c0 =>
      simp only [Forest.modifyLeafAt] at h
      by_cases hc : c0.id = id
      · rw [if_pos hc] at h
        have hlist := hlocal c0 f' c h
        rw [hlist]
        have h1' : c1 ≠ c0.id := by simpa [Forest.nodes] using h1
        have h2' : c2 ≠ c0.id := by simpa [Forest.nodes] using h2
        simp [List.nodup_cons, hne, h1', h2', Ne.symm h1', Ne.symm h2']
      · rw [if_neg hc] at h
        cases h
  | split k p lr rr l r ihl ihr =>
      simp only [Forest.nodes, List.map_cons, List.map_append] at hn h1 h2
      rw [List.nodup_cons] at hn
      obtain ⟨hp, hnd⟩ := hn
      rw [List.nodup_append] at hnd
      obtain ⟨hln, hrn, hdisj⟩ := hnd
      have h1l : c1 ∉ l.nodes.map Leaf.id := by
        intro hm
        exact h1 (List.mem_cons_of_mem p.id (List.mem_append.mpr (Or.inl hm)))
      have h2l : c2 ∉ l.nodes.map Leaf.id := by
        intro hm
        exact h2 (List.mem_cons_of_mem p.id (List.mem_append.mpr (Or.inl hm)))
      have h1r : c1 ∉ r.nodes.map Leaf.id := by
        intro hm
        exact h1 (List.mem_cons_of_mem p.id (List.mem_append.mpr (Or.inr hm)))
      have h2r : c2 ∉ r.nodes.map Leaf.id := by
        intro hm
        exact h2 (List.mem_cons_of_mem p.id (List.mem_append.mpr (Or.inr hm)))
      simp only [Forest.modifyLeafAt] at h
      split at h
      · rename_i l' c' hl
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hl' := ihl hl hln h1l h2l
        have hp_l : p.id ∉ l'.nodes.map Leaf.id := by
          intro hm
          rcases modifyLeafAt_nodes_mem hl hlocal hm with hm | hm | hm
          · exact hp (List.mem_append.mpr (Or.inl hm))
          · exact h1 (hm ▸ List.mem_cons_self)
          · exact h2 (hm ▸ List.mem_cons_self)
        have hp_r : p.id ∉ r.nodes.map Leaf.id := by
          intro hm; exact hp (List.mem_append.mpr (Or.inr hm))
        have hdisj' : ∀ x ∈ l'.nodes.map Leaf.id, x ∉ r.nodes.map Leaf.id := by
          intro x hx hy
          rcases modifyLeafAt_nodes_mem hl hlocal hx with hx | hx | hx
          · exact not_mem_of_disjoint hdisj hx hy
          · exact h1r (hx ▸ hy)
          · exact h2r (hx ▸ hy)
        simp only [Forest.nodes, List.map_cons, List.map_append]
        rw [List.nodup_cons, List.nodup_append]
        refine ⟨?_, hl', hrn, disjoint_of_not_mem hdisj'⟩
        intro hm
        rcases List.mem_append.mp hm with hm | hm
        · exact hp_l hm
        · exact hp_r hm
      · rename_i hl
        split at h
        · rename_i r' c' hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hr' := ihr hr hrn h1r h2r
          have hp_r : p.id ∉ r'.nodes.map Leaf.id := by
            intro hm
            rcases modifyLeafAt_nodes_mem hr hlocal hm with hm | hm | hm
            · exact hp (List.mem_append.mpr (Or.inr hm))
            · exact h1 (hm ▸ List.mem_cons_self)
            · exact h2 (hm ▸ List.mem_cons_self)
          have hp_l : p.id ∉ l.nodes.map Leaf.id := by
            intro hm; exact hp (List.mem_append.mpr (Or.inl hm))
          have hdisj' : ∀ x ∈ l.nodes.map Leaf.id, x ∉ r'.nodes.map Leaf.id := by
            intro x hx hy
            rcases modifyLeafAt_nodes_mem hr hlocal hy with hy | hy | hy
            · exact not_mem_of_disjoint hdisj hx hy
            · exact h1 (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl (hy ▸ hx))))
            · exact h2 (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl (hy ▸ hx))))
          simp only [Forest.nodes, List.map_cons, List.map_append]
          rw [List.nodup_cons, List.nodup_append]
          refine ⟨?_, hln, hr', disjoint_of_not_mem hdisj'⟩
          intro hm
          rcases List.mem_append.mp hm with hm | hm
          · exact hp_l hm
          · exact hp_r hm
        · cases h

/-- A split-shaped leaf modification only adds the two fresh child names to the
identity list. -/
theorem modifyLeafAt_ids_mem {f f' : Forest} {id : CapId}
    {g : Leaf → Option (Forest × Leaf)} {c : Leaf} {c1 c2 : CapId}
    (h : f.modifyLeafAt id g = some (f', c))
    (hlocal : ∀ (d : Leaf) (x : Forest) (d' : Leaf),
      g d = some (x, d') → ∀ y ∈ x.ids, y = d.id ∨ y = c1 ∨ y = c2)
    {y : CapId} (hy : y ∈ f'.ids) :
    y ∈ f.ids ∨ y = c1 ∨ y = c2 := by
  induction f generalizing f' c with
  | leaf c0 =>
      simp only [Forest.modifyLeafAt] at h
      by_cases hc : c0.id = id
      · rw [if_pos hc] at h
        rcases hlocal c0 f' c h y hy with hy | hy | hy
        · simp [Forest.ids, hy]
        · exact Or.inr (Or.inl hy)
        · exact Or.inr (Or.inr hy)
      · rw [if_neg hc] at h
        cases h
  | split k p lr rr l r ihl ihr =>
      simp only [Forest.modifyLeafAt] at h
      split at h
      · rename_i l' c' hl
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Forest.ids] at ⊢
        simp only [Forest.ids, List.mem_cons, List.mem_append] at hy
        rcases hy with rfl | rfl | rfl | hy | hy
        · exact Or.inl List.mem_cons_self
        · exact Or.inl (List.mem_cons_of_mem _ List.mem_cons_self)
        · exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
        · rcases ihl hl hy with hy | hy | hy
          · exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl hy)))))
          · exact Or.inr (Or.inl hy)
          · exact Or.inr (Or.inr hy)
        · exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr hy)))))
      · rename_i hl
        split at h
        · rename_i r' c' hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [Forest.ids] at ⊢
          simp only [Forest.ids, List.mem_cons, List.mem_append] at hy
          rcases hy with rfl | rfl | rfl | hy | hy
          · exact Or.inl List.mem_cons_self
          · exact Or.inl (List.mem_cons_of_mem _ List.mem_cons_self)
          · exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
          · exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl hy)))))
          · rcases ihr hr hy with hy | hy | hy
            · exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr hy)))))
            · exact Or.inr (Or.inl hy)
            · exact Or.inr (Or.inr hy)
        · cases h

/-- A split-shaped leaf modification only adds the two fresh child names to the
rule-fragment list. -/
theorem modifyLeafAt_ruleIds_mem {f f' : Forest} {id : CapId}
    {g : Leaf → Option (Forest × Leaf)} {c : Leaf} {c1 c2 : CapId}
    (h : f.modifyLeafAt id g = some (f', c))
    (hlocal : ∀ (d : Leaf) (x : Forest) (d' : Leaf),
      g d = some (x, d') → ∀ y ∈ x.ruleIds, y = c1 ∨ y = c2)
    {y : CapId} (hy : y ∈ f'.ruleIds) :
    y ∈ f.ruleIds ∨ y = c1 ∨ y = c2 := by
  induction f generalizing f' c with
  | leaf c0 =>
      simp only [Forest.modifyLeafAt] at h
      by_cases hc : c0.id = id
      · rw [if_pos hc] at h
        rcases hlocal c0 f' c h y hy with hy | hy
        · exact Or.inr (Or.inl hy)
        · exact Or.inr (Or.inr hy)
      · rw [if_neg hc] at h
        cases h
  | split k p lr rr l r ihl ihr =>
      simp only [Forest.modifyLeafAt] at h
      split at h
      · rename_i l' c' hl
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Forest.ruleIds] at ⊢
        simp only [Forest.ruleIds, List.mem_cons, List.mem_append] at hy
        rcases hy with rfl | rfl | hy | hy
        · exact Or.inl List.mem_cons_self
        · exact Or.inl (List.mem_cons_of_mem _ List.mem_cons_self)
        · rcases ihl hl hy with hy | hy | hy
          · exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_append.mpr (Or.inl hy))))
          · exact Or.inr (Or.inl hy)
          · exact Or.inr (Or.inr hy)
        · exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_append.mpr (Or.inr hy))))
      · rename_i hl
        split at h
        · rename_i r' c' hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [Forest.ruleIds] at ⊢
          simp only [Forest.ruleIds, List.mem_cons, List.mem_append] at hy
          rcases hy with rfl | rfl | hy | hy
          · exact Or.inl List.mem_cons_self
          · exact Or.inl (List.mem_cons_of_mem _ List.mem_cons_self)
          · exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_append.mpr (Or.inl hy))))
          · rcases ihr hr hy with hy | hy | hy
            · exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_append.mpr (Or.inr hy))))
            · exact Or.inr (Or.inl hy)
            · exact Or.inr (Or.inr hy)
        · cases h

/-- A split-shaped leaf modification only retains old authority nodes and the two
fresh children. -/
theorem modifyLeafAt_nodes_leaf_mem {f f' : Forest} {id : CapId}
    {g : Leaf → Option (Forest × Leaf)} {c : Leaf} {c1 c2 : CapId}
    (h : f.modifyLeafAt id g = some (f', c))
    (hlocal : ∀ (d : Leaf) (x : Forest) (d' : Leaf),
      g d = some (x, d') → ∀ c' ∈ x.nodes,
        c' = d ∨ c'.id = c1 ∨ c'.id = c2)
    {c' : Leaf} (hc' : c' ∈ f'.nodes) :
    c' ∈ f.nodes ∨ c'.id = c1 ∨ c'.id = c2 := by
  induction f generalizing f' c with
  | leaf c0 =>
      simp only [Forest.modifyLeafAt] at h
      by_cases hc : c0.id = id
      · rw [if_pos hc] at h
        rcases hlocal c0 f' c h c' hc' with hc' | hc' | hc'
        · simp [Forest.nodes, hc']
        · exact Or.inr (Or.inl hc')
        · exact Or.inr (Or.inr hc')
      · rw [if_neg hc] at h
        cases h
  | split k p lr rr l r ihl ihr =>
      simp only [Forest.nodes] at hc' ⊢
      simp only [Forest.modifyLeafAt] at h
      split at h
      · rename_i l' c' hl
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rcases List.mem_cons.mp hc' with rfl | hc'
        · exact Or.inl (List.mem_cons_self)
        · rcases List.mem_append.mp hc' with hc' | hc'
          · rcases ihl hl hc' with hc' | hc' | hc'
            · exact Or.inl (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl hc')))
            · exact Or.inr (Or.inl hc')
            · exact Or.inr (Or.inr hc')
          · exact Or.inl (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr hc')))
      · rename_i hl
        split at h
        · rename_i r' c' hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rcases List.mem_cons.mp hc' with rfl | hc'
          · exact Or.inl (List.mem_cons_self)
          · rcases List.mem_append.mp hc' with hc' | hc'
            · exact Or.inl (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl hc')))
            · rcases ihr hr hc' with hc' | hc' | hc'
              · exact Or.inl (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr hc')))
              · exact Or.inr (Or.inl hc')
              · exact Or.inr (Or.inr hc')
        · cases h

/-- The checked leaf-level spatial split: explicit child intervals must exactly
partition the parent interval, the ceiling and share are inherited, and the
parent must be an active leaf. -/
def spatialLeafSplit (p : Leaf) (c1 c2 : CapId) (lo1 hi1 lo2 hi2 : Nat) :
    Option (Forest × Leaf) :=
  if hact : p.state = .active then
    if hb : lo1 ≤ hi1 ∧ lo2 ≤ hi2 then
      if hpart : lo1 = p.lo ∧ hi1 = lo2 ∧ hi2 = p.hi then
        if hid : c1 ≠ c2 ∧ c1 ≠ p.id ∧ c2 ≠ p.id then
          let left : Leaf := { p with id := c1, lo := lo1, hi := hi1, ordered := hb.1 }
          let right : Leaf := { p with id := c2, lo := lo2, hi := hi2, ordered := hb.2 }
          some (.split .spatial p left right (.leaf left) (.leaf right), p)
        else none
      else none
    else none
  else none

/-- A checked spatial split preserves the frontier budget. -/
theorem spatialLeafSplit_nodes_ids {p p' : Leaf} {x : Forest} {c1 c2 : CapId}
    {lo1 hi1 lo2 hi2 : Nat}
    (h : spatialLeafSplit p c1 c2 lo1 hi1 lo2 hi2 = some (x, p')) :
    x.nodes.map Leaf.id = p.id :: c1 :: c2 :: [] := by
  unfold spatialLeafSplit at h
  split at h
  · split at h
    · split at h
      · split at h
        · rename_i hid
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp [Forest.nodes]
        · simp at h
      · simp at h
    · simp at h
  · simp at h

/-- The nodes of a checked spatial split are the parent and the two children. -/
theorem spatialLeafSplit_nodes_mem {p p' : Leaf} {x : Forest} {c1 c2 : CapId}
    {lo1 hi1 lo2 hi2 : Nat}
    (h : spatialLeafSplit p c1 c2 lo1 hi1 lo2 hi2 = some (x, p'))
    {c' : Leaf} (hc' : c' ∈ x.nodes) :
    c' = p ∨ c'.id = c1 ∨ c'.id = c2 := by
  unfold spatialLeafSplit at h
  split at h
  · split at h
    · split at h
      · split at h
        · rename_i hid
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [Forest.nodes, List.mem_cons, List.mem_append, List.mem_singleton,
            List.cons_append, List.nil_append, List.mem_nil_iff, or_false] at hc'
          rcases hc' with rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inl (by simp))
          · exact Or.inr (Or.inr (by simp))
        · simp at h
      · simp at h
    · simp at h
  · simp at h

/-- The identity list of a checked spatial split adds only the two children. -/
theorem spatialLeafSplit_ids_mem {p p' : Leaf} {x : Forest} {c1 c2 : CapId}
    {lo1 hi1 lo2 hi2 : Nat}
    (h : spatialLeafSplit p c1 c2 lo1 hi1 lo2 hi2 = some (x, p'))
    {y : CapId} (hy : y ∈ x.ids) :
    y = p.id ∨ y = c1 ∨ y = c2 := by
  unfold spatialLeafSplit at h
  split at h
  · split at h
    · split at h
      · split at h
        · rename_i hid
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [Forest.ids, List.mem_cons, List.mem_append, List.mem_singleton,
            List.cons_append, List.nil_append, List.mem_nil_iff, or_false] at hy
          rcases hy with h' | h' | h' | h' | h'
          · exact Or.inl h'
          · exact Or.inr (Or.inl h')
          · exact Or.inr (Or.inr h')
          · exact Or.inr (Or.inl h')
          · exact Or.inr (Or.inr h')
        · simp at h
      · simp at h
    · simp at h
  · simp at h

/-- The rule fragments of a checked spatial split are the two children. -/
theorem spatialLeafSplit_ruleIds_mem {p p' : Leaf} {x : Forest} {c1 c2 : CapId}
    {lo1 hi1 lo2 hi2 : Nat}
    (h : spatialLeafSplit p c1 c2 lo1 hi1 lo2 hi2 = some (x, p'))
    {y : CapId} (hy : y ∈ x.ruleIds) :
    y = c1 ∨ y = c2 := by
  unfold spatialLeafSplit at h
  split at h
  · split at h
    · split at h
      · split at h
        · rename_i hid
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [Forest.ruleIds, List.mem_cons, List.mem_append, List.mem_singleton,
            List.cons_append, List.nil_append, List.mem_nil_iff, or_false] at hy
          rcases hy with h' | h'
          · exact Or.inl h'
          · exact Or.inr h'
        · simp at h
      · simp at h
    · simp at h
  · simp at h

/-- A checked spatial split preserves the frontier budget. -/
theorem spatialLeafSplit_budget {p p' : Leaf} {x : Forest} {c1 c2 : CapId}
    {lo1 hi1 lo2 hi2 : Nat}
    (h : spatialLeafSplit p c1 c2 lo1 hi1 lo2 hi2 = some (x, p')) :
    ∀ b, x.budget b = (Forest.leaf p).budget b := by
  unfold spatialLeafSplit at h
  split at h
  · rename_i hact
    split at h
    · rename_i hb
      split at h
      · rename_i hpart
        split at h
        · rename_i hid
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          intro b
          exact
            (Forest.spatial_split_budget (p := p)
              (l := { p with id := c1, lo := lo1, hi := hi1, ordered := hb.1 })
              (r := { p with id := c2, lo := lo2, hi := hi2, ordered := hb.2 })
              (x := b) rfl rfl
              (by simp [hpart.1]) (by simp [hpart.2.1]) (by simp [hpart.2.2])
              rfl rfl (by change p.lo ≤ lo2; omega) (by change lo2 ≤ p.hi; omega))
        · simp at h
      · simp at h
    · simp at h
  · simp at h

/-- A checked spatial split records a valid rule. -/
theorem spatialLeafSplit_valid {p p' : Leaf} {x : Forest} {c1 c2 : CapId}
    {lo1 hi1 lo2 hi2 : Nat}
    (h : spatialLeafSplit p c1 c2 lo1 hi1 lo2 hi2 = some (x, p')) :
    x.Valid := by
  unfold spatialLeafSplit at h
  split at h
  · rename_i hact
    split at h
    · rename_i hb
      split at h
      · rename_i hpart
        split at h
        · rename_i hid
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨?_, trivial, trivial⟩
          unfold RuleValid
          refine ⟨hact, rfl, rfl, rfl, rfl, ?_, ?_, hid.1, hid.2.1, hid.2.2, ?_⟩
          · simp [hact]
          · simp [hact]
          · exact ⟨hpart.1, hpart.2.1, hpart.2.2, rfl, rfl⟩
        · simp at h
      · simp at h
    · simp at h
  · simp at h

/-- Checked spatial subdivision of the current leaf `id`. -/
def splitSpatialAt (id c1 c2 : CapId) (lo1 hi1 lo2 hi2 : Nat) :
    Forest → Option (Forest × Leaf) :=
  Forest.modifyLeafAt id (fun p => spatialLeafSplit p c1 c2 lo1 hi1 lo2 hi2)

/-- A checked spatial subdivision preserves the frontier budget. -/
theorem splitSpatialAt_budget {f f' : Forest} {p : Leaf} {id c1 c2 : CapId}
    {lo1 hi1 lo2 hi2 : Nat}
    (h : f.splitSpatialAt id c1 c2 lo1 hi1 lo2 hi2 = some (f', p)) :
    ∀ b, f'.budget b = f.budget b := by
  apply budget_modifyLeafAt h
  intro d x d' hg b
  exact spatialLeafSplit_budget hg b

/-- A checked spatial subdivision preserves validity. -/
theorem splitSpatialAt_valid {f f' : Forest} {p : Leaf} {id c1 c2 : CapId}
    {lo1 hi1 lo2 hi2 : Nat}
    (h : f.splitSpatialAt id c1 c2 lo1 hi1 lo2 hi2 = some (f', p))
    (hv : f.Valid) : f'.Valid := by
  apply valid_modifyLeafAt h hv
  intro d x d' hg
  exact spatialLeafSplit_valid hg

/-- A spatial subdivision preserves distinct authority identities when both child
names are fresh. -/
theorem splitSpatialAt_nodes_nodup {f f' : Forest} {p : Leaf} {id c1 c2 : CapId}
    {lo1 hi1 lo2 hi2 : Nat}
    (h : f.splitSpatialAt id c1 c2 lo1 hi1 lo2 hi2 = some (f', p))
    (hn : (f.nodes.map Leaf.id).Nodup)
    (h1 : c1 ∉ f.nodes.map Leaf.id) (h2 : c2 ∉ f.nodes.map Leaf.id)
    (hne : c1 ≠ c2) :
    (f'.nodes.map Leaf.id).Nodup := by
  unfold Forest.splitSpatialAt at h
  exact modifyLeafAt_nodes_nodup h hn
    (fun d x d' hg => spatialLeafSplit_nodes_ids hg) h1 h2 hne

/-- A spatial subdivision keeps every old authority node. -/
theorem splitSpatialAt_nodes_old {f f' : Forest} {p : Leaf} {id c1 c2 : CapId}
    {lo1 hi1 lo2 hi2 : Nat}
    (h : f.splitSpatialAt id c1 c2 lo1 hi1 lo2 hi2 = some (f', p))
    {y : CapId} (hy : y ∈ f.nodes.map Leaf.id) :
    y ∈ f'.nodes.map Leaf.id := by
  unfold Forest.splitSpatialAt at h
  exact modifyLeafAt_nodes_old h
    (fun d x d' hg => spatialLeafSplit_nodes_ids hg) hy

/-- A spatial subdivision retains old nodes and adds only the two fresh children. -/
theorem splitSpatialAt_nodes_leaf_mem {f f' : Forest} {p : Leaf} {id c1 c2 : CapId}
    {lo1 hi1 lo2 hi2 : Nat}
    (h : f.splitSpatialAt id c1 c2 lo1 hi1 lo2 hi2 = some (f', p))
    {c' : Leaf} (hc' : c' ∈ f'.nodes) :
    c' ∈ f.nodes ∨ c'.id = c1 ∨ c'.id = c2 := by
  unfold Forest.splitSpatialAt at h
  exact modifyLeafAt_nodes_leaf_mem h
    (fun d x d' hg c' hc' => spatialLeafSplit_nodes_mem hg hc') hc'

/-- A spatial subdivision adds only the two fresh child names to the identity
list. -/
theorem splitSpatialAt_ids_mem {f f' : Forest} {p : Leaf} {id c1 c2 : CapId}
    {lo1 hi1 lo2 hi2 : Nat}
    (h : f.splitSpatialAt id c1 c2 lo1 hi1 lo2 hi2 = some (f', p))
    {y : CapId} (hy : y ∈ f'.ids) :
    y ∈ f.ids ∨ y = c1 ∨ y = c2 := by
  unfold Forest.splitSpatialAt at h
  exact modifyLeafAt_ids_mem h
    (fun d x d' hg y hy => spatialLeafSplit_ids_mem hg hy) hy

/-- A spatial subdivision adds only the two fresh child names to the rule list. -/
theorem splitSpatialAt_ruleIds_mem {f f' : Forest} {p : Leaf} {id c1 c2 : CapId}
    {lo1 hi1 lo2 hi2 : Nat}
    (h : f.splitSpatialAt id c1 c2 lo1 hi1 lo2 hi2 = some (f', p))
    {y : CapId} (hy : y ∈ f'.ruleIds) :
    y ∈ f.ruleIds ∨ y = c1 ∨ y = c2 := by
  unfold Forest.splitSpatialAt at h
  exact modifyLeafAt_ruleIds_mem h
    (fun d x d' hg y hy => spatialLeafSplit_ruleIds_mem hg hy) hy

/-- The checked leaf-level fractional split: the children keep the parent
footprint, both shares are positive, and they sum to the parent's share. -/
def fractionalLeafSplit (p : Leaf) (c1 c2 : CapId) (q1 q2 : Nat) :
    Option (Forest × Leaf) :=
  if hact : p.state = .active then
    if hpos : 0 < q1 ∧ 0 < q2 then
      if hsum : q1 + q2 = p.q then
        if hid : c1 ≠ c2 ∧ c1 ≠ p.id ∧ c2 ≠ p.id then
          let left : Leaf := { p with id := c1, q := q1, pos := hpos.1 }
          let right : Leaf := { p with id := c2, q := q2, pos := hpos.2 }
          some (.split .fractional p left right (.leaf left) (.leaf right), p)
        else none
      else none
    else none
  else none

/-- The nodes of a checked fractional split are the parent and the two children. -/
theorem fractionalLeafSplit_nodes_ids {p p' : Leaf} {x : Forest} {c1 c2 : CapId}
    {q1 q2 : Nat}
    (h : fractionalLeafSplit p c1 c2 q1 q2 = some (x, p')) :
    x.nodes.map Leaf.id = p.id :: c1 :: c2 :: [] := by
  unfold fractionalLeafSplit at h
  split at h
  · split at h
    · split at h
      · split at h
        · rename_i hid
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp [Forest.nodes]
        · simp at h
      · simp at h
    · simp at h
  · simp at h

/-- The nodes of a checked fractional split are the parent and the two children. -/
theorem fractionalLeafSplit_nodes_mem {p p' : Leaf} {x : Forest} {c1 c2 : CapId}
    {q1 q2 : Nat}
    (h : fractionalLeafSplit p c1 c2 q1 q2 = some (x, p'))
    {c' : Leaf} (hc' : c' ∈ x.nodes) :
    c' = p ∨ c'.id = c1 ∨ c'.id = c2 := by
  unfold fractionalLeafSplit at h
  split at h
  · split at h
    · split at h
      · split at h
        · rename_i hid
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [Forest.nodes, List.mem_cons, List.mem_append, List.mem_singleton,
            List.cons_append, List.nil_append, List.mem_nil_iff, or_false] at hc'
          rcases hc' with rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inl (by simp))
          · exact Or.inr (Or.inr (by simp))
        · simp at h
      · simp at h
    · simp at h
  · simp at h

/-- The identity list of a checked fractional split adds only the two children. -/
theorem fractionalLeafSplit_ids_mem {p p' : Leaf} {x : Forest} {c1 c2 : CapId}
    {q1 q2 : Nat}
    (h : fractionalLeafSplit p c1 c2 q1 q2 = some (x, p'))
    {y : CapId} (hy : y ∈ x.ids) :
    y = p.id ∨ y = c1 ∨ y = c2 := by
  unfold fractionalLeafSplit at h
  split at h
  · split at h
    · split at h
      · split at h
        · rename_i hid
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [Forest.ids, List.mem_cons, List.mem_append, List.mem_singleton,
            List.cons_append, List.nil_append, List.mem_nil_iff, or_false] at hy
          rcases hy with h' | h' | h' | h' | h'
          · exact Or.inl h'
          · exact Or.inr (Or.inl h')
          · exact Or.inr (Or.inr h')
          · exact Or.inr (Or.inl h')
          · exact Or.inr (Or.inr h')
        · simp at h
      · simp at h
    · simp at h
  · simp at h

/-- The rule fragments of a checked fractional split are the two children. -/
theorem fractionalLeafSplit_ruleIds_mem {p p' : Leaf} {x : Forest} {c1 c2 : CapId}
    {q1 q2 : Nat}
    (h : fractionalLeafSplit p c1 c2 q1 q2 = some (x, p'))
    {y : CapId} (hy : y ∈ x.ruleIds) :
    y = c1 ∨ y = c2 := by
  unfold fractionalLeafSplit at h
  split at h
  · split at h
    · split at h
      · split at h
        · rename_i hid
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [Forest.ruleIds, List.mem_cons, List.mem_append, List.mem_singleton,
            List.cons_append, List.nil_append, List.mem_nil_iff, or_false] at hy
          rcases hy with h' | h'
          · exact Or.inl h'
          · exact Or.inr h'
        · simp at h
      · simp at h
    · simp at h
  · simp at h

/-- A checked fractional split preserves the frontier budget. -/
theorem fractionalLeafSplit_budget {p p' : Leaf} {x : Forest} {c1 c2 : CapId}
    {q1 q2 : Nat}
    (h : fractionalLeafSplit p c1 c2 q1 q2 = some (x, p')) :
    ∀ b, x.budget b = (Forest.leaf p).budget b := by
  unfold fractionalLeafSplit at h
  split at h
  · rename_i hact
    split at h
    · rename_i hpos
      split at h
      · rename_i hsum
        split at h
        · rename_i hid
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          intro b
          simpa [hid] using
            (Forest.fractional_split_budget (p := p)
              (l := { p with id := c1, q := q1, pos := hpos.1 })
              (r := { p with id := c2, q := q2, pos := hpos.2 })
              (x := b) rfl rfl
              rfl rfl rfl rfl hsum)
        · simp at h
      · simp at h
    · simp at h
  · simp at h

/-- A checked fractional split records a valid rule. -/
theorem fractionalLeafSplit_valid {p p' : Leaf} {x : Forest} {c1 c2 : CapId}
    {q1 q2 : Nat}
    (h : fractionalLeafSplit p c1 c2 q1 q2 = some (x, p')) :
    x.Valid := by
  unfold fractionalLeafSplit at h
  split at h
  · rename_i hact
    split at h
    · rename_i hpos
      split at h
      · rename_i hsum
        split at h
        · rename_i hid
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨?_, trivial, trivial⟩
          unfold RuleValid
          refine ⟨hact, rfl, rfl, rfl, rfl, ?_, ?_, hid.1, hid.2.1, hid.2.2, ?_⟩
          · simp [hact]
          · simp [hact]
          · exact ⟨rfl, rfl, rfl, rfl, hpos.1, hpos.2, hsum⟩
        · simp at h
      · simp at h
    · simp at h
  · simp at h

/-- Checked fractional subdivision of the current leaf `id`. -/
def splitFractionAt (id c1 c2 : CapId) (q1 q2 : Nat) :
    Forest → Option (Forest × Leaf) :=
  Forest.modifyLeafAt id (fun p => fractionalLeafSplit p c1 c2 q1 q2)

/-- A checked fractional subdivision preserves the frontier budget. -/
theorem splitFractionAt_budget {f f' : Forest} {p : Leaf} {id c1 c2 : CapId}
    {q1 q2 : Nat}
    (h : f.splitFractionAt id c1 c2 q1 q2 = some (f', p)) :
    ∀ b, f'.budget b = f.budget b := by
  apply budget_modifyLeafAt h
  intro d x d' hg b
  exact fractionalLeafSplit_budget hg b

/-- A checked fractional subdivision preserves validity. -/
theorem splitFractionAt_valid {f f' : Forest} {p : Leaf} {id c1 c2 : CapId}
    {q1 q2 : Nat}
    (h : f.splitFractionAt id c1 c2 q1 q2 = some (f', p))
    (hv : f.Valid) : f'.Valid := by
  apply valid_modifyLeafAt h hv
  intro d x d' hg
  exact fractionalLeafSplit_valid hg

/-- A fractional subdivision preserves distinct authority identities when both
child names are fresh. -/
theorem splitFractionAt_nodes_nodup {f f' : Forest} {p : Leaf} {id c1 c2 : CapId}
    {q1 q2 : Nat}
    (h : f.splitFractionAt id c1 c2 q1 q2 = some (f', p))
    (hn : (f.nodes.map Leaf.id).Nodup)
    (h1 : c1 ∉ f.nodes.map Leaf.id) (h2 : c2 ∉ f.nodes.map Leaf.id)
    (hne : c1 ≠ c2) :
    (f'.nodes.map Leaf.id).Nodup := by
  unfold Forest.splitFractionAt at h
  exact modifyLeafAt_nodes_nodup h hn
    (fun d x d' hg => fractionalLeafSplit_nodes_ids hg) h1 h2 hne

/-- A fractional subdivision keeps every old authority node. -/
theorem splitFractionAt_nodes_old {f f' : Forest} {p : Leaf} {id c1 c2 : CapId}
    {q1 q2 : Nat}
    (h : f.splitFractionAt id c1 c2 q1 q2 = some (f', p))
    {y : CapId} (hy : y ∈ f.nodes.map Leaf.id) :
    y ∈ f'.nodes.map Leaf.id := by
  unfold Forest.splitFractionAt at h
  exact modifyLeafAt_nodes_old h
    (fun d x d' hg => fractionalLeafSplit_nodes_ids hg) hy

/-- A fractional subdivision retains old nodes and adds only the two fresh
children. -/
theorem splitFractionAt_nodes_leaf_mem {f f' : Forest} {p : Leaf} {id c1 c2 : CapId}
    {q1 q2 : Nat}
    (h : f.splitFractionAt id c1 c2 q1 q2 = some (f', p))
    {c' : Leaf} (hc' : c' ∈ f'.nodes) :
    c' ∈ f.nodes ∨ c'.id = c1 ∨ c'.id = c2 := by
  unfold Forest.splitFractionAt at h
  exact modifyLeafAt_nodes_leaf_mem h
    (fun d x d' hg c' hc' => fractionalLeafSplit_nodes_mem hg hc') hc'

/-- A fractional subdivision adds only the two fresh child names to the identity
list. -/
theorem splitFractionAt_ids_mem {f f' : Forest} {p : Leaf} {id c1 c2 : CapId}
    {q1 q2 : Nat}
    (h : f.splitFractionAt id c1 c2 q1 q2 = some (f', p))
    {y : CapId} (hy : y ∈ f'.ids) :
    y ∈ f.ids ∨ y = c1 ∨ y = c2 := by
  unfold Forest.splitFractionAt at h
  exact modifyLeafAt_ids_mem h
    (fun d x d' hg y hy => fractionalLeafSplit_ids_mem hg hy) hy

/-- A fractional subdivision adds only the two fresh child names to the rule
list. -/
theorem splitFractionAt_ruleIds_mem {f f' : Forest} {p : Leaf} {id c1 c2 : CapId}
    {q1 q2 : Nat}
    (h : f.splitFractionAt id c1 c2 q1 q2 = some (f', p))
    {y : CapId} (hy : y ∈ f'.ruleIds) :
    y ∈ f.ruleIds ∨ y = c1 ∨ y = c2 := by
  unfold Forest.splitFractionAt at h
  exact modifyLeafAt_ruleIds_mem h
    (fun d x d' hg y hy => fractionalLeafSplit_ruleIds_mem hg hy) hy

/-- Reconstruct one suspension when both current children are the rule fragments.
Returns the restored forest and the two child fragments that are retired. -/
def reconstructHere (kind : RuleKind) (parent leftRule rightRule : Leaf)
    (left right : Forest) : Option (Forest × Leaf × Leaf) :=
  if hrule : RuleValid kind parent leftRule rightRule then
    match left, right with
    | .leaf lf, .leaf rf =>
        if hag : lf.Agrees leftRule ∧ rf.Agrees rightRule then
          some (.leaf parent, lf, rf)
        else none
    | _, _ => none
  else none

/-- Reconstructing one checked suspension preserves the frontier budget. -/
theorem reconstructHere_budget {kind : RuleKind} {parent leftRule rightRule : Leaf}
    {left right : Forest} {f' : Forest} {a b : Leaf}
    (h : reconstructHere kind parent leftRule rightRule left right = some (f', a, b)) :
    ∀ x, f'.budget x = (Forest.split kind parent leftRule rightRule left right).budget x := by
  unfold reconstructHere at h
  by_cases hrule : RuleValid kind parent leftRule rightRule
  · rw [dif_pos hrule] at h
    cases left with
    | leaf lf =>
      cases right with
      | leaf rf =>
        dsimp only at h
        by_cases hag : lf.Agrees leftRule ∧ rf.Agrees rightRule
        · rw [dif_pos hag] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          intro x
          have hbl : lf.budget x = leftRule.budget x := Leaf.budget_congr hag.1 x
          have hbr : rf.budget x = rightRule.budget x := Leaf.budget_congr hag.2 x
          cases kind with
          | spatial =>
              obtain ⟨hact, -, -, -, -, hlrstate, hrrstate, -, -, -, hpart⟩ := hrule
              obtain ⟨hlo, hhi, hrhi, hql, hqr⟩ := hpart
              have hjoin := Forest.spatial_join_budget (p := parent)
                (l := leftRule) (r := rightRule) (x := x)
                (by rw [hlrstate, hact]) (by rw [hrrstate, hact])
                hlo hhi hrhi hql hqr
                (by rw [← hlo, ← hhi]; exact leftRule.ordered)
                (by rw [← hrhi]; exact rightRule.ordered)
              simp only [Forest.budget] at hjoin ⊢
              rw [hbl, hbr]
              exact hjoin
          | fractional =>
              obtain ⟨hact, -, -, -, -, hlrstate, hrrstate, -, -, -, hpart⟩ := hrule
              obtain ⟨hlo1, hhi1, hlo2, hhi2, hq1, hq2, hsum⟩ := hpart
              have hjoin := Forest.fractional_join_budget (p := parent)
                (l := leftRule) (r := rightRule) (x := x)
                (by rw [hlrstate, hact]) (by rw [hrrstate, hact])
                hlo1 hhi1 hlo2 hhi2 hsum
              simp only [Forest.budget] at hjoin ⊢
              rw [hbl, hbr]
              exact hjoin
        · rw [dif_neg hag] at h
          cases h
      | split _ _ _ _ _ _ => cases h
    | split _ _ _ _ _ _ => cases h
  · rw [dif_neg hrule] at h
    cases h

/-- Reconstructing one checked suspension preserves validity. -/
theorem reconstructHere_valid {kind : RuleKind} {parent leftRule rightRule : Leaf}
    {left right : Forest} {f' : Forest} {a b : Leaf}
    (h : reconstructHere kind parent leftRule rightRule left right = some (f', a, b)) :
    f'.Valid := by
  unfold reconstructHere at h
  by_cases hrule : RuleValid kind parent leftRule rightRule
  · rw [dif_pos hrule] at h
    cases left with
    | leaf lf =>
      cases right with
      | leaf rf =>
        dsimp only at h
        by_cases hag : lf.Agrees leftRule ∧ rf.Agrees rightRule
        · rw [dif_pos hag] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _, _⟩ := h
          trivial
        · rw [dif_neg hag] at h
          cases h
      | split _ _ _ _ _ _ => cases h
    | split _ _ _ _ _ _ => cases h
  · rw [dif_neg hrule] at h
    cases h

/-- Reconstruct the suspension whose parent has the given name. Descendant
suspensions must already have been reconstructed. -/
def reconstructAt (id : CapId) : Forest → Option (Forest × Leaf × Leaf)
  | .leaf _ => none
  | .split k p lr rr l r =>
      if p.id = id then
        reconstructHere k p lr rr l r
      else
        match reconstructAt id l with
        | some (l', a, b) => some (.split k p lr rr l' r, a, b)
        | none =>
            match reconstructAt id r with
            | some (r', a, b) => some (.split k p lr rr l r', a, b)
            | none => none

/-- Reconstruction preserves the frontier budget. -/
theorem reconstructAt_budget {f f' : Forest} {id : CapId} {a b : Leaf}
    (h : f.reconstructAt id = some (f', a, b)) :
    ∀ x, f'.budget x = f.budget x := by
  induction f generalizing f' a b with
  | leaf c => simp [Forest.reconstructAt] at h
  | split k p lr rr l r ihl ihr =>
      simp only [Forest.reconstructAt] at h
      split at h
      · rename_i hp
        intro x
        exact Forest.reconstructHere_budget h x
      · rename_i hp
        split at h
        · rename_i l' a' b' hl
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          intro x
          simp only [Forest.budget]
          rw [ihl hl x]
        · rename_i hl
          split at h
          · rename_i r' a' b' hr
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            intro x
            simp only [Forest.budget]
            rw [ihr hr x]
          · simp at h

/-- Reconstruction preserves validity. -/
theorem reconstructAt_valid {f f' : Forest} {id : CapId} {a b : Leaf}
    (h : f.reconstructAt id = some (f', a, b)) (hv : f.Valid) : f'.Valid := by
  induction f generalizing f' a b with
  | leaf c => simp [Forest.reconstructAt] at h
  | split k p lr rr l r ihl ihr =>
      simp only [Forest.Valid] at hv
      obtain ⟨hrule, hvl, hvr⟩ := hv
      simp only [Forest.reconstructAt] at h
      split at h
      · rename_i hp
        exact Forest.reconstructHere_valid h
      · rename_i hp
        split at h
        · rename_i l' a' b' hl
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨hrule, ihl hl hvl, hvr⟩
        · rename_i hl
          split at h
          · rename_i r' a' b' hr
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact ⟨hrule, hvl, ihr hr hvr⟩
          · simp at h

/-- A successful reconstruction restores exactly the suspended parent. -/
theorem reconstructHere_nodes {kind : RuleKind} {parent leftRule rightRule : Leaf}
    {left right : Forest} {f' : Forest} {a b : Leaf}
    (h : reconstructHere kind parent leftRule rightRule left right = some (f', a, b)) :
    f' = .leaf parent := by
  unfold reconstructHere at h
  by_cases hrule : RuleValid kind parent leftRule rightRule
  · rw [dif_pos hrule] at h
    cases left with
    | leaf lf =>
      cases right with
      | leaf rf =>
        dsimp only at h
        by_cases hag : lf.Agrees leftRule ∧ rf.Agrees rightRule
        · rw [dif_pos hag] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _, _⟩ := h
          rfl
        · rw [dif_neg hag] at h
          cases h
      | split _ _ _ _ _ _ => cases h
    | split _ _ _ _ _ _ => cases h
  · rw [dif_neg hrule] at h
    cases h

/-- A successful reconstruction retires exactly the two rule fragments. -/
theorem reconstructHere_child_ids {kind : RuleKind} {parent leftRule rightRule : Leaf}
    {left right : Forest} {f' : Forest} {a b : Leaf}
    (h : reconstructHere kind parent leftRule rightRule left right = some (f', a, b)) :
    a.id = leftRule.id ∧ b.id = rightRule.id := by
  unfold reconstructHere at h
  by_cases hrule : RuleValid kind parent leftRule rightRule
  · rw [dif_pos hrule] at h
    cases left with
    | leaf lf =>
      cases right with
      | leaf rf =>
        dsimp only at h
        by_cases hag : lf.Agrees leftRule ∧ rf.Agrees rightRule
        · rw [dif_pos hag] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl, rfl⟩ := h
          exact ⟨hag.1.1, hag.2.1⟩
        · rw [dif_neg hag] at h
          cases h
      | split _ _ _ _ _ _ => cases h
    | split _ _ _ _ _ _ => cases h
  · rw [dif_neg hrule] at h
    cases h

/-- Each reconstructed-away fragment was an authority node of the old forest. -/
theorem reconstructHere_removed_mem_nodes {kind : RuleKind} {parent leftRule rightRule : Leaf}
    {left right : Forest} {f' : Forest} {a b : Leaf}
    (h : reconstructHere kind parent leftRule rightRule left right = some (f', a, b)) :
    a ∈ (Forest.split kind parent leftRule rightRule left right).nodes ∧
      b ∈ (Forest.split kind parent leftRule rightRule left right).nodes := by
  unfold reconstructHere at h
  by_cases hrule : RuleValid kind parent leftRule rightRule
  · rw [dif_pos hrule] at h
    cases left with
    | leaf lf =>
      cases right with
      | leaf rf =>
        dsimp only at h
        by_cases hag : lf.Agrees leftRule ∧ rf.Agrees rightRule
        · rw [dif_pos hag] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl, rfl⟩ := h
          constructor <;> simp [Forest.nodes]
        · rw [dif_neg hag] at h
          cases h
      | split _ _ _ _ _ _ => cases h
    | split _ _ _ _ _ _ => cases h
  · rw [dif_neg hrule] at h
    cases h

/-- Each reconstructed-away fragment was an authority node of the old forest. -/
theorem reconstructAt_removed_mem_nodes {f f' : Forest} {id : CapId} {a b : Leaf}
    (h : f.reconstructAt id = some (f', a, b)) :
    a ∈ f.nodes ∧ b ∈ f.nodes := by
  induction f generalizing f' a b with
  | leaf c => simp [Forest.reconstructAt] at h
  | split k p lr rr l r ihl ihr =>
      simp only [Forest.reconstructAt] at h
      split at h
      · rename_i hp
        exact reconstructHere_removed_mem_nodes h
      · rename_i hp
        split at h
        · rename_i l' a' b' hl
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          obtain ⟨ha, hb⟩ := ihl hl
          constructor
          · simp only [Forest.nodes]
            exact List.mem_cons_of_mem p (List.mem_append.mpr (Or.inl ha))
          · simp only [Forest.nodes]
            exact List.mem_cons_of_mem p (List.mem_append.mpr (Or.inl hb))
        · rename_i hl
          split at h
          · rename_i r' a' b' hr
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            obtain ⟨ha, hb⟩ := ihr hr
            constructor
            · simp only [Forest.nodes]
              exact List.mem_cons_of_mem p (List.mem_append.mpr (Or.inr ha))
            · simp only [Forest.nodes]
              exact List.mem_cons_of_mem p (List.mem_append.mpr (Or.inr hb))
          · simp at h

/-- Reconstruction only removes authority nodes; it never introduces one. -/
theorem reconstructAt_nodes_sub {f f' : Forest} {id : CapId} {a b : Leaf}
    (h : f.reconstructAt id = some (f', a, b)) {c : Leaf} (hc : c ∈ f'.nodes) :
    c ∈ f.nodes := by
  induction f generalizing f' a b with
  | leaf c0 => simp [Forest.reconstructAt] at h
  | split k p lr rr l r ihl ihr =>
      simp only [Forest.reconstructAt] at h
      split at h
      · rename_i hp
        have hf' : f' = .leaf p := reconstructHere_nodes h
        subst hf'
        simp only [Forest.nodes, List.mem_singleton] at hc
        subst hc
        simp [Forest.nodes]
      · rename_i hp
        split at h
        · rename_i l' a' b' hl
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          simp only [Forest.nodes] at hc ⊢
          rcases List.mem_cons.mp hc with rfl | hc
          · exact List.mem_cons_self
          · rcases List.mem_append.mp hc with hc | hc
            · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl (ihl hl hc)))
            · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr hc))
        · rename_i hl
          split at h
          · rename_i r' a' b' hr
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            simp only [Forest.nodes] at hc ⊢
            rcases List.mem_cons.mp hc with rfl | hc
            · exact List.mem_cons_self
            · rcases List.mem_append.mp hc with hc | hc
              · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl hc))
              · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr (ihr hr hc)))
          · simp at h

/-- Reconstruction preserves distinct authority identities. -/
theorem reconstructAt_nodes_nodup {f f' : Forest} {id : CapId} {a b : Leaf}
    (h : f.reconstructAt id = some (f', a, b))
    (hn : (f.nodes.map Leaf.id).Nodup) :
    (f'.nodes.map Leaf.id).Nodup := by
  induction f generalizing f' a b with
  | leaf c => simp [Forest.reconstructAt] at h
  | split k p lr rr l r ihl ihr =>
      simp only [Forest.nodes, List.map_cons, List.map_append] at hn
      rw [List.nodup_cons] at hn
      obtain ⟨hp, hnd⟩ := hn
      rw [List.nodup_append] at hnd
      obtain ⟨hln, hrn, hdisj⟩ := hnd
      simp only [Forest.reconstructAt] at h
      split at h
      · rename_i hp'
        have hf' : f' = .leaf p := reconstructHere_nodes h
        subst hf'
        simp [Forest.nodes]
      · rename_i hp'
        split at h
        · rename_i l' a' b' hl
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          have hl' := ihl hl hln
          have hp_l : p.id ∉ l'.nodes.map Leaf.id := by
            intro hm
            obtain ⟨c, hc, hcid⟩ := List.mem_map.mp hm
            exact hp (List.mem_append.mpr (Or.inl
              (List.mem_map.mpr ⟨c, reconstructAt_nodes_sub hl hc, hcid⟩)))
          have hp_r : p.id ∉ r.nodes.map Leaf.id := by
            intro hm; exact hp (List.mem_append.mpr (Or.inr hm))
          have hdisj' : ∀ x ∈ l'.nodes.map Leaf.id, x ∉ r.nodes.map Leaf.id := by
            intro x hx hy
            obtain ⟨c, hc, hcid⟩ := List.mem_map.mp hx
            have hcold : c ∈ l.nodes := reconstructAt_nodes_sub hl hc
            exact not_mem_of_disjoint hdisj (List.mem_map.mpr ⟨c, hcold, hcid⟩) hy
          simp only [Forest.nodes, List.map_cons, List.map_append]
          rw [List.nodup_cons, List.nodup_append]
          refine ⟨?_, hl', hrn, disjoint_of_not_mem hdisj'⟩
          intro hm
          rcases List.mem_append.mp hm with hm | hm
          · exact hp_l hm
          · exact hp_r hm
        · rename_i hl
          split at h
          · rename_i r' a' b' hr
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            have hr' := ihr hr hrn
            have hp_r : p.id ∉ r'.nodes.map Leaf.id := by
              intro hm
              obtain ⟨c, hc, hcid⟩ := List.mem_map.mp hm
              exact hp (List.mem_append.mpr (Or.inr
                (List.mem_map.mpr ⟨c, reconstructAt_nodes_sub hr hc, hcid⟩)))
            have hp_l : p.id ∉ l.nodes.map Leaf.id := by
              intro hm; exact hp (List.mem_append.mpr (Or.inl hm))
            have hdisj' : ∀ x ∈ l.nodes.map Leaf.id, x ∉ r'.nodes.map Leaf.id := by
              intro x hx hy
              obtain ⟨c, hc, hcid⟩ := List.mem_map.mp hy
              have hcold : c ∈ r.nodes := reconstructAt_nodes_sub hr hc
              exact not_mem_of_disjoint hdisj hx (List.mem_map.mpr ⟨c, hcold, hcid⟩)
            simp only [Forest.nodes, List.map_cons, List.map_append]
            rw [List.nodup_cons, List.nodup_append]
            refine ⟨?_, hln, hr', disjoint_of_not_mem hdisj'⟩
            intro hm
            rcases List.mem_append.mp hm with hm | hm
            · exact hp_l hm
            · exact hp_r hm
          · simp at h

/-- A successful reconstruction carries its checked rule. -/
theorem reconstructHere_ruleValid {kind : RuleKind} {parent leftRule rightRule : Leaf}
    {left right : Forest} {f' : Forest} {a b : Leaf}
    (h : reconstructHere kind parent leftRule rightRule left right = some (f', a, b)) :
    RuleValid kind parent leftRule rightRule := by
  unfold reconstructHere at h
  by_cases hrule : RuleValid kind parent leftRule rightRule
  · exact hrule
  · rw [dif_neg hrule] at h
    cases h

/-- The only old authority nodes a successful reconstruction removes are the two
reconstructed-away fragments. -/
theorem reconstructHere_nodes_removed {kind : RuleKind} {parent leftRule rightRule : Leaf}
    {left right : Forest} {f' : Forest} {a b : Leaf}
    (h : reconstructHere kind parent leftRule rightRule left right = some (f', a, b))
    {c : Leaf} (hc : c ∈ (Forest.split kind parent leftRule rightRule left right).nodes)
    (hnc : c ∉ f'.nodes) : c = a ∨ c = b := by
  unfold reconstructHere at h
  by_cases hrule : RuleValid kind parent leftRule rightRule
  · rw [dif_pos hrule] at h
    cases left with
    | leaf lf =>
      cases right with
      | leaf rf =>
        dsimp only at h
        by_cases hag : lf.Agrees leftRule ∧ rf.Agrees rightRule
        · rw [dif_pos hag] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          simp only [Forest.nodes, List.mem_cons, List.mem_append, List.mem_singleton,
            List.mem_nil_iff, or_false] at hc hnc
          rcases hc with rfl | rfl | rfl
          · exact absurd rfl hnc
          · exact Or.inl rfl
          · exact Or.inr rfl
        · rw [dif_neg hag] at h
          cases h
      | split _ _ _ _ _ _ => cases h
    | split _ _ _ _ _ _ => cases h
  · rw [dif_neg hrule] at h
    cases h

/-- A removed authority node was a rule fragment of the reconstructed
suspension. -/
theorem reconstructAt_nodes_removed_rule {f f' : Forest} {id : CapId} {a b : Leaf}
    (h : f.reconstructAt id = some (f', a, b)) {c : Leaf}
    (hc : c ∈ f.nodes) (hnc : c ∉ f'.nodes) :
    c.id ∈ f.ruleIds := by
  induction f generalizing f' a b with
  | leaf c0 => simp [Forest.reconstructAt] at h
  | split k p lr rr l r ihl ihr =>
      simp only [Forest.reconstructAt] at h
      split at h
      · rename_i hp
        have hf' : f' = .leaf p := reconstructHere_nodes h
        obtain ⟨ha, hb⟩ := reconstructHere_child_ids h
        subst hf'
        rcases reconstructHere_nodes_removed h hc hnc with rfl | rfl
        · simp only [Forest.ruleIds, List.mem_cons]
          exact Or.inl ha
        · simp only [Forest.ruleIds, List.mem_cons]
          exact Or.inr (Or.inl hb)
      · rename_i hp
        split at h
        · rename_i l' a' b' hl
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          simp only [Forest.nodes] at hc
          simp only [Forest.nodes] at hnc
          rcases List.mem_cons.mp hc with rfl | hc
          · exact absurd List.mem_cons_self hnc
          · rcases List.mem_append.mp hc with hc | hc
            · have hnc_l : c ∉ l'.nodes := by
                intro hm
                exact hnc (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl hm)))
              have hmem := ihl hl hc hnc_l
              simp only [Forest.ruleIds]
              exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_append.mpr (Or.inl hmem)))
            · exact absurd (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr hc))) hnc
        · rename_i hl
          split at h
          · rename_i r' a' b' hr
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            simp only [Forest.nodes] at hc
            simp only [Forest.nodes] at hnc
            rcases List.mem_cons.mp hc with rfl | hc
            · exact absurd List.mem_cons_self hnc
            · rcases List.mem_append.mp hc with hc | hc
              · exact absurd (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl hc))) hnc
              · have hnc_r : c ∉ r'.nodes := by
                  intro hm
                  exact hnc (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr hm)))
                have hmem := ihr hr hc hnc_r
                simp only [Forest.ruleIds]
                exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                  (List.mem_append.mpr (Or.inr hmem)))
          · simp at h

/-- The reconstructed-away fragments are absent from the new authority nodes. -/
theorem reconstructAt_removed_not_nodes {f f' : Forest} {id : CapId} {a b : Leaf}
    (h : f.reconstructAt id = some (f', a, b))
    (hn : (f.nodes.map Leaf.id).Nodup) :
    a.id ∉ f'.nodes.map Leaf.id ∧ b.id ∉ f'.nodes.map Leaf.id := by
  induction f generalizing f' a b with
  | leaf c => simp [Forest.reconstructAt] at h
  | split k p lr rr l r ihl ihr =>
      simp only [Forest.nodes, List.map_cons, List.map_append] at hn
      rw [List.nodup_cons] at hn
      obtain ⟨hp, hnd⟩ := hn
      rw [List.nodup_append] at hnd
      obtain ⟨hln, hrn, hdisj⟩ := hnd
      simp only [Forest.reconstructAt] at h
      split at h
      · rename_i hp'
        have hf' : f' = .leaf p := reconstructHere_nodes h
        obtain ⟨ha, hb⟩ := reconstructHere_child_ids h
        subst hf'
        have hrule := reconstructHere_ruleValid h
        obtain ⟨-, -, -, -, -, -, -, -, hlr, hrr, -⟩ := hrule
        simp only [Forest.nodes, List.map_cons, List.map_nil, List.mem_cons,
          List.not_mem_nil, or_false]
        constructor
        · rw [ha]; exact hlr
        · rw [hb]; exact hrr
      · rename_i hp'
        split at h
        · rename_i l' a' b' hl
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          obtain ⟨ha', hb'⟩ := ihl hl hln
          have ha_mem := (reconstructAt_removed_mem_nodes hl).1
          have hb_mem := (reconstructAt_removed_mem_nodes hl).2
          have ha_l : a' ∈ l.nodes := ha_mem
          have hb_l : b' ∈ l.nodes := hb_mem
          simp only [Forest.nodes, List.map_cons, List.map_append]
          constructor
          · intro hm
            rcases List.mem_cons.mp hm with hm | hm
            · -- a'.id = p.id, contradict hp
              exact hp (List.mem_append.mpr (Or.inl
                (List.mem_map.mpr ⟨a', ha_l, hm⟩)))
            · rcases List.mem_append.mp hm with hm | hm
              · exact ha' hm
              · exact not_mem_of_disjoint hdisj
                  (List.mem_map.mpr ⟨a', ha_l, rfl⟩) hm
          · intro hm
            rcases List.mem_cons.mp hm with hm | hm
            · exact hp (List.mem_append.mpr (Or.inl
                (List.mem_map.mpr ⟨b', hb_l, hm⟩)))
            · rcases List.mem_append.mp hm with hm | hm
              · exact hb' hm
              · exact not_mem_of_disjoint hdisj
                  (List.mem_map.mpr ⟨b', hb_l, rfl⟩) hm
        · rename_i hl
          split at h
          · rename_i r' a' b' hr
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            obtain ⟨ha', hb'⟩ := ihr hr hrn
            have ha_mem := (reconstructAt_removed_mem_nodes hr).1
            have hb_mem := (reconstructAt_removed_mem_nodes hr).2
            have ha_r : a' ∈ r.nodes := ha_mem
            have hb_r : b' ∈ r.nodes := hb_mem
            have hdisj_symm : ∀ x ∈ r.nodes.map Leaf.id,
                ∀ y ∈ l.nodes.map Leaf.id, x ≠ y := by
              intro x hx y hy
              exact Ne.symm (hdisj y hy x hx)
            simp only [Forest.nodes, List.map_cons, List.map_append]
            constructor
            · intro hm
              rcases List.mem_cons.mp hm with hm | hm
              · exact hp (List.mem_append.mpr (Or.inr
                  (List.mem_map.mpr ⟨a', ha_r, hm⟩)))
              · rcases List.mem_append.mp hm with hm | hm
                · exact not_mem_of_disjoint hdisj_symm
                    (List.mem_map.mpr ⟨a', ha_r, rfl⟩) hm
                · exact ha' hm
            · intro hm
              rcases List.mem_cons.mp hm with hm | hm
              · exact hp (List.mem_append.mpr (Or.inr
                  (List.mem_map.mpr ⟨b', hb_r, hm⟩)))
              · rcases List.mem_append.mp hm with hm | hm
                · exact not_mem_of_disjoint hdisj_symm
                    (List.mem_map.mpr ⟨b', hb_r, rfl⟩) hm
                · exact hb' hm
          · simp at h

/-- Reconstruction only removes rule fragments. -/
theorem reconstructAt_ruleIds_mem {f f' : Forest} {id : CapId} {a b : Leaf}
    (h : f.reconstructAt id = some (f', a, b)) {y : CapId}
    (hy : y ∈ f'.ruleIds) : y ∈ f.ruleIds := by
  induction f generalizing f' a b with
  | leaf c => simp [Forest.reconstructAt] at h
  | split k p lr rr l r ihl ihr =>
      simp only [Forest.reconstructAt] at h
      split at h
      · rename_i hp
        have hf' : f' = .leaf p := reconstructHere_nodes h
        subst hf'
        simp [Forest.ruleIds] at hy
      · rename_i hp
        split at h
        · rename_i l' a' b' hl
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          simp only [Forest.ruleIds] at ⊢
          simp only [Forest.ruleIds, List.mem_cons, List.mem_append] at hy
          rcases hy with rfl | rfl | hy | hy
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_append.mpr (Or.inl (ihl hl hy))))
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_append.mpr (Or.inr hy)))
        · rename_i hl
          split at h
          · rename_i r' a' b' hr
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            simp only [Forest.ruleIds] at ⊢
            simp only [Forest.ruleIds, List.mem_cons, List.mem_append] at hy
            rcases hy with rfl | rfl | hy | hy
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ List.mem_cons_self
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_append.mpr (Or.inl hy)))
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_append.mpr (Or.inr (ihr hr hy))))
          · simp at h

/-- Retag a current active leaf, keeping its resource description. -/
def retagLeafAt (newId : CapId) (c : Leaf) : Option (Forest × Leaf) :=
  if c.state = .active then some (.leaf { c with id := newId }, c) else none

/-- Retag a current leaf by access name. -/
def retagLeaf (id newId : CapId) : Forest → Option (Forest × Leaf) :=
  Forest.modifyLeafAt id (fun c => retagLeafAt newId c)

/-- Retagging preserves the frontier budget (the access name is not part of the
budget). -/
theorem retagLeaf_budget {f f' : Forest} {id newId : CapId} {p : Leaf}
    (h : f.retagLeaf id newId = some (f', p)) :
    ∀ x, f'.budget x = f.budget x := by
  apply budget_modifyLeafAt h
  intro d x d' hg b
  unfold retagLeafAt at hg
  split at hg
  · simp only [Option.some.injEq, Prod.mk.injEq] at hg
    obtain ⟨rfl, _⟩ := hg
    simp [Forest.budget, Leaf.budget]
  · cases hg

/-- Retagging preserves validity. -/
theorem retagLeaf_valid {f f' : Forest} {id newId : CapId} {p : Leaf}
    (h : f.retagLeaf id newId = some (f', p)) (hv : f.Valid) : f'.Valid := by
  apply valid_modifyLeafAt h hv
  intro d x d' hg
  unfold retagLeafAt at hg
  split at hg
  · simp only [Option.some.injEq, Prod.mk.injEq] at hg
    obtain ⟨rfl, _⟩ := hg
    trivial
  · cases hg

/-- The leaf a retagging replaced, and the identity it carried. -/
theorem retag_modify_found {f f' : Forest} {id newId : CapId} {p : Leaf}
    (h : f.modifyLeafAt id (fun c => retagLeafAt newId c) = some (f', p)) :
    p.id = id ∧ p ∈ f.nodes := by
  induction f generalizing f' p with
  | leaf c0 =>
      simp only [Forest.modifyLeafAt] at h
      by_cases hc : c0.id = id
      · rw [if_pos hc] at h
        unfold Forest.retagLeafAt at h
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          exact ⟨hc, by simp [Forest.nodes]⟩
        · cases h
      · rw [if_neg hc] at h
        cases h
  | split k p0 lr rr l r ihl ihr =>
      simp only [Forest.modifyLeafAt] at h
      split at h
      · rename_i l' p' hl
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        obtain ⟨hid, hmem⟩ := ihl hl
        exact ⟨hid, by
          simp only [Forest.nodes, List.mem_cons, List.mem_append]
          exact Or.inr (Or.inl hmem)⟩
      · rename_i hl
        split at h
        · rename_i r' p' hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          obtain ⟨hid, hmem⟩ := ihr hr
          exact ⟨hid, by
            simp only [Forest.nodes, List.mem_cons, List.mem_append]
            exact Or.inr (Or.inr hmem)⟩
        · cases h

/-- The retagged leaf is a node of the new forest. -/
theorem retag_modify_newnode_mem {f f' : Forest} {id newId : CapId} {p : Leaf}
    (h : f.modifyLeafAt id (fun c => retagLeafAt newId c) = some (f', p)) :
    { p with id := newId } ∈ f'.nodes := by
  induction f generalizing f' p with
  | leaf c0 =>
      simp only [Forest.modifyLeafAt] at h
      by_cases hc : c0.id = id
      · rw [if_pos hc] at h
        unfold Forest.retagLeafAt at h
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp [Forest.nodes]
        · cases h
      · rw [if_neg hc] at h
        cases h
  | split k p0 lr rr l r ihl ihr =>
      simp only [Forest.modifyLeafAt] at h
      split at h
      · rename_i l' p' hl
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Forest.nodes, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inl (ihl hl))
      · rename_i hl
        split at h
        · rename_i r' p' hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [Forest.nodes, List.mem_cons, List.mem_append]
          exact Or.inr (Or.inr (ihr hr))
        · cases h

/-- A retagging keeps every old node or introduces the new name. -/
theorem retag_modify_nodes_mem {f f' : Forest} {id newId : CapId} {p : Leaf}
    (h : f.modifyLeafAt id (fun c => retagLeafAt newId c) = some (f', p))
    {c' : Leaf} (hc' : c' ∈ f'.nodes) : c' ∈ f.nodes ∨ c'.id = newId := by
  induction f generalizing f' p with
  | leaf c0 =>
      simp only [Forest.modifyLeafAt] at h
      by_cases hc : c0.id = id
      · rw [if_pos hc] at h
        unfold Forest.retagLeafAt at h
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _⟩ := h
          simp only [Forest.nodes, List.mem_singleton] at hc'
          subst hc'
          exact Or.inr rfl
        · cases h
      · rw [if_neg hc] at h
        cases h
  | split k p0 lr rr l r ihl ihr =>
      simp only [Forest.modifyLeafAt] at h
      split at h
      · rename_i l' p' hl
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Forest.nodes] at hc' ⊢
        rcases List.mem_cons.mp hc' with rfl | hc'
        · exact Or.inl List.mem_cons_self
        · rcases List.mem_append.mp hc' with hc' | hc'
          · rcases ihl hl hc' with hc' | hc'
            · exact Or.inl (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl hc')))
            · exact Or.inr hc'
          · exact Or.inl (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr hc')))
      · rename_i hl
        split at h
        · rename_i r' p' hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [Forest.nodes] at hc' ⊢
          rcases List.mem_cons.mp hc' with rfl | hc'
          · exact Or.inl List.mem_cons_self
          · rcases List.mem_append.mp hc' with hc' | hc'
            · exact Or.inl (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl hc')))
            · rcases ihr hr hc' with hc' | hc'
              · exact Or.inl (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr hc')))
              · exact Or.inr hc'
        · cases h

/-- An old node whose identity is not retagged survives. -/
theorem retag_modify_nodes_old_of_ne {f f' : Forest} {id newId : CapId} {p : Leaf}
    (h : f.modifyLeafAt id (fun c => retagLeafAt newId c) = some (f', p))
    {y : CapId} (hy : y ∈ f.nodes.map Leaf.id) (hne : y ≠ id) :
    y ∈ f'.nodes.map Leaf.id := by
  induction f generalizing f' p with
  | leaf c0 =>
      simp only [Forest.modifyLeafAt] at h
      by_cases hc : c0.id = id
      · rw [if_pos hc] at h
        simp only [Forest.nodes, List.map_cons, List.map_nil, List.mem_singleton] at hy
        exact absurd (hy.trans hc) hne
      · rw [if_neg hc] at h
        cases h
  | split k p0 lr rr l r ihl ihr =>
      simp only [Forest.modifyLeafAt] at h
      split at h
      · rename_i l' p' hl
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Forest.nodes, List.map_cons, List.map_append] at hy ⊢
        rcases List.mem_cons.mp hy with rfl | hy
        · exact List.mem_cons_self
        · rcases List.mem_append.mp hy with hy | hy
          · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl (ihl hl hy)))
          · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr hy))
      · rename_i hl
        split at h
        · rename_i r' p' hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [Forest.nodes, List.map_cons, List.map_append] at hy ⊢
          rcases List.mem_cons.mp hy with rfl | hy
          · exact List.mem_cons_self
          · rcases List.mem_append.mp hy with hy | hy
            · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl hy))
            · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr (ihr hr hy)))
        · cases h

/-- A retagging only adds the new name to the identity list. -/
theorem retag_modify_ids_mem {f f' : Forest} {id newId : CapId} {p : Leaf}
    (h : f.modifyLeafAt id (fun c => retagLeafAt newId c) = some (f', p))
    {y : CapId} (hy : y ∈ f'.ids) : y ∈ f.ids ∨ y = newId := by
  induction f generalizing f' p with
  | leaf c0 =>
      simp only [Forest.modifyLeafAt] at h
      by_cases hc : c0.id = id
      · rw [if_pos hc] at h
        unfold Forest.retagLeafAt at h
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _⟩ := h
          simp only [Forest.ids, List.mem_singleton] at hy
          exact Or.inr hy
        · cases h
      · rw [if_neg hc] at h
        cases h
  | split k p0 lr rr l r ihl ihr =>
      simp only [Forest.modifyLeafAt] at h
      split at h
      · rename_i l' p' hl
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Forest.ids] at ⊢
        simp only [Forest.ids, List.mem_cons, List.mem_append] at hy
        rcases hy with rfl | rfl | rfl | hy | hy
        · exact Or.inl List.mem_cons_self
        · exact Or.inl (List.mem_cons_of_mem _ List.mem_cons_self)
        · exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
        · rcases ihl hl hy with hy | hy
          · exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl hy)))))
          · exact Or.inr hy
        · exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr hy)))))
      · rename_i hl
        split at h
        · rename_i r' p' hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [Forest.ids] at ⊢
          simp only [Forest.ids, List.mem_cons, List.mem_append] at hy
          rcases hy with rfl | rfl | rfl | hy | hy
          · exact Or.inl List.mem_cons_self
          · exact Or.inl (List.mem_cons_of_mem _ List.mem_cons_self)
          · exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
          · exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl hy)))))
          · rcases ihr hr hy with hy | hy
            · exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr hy)))))
            · exact Or.inr hy
        · cases h

/-- A retagging leaves rule fragments unchanged. -/
theorem retag_modify_ruleIds_mem {f f' : Forest} {id newId : CapId} {p : Leaf}
    (h : f.modifyLeafAt id (fun c => retagLeafAt newId c) = some (f', p))
    {y : CapId} (hy : y ∈ f'.ruleIds) : y ∈ f.ruleIds := by
  induction f generalizing f' p with
  | leaf c0 =>
      simp only [Forest.modifyLeafAt] at h
      by_cases hc : c0.id = id
      · rw [if_pos hc] at h
        unfold Forest.retagLeafAt at h
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _⟩ := h
          simp [Forest.ruleIds] at hy
        · cases h
      · rw [if_neg hc] at h
        cases h
  | split k p0 lr rr l r ihl ihr =>
      simp only [Forest.modifyLeafAt] at h
      split at h
      · rename_i l' p' hl
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Forest.ruleIds] at ⊢
        simp only [Forest.ruleIds, List.mem_cons, List.mem_append] at hy
        rcases hy with rfl | rfl | hy | hy
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_append.mpr (Or.inl (ihl hl hy))))
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_append.mpr (Or.inr hy)))
      · rename_i hl
        split at h
        · rename_i r' p' hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [Forest.ruleIds] at ⊢
          simp only [Forest.ruleIds, List.mem_cons, List.mem_append] at hy
          rcases hy with rfl | rfl | hy | hy
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_append.mpr (Or.inl hy)))
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_append.mpr (Or.inr (ihr hr hy))))
        · cases h

/-- The retagged identity is absent from the new authority nodes. -/
theorem retag_modify_nodes_id_absent {f f' : Forest} {id newId : CapId} {p : Leaf}
    (h : f.modifyLeafAt id (fun c => retagLeafAt newId c) = some (f', p))
    (hn : (f.nodes.map Leaf.id).Nodup) (hne : newId ≠ id) :
    id ∉ f'.nodes.map Leaf.id := by
  induction f generalizing f' p with
  | leaf c0 =>
      simp only [Forest.modifyLeafAt] at h
      by_cases hc : c0.id = id
      · rw [if_pos hc] at h
        unfold Forest.retagLeafAt at h
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _⟩ := h
          simpa [Forest.nodes] using (Ne.symm hne)
        · cases h
      · rw [if_neg hc] at h
        cases h
  | split k p0 lr rr l r ihl ihr =>
      simp only [Forest.nodes, List.map_cons, List.map_append] at hn
      rw [List.nodup_cons] at hn
      obtain ⟨hp0, hnd⟩ := hn
      rw [List.nodup_append] at hnd
      obtain ⟨hln, hrn, hdisj⟩ := hnd
      simp only [Forest.modifyLeafAt] at h
      split at h
      · rename_i l' p' hl
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hid, hmem⟩ := retag_modify_found hl
        have hid_l : id ∈ l.nodes.map Leaf.id :=
          List.mem_map.mpr ⟨p', hmem, hid⟩
        have hp0_ne : p0.id ≠ id := by
          intro heq
          exact hp0 (heq ▸ List.mem_append.mpr (Or.inl hid_l))
        have hid_r : id ∉ r.nodes.map Leaf.id := by
          intro hm; exact not_mem_of_disjoint hdisj hid_l hm
        have hid_l' : id ∉ l'.nodes.map Leaf.id := ihl hl hln
        simp only [Forest.nodes, List.map_cons, List.map_append]
        intro hm
        rcases List.mem_cons.mp hm with hm | hm
        · exact hp0_ne hm.symm
        · rcases List.mem_append.mp hm with hm | hm
          · exact hid_l' hm
          · exact hid_r hm
      · rename_i hl
        split at h
        · rename_i r' p' hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨hid, hmem⟩ := retag_modify_found hr
          have hid_r : id ∈ r.nodes.map Leaf.id :=
            List.mem_map.mpr ⟨p', hmem, hid⟩
          have hp0_ne : p0.id ≠ id := by
            intro heq
            exact hp0 (heq ▸ List.mem_append.mpr (Or.inr hid_r))
          have hid_l : id ∉ l.nodes.map Leaf.id := by
            intro hm; exact (hdisj id hm id hid_r) rfl
          have hid_r' : id ∉ r'.nodes.map Leaf.id := ihr hr hrn
          simp only [Forest.nodes, List.map_cons, List.map_append]
          intro hm
          rcases List.mem_cons.mp hm with hm | hm
          · exact hp0_ne hm.symm
          · rcases List.mem_append.mp hm with hm | hm
            · exact hid_l hm
            · exact hid_r' hm
        · cases h

/-- A retagging preserves distinct authority identities. -/
theorem retag_modify_nodes_nodup {f f' : Forest} {id newId : CapId} {p : Leaf}
    (h : f.modifyLeafAt id (fun c => retagLeafAt newId c) = some (f', p))
    (hn : (f.nodes.map Leaf.id).Nodup)
    (hnew : newId ∉ f.nodes.map Leaf.id) :
    (f'.nodes.map Leaf.id).Nodup := by
  induction f generalizing f' p with
  | leaf c0 =>
      simp only [Forest.modifyLeafAt] at h
      by_cases hc : c0.id = id
      · rw [if_pos hc] at h
        unfold Forest.retagLeafAt at h
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _⟩ := h
          simp [Forest.nodes]
        · cases h
      · rw [if_neg hc] at h
        cases h
  | split k p0 lr rr l r ihl ihr =>
      simp only [Forest.nodes, List.map_cons, List.map_append] at hn
      rw [List.nodup_cons] at hn
      obtain ⟨hp0, hnd⟩ := hn
      rw [List.nodup_append] at hnd
      obtain ⟨hln, hrn, hdisj⟩ := hnd
      simp only [Forest.modifyLeafAt] at h
      split at h
      · rename_i l' p' hl
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hnew_l : newId ∉ l.nodes.map Leaf.id := by
          intro hm
          exact hnew (List.mem_cons_of_mem p0.id (by
            rw [List.map_append]; exact List.mem_append.mpr (Or.inl hm)))
        have hnew_r : newId ∉ r.nodes.map Leaf.id := by
          intro hm
          exact hnew (List.mem_cons_of_mem p0.id (by
            rw [List.map_append]; exact List.mem_append.mpr (Or.inr hm)))
        have hl' := ihl hl hln hnew_l
        have hp_l : p0.id ∉ l'.nodes.map Leaf.id := by
          intro hm
          obtain ⟨c', hc', hcid⟩ := List.mem_map.mp hm
          rcases retag_modify_nodes_mem hl hc' with hc' | hc'
          · exact hp0 (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨c', hc', hcid⟩)))
          · exact hnew (by
              have : newId = p0.id := hc'.symm.trans hcid
              rw [this]
              simp only [Forest.nodes, List.map_cons]
              exact List.mem_cons_self)
        have hp_r : p0.id ∉ r.nodes.map Leaf.id := by
          intro hm; exact hp0 (List.mem_append.mpr (Or.inr hm))
        have hdisj' : ∀ x ∈ l'.nodes.map Leaf.id, x ∉ r.nodes.map Leaf.id := by
          intro x hx hy
          obtain ⟨c', hc', hcid⟩ := List.mem_map.mp hx
          rcases retag_modify_nodes_mem hl hc' with hc' | hc'
          · exact (hdisj x (List.mem_map.mpr ⟨c', hc', hcid⟩) x hy) rfl
          · exact hnew_r (hc' ▸ (hcid ▸ hy))
        simp only [Forest.nodes, List.map_cons, List.map_append]
        rw [List.nodup_cons, List.nodup_append]
        refine ⟨?_, hl', hrn, disjoint_of_not_mem hdisj'⟩
        intro hm
        rcases List.mem_append.mp hm with hm | hm
        · exact hp_l hm
        · exact hp_r hm
      · rename_i hl
        split at h
        · rename_i r' p' hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hnew_r : newId ∉ r.nodes.map Leaf.id := by
            intro hm
            exact hnew (List.mem_cons_of_mem p0.id (by
              rw [List.map_append]; exact List.mem_append.mpr (Or.inr hm)))
          have hnew_l : newId ∉ l.nodes.map Leaf.id := by
            intro hm
            exact hnew (List.mem_cons_of_mem p0.id (by
              rw [List.map_append]; exact List.mem_append.mpr (Or.inl hm)))
          have hr' := ihr hr hrn hnew_r
          have hp_r : p0.id ∉ r'.nodes.map Leaf.id := by
            intro hm
            obtain ⟨c', hc', hcid⟩ := List.mem_map.mp hm
            rcases retag_modify_nodes_mem hr hc' with hc' | hc'
            · exact hp0 (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨c', hc', hcid⟩)))
            · exact hnew (by
                have : newId = p0.id := hc'.symm.trans hcid
                rw [this]
                simp only [Forest.nodes, List.map_cons]
                exact List.mem_cons_self)
          have hp_l : p0.id ∉ l.nodes.map Leaf.id := by
            intro hm; exact hp0 (List.mem_append.mpr (Or.inl hm))
          have hdisj' : ∀ x ∈ l.nodes.map Leaf.id, x ∉ r'.nodes.map Leaf.id := by
            intro x hx hy
            obtain ⟨c', hc', hcid⟩ := List.mem_map.mp hy
            rcases retag_modify_nodes_mem hr hc' with hc' | hc'
            · exact (hdisj x hx x (List.mem_map.mpr ⟨c', hc', hcid⟩)) rfl
            · exact hnew_l (hc' ▸ (hcid ▸ hx))
          simp only [Forest.nodes, List.map_cons, List.map_append]
          rw [List.nodup_cons, List.nodup_append]
          refine ⟨?_, hln, hr', disjoint_of_not_mem hdisj'⟩
          intro hm
          rcases List.mem_append.mp hm with hm | hm
          · exact hp_l hm
          · exact hp_r hm
        · cases h

/-- The replaced leaf carries the queried identity. -/
theorem retagLeaf_found {f f' : Forest} {id newId : CapId} {p : Leaf}
    (h : f.retagLeaf id newId = some (f', p)) : p.id = id ∧ p ∈ f.nodes := by
  unfold Forest.retagLeaf at h
  exact retag_modify_found h

/-- The retagged leaf is a node of the new forest. -/
theorem retagLeaf_newnode_mem {f f' : Forest} {id newId : CapId} {p : Leaf}
    (h : f.retagLeaf id newId = some (f', p)) :
    { p with id := newId } ∈ f'.nodes := by
  unfold Forest.retagLeaf at h
  exact retag_modify_newnode_mem h

/-- A retagging keeps every old node or introduces the new name. -/
theorem retagLeaf_nodes_mem {f f' : Forest} {id newId : CapId} {p : Leaf}
    (h : f.retagLeaf id newId = some (f', p)) {c' : Leaf} (hc' : c' ∈ f'.nodes) :
    c' ∈ f.nodes ∨ c'.id = newId := by
  unfold Forest.retagLeaf at h
  exact retag_modify_nodes_mem h hc'

/-- An old node whose identity is not retagged survives. -/
theorem retagLeaf_nodes_old_of_ne {f f' : Forest} {id newId : CapId} {p : Leaf}
    (h : f.retagLeaf id newId = some (f', p)) {y : CapId}
    (hy : y ∈ f.nodes.map Leaf.id) (hne : y ≠ id) :
    y ∈ f'.nodes.map Leaf.id := by
  unfold Forest.retagLeaf at h
  exact retag_modify_nodes_old_of_ne h hy hne

/-- A retagging only adds the new name to the identity list. -/
theorem retagLeaf_ids_mem {f f' : Forest} {id newId : CapId} {p : Leaf}
    (h : f.retagLeaf id newId = some (f', p)) {y : CapId} (hy : y ∈ f'.ids) :
    y ∈ f.ids ∨ y = newId := by
  unfold Forest.retagLeaf at h
  exact retag_modify_ids_mem h hy

/-- A retagging leaves rule fragments unchanged. -/
theorem retagLeaf_ruleIds_mem {f f' : Forest} {id newId : CapId} {p : Leaf}
    (h : f.retagLeaf id newId = some (f', p)) {y : CapId} (hy : y ∈ f'.ruleIds) :
    y ∈ f.ruleIds := by
  unfold Forest.retagLeaf at h
  exact retag_modify_ruleIds_mem h hy

/-- The retagged identity is absent from the new authority nodes. -/
theorem retagLeaf_nodes_id_absent {f f' : Forest} {id newId : CapId} {p : Leaf}
    (h : f.retagLeaf id newId = some (f', p))
    (hn : (f.nodes.map Leaf.id).Nodup) (hne : newId ≠ id) :
    id ∉ f'.nodes.map Leaf.id := by
  unfold Forest.retagLeaf at h
  exact retag_modify_nodes_id_absent h hn hne

/-- A retagging preserves distinct authority identities. -/
theorem retagLeaf_nodes_nodup {f f' : Forest} {id newId : CapId} {p : Leaf}
    (h : f.retagLeaf id newId = some (f', p))
    (hn : (f.nodes.map Leaf.id).Nodup)
    (hnew : newId ∉ f.nodes.map Leaf.id) :
    (f'.nodes.map Leaf.id).Nodup := by
  unfold Forest.retagLeaf at h
  exact retag_modify_nodes_nodup h hn hnew

/-- A forest identity is either an authority node identity or a rule fragment. -/
theorem ids_mem_nodes_or_ruleIds {f : Forest} {y : CapId} (hy : y ∈ f.ids) :
    y ∈ f.nodes.map Leaf.id ∨ y ∈ f.ruleIds := by
  induction f with
  | leaf c =>
      exact Or.inl (by simpa [Forest.ids, Forest.nodes] using hy)
  | split k p lr rr l r ihl ihr =>
      simp only [Forest.ids, List.mem_cons, List.mem_append] at hy
      simp only [Forest.nodes, Forest.ruleIds, List.map_cons, List.map_append,
        List.mem_cons, List.mem_append, List.mem_nil_iff, or_false]
      rcases hy with rfl | rfl | rfl | hy | hy
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · rcases ihl hy with h | h
        · exact Or.inl (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · rcases ihr hy with h | h
        · exact Or.inl (Or.inr (Or.inr h))
        · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- A checked spatial leaf split uses two distinct child names. -/
theorem spatialLeafSplit_children_ne {p p' : Leaf} {x : Forest} {c1 c2 : CapId}
    {lo1 hi1 lo2 hi2 : Nat}
    (h : spatialLeafSplit p c1 c2 lo1 hi1 lo2 hi2 = some (x, p')) : c1 ≠ c2 := by
  unfold spatialLeafSplit at h
  split at h
  · split at h
    · split at h
      · split at h
        · rename_i hid
          exact hid.1
        · simp at h
      · simp at h
    · simp at h
  · simp at h

/-- A checked fractional leaf split uses two distinct child names. -/
theorem fractionalLeafSplit_children_ne {p p' : Leaf} {x : Forest} {c1 c2 : CapId}
    {q1 q2 : Nat}
    (h : fractionalLeafSplit p c1 c2 q1 q2 = some (x, p')) : c1 ≠ c2 := by
  unfold fractionalLeafSplit at h
  split at h
  · split at h
    · split at h
      · split at h
        · rename_i hid
          exact hid.1
        · simp at h
      · simp at h
    · simp at h
  · simp at h

/-- A split-shaped leaf modification inherits a property of every local split. -/
theorem modifyLeafAt_child_ne {f : Forest} {id : CapId}
    {g : Leaf → Option (Forest × Leaf)} {c1 c2 : CapId}
    (hlocal : ∀ (d : Leaf) (x : Forest) (d' : Leaf),
      g d = some (x, d') → c1 ≠ c2) :
    ∀ {f' : Forest} {c : Leaf}, f.modifyLeafAt id g = some (f', c) → c1 ≠ c2 := by
  induction f with
  | leaf c0 =>
      intro f' c h
      simp only [Forest.modifyLeafAt] at h
      by_cases hc : c0.id = id
      · rw [if_pos hc] at h
        exact hlocal c0 f' c h
      · rw [if_neg hc] at h
        cases h
  | split k p lr rr l r ihl ihr =>
      intro f' c h
      simp only [Forest.modifyLeafAt] at h
      split at h
      · rename_i l' c' hl
        exact ihl hl
      · rename_i hl
        split at h
        · rename_i r' c' hr
          exact ihr hr
        · cases h

/-- A spatial subdivision uses two distinct child names. -/
theorem splitSpatialAt_children_ne {f f' : Forest} {p : Leaf} {id c1 c2 : CapId}
    {lo1 hi1 lo2 hi2 : Nat}
    (h : f.splitSpatialAt id c1 c2 lo1 hi1 lo2 hi2 = some (f', p)) : c1 ≠ c2 := by
  unfold Forest.splitSpatialAt at h
  exact modifyLeafAt_child_ne
    (fun d x d' hg => spatialLeafSplit_children_ne hg) h

/-- A fractional subdivision uses two distinct child names. -/
theorem splitFractionAt_children_ne {f f' : Forest} {p : Leaf} {id c1 c2 : CapId}
    {q1 q2 : Nat}
    (h : f.splitFractionAt id c1 c2 q1 q2 = some (f', p)) : c1 ≠ c2 := by
  unfold Forest.splitFractionAt at h
  exact modifyLeafAt_child_ne
    (fun d x d' hg => fractionalLeafSplit_children_ne hg) h

/-- Every authority node after a retagging is either an old node or exactly the
retagged leaf. -/
theorem retag_modify_nodes_cases {f f' : Forest} {id newId : CapId} {p : Leaf}
    (h : f.modifyLeafAt id (fun c => retagLeafAt newId c) = some (f', p))
    {c' : Leaf} (hc' : c' ∈ f'.nodes) :
    c' ∈ f.nodes ∨ c' = { p with id := newId } := by
  induction f generalizing f' p c' with
  | leaf c0 =>
      simp only [Forest.modifyLeafAt] at h
      by_cases hc : c0.id = id
      · rw [if_pos hc] at h
        unfold Forest.retagLeafAt at h
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [Forest.nodes, List.mem_singleton] at hc'
          exact Or.inr hc'
        · cases h
      · rw [if_neg hc] at h
        cases h
  | split k p0 lr rr l r ihl ihr =>
      simp only [Forest.modifyLeafAt] at h
      split at h
      · rename_i l' p' hl
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [Forest.nodes] at hc' ⊢
        rcases List.mem_cons.mp hc' with rfl | hc'
        · exact Or.inl List.mem_cons_self
        · rcases List.mem_append.mp hc' with hc' | hc'
          · rcases ihl hl hc' with hm | hm
            · exact Or.inl (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl hm)))
            · exact Or.inr hm
          · exact Or.inl (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr hc')))
      · rename_i hl
        split at h
        · rename_i r' p' hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [Forest.nodes] at hc' ⊢
          rcases List.mem_cons.mp hc' with rfl | hc'
          · exact Or.inl List.mem_cons_self
          · rcases List.mem_append.mp hc' with hc' | hc'
            · exact Or.inl (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl hc')))
            · rcases ihr hr hc' with hm | hm
              · exact Or.inl (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr hm)))
              · exact Or.inr hm
        · cases h

/-- Every authority node after a retagging is either an old node or exactly the
retagged leaf. -/
theorem retagLeaf_nodes_cases {f f' : Forest} {id newId : CapId} {p : Leaf}
    (h : f.retagLeaf id newId = some (f', p))
    {c' : Leaf} (hc' : c' ∈ f'.nodes) :
    c' ∈ f.nodes ∨ c' = { p with id := newId } := by
  unfold Forest.retagLeaf at h
  exact retag_modify_nodes_cases h hc'

/-- A successful leaf lookup returns a current leaf with the queried identity. -/
theorem findLeaf?_mem_leaves {f : Forest} {id : CapId} {c : Leaf}
    (h : f.findLeaf? id = some c) : c ∈ f.leaves ∧ c.id = id := by
  induction f with
  | leaf c0 =>
      simp only [Forest.findLeaf?] at h
      split at h
      · rename_i hc
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨by simp [Forest.leaves], hc⟩
      · cases h
  | split k p lr rr l r ihl ihr =>
      simp only [Forest.findLeaf?] at h
      split at h
      · rename_i hc
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨hm, hid⟩ := ihl hc
        exact ⟨by simp only [Forest.leaves, List.mem_append]; exact Or.inl hm, hid⟩
      · rename_i hc
        obtain ⟨hm, hid⟩ := ihr h
        exact ⟨by simp only [Forest.leaves, List.mem_append]; exact Or.inr hm, hid⟩

/-- Distinct identity lists mean two elements with the same mapped identity are
the same element. -/
theorem eq_of_mem_of_map_nodup {l : List Leaf} (hn : (l.map Leaf.id).Nodup)
    {a b : Leaf} (ha : a ∈ l) (hb : b ∈ l) (hid : a.id = b.id) : a = b := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
      rw [List.map_cons, List.nodup_cons] at hn
      obtain ⟨hx, hxs⟩ := hn
      rcases List.mem_cons.mp ha with hhead | htail
      · cases hhead
        rcases List.mem_cons.mp hb with hhead | htailb
        · cases hhead; rfl
        · exact absurd (hid.symm ▸ List.mem_map.mpr ⟨b, htailb, rfl⟩) hx
      · rcases List.mem_cons.mp hb with hhead | htailb
        · cases hhead
          exact absurd (hid ▸ List.mem_map.mpr ⟨a, htail, rfl⟩) hx
        · exact ih hxs htail htailb

/-- A list whose mapped identities are distinct has distinct mapped values for
distinct elements. -/
theorem ne_of_map_nodup {α β : Type} {l : List α} {f : α → β}
    (hn : (l.map f).Nodup) {a b : α} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) :
    f a ≠ f b := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
      rw [List.map_cons, List.nodup_cons] at hn
      obtain ⟨hx, hxs⟩ := hn
      rcases List.mem_cons.mp ha with hhead | htail
      · cases hhead
        rcases List.mem_cons.mp hb with hhead | htailb
        · cases hhead
          exact fun _ => hne rfl
        · intro heq
          exact hx (heq ▸ List.mem_map.mpr ⟨b, htailb, rfl⟩)
      · rcases List.mem_cons.mp hb with hhead | htailb
        · cases hhead
          intro heq
          exact hx (heq ▸ List.mem_map.mpr ⟨a, htail, rfl⟩)
        · exact ih hxs htail htailb

/-- An old node whose identity is not retagged survives the retagging. -/
theorem retag_modify_nodes_old_mem {f f' : Forest} {id newId : CapId} {p c : Leaf}
    (h : f.modifyLeafAt id (fun x => retagLeafAt newId x) = some (f', p))
    (hc : c ∈ f.nodes) (hid : c.id ≠ id) : c ∈ f'.nodes := by
  induction f generalizing f' p c with
  | leaf c0 =>
      simp only [Forest.modifyLeafAt] at h
      by_cases hc0 : c0.id = id
      · rw [if_pos hc0] at h
        simp only [Forest.nodes, List.mem_singleton] at hc
        rcases hc with rfl
        exact absurd hc0 hid
      · rw [if_neg hc0] at h
        cases h
  | split k p0 lr rr l r ihl ihr =>
      simp only [Forest.nodes] at hc
      simp only [Forest.modifyLeafAt] at h
      split at h
      · rename_i l' p' hl
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hf', _⟩ := h
        rw [← hf']
        simp only [Forest.nodes]
        rcases List.mem_cons.mp hc with rfl | hc
        · exact List.mem_cons_self
        · rcases List.mem_append.mp hc with hc | hc
          · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl (ihl hl hc hid)))
          · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr hc))
      · rename_i hl
        split at h
        · rename_i r' p' hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hf', _⟩ := h
          rw [← hf']
          simp only [Forest.nodes]
          rcases List.mem_cons.mp hc with rfl | hc
          · exact List.mem_cons_self
          · rcases List.mem_append.mp hc with hc | hc
            · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl hc))
            · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr (ihr hr hc hid)))
        · cases h

/-- An old node whose identity is not retagged survives the retagging. -/
theorem retagLeaf_nodes_old_mem {f f' : Forest} {id newId : CapId} {p c : Leaf}
    (h : f.retagLeaf id newId = some (f', p))
    (hc : c ∈ f.nodes) (hid : c.id ≠ id) : c ∈ f'.nodes := by
  unfold Forest.retagLeaf at h
  exact retag_modify_nodes_old_mem h hc hid

end Forest

/-- The reconstruction state of one allocation. The heap is the reference byte
heap; the forest is the authority frontier. -/
structure State where
  alloc : AllocId
  len : Nat
  D : Nat
  forest : Forest
  heap : Heap
  /-- Every access name ever issued in this state. -/
  issued : List CapId
  /-- Access names retired by reconstruction or return; never reissued. -/
  retired : List CapId
  /-- Outstanding return obligations, outermost first. -/
  restores : List Restore

/-- A whole active allocation. -/
def State.initial (a : AllocId) (n D : Nat) (pos : 0 < D)
    (rootId disposalId : CapId) : State :=
  { alloc := a, len := n, D := D,
    forest := .leaf
      { id := rootId, alloc := a, lo := 0, hi := n, ordered := Nat.zero_le n,
        q := D, pos := pos, ceiling := .readWrite, state := .active },
    heap := Heap.alloc Heap.empty a n,
    issued := [rootId, disposalId],
    retired := [],
    restores := [] }

/-- The frontier covers every byte of the allocation. -/
def State.Covered (s : State) : Prop :=
  ∀ x, x < s.len → s.forest.budget x = s.D

/-- Ownership accounting for one allocation.

* `nodeIds_nodup` — the authority-carrying fragments (current leaves and
  suspended parents) have distinct identities; in particular the current active
  leaves are distinct.
* `issue_covers` — every identity the forest mentions was issued here, so a
  current leaf and a restoration name belong to this allocation's issuance
  history.
* `retired_absent` — a retired name is not a current authority identity (a
  current leaf or a suspended parent), so retirement cannot be undone by a later
  transition and no retired name can be used for access. Rule fragments are
  templates rather than current authority, so reconstruction may retire a name
  that was also that suspension's rule fragment.
* `restores_issued`, `borrowers_nodup`, `lenders_nodup`, `lender_ne_borrower` —
  the outstanding obligations name issued, pairwise-distinct lenders and
  borrowers, and no obligation lends to itself.
* `dormant_absent` — a lender awaiting return is not exercising authority in the
  current frontier.
* `borrower_not_rule` — a borrower identity is not also a rule fragment, so a
  suspension cannot retire a live obligation's identity.
* `restore_realized` — every obligation's borrower either holds a current or
  suspended fragment with the recorded resource, or has lent that fragment
  onward to another outstanding obligation.
* `node_agrees` and `nested_agrees` — the resource recorded by an obligation
  agrees with its live fragment, and nested obligations agree on the same
  resource; this is what prevents one budget from being claimed twice.
* `rule_fragments_issued` — the rule fragments of every suspension were issued,
  which makes a fresh child name disjoint from every existing obligation. -/
structure State.Accounts (s : State) : Prop where
  nodeIds_nodup : (s.forest.nodes.map Leaf.id).Nodup
  issue_covers : ∀ id ∈ s.forest.ids, id ∈ s.issued
  retired_absent : ∀ id ∈ s.forest.nodes.map Leaf.id, id ∉ s.retired
  restores_issued : ∀ r ∈ s.restores, r.lender ∈ s.issued ∧ r.borrower ∈ s.issued
  borrowers_nodup : (s.restores.map Restore.borrower).Nodup
  lenders_nodup : (s.restores.map Restore.lender).Nodup
  lender_ne_borrower : ∀ r ∈ s.restores, r.lender ≠ r.borrower
  dormant_absent : ∀ r ∈ s.restores, r.lender ∉ s.forest.nodes.map Leaf.id
  borrower_not_rule : ∀ r ∈ s.restores, r.borrower ∉ s.forest.ruleIds
  restore_realized : ∀ r ∈ s.restores,
      (∃ c ∈ s.forest.nodes, c.id = r.borrower ∧ r.Agrees c) ∨
      (∃ r' ∈ s.restores, r'.lender = r.borrower)
  node_agrees : ∀ r ∈ s.restores, ∀ c ∈ s.forest.nodes,
      c.id = r.borrower → r.Agrees c
  nested_agrees : ∀ r ∈ s.restores, ∀ r' ∈ s.restores,
      r'.lender = r.borrower → r.SameResource r'
  rule_fragments_issued : ∀ id ∈ s.forest.ruleIds, id ∈ s.issued

/-- Current active leaf identities are distinct. -/
theorem State.Accounts.leaves_nodup {s : State} (h : s.Accounts) :
    (s.forest.leaves.map Leaf.id).Nodup := by
  have hsub : List.Sublist s.forest.leaves s.forest.nodes :=
    Forest.leaves_sublist_nodes _
  exact List.Sublist.nodup (List.Sublist.map Leaf.id hsub) h.nodeIds_nodup

/-- A retired name is absent from the current frontier. -/
theorem State.Accounts.retired_not_leaves {s : State} (h : s.Accounts)
    {c : Leaf} (hc : c ∈ s.forest.leaves) : c.id ∉ s.retired := by
  have hnode : c ∈ s.forest.nodes := Forest.mem_nodes_of_mem_leaves hc
  exact h.retired_absent c.id (List.mem_map.mpr ⟨c, hnode, rfl⟩)

/-- A dormant lender is absent from the current frontier. -/
theorem State.Accounts.dormant_not_leaves {s : State} (h : s.Accounts)
    {r : Restore} (hr : r ∈ s.restores) {c : Leaf} (hc : c ∈ s.forest.leaves) :
    r.lender ≠ c.id := by
  intro heq
  have hnode : c ∈ s.forest.nodes := Forest.mem_nodes_of_mem_leaves hc
  exact h.dormant_absent r hr (heq ▸ List.mem_map.mpr ⟨c, hnode, rfl⟩)

/-- The reconstruction invariant: the frontier is covered, every recorded rule
is checked, and the ownership accounts are complete. -/
def State.Inv (s : State) : Prop :=
  s.Covered ∧ s.forest.Valid ∧ s.Accounts

/-- The component's represented storage: its heap holds the allocation with
exactly `len` bytes. This is the storage half of the integrated invariant; the
reconstruction invariant alone does not mention the heap. -/
def State.Storage (s : State) : Prop :=
  ∃ xs, s.heap.lookup? s.alloc = some xs ∧ xs.length = s.len

/-- A state whose heap still holds the same allocation and length satisfies
`Storage` whenever its predecessor does. -/
theorem State.Storage.of_heap {s s' : State} (hheap : s'.heap = s.heap)
    (ha : s'.alloc = s.alloc) (hlen : s'.len = s.len) (hs : s.Storage) :
    s'.Storage := by
  obtain ⟨xs, hlook, hlen'⟩ := hs
  exact ⟨xs, by rw [hheap, ha, hlook], by rw [hlen, hlen']⟩

/-- A whole live allocation satisfies the reconstruction invariant. -/
theorem State.initial_inv (a : AllocId) (n D : Nat) (pos : 0 < D)
    (rootId disposalId : CapId) : (State.initial a n D pos rootId disposalId).Inv := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    change (Forest.leaf
      { id := rootId, alloc := a, lo := 0, hi := n, ordered := Nat.zero_le n,
        q := D, pos := pos, ceiling := .readWrite, state := .active }).budget x = D
    have hx' : 0 ≤ x ∧ x < n := ⟨Nat.zero_le x, hx⟩
    simp [Forest.budget, Leaf.budget, hx']
  · trivial
  · refine
      { nodeIds_nodup := ?_
        issue_covers := ?_
        retired_absent := ?_
        restores_issued := ?_
        borrowers_nodup := ?_
        lenders_nodup := ?_
        lender_ne_borrower := ?_
        dormant_absent := ?_
        borrower_not_rule := ?_
        restore_realized := ?_
        node_agrees := ?_
        nested_agrees := ?_
        rule_fragments_issued := ?_ }
    · simp [State.initial, Forest.nodes]
    · intro id hid
      simp only [State.initial, Forest.ids, List.mem_cons, List.mem_nil_iff, or_false] at hid
      simp [State.initial, hid]
    · intro id _ hid
      simp [State.initial] at hid
    · intro r hr
      simp [State.initial] at hr
    · simp [State.initial]
    · simp [State.initial]
    · intro r hr
      simp [State.initial] at hr
    · intro r hr
      simp [State.initial] at hr
    · intro r hr
      simp [State.initial] at hr
    · intro r hr
      simp [State.initial] at hr
    · intro r hr
      simp [State.initial] at hr
    · intro r hr
      simp [State.initial] at hr
    · intro id hid
      simp [State.initial, Forest.ruleIds] at hid

/-- A whole live allocation's heap holds exactly its `len` bytes. -/
theorem State.initial_storage (a : AllocId) (n D : Nat) (pos : 0 < D)
    (rootId disposalId : CapId) :
    (State.initial a n D pos rootId disposalId).Storage := by
  refine ⟨List.replicate n 0, ?_, by simp [State.initial]⟩
  simp [State.initial, Heap.alloc, Heap.empty, Heap.lookup?, Heap.lookupList?, Heap.updateList]

/-- The restored whole fragment of the 64-byte fixture, as observed. -/
def wholeFragment : Fragment :=
  { alloc := ⟨0⟩, lo := 0, hi := 64, q := 64,
    ceiling := .readWrite, state := .active }

/-- The heap after the first 64-byte lifecycle: byte 0 written through the left
child and byte 40 through the right child. -/
def firstSnapshot : List UInt8 :=
  [7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The heap after both lifecycles: the first cycle's bytes at 0 and 40, plus
the second cycle's bytes at 1 and 33. -/
def secondSnapshot : List UInt8 :=
  [7, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 13, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Write a byte through an active whole-share fragment of a read--write
ceiling. The access name must be a current leaf. -/
def State.write (s : State) (id : CapId) (i : Nat) (v : UInt8) : Option State :=
  match s.forest.findLeaf? id with
  | none => none
  | some c =>
      if h : c.state = .active ∧ c.q = s.D ∧ c.ceiling = .readWrite ∧
              c.lo ≤ i ∧ i < c.hi then
        match s.heap.write? s.alloc i v with
        | some h' => some { s with heap := h' }
        | none => none
      else none

/-- A write changes only the heap, so it preserves the reconstruction
invariant. -/
theorem State.write_inv {s s' : State} {id : CapId} {i : Nat} {v : UInt8}
    (h : s.write id i v = some s') (hinv : s.Inv) : s'.Inv := by
  unfold State.write at h
  split at h
  · simp at h
  · split at h
    · split at h
      · rename_i hw
        simp only [Option.some.injEq] at h
        subst s'
        refine ⟨hinv.1, hinv.2.1, ?_⟩
        exact
          { nodeIds_nodup := hinv.2.2.nodeIds_nodup
            issue_covers := hinv.2.2.issue_covers
            retired_absent := hinv.2.2.retired_absent
            restores_issued := hinv.2.2.restores_issued
            borrowers_nodup := hinv.2.2.borrowers_nodup
            lenders_nodup := hinv.2.2.lenders_nodup
            lender_ne_borrower := hinv.2.2.lender_ne_borrower
            dormant_absent := hinv.2.2.dormant_absent
            borrower_not_rule := hinv.2.2.borrower_not_rule
            restore_realized := hinv.2.2.restore_realized
            node_agrees := hinv.2.2.node_agrees
            nested_agrees := hinv.2.2.nested_agrees
            rule_fragments_issued := hinv.2.2.rule_fragments_issued }
      · simp at h
    · simp at h

/-- A write changes only the bytes, not the represented allocation or its
length. -/
theorem State.write_storage {s s' : State} {id : CapId} {i : Nat} {v : UInt8}
    (h : s.write id i v = some s') (hst : s.Storage) : s'.Storage := by
  obtain ⟨xs, hlook, hlen⟩ := hst
  unfold State.write at h
  split at h
  · simp at h
  · split at h
    · cases hw : s.heap.write? s.alloc i v with
      | none => simp [hw] at h
      | some h' =>
          simp only [hw, Option.some.injEq] at h
          subst h
          have hmap : (Heap.lookup? h' s.alloc).map List.length = some s.len := by
            rw [Heap.write_preserves_length hw]
            simp [hlook, hlen]
          cases hl : Heap.lookup? h' s.alloc with
          | none => simp [hl] at hmap
          | some ys => exact ⟨ys, by simpa using hl, by simpa [hl] using hmap⟩
    · simp at h

/-- Borrow a current active fragment: retag its access name and record the
dormant lender's restoration obligation for the same footprint and share. -/
def State.borrow (s : State) (lender borrower : CapId) : Option State :=
  match s.forest.findLeaf? lender with
  | none => none
  | some c =>
      if h : c.state = .active ∧ borrower ∉ s.issued ∧ borrower ∉ s.retired ∧
              borrower ≠ lender then
        match s.forest.retagLeaf lender borrower with
        | none => none
        | some (f', p) =>
            some { s with
              forest := f'
              issued := borrower :: s.issued
              restores :=
                { lender := lender, borrower := borrower, alloc := p.alloc,
                  lo := p.lo, hi := p.hi, q := p.q, ceiling := p.ceiling } :: s.restores }
      else none

/-- Checked spatial subdivision of a current fragment while any sibling loan may
be outstanding. The explicit child intervals must partition the parent, and the
child names must never have been issued or retired. -/
def State.splitSpatial (s : State) (parentId c1 c2 : CapId)
    (lo1 hi1 lo2 hi2 : Nat) : Option State :=
  match s.forest.splitSpatialAt parentId c1 c2 lo1 hi1 lo2 hi2 with
  | none => none
  | some (f', _p) =>
      if h : c1 ∉ s.issued ∧ c2 ∉ s.issued ∧ c1 ∉ s.retired ∧ c2 ∉ s.retired then
        some { s with forest := f', issued := c1 :: c2 :: s.issued }
      else none

/-- Checked fractional subdivision of a current fragment. -/
def State.splitFraction (s : State) (parentId c1 c2 : CapId)
    (q1 q2 : Nat) : Option State :=
  match s.forest.splitFractionAt parentId c1 c2 q1 q2 with
  | none => none
  | some (f', _p) =>
      if h : c1 ∉ s.issued ∧ c2 ∉ s.issued ∧ c1 ∉ s.retired ∧ c2 ∉ s.retired then
        some { s with forest := f', issued := c1 :: c2 :: s.issued }
      else none

/-- Reconstruct a suspended fragment. The operation refuses while either child is
still subdivided or lent, and retires both child access names. -/
def State.reconstruct (s : State) (parentId : CapId) : Option State :=
  match s.forest.reconstructAt parentId with
  | none => none
  | some (f', lf, rf) =>
      some { s with forest := f', retired := lf.id :: rf.id :: s.retired }

/-- Return a borrowed fragment: the resource must be a reconstructed whole
fragment, no loan may descend from it, the borrower name is retired and the
dormant lender name is restored. -/
def State.return (s : State) (borrower : CapId) : Option State :=
  match s.restores.find? (fun r => r.borrower = borrower) with
  | none => none
  | some r =>
      match s.forest.findLeaf? borrower with
      | none => none
      | some c =>
          if h : c.state = .active ∧ c.alloc = r.alloc ∧ c.lo = r.lo ∧
                  c.hi = r.hi ∧ c.q = r.q ∧ c.ceiling = r.ceiling ∧
                  r.lender ∉ s.retired ∧
                  (∀ r' ∈ s.restores, r'.lender ≠ borrower) then
            match s.forest.retagLeaf borrower r.lender with
            | none => none
            | some (f', _) =>
                some { s with
                  forest := f'
                  restores := s.restores.filter (fun x => x.borrower ≠ borrower)
                  retired := borrower :: s.retired }
          else none

/-- A checked spatial subdivision preserves the reconstruction invariant. -/
theorem State.splitSpatial_inv {s s' : State} {parentId c1 c2 : CapId}
    {lo1 hi1 lo2 hi2 : Nat}
    (h : s.splitSpatial parentId c1 c2 lo1 hi1 lo2 hi2 = some s')
    (hinv : s.Inv) : s'.Inv := by
  obtain ⟨hcov, hval, hacct⟩ := hinv
  unfold State.splitSpatial at h
  split at h
  · simp at h
  · rename_i f' p hsplit
    split at h
    · rename_i hfresh
      simp only [Option.some.injEq] at h
      subst h
      have hchildren := Forest.splitSpatialAt_children_ne hsplit
      have hnf1 : c1 ∉ s.forest.nodes.map Leaf.id := by
        intro hm
        obtain ⟨c', hc', hid⟩ := List.mem_map.mp hm
        exact hfresh.1 (hid ▸ hacct.issue_covers c'.id (Forest.node_id_mem_ids hc'))
      have hnf2 : c2 ∉ s.forest.nodes.map Leaf.id := by
        intro hm
        obtain ⟨c', hc', hid⟩ := List.mem_map.mp hm
        exact hfresh.2.1 (hid ▸ hacct.issue_covers c'.id (Forest.node_id_mem_ids hc'))
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        change f'.budget x = s.D
        rw [Forest.splitSpatialAt_budget hsplit x]
        exact hcov x hx
      · exact Forest.splitSpatialAt_valid hsplit hval
      · refine
          { nodeIds_nodup :=
              Forest.splitSpatialAt_nodes_nodup hsplit hacct.nodeIds_nodup hnf1 hnf2 hchildren
            issue_covers := ?_
            retired_absent := ?_
            restores_issued := ?_
            borrowers_nodup := ?_
            lenders_nodup := ?_
            lender_ne_borrower := ?_
            dormant_absent := ?_
            borrower_not_rule := ?_
            restore_realized := ?_
            node_agrees := ?_
            nested_agrees := ?_
            rule_fragments_issued := ?_ }
        · intro id hid
          rcases Forest.splitSpatialAt_ids_mem hsplit hid with ho | ho | ho
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (hacct.issue_covers id ho))
          · exact ho ▸ List.mem_cons_self
          · exact ho ▸ List.mem_cons_of_mem _ List.mem_cons_self
        · intro id hid hret
          obtain ⟨c', hc', hcid⟩ := List.mem_map.mp hid
          rcases Forest.splitSpatialAt_nodes_leaf_mem hsplit hc' with ho | ho | ho
          · exact hacct.retired_absent c'.id (List.mem_map.mpr ⟨c', ho, rfl⟩)
              (by rwa [← hcid] at hret)
          · exact hfresh.2.2.1 (by rwa [← hcid, ho] at hret)
          · exact hfresh.2.2.2 (by rwa [← hcid, ho] at hret)
        · intro r hr
          exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (hacct.restores_issued r hr).1),
            List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (hacct.restores_issued r hr).2)⟩
        · exact hacct.borrowers_nodup
        · exact hacct.lenders_nodup
        · intro r hr
          exact hacct.lender_ne_borrower r hr
        · intro r hr hm
          obtain ⟨c', hc', hcid⟩ := List.mem_map.mp hm
          rcases Forest.splitSpatialAt_nodes_leaf_mem hsplit hc' with ho | ho | ho
          · exact hacct.dormant_absent r hr (List.mem_map.mpr ⟨c', ho, hcid⟩)
          · exact hfresh.1 ((hcid.symm.trans ho) ▸ (hacct.restores_issued r hr).1)
          · exact hfresh.2.1 ((hcid.symm.trans ho) ▸ (hacct.restores_issued r hr).1)
        · intro r hr hm
          rcases Forest.splitSpatialAt_ruleIds_mem hsplit hm with ho | ho | ho
          · exact hacct.borrower_not_rule r hr ho
          · exact hfresh.1 (ho ▸ (hacct.restores_issued r hr).2)
          · exact hfresh.2.1 (ho ▸ (hacct.restores_issued r hr).2)
        · intro r hr
          rcases hacct.restore_realized r hr with ho | ho
          · obtain ⟨c, hc, hcid, hag⟩ := ho
            have hc_id : c.id ∈ f'.nodes.map Leaf.id :=
              Forest.splitSpatialAt_nodes_old hsplit
                (List.mem_map.mpr ⟨c, hc, rfl⟩)
            obtain ⟨c'', hc'', hcid''⟩ := List.mem_map.mp hc_id
            have hcid' : c''.id = r.borrower := hcid''.trans hcid
            have hc''_old : c'' ∈ s.forest.nodes := by
              rcases Forest.splitSpatialAt_nodes_leaf_mem hsplit hc'' with ho | ho | ho
              · exact ho
              · exact absurd (by rw [← ho, hcid']; exact (hacct.restores_issued r hr).2)
                  hfresh.1
              · exact absurd (by rw [← ho, hcid']; exact (hacct.restores_issued r hr).2)
                  hfresh.2.1
            exact Or.inl ⟨c'', hc'', hcid',
              hacct.node_agrees r hr c'' hc''_old hcid'⟩
          · exact Or.inr ho
        · intro r hr c' hc' hcid
          rcases Forest.splitSpatialAt_nodes_leaf_mem hsplit hc' with ho | ho | ho
          · exact hacct.node_agrees r hr c' ho hcid
          · exact absurd (by rw [← ho, hcid]; exact (hacct.restores_issued r hr).2) hfresh.1
          · exact absurd (by rw [← ho, hcid]; exact (hacct.restores_issued r hr).2) hfresh.2.1
        · intro r hr r' hr' hrel
          exact hacct.nested_agrees r hr r' hr' hrel
        · intro id hid
          rcases Forest.splitSpatialAt_ruleIds_mem hsplit hid with ho | ho | ho
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (hacct.rule_fragments_issued id ho))
          · exact ho ▸ List.mem_cons_self
          · exact ho ▸ List.mem_cons_of_mem _ List.mem_cons_self
    · simp at h

/-- A checked fractional subdivision preserves the reconstruction invariant. -/
theorem State.splitFraction_inv {s s' : State} {parentId c1 c2 : CapId}
    {q1 q2 : Nat}
    (h : s.splitFraction parentId c1 c2 q1 q2 = some s')
    (hinv : s.Inv) : s'.Inv := by
  obtain ⟨hcov, hval, hacct⟩ := hinv
  unfold State.splitFraction at h
  split at h
  · simp at h
  · rename_i f' p hsplit
    split at h
    · rename_i hfresh
      simp only [Option.some.injEq] at h
      subst h
      have hchildren := Forest.splitFractionAt_children_ne hsplit
      have hnf1 : c1 ∉ s.forest.nodes.map Leaf.id := by
        intro hm
        obtain ⟨c', hc', hid⟩ := List.mem_map.mp hm
        exact hfresh.1 (hid ▸ hacct.issue_covers c'.id (Forest.node_id_mem_ids hc'))
      have hnf2 : c2 ∉ s.forest.nodes.map Leaf.id := by
        intro hm
        obtain ⟨c', hc', hid⟩ := List.mem_map.mp hm
        exact hfresh.2.1 (hid ▸ hacct.issue_covers c'.id (Forest.node_id_mem_ids hc'))
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        change f'.budget x = s.D
        rw [Forest.splitFractionAt_budget hsplit x]
        exact hcov x hx
      · exact Forest.splitFractionAt_valid hsplit hval
      · refine
          { nodeIds_nodup :=
              Forest.splitFractionAt_nodes_nodup hsplit hacct.nodeIds_nodup hnf1 hnf2 hchildren
            issue_covers := ?_
            retired_absent := ?_
            restores_issued := ?_
            borrowers_nodup := ?_
            lenders_nodup := ?_
            lender_ne_borrower := ?_
            dormant_absent := ?_
            borrower_not_rule := ?_
            restore_realized := ?_
            node_agrees := ?_
            nested_agrees := ?_
            rule_fragments_issued := ?_ }
        · intro id hid
          rcases Forest.splitFractionAt_ids_mem hsplit hid with ho | ho | ho
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (hacct.issue_covers id ho))
          · exact ho ▸ List.mem_cons_self
          · exact ho ▸ List.mem_cons_of_mem _ List.mem_cons_self
        · intro id hid hret
          obtain ⟨c', hc', hcid⟩ := List.mem_map.mp hid
          rcases Forest.splitFractionAt_nodes_leaf_mem hsplit hc' with ho | ho | ho
          · exact hacct.retired_absent c'.id (List.mem_map.mpr ⟨c', ho, rfl⟩)
              (by rwa [← hcid] at hret)
          · exact hfresh.2.2.1 (by rwa [← hcid, ho] at hret)
          · exact hfresh.2.2.2 (by rwa [← hcid, ho] at hret)
        · intro r hr
          exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (hacct.restores_issued r hr).1),
            List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (hacct.restores_issued r hr).2)⟩
        · exact hacct.borrowers_nodup
        · exact hacct.lenders_nodup
        · intro r hr
          exact hacct.lender_ne_borrower r hr
        · intro r hr hm
          obtain ⟨c', hc', hcid⟩ := List.mem_map.mp hm
          rcases Forest.splitFractionAt_nodes_leaf_mem hsplit hc' with ho | ho | ho
          · exact hacct.dormant_absent r hr (List.mem_map.mpr ⟨c', ho, hcid⟩)
          · exact hfresh.1 ((hcid.symm.trans ho) ▸ (hacct.restores_issued r hr).1)
          · exact hfresh.2.1 ((hcid.symm.trans ho) ▸ (hacct.restores_issued r hr).1)
        · intro r hr hm
          rcases Forest.splitFractionAt_ruleIds_mem hsplit hm with ho | ho | ho
          · exact hacct.borrower_not_rule r hr ho
          · exact hfresh.1 (ho ▸ (hacct.restores_issued r hr).2)
          · exact hfresh.2.1 (ho ▸ (hacct.restores_issued r hr).2)
        · intro r hr
          rcases hacct.restore_realized r hr with ho | ho
          · obtain ⟨c, hc, hcid, hag⟩ := ho
            have hc_id : c.id ∈ f'.nodes.map Leaf.id :=
              Forest.splitFractionAt_nodes_old hsplit
                (List.mem_map.mpr ⟨c, hc, rfl⟩)
            obtain ⟨c'', hc'', hcid''⟩ := List.mem_map.mp hc_id
            have hcid' : c''.id = r.borrower := hcid''.trans hcid
            have hc''_old : c'' ∈ s.forest.nodes := by
              rcases Forest.splitFractionAt_nodes_leaf_mem hsplit hc'' with ho | ho | ho
              · exact ho
              · exact absurd (by rw [← ho, hcid']; exact (hacct.restores_issued r hr).2)
                  hfresh.1
              · exact absurd (by rw [← ho, hcid']; exact (hacct.restores_issued r hr).2)
                  hfresh.2.1
            exact Or.inl ⟨c'', hc'', hcid',
              hacct.node_agrees r hr c'' hc''_old hcid'⟩
          · exact Or.inr ho
        · intro r hr c' hc' hcid
          rcases Forest.splitFractionAt_nodes_leaf_mem hsplit hc' with ho | ho | ho
          · exact hacct.node_agrees r hr c' ho hcid
          · exact absurd (by rw [← ho, hcid]; exact (hacct.restores_issued r hr).2) hfresh.1
          · exact absurd (by rw [← ho, hcid]; exact (hacct.restores_issued r hr).2) hfresh.2.1
        · intro r hr r' hr' hrel
          exact hacct.nested_agrees r hr r' hr' hrel
        · intro id hid
          rcases Forest.splitFractionAt_ruleIds_mem hsplit hid with ho | ho | ho
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (hacct.rule_fragments_issued id ho))
          · exact ho ▸ List.mem_cons_self
          · exact ho ▸ List.mem_cons_of_mem _ List.mem_cons_self
    · simp at h

/-- A spatial subdivision frames every outstanding return obligation. -/
theorem State.splitSpatial_frames_restores {s s' : State} {parentId c1 c2 : CapId}
    {lo1 hi1 lo2 hi2 : Nat}
    (h : s.splitSpatial parentId c1 c2 lo1 hi1 lo2 hi2 = some s') :
    s'.restores = s.restores := by
  unfold State.splitSpatial at h
  split at h
  · simp at h
  · rename_i f' p hsplit
    split at h
    · rename_i hfresh
      simp only [Option.some.injEq] at h
      subst h
      rfl
    · simp at h

/-- A fractional subdivision frames every outstanding return obligation. -/
theorem State.splitFraction_frames_restores {s s' : State} {parentId c1 c2 : CapId}
    {q1 q2 : Nat}
    (h : s.splitFraction parentId c1 c2 q1 q2 = some s') :
    s'.restores = s.restores := by
  unfold State.splitFraction at h
  split at h
  · simp at h
  · rename_i f' p hsplit
    split at h
    · rename_i hfresh
      simp only [Option.some.injEq] at h
      subst h
      rfl
    · simp at h

/-- Reconstruction preserves the reconstruction invariant. -/
theorem State.reconstruct_inv {s s' : State} {parentId : CapId}
    (h : s.reconstruct parentId = some s') (hinv : s.Inv) : s'.Inv := by
  obtain ⟨hcov, hval, hacct⟩ := hinv
  unfold State.reconstruct at h
  split at h
  · simp at h
  · rename_i f' lf rf hrec
    simp only [Option.some.injEq] at h
    subst h
    have hsub : ∀ {c : Leaf}, c ∈ f'.nodes → c ∈ s.forest.nodes :=
      fun hc => Forest.reconstructAt_nodes_sub hrec hc
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      change f'.budget x = s.D
      rw [Forest.reconstructAt_budget hrec x]
      exact hcov x hx
    · exact Forest.reconstructAt_valid hrec hval
    · refine
        { nodeIds_nodup := Forest.reconstructAt_nodes_nodup hrec hacct.nodeIds_nodup
          issue_covers := ?_
          retired_absent := ?_
          restores_issued := ?_
          borrowers_nodup := ?_
          lenders_nodup := ?_
          lender_ne_borrower := ?_
          dormant_absent := ?_
          borrower_not_rule := ?_
          restore_realized := ?_
          node_agrees := ?_
          nested_agrees := ?_
          rule_fragments_issued := ?_ }
      · intro id hid
        rcases Forest.ids_mem_nodes_or_ruleIds hid with ho | ho
        · obtain ⟨c, hc, hcid⟩ := List.mem_map.mp ho
          exact hcid ▸ hacct.issue_covers c.id
            (Forest.node_id_mem_ids (hsub hc))
        · exact hacct.issue_covers id
            (Forest.rule_id_mem_ids (Forest.reconstructAt_ruleIds_mem hrec ho))
      · intro id hid hret
        obtain ⟨c', hc', hcid⟩ := List.mem_map.mp hid
        have hremoved := Forest.reconstructAt_removed_not_nodes hrec hacct.nodeIds_nodup
        have hid_ne_l : id ≠ lf.id := by
          intro heq
          exact hremoved.1 (List.mem_map.mpr ⟨c', hc', hcid.trans heq⟩)
        have hid_ne_r : id ≠ rf.id := by
          intro heq
          exact hremoved.2 (List.mem_map.mpr ⟨c', hc', hcid.trans heq⟩)
        rcases List.mem_cons.mp hret with heq | hret
        · exact hid_ne_l heq
        · rcases List.mem_cons.mp hret with heq | hret
          · exact hid_ne_r heq
          · exact hacct.retired_absent c'.id
              (List.mem_map.mpr ⟨c', hsub hc', rfl⟩) (by rwa [← hcid] at hret)
      · intro r hr
        exact hacct.restores_issued r hr
      · exact hacct.borrowers_nodup
      · exact hacct.lenders_nodup
      · intro r hr
        exact hacct.lender_ne_borrower r hr
      · intro r hr hm
        obtain ⟨c', hc', hcid⟩ := List.mem_map.mp hm
        exact hacct.dormant_absent r hr (List.mem_map.mpr ⟨c', hsub hc', hcid⟩)
      · intro r hr hm
        exact hacct.borrower_not_rule r hr (Forest.reconstructAt_ruleIds_mem hrec hm)
      · intro r hr
        rcases hacct.restore_realized r hr with ho | ho
        · obtain ⟨c, hc, hcid, hag⟩ := ho
          have hc' : c ∈ f'.nodes := by
            by_cases hmem : c ∈ f'.nodes
            · exact hmem
            · exfalso
              have hrule := Forest.reconstructAt_nodes_removed_rule hrec hc hmem
              exact hacct.borrower_not_rule r hr (by rw [hcid.symm]; exact hrule)
          exact Or.inl ⟨c, hc', hcid, hag⟩
        · exact Or.inr ho
      · intro r hr c' hc' hcid
        exact hacct.node_agrees r hr c' (hsub hc') hcid
      · intro r hr r' hr' hrel
        exact hacct.nested_agrees r hr r' hr' hrel
      · intro id hid
        exact hacct.rule_fragments_issued id
          (Forest.reconstructAt_ruleIds_mem hrec hid)

/-- Beginning a borrow preserves the reconstruction invariant. -/
theorem State.borrow_inv {s s' : State} {lender borrower : CapId}
    (h : s.borrow lender borrower = some s') (hinv : s.Inv) : s'.Inv := by
  obtain ⟨hcov, hval, hacct⟩ := hinv
  unfold State.borrow at h
  split at h
  · simp at h
  · rename_i c hfind
    obtain ⟨hcleaf, hcid⟩ := Forest.findLeaf?_mem_leaves hfind
    split at h
    · rename_i hok
      split at h
      · simp at h
      · rename_i f' p hretag
        simp only [Option.some.injEq] at h
        subst h
        have hnf : borrower ∉ s.forest.nodes.map Leaf.id := by
          intro hm
          obtain ⟨c', hc', hid⟩ := List.mem_map.mp hm
          exact hok.2.1 (hid ▸ hacct.issue_covers c'.id (Forest.node_id_mem_ids hc'))
        have hLenderNode : lender ∈ s.forest.nodes.map Leaf.id :=
          hcid ▸ List.mem_map.mpr ⟨c, Forest.mem_nodes_of_mem_leaves hcleaf, rfl⟩
        have hLenderIssued : lender ∈ s.issued :=
          hacct.issue_covers lender
            (hcid ▸ Forest.node_id_mem_ids (Forest.mem_nodes_of_mem_leaves hcleaf))
        have hne : borrower ≠ lender := hok.2.2.2
        refine ⟨?_, ?_, ?_⟩
        · intro x hx
          change f'.budget x = s.D
          rw [Forest.retagLeaf_budget hretag x]
          exact hcov x hx
        · exact Forest.retagLeaf_valid hretag hval
        · refine
            { nodeIds_nodup :=
                Forest.retagLeaf_nodes_nodup hretag hacct.nodeIds_nodup hnf
              issue_covers := ?_
              retired_absent := ?_
              restores_issued := ?_
              borrowers_nodup := ?_
              lenders_nodup := ?_
              lender_ne_borrower := ?_
              dormant_absent := ?_
              borrower_not_rule := ?_
              restore_realized := ?_
              node_agrees := ?_
              nested_agrees := ?_
              rule_fragments_issued := ?_ }
          · intro id hid
            rcases Forest.retagLeaf_ids_mem hretag hid with ho | ho
            · exact List.mem_cons_of_mem _ (hacct.issue_covers id ho)
            · exact ho ▸ List.mem_cons_self
          · intro id hid hret
            obtain ⟨c', hc', hcid'⟩ := List.mem_map.mp hid
            rcases Forest.retagLeaf_nodes_cases hretag hc' with ho | ho
            · exact hacct.retired_absent c'.id
                (List.mem_map.mpr ⟨c', ho, rfl⟩) (by rwa [← hcid'] at hret)
            · exact hok.2.2.1 (by rwa [← hcid', ho] at hret)
          · intro r hr
            rcases List.mem_cons.mp hr with rfl | hr
            · exact ⟨List.mem_cons_of_mem _ hLenderIssued, List.mem_cons_self⟩
            · exact ⟨List.mem_cons_of_mem _ (hacct.restores_issued r hr).1,
                List.mem_cons_of_mem _ (hacct.restores_issued r hr).2⟩
          · refine List.nodup_cons.mpr ⟨?_, hacct.borrowers_nodup⟩
            intro hm
            obtain ⟨r', hr', hbr⟩ := List.mem_map.mp hm
            have hbr' : r'.borrower = borrower := by simpa using hbr
            exact hok.2.1 (hbr' ▸ (hacct.restores_issued r' hr').2)
          · refine List.nodup_cons.mpr ⟨?_, hacct.lenders_nodup⟩
            intro hm
            obtain ⟨r', hr', hlr⟩ := List.mem_map.mp hm
            exact hacct.dormant_absent r' hr' (hlr ▸ hLenderNode)
          · intro r hr
            rcases List.mem_cons.mp hr with rfl | hr
            · intro heq; exact hne heq.symm
            · exact hacct.lender_ne_borrower r hr
          · intro r hr hm
            rcases List.mem_cons.mp hr with rfl | hr
            · exact Forest.retagLeaf_nodes_id_absent hretag hacct.nodeIds_nodup hne hm
            · obtain ⟨c', hc', hcid'⟩ := List.mem_map.mp hm
              rcases Forest.retagLeaf_nodes_cases hretag hc' with ho | ho
              · exact hacct.dormant_absent r hr (List.mem_map.mpr ⟨c', ho, hcid'⟩)
              · have hc'id : c'.id = borrower := by rw [ho]
                have hlend : r.lender = borrower := hcid'.symm.trans hc'id
                exact hok.2.1 (by rw [← hlend]; exact (hacct.restores_issued r hr).1)
          · intro r hr hm
            rcases List.mem_cons.mp hr with rfl | hr
            · exact hok.2.1 (hacct.rule_fragments_issued borrower
                (Forest.retagLeaf_ruleIds_mem hretag hm))
            · exact hacct.borrower_not_rule r hr (Forest.retagLeaf_ruleIds_mem hretag hm)
          · intro r hr
            rcases List.mem_cons.mp hr with rfl | hr
            · exact Or.inl ⟨{ p with id := borrower }, Forest.retagLeaf_newnode_mem hretag,
                rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
            · rcases hacct.restore_realized r hr with ho | ho
              · obtain ⟨c', hc', hcid', hag⟩ := ho
                by_cases hcl : c'.id = lender
                · exact Or.inr ⟨_, List.mem_cons_self, hcl.symm.trans hcid'⟩
                · exact Or.inl ⟨c', Forest.retagLeaf_nodes_old_mem hretag hc'
                    (fun heq => hcl heq), hcid', hag⟩
              · obtain ⟨r', hr', hrel⟩ := ho
                exact Or.inr ⟨r', List.mem_cons_of_mem _ hr', hrel⟩
          · intro r hr c' hc' hcid'
            rcases List.mem_cons.mp hr with rfl | hr
            · rcases Forest.retagLeaf_nodes_cases hretag hc' with ho | ho
              · have hcid'' : c'.id = borrower := by simpa using hcid'
                exact absurd (by rw [← hcid'']; exact
                  hacct.issue_covers c'.id (Forest.node_id_mem_ids ho)) hok.2.1
              · rw [ho]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
            · rcases Forest.retagLeaf_nodes_cases hretag hc' with ho | ho
              · exact hacct.node_agrees r hr c' ho hcid'
              · have hc'id : c'.id = borrower := by rw [ho]
                have hrb : r.borrower = borrower := by
                  have := hcid'.symm.trans hc'id; simpa using this
                exact absurd (by rw [← hrb]; exact (hacct.restores_issued r hr).2)
                  hok.2.1
          · intro r hr r' hr' hrel
            rcases List.mem_cons.mp hr with rfl | hr
            · rcases List.mem_cons.mp hr' with rfl | hr'
              · exact absurd (by simpa using hrel) (Ne.symm hne)
              · have hrel' : r'.lender = borrower := by simpa using hrel
                exact absurd (hrel' ▸ (hacct.restores_issued r' hr').1) hok.2.1
            · rcases List.mem_cons.mp hr' with rfl | hr'
              · obtain ⟨hp_id, hpnode⟩ := Forest.retagLeaf_found hretag
                have hcnode : c ∈ s.forest.nodes :=
                  Forest.mem_nodes_of_mem_leaves hcleaf
                have hpc : p = c := Forest.eq_of_mem_of_map_nodup hacct.nodeIds_nodup
                  hpnode hcnode (hp_id.trans hcid.symm)
                have hrborrow : r.borrower = lender := hrel.symm
                have hag : r.Agrees c := hacct.node_agrees r hr c hcnode
                  (by rw [hrborrow, hcid])
                rw [hpc]
                exact ⟨hag.1, hag.2.1, hag.2.2.1, hag.2.2.2.1, hag.2.2.2.2⟩
              · exact hacct.nested_agrees r hr r' hr' hrel
          · intro id hid
            exact List.mem_cons_of_mem _
              (hacct.rule_fragments_issued id (Forest.retagLeaf_ruleIds_mem hretag hid))
    · simp at h

/-- Returning a borrow preserves the reconstruction invariant. -/
theorem State.return_inv {s s' : State} {borrower : CapId}
    (h : s.return borrower = some s') (hinv : s.Inv) : s'.Inv := by
  obtain ⟨hcov, hval, hacct⟩ := hinv
  unfold State.return at h
  split at h
  · simp at h
  · rename_i r hrestore
    split at h
    · simp at h
    · rename_i c hleaf
      obtain ⟨hcleaf, hcid⟩ := Forest.findLeaf?_mem_leaves hleaf
      split at h
      · rename_i hok
        split at h
        · simp at h
        · rename_i f' p hretag
          simp only [Option.some.injEq] at h
          subst h
          have hrmem : r ∈ s.restores := List.mem_of_find?_eq_some hrestore
          have hrb' : r.borrower = borrower := by
            have := List.find?_some hrestore
            simpa using this
          have hne : r.lender ≠ borrower := hok.2.2.2.2.2.2.2 r hrmem
          have hnf : r.lender ∉ s.forest.nodes.map Leaf.id :=
            hacct.dormant_absent r hrmem
          have hcnode : c ∈ s.forest.nodes := Forest.mem_nodes_of_mem_leaves hcleaf
          have hrc : r.Agrees c :=
            ⟨hok.2.1.symm, hok.2.2.1.symm, hok.2.2.2.1.symm,
             hok.2.2.2.2.1.symm, hok.2.2.2.2.2.1.symm⟩
          refine ⟨?_, ?_, ?_⟩
          · intro x hx
            change f'.budget x = s.D
            rw [Forest.retagLeaf_budget hretag x]
            exact hcov x hx
          · exact Forest.retagLeaf_valid hretag hval
          · refine
              { nodeIds_nodup :=
                  Forest.retagLeaf_nodes_nodup hretag hacct.nodeIds_nodup hnf
                issue_covers := ?_
                retired_absent := ?_
                restores_issued := ?_
                borrowers_nodup := ?_
                lenders_nodup := ?_
                lender_ne_borrower := ?_
                dormant_absent := ?_
                borrower_not_rule := ?_
                restore_realized := ?_
                node_agrees := ?_
                nested_agrees := ?_
                rule_fragments_issued := ?_ }
            · intro id hid
              rcases Forest.retagLeaf_ids_mem hretag hid with ho | ho
              · exact hacct.issue_covers id ho
              · exact ho ▸ (hacct.restores_issued r hrmem).1
            · intro id hid hret
              have hborrower_absent : borrower ∉ f'.nodes.map Leaf.id :=
                Forest.retagLeaf_nodes_id_absent hretag hacct.nodeIds_nodup hne
              have hid_ne_borrower : id ≠ borrower :=
                fun heq => hborrower_absent (heq ▸ hid)
              obtain ⟨c', hc', hcid'⟩ := List.mem_map.mp hid
              rcases List.mem_cons.mp hret with heq | hret
              · exact hid_ne_borrower heq
              · rcases Forest.retagLeaf_nodes_cases hretag hc' with ho | ho
                · exact hacct.retired_absent c'.id (List.mem_map.mpr ⟨c', ho, rfl⟩)
                    (by rwa [← hcid'] at hret)
                · exact hok.2.2.2.2.2.2.1 (by rwa [← hcid', ho] at hret)
            · intro r' hr'
              exact hacct.restores_issued r' (List.mem_filter.mp hr').1
            · exact List.Sublist.nodup
                (List.Sublist.map Restore.borrower
                  (List.filter_sublist (l := s.restores)
                    (p := fun x => x.borrower ≠ borrower)))
                hacct.borrowers_nodup
            · exact List.Sublist.nodup
                (List.Sublist.map Restore.lender
                  (List.filter_sublist (l := s.restores)
                    (p := fun x => x.borrower ≠ borrower)))
                hacct.lenders_nodup
            · intro r' hr'
              exact hacct.lender_ne_borrower r' (List.mem_filter.mp hr').1
            · intro r' hr' hm
              obtain ⟨hr'_old, hnb⟩ := List.mem_filter.mp hr'
              have hnb' : r'.borrower ≠ borrower := by simpa using hnb
              obtain ⟨c', hc', hcid'⟩ := List.mem_map.mp hm
              rcases Forest.retagLeaf_nodes_cases hretag hc' with ho | ho
              · exact hacct.dormant_absent r' hr'_old (List.mem_map.mpr ⟨c', ho, hcid'⟩)
              · have hc'id : c'.id = r.lender := by rw [ho]
                have hr'lend : r'.lender = r.lender := hcid'.symm.trans hc'id
                have hne' : r' ≠ r := fun heq => hnb' (by rw [heq]; exact hrb')
                exact absurd hr'lend
                  (Forest.ne_of_map_nodup hacct.lenders_nodup hr'_old hrmem hne')
            · intro r' hr' hm
              obtain ⟨hr'_old, _⟩ := List.mem_filter.mp hr'
              exact hacct.borrower_not_rule r' hr'_old
                (Forest.retagLeaf_ruleIds_mem hretag hm)
            · intro r' hr'
              obtain ⟨hr'_old, hnb⟩ := List.mem_filter.mp hr'
              have hnb' : r'.borrower ≠ borrower := by simpa using hnb
              rcases hacct.restore_realized r' hr'_old with ho | ho
              · obtain ⟨c'', hc'', hcid'', hag⟩ := ho
                exact Or.inl ⟨c'', Forest.retagLeaf_nodes_old_mem hretag hc''
                  (fun heq => hnb' (hcid''.symm.trans heq)), hcid'', hag⟩
              · obtain ⟨r'', hr'', hrel⟩ := ho
                by_cases hr''r : r'' = r
                · have hs : r'.SameResource r :=
                    hacct.nested_agrees r' hr'_old r hrmem (by rw [← hr''r]; exact hrel)
                  obtain ⟨hp_id, hpnode⟩ := Forest.retagLeaf_found hretag
                  have hpc : p = c := Forest.eq_of_mem_of_map_nodup hacct.nodeIds_nodup
                    hpnode hcnode (hp_id.trans hcid.symm)
                  have hrc'' : r''.Agrees c := by rw [hr''r]; exact hrc
                  refine Or.inl ⟨{ p with id := r.lender },
                    Forest.retagLeaf_newnode_mem hretag, ?_, ?_⟩
                  · show r.lender = r'.borrower
                    rw [← hr''r]; exact hrel
                  · rw [hpc]
                    exact Restore.Agrees.of_sameResource (by rw [hr''r]; exact hs.symm) hrc''
                · have hnb'' : r''.borrower ≠ borrower := by
                    have hneq : r''.borrower ≠ r.borrower :=
                      Forest.ne_of_map_nodup hacct.borrowers_nodup hr'' hrmem
                        (fun heq => hr''r heq)
                    rwa [hrb'] at hneq
                  exact Or.inr ⟨r'', List.mem_filter.mpr ⟨hr'', by simpa using hnb''⟩,
                    hrel⟩
            · intro r' hr' c' hc' hcid'
              obtain ⟨hr'_old, hnb⟩ := List.mem_filter.mp hr'
              have hnb' : r'.borrower ≠ borrower := by simpa using hnb
              rcases Forest.retagLeaf_nodes_cases hretag hc' with ho | ho
              · exact hacct.node_agrees r' hr'_old c' ho hcid'
              · have hc'id : c'.id = r.lender := by rw [ho]
                have hrel : r.lender = r'.borrower := hc'id.symm.trans hcid'
                have hs : r'.SameResource r :=
                  hacct.nested_agrees r' hr'_old r hrmem hrel
                obtain ⟨hp_id, hpnode⟩ := Forest.retagLeaf_found hretag
                have hpc : p = c := Forest.eq_of_mem_of_map_nodup hacct.nodeIds_nodup
                  hpnode hcnode (hp_id.trans hcid.symm)
                rw [ho, hpc]
                exact Restore.Agrees.of_sameResource hs.symm hrc
            · intro r' hr' r'' hr'' hrel
              exact hacct.nested_agrees r' (List.mem_filter.mp hr').1 r''
                (List.mem_filter.mp hr'').1 hrel
            · intro id hid
              exact hacct.rule_fragments_issued id
                (Forest.retagLeaf_ruleIds_mem hretag hid)
      · simp at h

/-- Beginning a borrow leaves the represented heap, allocation and length
unchanged. -/
theorem State.borrow_storage {s s' : State} {lender borrower : CapId}
    (h : s.borrow lender borrower = some s') (hst : s.Storage) : s'.Storage := by
  obtain ⟨xs, hlook, hlen⟩ := hst
  unfold State.borrow at h
  split at h
  · simp at h
  · rename_i c hfind
    split at h
    · rename_i hok
      split at h
      · simp at h
      · rename_i f' p hretag
        simp only [Option.some.injEq] at h
        subst h
        exact State.Storage.of_heap rfl rfl rfl ⟨xs, hlook, hlen⟩
    · simp at h

/-- A spatial subdivision leaves the represented heap, allocation and length
unchanged. -/
theorem State.splitSpatial_storage {s s' : State} {parentId c1 c2 : CapId}
    {lo1 hi1 lo2 hi2 : Nat}
    (h : s.splitSpatial parentId c1 c2 lo1 hi1 lo2 hi2 = some s')
    (hst : s.Storage) : s'.Storage := by
  obtain ⟨xs, hlook, hlen⟩ := hst
  unfold State.splitSpatial at h
  split at h
  · simp at h
  · rename_i f' p hsplit
    split at h
    · rename_i hfresh
      simp only [Option.some.injEq] at h
      subst h
      exact State.Storage.of_heap rfl rfl rfl ⟨xs, hlook, hlen⟩
    · simp at h

/-- A fractional subdivision leaves the represented heap, allocation and length
unchanged. -/
theorem State.splitFraction_storage {s s' : State} {parentId c1 c2 : CapId}
    {q1 q2 : Nat}
    (h : s.splitFraction parentId c1 c2 q1 q2 = some s')
    (hst : s.Storage) : s'.Storage := by
  obtain ⟨xs, hlook, hlen⟩ := hst
  unfold State.splitFraction at h
  split at h
  · simp at h
  · rename_i f' p hsplit
    split at h
    · rename_i hfresh
      simp only [Option.some.injEq] at h
      subst h
      exact State.Storage.of_heap rfl rfl rfl ⟨xs, hlook, hlen⟩
    · simp at h

/-- Reconstruction leaves the represented heap, allocation and length
unchanged. -/
theorem State.reconstruct_storage {s s' : State} {parentId : CapId}
    (h : s.reconstruct parentId = some s') (hst : s.Storage) : s'.Storage := by
  obtain ⟨xs, hlook, hlen⟩ := hst
  unfold State.reconstruct at h
  split at h
  · simp at h
  · rename_i f' lf rf hrec
    simp only [Option.some.injEq] at h
    subst h
    exact State.Storage.of_heap rfl rfl rfl ⟨xs, hlook, hlen⟩

/-- Returning a borrow leaves the represented heap, allocation and length
unchanged. -/
theorem State.return_storage {s s' : State} {borrower : CapId}
    (h : s.return borrower = some s') (hst : s.Storage) : s'.Storage := by
  obtain ⟨xs, hlook, hlen⟩ := hst
  unfold State.return at h
  split at h
  · simp at h
  · rename_i r hrestore
    split at h
    · simp at h
    · rename_i c hleaf
      split at h
      · rename_i hok
        split at h
        · simp at h
        · rename_i f' p hretag
          simp only [Option.some.injEq] at h
          subst h
          exact State.Storage.of_heap rfl rfl rfl ⟨xs, hlook, hlen⟩
      · simp at h

/-- A return is refused while the borrowed name is not a current leaf, in
particular before the borrowed resource has been reconstructed. -/
theorem State.return_none_of_no_leaf {s : State} {borrower : CapId}
    (h : s.forest.findLeaf? borrower = none) : s.return borrower = none := by
  unfold State.return
  split
  · rfl
  · rename_i r _
    rw [h]

/-- A split is refused if the child name has already been issued. -/
theorem State.splitSpatial_none_of_issued {s : State} {parentId c1 c2 : CapId}
    {lo1 hi1 lo2 hi2 : Nat} (h : c1 ∈ s.issued) :
    s.splitSpatial parentId c1 c2 lo1 hi1 lo2 hi2 = none := by
  unfold State.splitSpatial
  split
  · rfl
  · rename_i f' p hsplit
    split
    · rename_i hfresh
      exact (hfresh.1 h).elim
    · rfl

/-- A fractional split is refused if the child name has been retired. -/
theorem State.splitFraction_none_of_retired {s : State} {parentId c1 c2 : CapId}
    {q1 q2 : Nat} (h : c1 ∈ s.retired) :
    s.splitFraction parentId c1 c2 q1 q2 = none := by
  unfold State.splitFraction
  split
  · rfl
  · rename_i f' p hsplit
    split
    · rename_i hfresh
      exact (hfresh.2.2.1 h).elim
    · rfl

/-- The current allocation-wide world split guard refuses a split while any loan
on the allocation is outstanding. This is the guard the reconstruction model
replaces: it excludes a borrowed range's independent sibling as well as the
borrowed range itself. -/
theorem World.splitAtChecked_refuses_with_loan {w : World} {a : AllocId}
    {id id1 id2 : CapId} {k : Nat}
    (h : ∃ l ∈ w.ctx.loans.loans, l.alloc = a) :
    (w.splitAtChecked a id id1 id2 k).isOk = false := by
  obtain ⟨l, hmem, halloc⟩ := h
  unfold World.splitAtChecked
  split
  · rename_i hnone
    rfl
  · rename_i o _
    have hnot : ¬ (∀ l ∈ w.ctx.loans.loans, l.alloc ≠ a) := by
      intro hforall
      exact (hforall l hmem) halloc
    simp only [hnot, if_false]
    rfl

/-- A dormant lender is not a current leaf: an authority name awaiting return
cannot be used to access the resource. -/
theorem State.Accounts.dormant_not_current {s : State} (h : s.Accounts)
    {r : Restore} (hr : r ∈ s.restores) : s.forest.findLeaf? r.lender = none := by
  cases hf : s.forest.findLeaf? r.lender with
  | none => rfl
  | some c =>
      obtain ⟨hc, hcid⟩ := Forest.findLeaf?_mem_leaves hf
      exact absurd hcid.symm (State.Accounts.dormant_not_leaves h hr hc)

/-- A retired name is not a current leaf: retirement cannot be undone by using an
old handle. -/
theorem State.Accounts.retired_not_current {s : State} (h : s.Accounts)
    {id : CapId} (hid : id ∈ s.retired) : s.forest.findLeaf? id = none := by
  cases hf : s.forest.findLeaf? id with
  | none => rfl
  | some c =>
      obtain ⟨hc, hcid⟩ := Forest.findLeaf?_mem_leaves hf
      exact absurd (hcid.symm ▸ hid) (State.Accounts.retired_not_leaves h hc)

/-- Appending a restoration record that names an unissued party, or whose
borrower is a live rule fragment, breaks the accounting invariant. -/
theorem State.Accounts.cons_restore_not_accounts {s : State} (h : s.Accounts)
    {r : Restore}
    (hnot : r.lender ∉ s.issued ∨ r.borrower ∉ s.issued ∨
      r.borrower ∈ s.forest.ruleIds) :
    ¬ ({ s with restores := r :: s.restores } : State).Accounts := by
  intro hc
  have hr : r ∈ ({ s with restores := r :: s.restores } : State).restores := by simp
  rcases hnot with hnot | hnot | hnot
  · exact hnot (hc.restores_issued r hr).1
  · exact hnot (hc.restores_issued r hr).2
  · exact (hc.borrower_not_rule r hr) hnot

end Reconstruction

end Cap
