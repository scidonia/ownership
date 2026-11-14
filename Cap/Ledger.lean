/-
The budget algebra of the ledger.

A capability is a leaf of a decomposition tree: a footprint, a share, a ceiling
and a state. Internal nodes record fractional and spatial splits; their budget is
the sum of their children's, so a split preserves the byte budget and a join
restores it. This is stage 2a: the tree and its arithmetic. The context (forest,
disposal entitlement, lifetimes, loans) and the executable transitions are the
next slice, and the `Realizes` invariant is stated over this budget.

Theorems:
* `frac_split_budget` / `frac_join_budget` — a fractional split and its sibling
  join preserve the budget at every byte.
* `spatial_split_budget` / `spatial_join_budget` — a spatial split at `k` and its
  join preserve the budget; the children partition the parent's range.
-/
import Cap.Id
import Cap.Bytes

namespace Cap

inductive Ceiling where
  | readOnly
  | readWrite
deriving DecidableEq, Repr

inductive CapState where
  | active
  | retired
  | consumed
deriving DecidableEq, Repr

structure Leaf where
  id : CapId
  alloc : AllocId
  lo : Nat
  hi : Nat
  ordered : lo ≤ hi
  q : Nat
  pos : 0 < q
  ceiling : Ceiling
  state : CapState

def Leaf.budget (c : Leaf) (x : Nat) : Nat :=
  if c.state = .consumed then 0
  else if c.lo ≤ x ∧ x < c.hi then c.q else 0

inductive Tree where
  | leaf (c : Leaf)
  | frac (id : CapId) (l r : Tree)
  | spatial (id : CapId) (l r : Tree)

namespace Tree

def budget (x : Nat) : Tree → Nat
  | leaf c => c.budget x
  | frac _ l r => l.budget x + r.budget x
  | spatial _ l r => l.budget x + r.budget x

end Tree

/-- A fractional split replaces one leaf's budget by its two children's. -/
theorem frac_split_budget {c c1 c2 : Leaf} {x : Nat}
    (hstate1 : c1.state = c.state) (hstate2 : c2.state = c.state)
    (hlo1 : c1.lo = c.lo) (hhi1 : c1.hi = c.hi)
    (hlo2 : c2.lo = c.lo) (hhi2 : c2.hi = c.hi)
    (hq : c1.q + c2.q = c.q) :
    (Tree.frac c1.id (.leaf c1) (.leaf c2)).budget x = (Tree.leaf c).budget x := by
  by_cases hc : c.state = .consumed
  · simp [Tree.budget, Leaf.budget, hstate1, hstate2, hc]
  · by_cases hx : c.lo ≤ x ∧ x < c.hi
    · have hx1 : c1.lo ≤ x ∧ x < c1.hi := by rw [hlo1, hhi1]; exact hx
      have hx2 : c2.lo ≤ x ∧ x < c2.hi := by rw [hlo2, hhi2]; exact hx
      simp [Tree.budget, Leaf.budget, hstate1, hstate2, hc, hx, hx1, hx2]
      omega
    · have hx1 : ¬ (c1.lo ≤ x ∧ x < c1.hi) := by rw [hlo1, hhi1]; exact hx
      have hx2 : ¬ (c2.lo ≤ x ∧ x < c2.hi) := by rw [hlo2, hhi2]; exact hx
      simp [Tree.budget, Leaf.budget, hstate1, hstate2, hc, hx, hx1, hx2]

/-- A spatial split at `k`: the children partition the parent's range. -/
theorem spatial_split_budget {c c1 c2 : Leaf} {x k : Nat}
    (hstate1 : c1.state = c.state) (hstate2 : c2.state = c.state)
    (hlo1 : c1.lo = c.lo) (hhi1 : c1.hi = k)
    (hlo2 : c2.lo = k) (hhi2 : c2.hi = c.hi)
    (hq1 : c1.q = c.q) (hq2 : c2.q = c.q)
    (hk1 : c.lo ≤ k) (hk2 : k ≤ c.hi) :
    (Tree.spatial c1.id (.leaf c1) (.leaf c2)).budget x = (Tree.leaf c).budget x := by
  by_cases hc : c.state = .consumed
  · simp [Tree.budget, Leaf.budget, hstate1, hstate2, hc]
  · by_cases hx : c.lo ≤ x ∧ x < c.hi
    · by_cases hxk : x < k
      · have hx1 : c1.lo ≤ x ∧ x < c1.hi := by rw [hlo1, hhi1]; exact ⟨hx.1, hxk⟩
        have hx2 : ¬ (c2.lo ≤ x ∧ x < c2.hi) := by rw [hlo2, hhi2]; exact fun h => by omega
        simp [Tree.budget, Leaf.budget, hstate1, hstate2, hc, hx, hx1, hx2, hq1]
      · have hx1 : ¬ (c1.lo ≤ x ∧ x < c1.hi) := by rw [hlo1, hhi1]; exact fun h => by omega
        have hx2 : c2.lo ≤ x ∧ x < c2.hi := by rw [hlo2, hhi2]; exact ⟨by omega, hx.2⟩
        simp [Tree.budget, Leaf.budget, hstate1, hstate2, hc, hx, hx1, hx2, hq2]
    · have hx1 : ¬ (c1.lo ≤ x ∧ x < c1.hi) := by rw [hlo1, hhi1]; exact fun h => hx ⟨h.1, by omega⟩
      have hx2 : ¬ (c2.lo ≤ x ∧ x < c2.hi) := by rw [hlo2, hhi2]; exact fun h => hx ⟨by omega, h.2⟩
      simp [Tree.budget, Leaf.budget, hstate1, hstate2, hc, hx, hx1, hx2]

/-- Joining the two children restores the parent's budget (sibling join). -/
theorem frac_join_budget {c c1 c2 : Leaf} {x : Nat}
    (hstate1 : c1.state = c.state) (hstate2 : c2.state = c.state)
    (hlo1 : c1.lo = c.lo) (hhi1 : c1.hi = c.hi)
    (hlo2 : c2.lo = c.lo) (hhi2 : c2.hi = c.hi)
    (hq : c.q = c1.q + c2.q) :
    (Tree.leaf c).budget x = (Tree.frac c1.id (.leaf c1) (.leaf c2)).budget x := by
  rw [frac_split_budget hstate1 hstate2 hlo1 hhi1 hlo2 hhi2 (by omega)]

theorem spatial_join_budget {c c1 c2 : Leaf} {x k : Nat}
    (hstate1 : c1.state = c.state) (hstate2 : c2.state = c.state)
    (hlo1 : c1.lo = c.lo) (hhi1 : c1.hi = k)
    (hlo2 : c2.lo = k) (hhi2 : c2.hi = c.hi)
    (hq1 : c1.q = c.q) (hq2 : c2.q = c.q)
    (hk1 : c.lo ≤ k) (hk2 : k ≤ c.hi) :
    (Tree.leaf c).budget x = (Tree.spatial c1.id (.leaf c1) (.leaf c2)).budget x := by
  rw [spatial_split_budget hstate1 hstate2 hlo1 hhi1 hlo2 hhi2 hq1 hq2 hk1 hk2]

/-- Find a leaf by capability id. -/
def Tree.find? (id : CapId) : Tree → Option Leaf
  | .leaf c => if c.id = id then some c else none
  | .frac _ l r =>
    match l.find? id with
    | some c => some c
    | none => r.find? id
  | .spatial _ l r =>
    match l.find? id with
    | some c => some c
    | none => r.find? id

/-- Replace the first leaf with the given id by the tree the function returns. -/
def Tree.replace (id : CapId) (f : Leaf → Tree) : Tree → Tree
  | .leaf c => if c.id = id then f c else .leaf c
  | .frac i l r =>
    match l.find? id with
    | some _ => .frac i (replace id f l) r
    | none => .frac i l (replace id f r)
  | .spatial i l r =>
    match l.find? id with
    | some _ => .spatial i (replace id f l) r
    | none => .spatial i l (replace id f r)

/-- Replacing a leaf preserves the budget at every byte whenever the replacement
has the replaced leaf's budget at that byte. -/
theorem Tree.budget_replace (t : Tree) (id : CapId) (f : Leaf → Tree) (x : Nat)
    (h : ∀ c, t.find? id = some c → (f c).budget x = (Tree.leaf c).budget x) :
    (t.replace id f).budget x = t.budget x := by
  induction t with
  | leaf c =>
    by_cases hc : c.id = id
    · simp [Tree.find?, Tree.replace, hc]
      exact h c (by simp [Tree.find?, hc])
    · simp [Tree.find?, Tree.replace, hc]
  | frac i l r ihl ihr =>
    cases hf : l.find? id with
    | some c =>
      have hl : ∀ c', l.find? id = some c' → (f c').budget x = (Tree.leaf c').budget x := by
        intro c' hc'
        exact h c' (by simp [Tree.find?, hc'])
      simp only [Tree.replace, Tree.budget, hf]
      rw [ihl hl]
    | none =>
      have hr : ∀ c', r.find? id = some c' → (f c').budget x = (Tree.leaf c').budget x := by
        intro c' hc'
        exact h c' (by simp [Tree.find?, hf, hc'])
      simp only [Tree.replace, Tree.budget, hf]
      rw [ihr hr]
  | spatial i l r ihl ihr =>
    cases hf : l.find? id with
    | some c =>
      have hl : ∀ c', l.find? id = some c' → (f c').budget x = (Tree.leaf c').budget x := by
        intro c' hc'
        exact h c' (by simp [Tree.find?, hc'])
      simp only [Tree.replace, Tree.budget, hf]
      rw [ihl hl]
    | none =>
      have hr : ∀ c', r.find? id = some c' → (f c').budget x = (Tree.leaf c').budget x := by
        intro c' hc'
        exact h c' (by simp [Tree.find?, hf, hc'])
      simp only [Tree.replace, Tree.budget, hf]
      rw [ihr hr]

/-- One live allocation: a root decomposition, its length and its disposal
capability. -/
structure Owner where
  alloc : AllocId
  len : Nat
  root : Tree
  disposal : CapId

/-- Every byte of the allocation is fully covered by the frontier. -/
def Owner.Covered (o : Owner) (D : Nat) : Prop :=
  ∀ x, x < o.len → o.root.budget x = D

/-- Replace the first leaf with the given id by `f`. -/
def Owner.split? (o : Owner) (id : CapId) (f : Leaf → Tree) : Option Owner :=
  match o.root.find? id with
  | some _ => some { o with root := o.root.replace id f }
  | none => none

/-- A split preserves coverage when the replacement has the replaced leaf's budget
at every byte. -/
theorem Owner.split_covered {o o' : Owner} {D : Nat} {id : CapId} {f : Leaf → Tree}
    (h : o.split? id f = some o')
    (hb : ∀ c, o.root.find? id = some c → ∀ x, (f c).budget x = (Tree.leaf c).budget x)
    (hcov : o.Covered D) : o'.Covered D := by
  unfold Owner.split? at h
  cases hf : o.root.find? id with
  | none => simp [hf] at h
  | some c =>
    simp [hf] at h
    subst h
    intro x hx
    rw [Tree.budget_replace o.root id f x (by intro c' hc'; exact hb c' hc' x)]
    exact hcov x hx

/-- Allocation: a zeroed buffer of `n` bytes, one root leaf of share `D`, and the
disposal capability. -/
def Owner.init (a : AllocId) (n D : Nat) (pos : 0 < D) (disposal : CapId) : Owner :=
  { alloc := a, len := n, disposal := disposal,
    root := .leaf
      { id := disposal, alloc := a, lo := 0, hi := n, ordered := Nat.zero_le n,
        q := D, pos := pos, ceiling := .readWrite, state := .active } }

theorem Owner.init_covered (a : AllocId) (n D : Nat) (pos : 0 < D) (disposal : CapId) :
    (Owner.init a n D pos disposal).Covered D := by
  intro x hx
  have hx' : 0 ≤ x ∧ x < n := ⟨Nat.zero_le x, hx⟩
  simp [Owner.init, Tree.budget, Leaf.budget, hx']

/-- The write guard: an active leaf of the whole share with a read--write
ceiling, at an index inside its footprint. -/
def Owner.Writable (o : Owner) (D : Nat) (id : CapId) (i : Nat) : Prop :=
  ∃ c, o.root.find? id = some c ∧ c.state = .active ∧ c.q = D ∧
    c.ceiling = .readWrite ∧ c.lo ≤ i ∧ i < c.hi

/-- A readable leaf only needs a positive share, an active state and an index in
range; a read-only ceiling is enough. -/
def Owner.Readable (o : Owner) (id : CapId) (i : Nat) : Prop :=
  ∃ c, o.root.find? id = some c ∧ c.state = .active ∧ 0 < c.q ∧
    c.lo ≤ i ∧ i < c.hi

theorem Owner.writable_share {o : Owner} {D : Nat} {id : CapId} {i : Nat}
    (h : o.Writable D id i) : ∃ c, o.root.find? id = some c ∧ c.q = D := by
  obtain ⟨c, hc, _, hq, _, _, _⟩ := h
  exact ⟨c, hc, hq⟩

theorem Owner.writable_not_shared {o : Owner} {D : Nat} {id : CapId} {i : Nat}
    (h : o.Writable D id i) : ¬ ∃ c, o.root.find? id = some c ∧ c.q < D := by
  obtain ⟨c, hc, _, hq, _, _, _⟩ := h
  rintro ⟨c', hc', hlt⟩
  rw [hc] at hc'
  cases hc'
  omega

/-- The tree produced by splitting `c` into two shares that add to its own. -/
def Leaf.splitFractionTree (c : Leaf) (id1 id2 : CapId) (q1 q2 : Nat)
    (p1 : 0 < q1) (p2 : 0 < q2) : Option Tree :=
  if q1 + q2 = c.q then
    some (.frac id1
      (.leaf { c with id := id1, q := q1, pos := p1 })
      (.leaf { c with id := id2, q := q2, pos := p2 }))
  else none

/-- Fractionally split the owner's leaf `id` into two leaves of shares `q1` and
`q2`, provided they add to the leaf's share. -/
def Owner.splitFraction? (o : Owner) (id id1 id2 : CapId) (q1 q2 : Nat)
    (p1 : 0 < q1) (p2 : 0 < q2) : Option Owner :=
  match o.root.find? id with
  | none => none
  | some c =>
    (c.splitFractionTree id1 id2 q1 q2 p1 p2).map
      (fun t => { o with root := o.root.replace id (fun _ => t) })

theorem Owner.splitFraction_covered {o o' : Owner} {D : Nat} {id id1 id2 : CapId}
    {q1 q2 : Nat} {p1 : 0 < q1} {p2 : 0 < q2}
    (hs : o.splitFraction? id id1 id2 q1 q2 p1 p2 = some o')
    (hcov : o.Covered D) : o'.Covered D := by
  unfold Owner.splitFraction? at hs
  cases hf : o.root.find? id with
  | none => simp [hf] at hs
  | some c =>
    by_cases hq : q1 + q2 = c.q
    · simp [hf, hq, Leaf.splitFractionTree] at hs
      cases hs
      apply Owner.split_covered (o := o) (id := id)
        (f := fun _ => .frac id1
          (.leaf { c with id := id1, q := q1, pos := p1 })
          (.leaf { c with id := id2, q := q2, pos := p2 }))
      · simp [Owner.split?, hf]
      · intro c' hc' x
        have hc'c : c' = c := by
          rw [hf] at hc'
          cases hc'
          rfl
        subst hc'c
        exact frac_split_budget rfl rfl rfl rfl rfl rfl hq
      · exact hcov
    · simp [hf, hq, Leaf.splitFractionTree] at hs

/-- Write a byte through the owner's guard: the caller supplies the guard proof,
and the write is performed on the reference heap at the owner's allocation. -/
def Owner.writeByte? (o : Owner) (D : Nat) (id : CapId) (h : Heap) (i : Nat)
    (v : UInt8) (hw : o.Writable D id i) : Option (Owner × Heap) :=
  match h.write? o.alloc i v with
  | some h' => some (o, h')
  | none => none

theorem Owner.writeByte_sound {o o' : Owner} {h h' : Heap} {D : Nat} {id : CapId}
    {i : Nat} {v : UInt8} {hg : o.Writable D id i}
    (hr : o.writeByte? D id h i v hg = some (o', h')) :
    o' = o ∧ h'.read? o.alloc i = some v := by
  unfold Owner.writeByte? at hr
  cases hb : h.write? o.alloc i v with
  | none => simp [hb] at hr
  | some h'' =>
    simp [hb] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨rfl, Heap.write_get hb⟩

/-- The tree produced by splitting `c` spatially at `k`, when `k` lies in range. -/
def Leaf.splitSpatial? (c : Leaf) (id1 id2 : CapId) (k : Nat) : Option Tree :=
  if h : c.lo ≤ k ∧ k ≤ c.hi then
    some (.spatial id1
      (.leaf { c with id := id1, hi := k, ordered := h.1 })
      (.leaf { c with id := id2, lo := k, ordered := h.2 }))
  else none

theorem Leaf.splitSpatial?_some {c : Leaf} {id1 id2 : CapId} {k : Nat} {t : Tree}
    (h : c.splitSpatial? id1 id2 k = some t) :
    ∃ (h1 : c.lo ≤ k) (h2 : k ≤ c.hi),
      t = .spatial id1
        (.leaf { c with id := id1, hi := k, ordered := h1 })
        (.leaf { c with id := id2, lo := k, ordered := h2 }) := by
  unfold Leaf.splitSpatial? at h
  split at h
  · rename_i hk
    exact ⟨hk.1, hk.2, by simp at h; subst h; rfl⟩
  · simp at h

/-- Spatially split the owner's leaf `id` at `k`. -/
def Owner.splitAt? (o : Owner) (id id1 id2 : CapId) (k : Nat) : Option Owner :=
  match o.root.find? id with
  | none => none
  | some c =>
    (c.splitSpatial? id1 id2 k).map
      (fun t => { o with root := o.root.replace id (fun _ => t) })

theorem Owner.splitAt_covered {o o' : Owner} {D : Nat} {id id1 id2 : CapId} {k : Nat}
    (hs : o.splitAt? id id1 id2 k = some o') (hcov : o.Covered D) : o'.Covered D := by
  unfold Owner.splitAt? at hs
  cases hf : o.root.find? id with
  | none => simp [hf] at hs
  | some c =>
    cases hsp : c.splitSpatial? id1 id2 k with
    | none => simp [hf, hsp] at hs
    | some t =>
      obtain ⟨h1, h2, ht⟩ := Leaf.splitSpatial?_some hsp
      simp [hf, hsp] at hs
      cases hs
      subst ht
      apply Owner.split_covered (o := o) (id := id)
        (f := fun _ => .spatial id1
          (.leaf { c with id := id1, hi := k, ordered := h1 })
          (.leaf { c with id := id2, lo := k, ordered := h2 }))
      · simp [Owner.split?, hf]
      · intro c' hc' x
        have hc'c : c' = c := by
          rw [hf] at hc'
          cases hc'
          rfl
        subst hc'c
        exact spatial_split_budget rfl rfl rfl rfl rfl rfl rfl rfl h1 h2
      · exact hcov

-- Concrete checks: a whole-capability read budget and a spatial split.
namespace LedgerExamples

private def root : Leaf :=
  { id := ⟨0⟩, alloc := ⟨0⟩, lo := 0, hi := 8, ordered := by decide,
    q := 8, pos := by decide, ceiling := .readWrite, state := .active }

private def left : Leaf :=
  { id := ⟨1⟩, alloc := ⟨0⟩, lo := 0, hi := 4, ordered := by decide,
    q := 8, pos := by decide, ceiling := .readWrite, state := .active }

private def right : Leaf :=
  { id := ⟨2⟩, alloc := ⟨0⟩, lo := 4, hi := 8, ordered := by decide,
    q := 8, pos := by decide, ceiling := .readWrite, state := .active }

example : root.budget 3 = 8 := by decide
example : root.budget 8 = 0 := by decide
example : (Tree.spatial ⟨9⟩ (.leaf left) (.leaf right)).budget 5 = 8 := by decide

end LedgerExamples

end Cap
