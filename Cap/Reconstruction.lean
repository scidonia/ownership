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

/-- The reconstruction invariant: the frontier is covered and every recorded
rule is checked. -/
def State.Inv (s : State) : Prop :=
  s.Covered ∧ s.forest.Valid

/-- A whole live allocation satisfies the reconstruction invariant. -/
theorem State.initial_inv (a : AllocId) (n D : Nat) (pos : 0 < D)
    (rootId disposalId : CapId) : (State.initial a n D pos rootId disposalId).Inv := by
  constructor
  · intro x hx
    change (Forest.leaf
      { id := rootId, alloc := a, lo := 0, hi := n, ordered := Nat.zero_le n,
        q := D, pos := pos, ceiling := .readWrite, state := .active }).budget x = D
    have hx' : 0 ≤ x ∧ x < n := ⟨Nat.zero_le x, hx⟩
    simp [Forest.budget, Leaf.budget, hx']
  · trivial

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
        exact hinv
      · simp at h
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
        | some (f', _) =>
            some { s with
              forest := f'
              issued := borrower :: s.issued
              restores :=
                { lender := lender, borrower := borrower, alloc := c.alloc,
                  lo := c.lo, hi := c.hi, q := c.q, ceiling := c.ceiling } :: s.restores }
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
  obtain ⟨hcov, hval⟩ := hinv
  unfold State.splitSpatial at h
  split at h
  · simp at h
  · rename_i f' p hsplit
    split at h
    · rename_i hfresh
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨?_, ?_⟩
      · intro x hx
        change f'.budget x = s.D
        rw [Forest.splitSpatialAt_budget hsplit x]
        exact hcov x hx
      · exact Forest.splitSpatialAt_valid hsplit hval
    · simp at h

/-- A checked fractional subdivision preserves the reconstruction invariant. -/
theorem State.splitFraction_inv {s s' : State} {parentId c1 c2 : CapId}
    {q1 q2 : Nat}
    (h : s.splitFraction parentId c1 c2 q1 q2 = some s')
    (hinv : s.Inv) : s'.Inv := by
  obtain ⟨hcov, hval⟩ := hinv
  unfold State.splitFraction at h
  split at h
  · simp at h
  · rename_i f' p hsplit
    split at h
    · rename_i hfresh
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨?_, ?_⟩
      · intro x hx
        change f'.budget x = s.D
        rw [Forest.splitFractionAt_budget hsplit x]
        exact hcov x hx
      · exact Forest.splitFractionAt_valid hsplit hval
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
  obtain ⟨hcov, hval⟩ := hinv
  unfold State.reconstruct at h
  split at h
  · simp at h
  · rename_i f' lf rf hrec
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨?_, ?_⟩
    · intro x hx
      change f'.budget x = s.D
      rw [Forest.reconstructAt_budget hrec x]
      exact hcov x hx
    · exact Forest.reconstructAt_valid hrec hval

/-- Beginning a borrow preserves the reconstruction invariant. -/
theorem State.borrow_inv {s s' : State} {lender borrower : CapId}
    (h : s.borrow lender borrower = some s') (hinv : s.Inv) : s'.Inv := by
  obtain ⟨hcov, hval⟩ := hinv
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
        refine ⟨?_, ?_⟩
        · intro x hx
          change f'.budget x = s.D
          rw [Forest.retagLeaf_budget hretag x]
          exact hcov x hx
        · exact Forest.retagLeaf_valid hretag hval
    · simp at h

/-- Returning a borrow preserves the reconstruction invariant. -/
theorem State.return_inv {s s' : State} {borrower : CapId}
    (h : s.return borrower = some s') (hinv : s.Inv) : s'.Inv := by
  obtain ⟨hcov, hval⟩ := hinv
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
          refine ⟨?_, ?_⟩
          · intro x hx
            change f'.budget x = s.D
            rw [Forest.retagLeaf_budget hretag x]
            exact hcov x hx
          · exact Forest.retagLeaf_valid hretag hval
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

end Reconstruction

end Cap
