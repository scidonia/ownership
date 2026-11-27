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

/-- One leaf's resource contains another's: same allocation and ceiling, with the
interval contained and the share no larger. This is the scope a decomposition
transfers to its children; like `SameResource` it says nothing about access
identity, so retagging preserves it. -/
def Leaf.Within (a b : Leaf) : Prop :=
  a.alloc = b.alloc ∧ b.lo ≤ a.lo ∧ a.hi ≤ b.hi ∧ a.ceiling = b.ceiling ∧ a.q ≤ b.q

instance (a b : Leaf) : Decidable (a.Within b) := by
  unfold Leaf.Within
  infer_instance

/-- One leaf's allocation, interval and share lie within a component of
allocation `a`, length `len` and denominator `D`. The empty-range policy is the
disjunction: a fragment may be empty only when the whole allocation is empty, so
a zero-length allocation is admitted and a zero-length fragment inside a
non-empty allocation is not. -/
def Leaf.InScope (a : AllocId) (len D : Nat) (c : Leaf) : Prop :=
  c.alloc = a ∧ c.hi ≤ len ∧ (c.lo < c.hi ∨ len = 0) ∧ c.q ≤ D

/-- Resource containment is reflexive. -/
theorem Leaf.Within.refl (a : Leaf) : a.Within a :=
  ⟨rfl, Nat.le_refl _, Nat.le_refl _, rfl, Nat.le_refl _⟩

/-- Resource containment is transitive. -/
theorem Leaf.Within.trans {a b c : Leaf} (hab : a.Within b) (hbc : b.Within c) :
    a.Within c :=
  ⟨hab.1.trans hbc.1, Nat.le_trans hbc.2.1 hab.2.1,
   Nat.le_trans hab.2.2.1 hbc.2.2.1, hab.2.2.2.1.trans hbc.2.2.2.1,
   Nat.le_trans hab.2.2.2.2 hbc.2.2.2.2⟩

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

/-- Resource agreement is reflexive. -/
theorem Restore.SameResource.refl (r : Restore) : r.SameResource r :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Resource agreement is transitive. -/
theorem Restore.SameResource.trans {r r' r'' : Restore}
    (h : r.SameResource r') (h' : r'.SameResource r'') : r.SameResource r'' :=
  ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.1.trans h'.2.2.1,
   h.2.2.2.1.trans h'.2.2.2.1, h.2.2.2.2.trans h'.2.2.2.2⟩

/-- A return obligation depends on another when it delegates the resource onward:
the other record's lender is this record's borrower. -/
def Restore.Depends (r r' : Restore) : Prop := r'.lender = r.borrower

instance (r r' : Restore) : Decidable (r.Depends r') := by
  unfold Restore.Depends
  infer_instance

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

/-- One suspended decomposition: the checked rule, the suspended parent and the
two current subtrees that must be reconstructed to the rule fragments. The
current subtrees carry their own access names, which retagging may change; the
rule fragments record the resource, not the name. -/
structure Suspension where
  kind : RuleKind
  parent : Leaf
  leftRule : Leaf
  rightRule : Leaf
  left : Forest
  right : Forest

/-- The suspensions of a forest, outermost first. -/
def suspensions : Forest → List Suspension
  | .leaf _ => []
  | .split k p lr rr l r =>
      { kind := k, parent := p, leftRule := lr, rightRule := rr, left := l, right := r } ::
        (l.suspensions ++ r.suspensions)

/-- The rule descriptors of every suspension. -/
def ruleFragments : Forest → List Leaf
  | .leaf _ => []
  | .split _ _ lr rr l r => lr :: rr :: (l.ruleFragments ++ r.ruleFragments)

/-- The left rule fragment of a checked rule lies within the parent's resource. -/
theorem RuleValid.left_within {kind : RuleKind} {p lr rr : Leaf}
    (h : RuleValid kind p lr rr) : lr.Within p := by
  obtain ⟨-, hla, -, hlc, -, -, -, -, -, -, hpart⟩ := h
  cases kind with
  | spatial =>
      obtain ⟨hlo, hhi, hrhi, hql, -⟩ := hpart
      exact ⟨hla, Nat.le_of_eq (hlo.symm),
        Nat.le_trans (Nat.le_of_eq hhi) (Nat.le_trans rr.ordered (Nat.le_of_eq hrhi)),
        hlc, Nat.le_of_eq hql⟩
  | fractional =>
      obtain ⟨hlo, hhi, -, -, -, hq2, hsum⟩ := hpart
      exact ⟨hla, Nat.le_of_eq (hlo.symm), Nat.le_of_eq hhi, hlc, by omega⟩

/-- The right rule fragment of a checked rule lies within the parent's resource. -/
theorem RuleValid.right_within {kind : RuleKind} {p lr rr : Leaf}
    (h : RuleValid kind p lr rr) : rr.Within p := by
  obtain ⟨-, -, hra, -, hrc, -, -, -, -, -, hpart⟩ := h
  cases kind with
  | spatial =>
      obtain ⟨hlo, hhi, hrhi, -, hqr⟩ := hpart
      exact ⟨hra,
        Nat.le_trans (Nat.le_of_eq (hlo.symm)) (Nat.le_trans lr.ordered (Nat.le_of_eq hhi)),
        Nat.le_of_eq hrhi, hrc, Nat.le_of_eq hqr⟩
  | fractional =>
      obtain ⟨-, -, hlo2, hhi2, hq1, -, hsum⟩ := hpart
      exact ⟨hra, Nat.le_of_eq (hlo2.symm), Nat.le_of_eq hhi2, hrc, by omega⟩

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

/-- Every authority node of the subtree — a current leaf or a suspended parent —
lies within the fragment's resource. Rule descriptors are excluded: they are
templates a reconstruction fills, not authority the subtree currently carries. -/
def Inside (f : Forest) (c : Leaf) : Prop := ∀ d ∈ f.nodes, d.Within c

/-- A subtree realizes a recorded resource: its frontier has the resource's share
at every byte, and every authority node it carries lies within the resource's
allocation, interval, ceiling and share. This is the connection between a
suspended parent and what is actually live below it. -/
def Realizes (f : Forest) (c : Leaf) : Prop :=
  (∀ x, f.budget x = (Forest.leaf c).budget x) ∧ f.Inside c

/-- Recursive forest coherence. At every suspension the checked rule holds and
each current child subtree realizes the rule fragment it must be reconstructed
to; the children are themselves coherent. The resource connection is stated by
`Realizes` rather than by identifier equality, so a borrowed or retagged child
survives: restoration records, not names, explain how identities return. -/
def Coherent : Forest → Prop
  | .leaf _ => True
  | .split k p lr rr l r =>
      RuleValid k p lr rr ∧ l.Realizes lr ∧ r.Realizes rr ∧ l.Coherent ∧ r.Coherent

/-- A finite chain of outstanding restoration records from one access name to
another. The empty chain names an identity twice; a record whose lender is the
chain's current endpoint extends the chain to that record's borrower. Following
a chain backwards through `return` is how a borrowed name is recovered. -/
inductive RestoreChain (restores : List Restore) : CapId → CapId → Prop where
  | nil (a : CapId) : RestoreChain restores a a
  | snoc {a b : CapId} (r : Restore) (h : RestoreChain restores a b)
      (hr : r ∈ restores) (hl : r.lender = b) :
      RestoreChain restores a r.borrower

/-- With no outstanding records, a restoration chain can only name one identity
twice. -/
theorem RestoreChain.nil_left {a b : CapId} (h : RestoreChain [] a b) : a = b := by
  cases h with
  | nil => rfl
  | snoc => simp_all

/-- A single outstanding record is a one-step chain. -/
theorem RestoreChain.single {restores : List Restore} {r : Restore}
    (hr : r ∈ restores) : RestoreChain restores r.lender r.borrower :=
  .snoc r (.nil r.lender) hr rfl

/-- A chain through a restoration list is a chain through any list containing it. -/
theorem RestoreChain.mono {restores restores' : List Restore}
    (hsub : ∀ r ∈ restores, r ∈ restores') {a b : CapId}
    (h : RestoreChain restores a b) : RestoreChain restores' a b := by
  induction h with
  | nil => exact .nil _
  | snoc r _ hr hl ih => exact .snoc r ih (hsub _ hr) hl

/-- Chains compose. -/
theorem RestoreChain.trans {restores : List Restore} {a b c : CapId}
    (h : RestoreChain restores a b) (h' : RestoreChain restores b c) :
    RestoreChain restores a c := by
  induction h' with
  | nil => exact h
  | snoc r _ hr hl ih => exact .snoc r ih hr hl

/-- A subtree carries the identity protocol for an expected access name. A leaf
qualifies when its own identity is reachable from the expected name through
outstanding restoration records; a suspension qualifies when its parent identity
is so reachable and its two subtrees in turn recover their own rule fragment
identities. Resource agreement is `Realizes`'s business; this relation tracks
only where the identities a pending reconstruction must recover actually live. -/
inductive Recovers (restores : List Restore) : Forest → CapId → Prop where
  | leaf (c : Leaf) {e : CapId} (h : RestoreChain restores e c.id) :
      Recovers restores (.leaf c) e
  | split (kind : RuleKind) (p lr rr : Leaf) (l r : Forest) {e : CapId}
      (h : RestoreChain restores e p.id)
      (hl : Recovers restores l lr.id) (hr : Recovers restores r rr.id) :
      Recovers restores (.split kind p lr rr l r) e

/-- Every suspension's children recover the rule fragment identities it records,
and every nested suspension does so too. -/
def WellRecovered (restores : List Restore) : Forest → Prop
  | .leaf _ => True
  | .split _ _ lr rr l r =>
      l.Recovers restores lr.id ∧ r.Recovers restores rr.id ∧
      l.WellRecovered restores ∧ r.WellRecovered restores

/-- Identity recovery is monotone in the restoration list. -/
theorem Recovers.mono {restores restores' : List Restore}
    (hsub : ∀ r ∈ restores, r ∈ restores') {f : Forest} {e : CapId}
    (h : f.Recovers restores e) : f.Recovers restores' e := by
  induction h with
  | leaf c hc => exact Forest.Recovers.leaf c (RestoreChain.mono hsub hc)
  | split kind par lrule rrule lf rt hc _ _ ihl ihr =>
      exact Forest.Recovers.split kind par lrule rrule lf rt
        (RestoreChain.mono hsub hc) ihl ihr

/-- Identity recovery is monotone in the restoration relation itself, not only
in the list. -/
theorem Recovers.chainMono {restores restores' : List Restore}
    (hmono : ∀ {a b : CapId}, RestoreChain restores a b → RestoreChain restores' a b)
    {f : Forest} {e : CapId} (h : f.Recovers restores e) : f.Recovers restores' e := by
  induction h with
  | leaf c hc => exact Forest.Recovers.leaf c (hmono hc)
  | split kind par lrule rrule lf rt hc _ _ ihl ihr =>
      exact Forest.Recovers.split kind par lrule rrule lf rt (hmono hc) ihl ihr

/-- Whole-forest recovery is monotone in the restoration relation. -/
theorem WellRecovered.chainMono {restores restores' : List Restore}
    (hmono : ∀ {a b : CapId}, RestoreChain restores a b → RestoreChain restores' a b)
    {f : Forest} (h : f.WellRecovered restores) : f.WellRecovered restores' := by
  induction f with
  | leaf c => trivial
  | split k p lr rr l r ihl ihr =>
      simp only [Forest.WellRecovered] at h ⊢
      exact ⟨Forest.Recovers.chainMono hmono h.1, Forest.Recovers.chainMono hmono h.2.1,
        ihl h.2.2.1, ihr h.2.2.2⟩

/-- Whole-forest recovery is monotone in the restoration list. -/
theorem WellRecovered.mono {restores restores' : List Restore}
    (hsub : ∀ r ∈ restores, r ∈ restores') {f : Forest}
    (h : f.WellRecovered restores) : f.WellRecovered restores' := by
  induction f with
  | leaf c => trivial
  | split k p lr rr l r ihl ihr =>
      simp only [Forest.WellRecovered] at h ⊢
      exact ⟨Forest.Recovers.mono hsub h.1, Forest.Recovers.mono hsub h.2.1,
        ihl h.2.2.1, ihr h.2.2.2⟩

/-- Every suspension of a well-recovered forest has children that recover the
rule identities the suspension records. -/
theorem wellRecovered_suspension {restores : List Restore} {f : Forest}
    (h : f.WellRecovered restores) {susp : Suspension}
    (hs : susp ∈ f.suspensions) :
    susp.left.Recovers restores susp.leftRule.id ∧
      susp.right.Recovers restores susp.rightRule.id := by
  induction f with
  | leaf c => simp [Forest.suspensions] at hs
  | split k p lr rr l r ihl ihr =>
      simp only [Forest.WellRecovered] at h
      obtain ⟨hL, hR, hWL, hWR⟩ := h
      simp only [Forest.suspensions, List.mem_cons, List.mem_append] at hs
      rcases hs with rfl | hs | hs
      · exact ⟨hL, hR⟩
      · exact ihl hWL hs
      · exact ihr hWR hs

/-- The recorded resource of an authority node agrees with everything actually
below it. A current leaf is its own frontier. A suspended parent's frontier is
the pair of current subtrees its suspension records: their pointwise budget is
the parent's, and their authority nodes lie within the parent's resource. -/
def NodeRealized (f : Forest) (c : Leaf) : Prop :=
  c ∈ f.leaves ∨
  ∃ l r : Forest,
    (∃ s ∈ f.suspensions, s.parent = c ∧ s.left = l ∧ s.right = r) ∧
    (∀ x, l.budget x + r.budget x = (Forest.leaf c).budget x) ∧
    l.Inside c ∧ r.Inside c

/-- Resource containment lifts through a subtree: if the subtree lies in `a` and
`a` lies in `b`, the subtree lies in `b`. -/
theorem Inside.trans {f : Forest} {a b : Leaf} (h : f.Inside a) (hab : a.Within b) :
    f.Inside b := fun d hd => (h d hd).trans hab

/-- A single leaf realizes its own resource. -/
theorem realizes_leaf (c : Leaf) : (Forest.leaf c).Realizes c := by
  refine ⟨fun _ => rfl, ?_⟩
  intro d hd
  simp only [Forest.nodes, List.mem_singleton] at hd
  rw [hd]
  exact Leaf.Within.refl c

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

/-- A split's budget depends only on the budgets of its two current subtrees. -/
theorem split_budget_of_children {kind : RuleKind} {p lr rr : Leaf} {l r : Forest}
    (hl : ∀ x, l.budget x = (Forest.leaf lr).budget x)
    (hr : ∀ x, r.budget x = (Forest.leaf rr).budget x) :
    ∀ x, (Forest.split kind p lr rr l r).budget x =
      (Forest.split kind p lr rr (.leaf lr) (.leaf rr)).budget x := by
  intro x
  cases kind <;> simp [Forest.budget, hl x, hr x]

/-- A suspended parent is an authority node, its rule fragments are the frontier
identities recorded by `ruleIds` rather than current nodes, and the parent's
allocation and ceiling are carried by those descendants. When each current
subtree realizes its rule fragment's budget, the split's frontier budget is the
suspended parent's budget at every byte. -/
theorem suspended_frontier_realizes {kind : RuleKind} {parent leftRule rightRule : Leaf}
    {left right : Forest}
    (hv : RuleValid kind parent leftRule rightRule)
    (hl : ∀ x, left.budget x = (Forest.leaf leftRule).budget x)
    (hr : ∀ x, right.budget x = (Forest.leaf rightRule).budget x) :
    parent ∈ Forest.nodes (Forest.split kind parent leftRule rightRule left right) ∧
    leftRule.id ∈ Forest.ruleIds (Forest.split kind parent leftRule rightRule left right) ∧
    rightRule.id ∈ Forest.ruleIds (Forest.split kind parent leftRule rightRule left right) ∧
    leftRule.alloc = parent.alloc ∧ rightRule.alloc = parent.alloc ∧
    leftRule.ceiling = parent.ceiling ∧ rightRule.ceiling = parent.ceiling ∧
    (∀ x, (Forest.split kind parent leftRule rightRule left right).budget x =
      (Forest.leaf parent).budget x) := by
  obtain ⟨hps, hla, hra, hlc, hrc, hls, hrs, -, -, -, hpart⟩ := hv
  refine ⟨by simp [Forest.nodes], by simp [Forest.ruleIds], by simp [Forest.ruleIds],
    hla, hra, hlc, hrc, ?_⟩
  intro x
  rw [split_budget_of_children hl hr x]
  cases kind with
  | spatial =>
      obtain ⟨hlo, hhi, hrhi, hql, hqr⟩ := hpart
      exact Forest.spatial_split_budget (p := parent) (l := leftRule)
        (r := rightRule) (x := x)
        (by rw [hls, hps]) (by rw [hrs, hps]) hlo hhi hrhi hql hqr
        (by rw [← hlo, ← hhi]; exact leftRule.ordered)
        (by rw [← hrhi]; exact rightRule.ordered)
  | fractional =>
      obtain ⟨hlo1, hhi1, hlo2, hhi2, hq1, hq2, hsum⟩ := hpart
      exact Forest.fractional_split_budget (p := parent) (l := leftRule)
        (r := rightRule) (x := x)
        (by rw [hls, hps]) (by rw [hrs, hps]) hlo1 hhi1 hlo2 hhi2 hsum

/-- Forest coherence entails rule validity at every suspension. -/
theorem coherent_valid {f : Forest} (h : f.Coherent) : f.Valid := by
  induction f with
  | leaf c => trivial
  | split k p lr rr l r ihl ihr =>
      simp only [Forest.Coherent] at h
      obtain ⟨hrule, -, -, hCL, hCR⟩ := h
      exact ⟨hrule, ihl hCL, ihr hCR⟩

/-- The local coherence facts of any suspension of a coherent forest: the rule is
checked and each current child subtree realizes its rule fragment. -/
theorem coherent_suspension {f : Forest} (h : f.Coherent) {s : Suspension}
    (hs : s ∈ f.suspensions) :
    RuleValid s.kind s.parent s.leftRule s.rightRule ∧
      s.left.Realizes s.leftRule ∧ s.right.Realizes s.rightRule := by
  induction f with
  | leaf c => simp [Forest.suspensions] at hs
  | split k p lr rr l r ihl ihr =>
      simp only [Forest.Coherent] at h
      obtain ⟨hrule, hL, hR, hCL, hCR⟩ := h
      simp only [Forest.suspensions, List.mem_cons, List.mem_append] at hs
      rcases hs with rfl | hs | hs
      · exact ⟨hrule, hL, hR⟩
      · exact ihl hCL hs
      · exact ihr hCR hs

/-- The frontier budget of a suspension whose children realize the rule fragments
is the suspended parent's budget. This is the premise `suspended_frontier_realizes`
takes, derived from coherence rather than supplied by a caller. -/
theorem split_budget_realizes {kind : RuleKind} {p lr rr : Leaf} {l r : Forest}
    (hrule : RuleValid kind p lr rr) (hl : l.Realizes lr) (hr : r.Realizes rr) :
    ∀ x, l.budget x + r.budget x = (Forest.leaf p).budget x := by
  intro x
  obtain ⟨-, -, -, -, -, -, -, hb⟩ := suspended_frontier_realizes hrule hl.1 hr.1
  simpa [Forest.budget] using hb x

/-- The premises `suspended_frontier_realizes` takes are consequences of
coherence: for every suspension, its current subtrees realize the recorded rule
fragments, so the parent's budget is their pointwise sum and both subtrees lie
inside the parent's resource. -/
theorem coherent_suspension_realizes {f : Forest} (h : f.Coherent) {s : Suspension}
    (hs : s ∈ f.suspensions) :
    (∀ x, s.left.budget x + s.right.budget x = (Forest.leaf s.parent).budget x) ∧
      s.left.Inside s.parent ∧ s.right.Inside s.parent := by
  obtain ⟨hrule, hL, hR⟩ := coherent_suspension h hs
  exact ⟨split_budget_realizes hrule hL hR, hL.2.trans (RuleValid.left_within hrule),
    hR.2.trans (RuleValid.right_within hrule)⟩

/-- In a coherent forest every authority node's recorded resource is realized by
everything actually below it. -/
theorem coherent_nodeRealized {f : Forest} (h : f.Coherent) {c : Leaf}
    (hc : c ∈ f.nodes) : f.NodeRealized c := by
  induction f with
  | leaf c0 =>
      simp only [Forest.nodes, List.mem_singleton] at hc
      rcases hc with rfl
      exact Or.inl (by simp [Forest.leaves])
  | split k p lr rr l r ihl ihr =>
      simp only [Forest.Coherent] at h
      obtain ⟨hrule, hL, hR, hCL, hCR⟩ := h
      simp only [Forest.nodes, List.mem_cons, List.mem_append] at hc
      rcases hc with hcp | hc | hc
      · have hnc : (Forest.split k p lr rr l r).NodeRealized p := by
          refine Or.inr ⟨l, r, ?_, ?_, ?_, ?_⟩
          · exact ⟨{ kind := k, parent := p, leftRule := lr, rightRule := rr,
                     left := l, right := r }, by simp [Forest.suspensions], rfl, rfl, rfl⟩
          · exact split_budget_realizes hrule hL hR
          · exact Forest.Inside.trans hL.2 (RuleValid.left_within hrule)
          · exact Forest.Inside.trans hR.2 (RuleValid.right_within hrule)
        rw [hcp]
        exact hnc
      · rcases ihl hCL hc with hleaf | ⟨l', r', hmem, hbud, hinl, hinr⟩
        · exact Or.inl (by
            simp only [Forest.leaves, List.mem_append]
            exact Or.inl hleaf)
        · obtain ⟨s, hs, hpar, hl', hr'⟩ := hmem
          exact Or.inr ⟨l', r', ⟨s, by
            simp only [Forest.suspensions, List.mem_cons, List.mem_append]
            exact Or.inr (Or.inl hs), hpar, hl', hr'⟩, hbud, hinl, hinr⟩
      · rcases ihr hCR hc with hleaf | ⟨l', r', hmem, hbud, hinl, hinr⟩
        · exact Or.inl (by
            simp only [Forest.leaves, List.mem_append]
            exact Or.inr hleaf)
        · obtain ⟨s, hs, hpar, hl', hr'⟩ := hmem
          exact Or.inr ⟨l', r', ⟨s, by
            simp only [Forest.suspensions, List.mem_cons, List.mem_append]
            exact Or.inr (Or.inr hs), hpar, hl', hr'⟩, hbud, hinl, hinr⟩

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

/-- A leaf replacement that keeps every new node inside the replaced leaf keeps
the subtree inside any resource the old nodes lay in. -/
theorem inside_modifyLeafAt {f f' : Forest} {id : CapId}
    {g : Leaf → Option (Forest × Leaf)} {c d0 : Leaf}
    (h : f.modifyLeafAt id g = some (f', d0))
    (hc : f.Inside c)
    (hg : ∀ (d : Leaf) (x : Forest) (d' : Leaf), g d = some (x, d') → x.Inside d) :
    f'.Inside c := by
  induction f generalizing f' d0 with
  | leaf c0 =>
      simp only [Forest.modifyLeafAt] at h
      by_cases hc0 : c0.id = id
      · rw [if_pos hc0] at h
        exact Forest.Inside.trans (hg c0 f' d0 h) (hc c0 (by simp [Forest.nodes]))
      · rw [if_neg hc0] at h
        cases h
  | split k p lr rr l r ihl ihr =>
      simp only [Forest.modifyLeafAt] at h
      split at h
      · rename_i l' d' hl
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        intro e he
        simp only [Forest.nodes, List.mem_cons, List.mem_append] at he
        rcases he with he | he | he
        · exact hc e (by simp only [Forest.nodes, List.mem_cons]; exact Or.inl he)
        · exact (ihl hl (fun x hx => hc x (by
            simp only [Forest.nodes, List.mem_cons, List.mem_append]
            exact Or.inr (Or.inl hx)))) e he
        · exact hc e (by
            simp only [Forest.nodes, List.mem_cons, List.mem_append]
            exact Or.inr (Or.inr he))
      · rename_i hl
        split at h
        · rename_i r' d' hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          intro e he
          simp only [Forest.nodes, List.mem_cons, List.mem_append] at he
          rcases he with he | he | he
          · exact hc e (by simp only [Forest.nodes, List.mem_cons]; exact Or.inl he)
          · exact hc e (by
              simp only [Forest.nodes, List.mem_cons, List.mem_append]
              exact Or.inr (Or.inl he))
          · exact (ihr hr (fun x hx => hc x (by
              simp only [Forest.nodes, List.mem_cons, List.mem_append]
              exact Or.inr (Or.inr hx)))) e he
        · cases h

/-- A leaf replacement that preserves the budget and the resource scope of the
replaced leaf preserves subtree realization. -/
theorem realizes_modifyLeafAt {f f' : Forest} {id : CapId}
    {g : Leaf → Option (Forest × Leaf)} {c d0 : Leaf}
    (h : f.modifyLeafAt id g = some (f', d0))
    (hc : f.Realizes c)
    (hg : ∀ (d : Leaf) (x : Forest) (d' : Leaf), g d = some (x, d') → x.Realizes d) :
    f'.Realizes c := by
  refine ⟨?_, ?_⟩
  · intro b
    rw [budget_modifyLeafAt h (fun d x d' hgd b => (hg d x d' hgd).1 b) b]
    exact hc.1 b
  · exact inside_modifyLeafAt h hc.2 (fun d x d' hgd => (hg d x d' hgd).2)

/-- A coherent forest stays coherent when one current leaf is replaced by a
coherent forest that realizes it. -/
theorem coherent_modifyLeafAt {f f' : Forest} {id : CapId}
    {g : Leaf → Option (Forest × Leaf)} {d0 : Leaf}
    (h : f.modifyLeafAt id g = some (f', d0))
    (hc : f.Coherent)
    (hgR : ∀ (d : Leaf) (x : Forest) (d' : Leaf), g d = some (x, d') → x.Realizes d)
    (hgC : ∀ (d : Leaf) (x : Forest) (d' : Leaf), g d = some (x, d') → x.Coherent) :
    f'.Coherent := by
  induction f generalizing f' d0 with
  | leaf c0 =>
      simp only [Forest.modifyLeafAt] at h
      by_cases hc0 : c0.id = id
      · rw [if_pos hc0] at h
        exact hgC c0 f' d0 h
      · rw [if_neg hc0] at h
        cases h
  | split k p lr rr l r ihl ihr =>
      simp only [Forest.Coherent] at hc
      obtain ⟨hrule, hL, hR, hCL, hCR⟩ := hc
      simp only [Forest.modifyLeafAt] at h
      split at h
      · rename_i l' d' hl
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hrule, realizes_modifyLeafAt hl hL hgR, hR,
          ihl hl hCL, hCR⟩
      · rename_i hl
        split at h
        · rename_i r' d' hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨hrule, hL, realizes_modifyLeafAt hr hR hgR,
            hCL, ihr hr hCR⟩
        · cases h


/-- A leaf replacement that keeps every new node in scope keeps the subtree in
scope, provided the replaced leaf itself is in scope. -/
theorem nodes_scope_modifyLeafAt {f f' : Forest} {id : CapId}
    {g : Leaf → Option (Forest × Leaf)} {d0 : Leaf} {a : AllocId} {len D : Nat}
    (h : f.modifyLeafAt id g = some (f', d0))
    (hf : ∀ c ∈ f.nodes, c.InScope a len D)
    (hg : ∀ (d : Leaf) (x : Forest) (d' : Leaf), g d = some (x, d') →
        d.InScope a len D → ∀ c ∈ x.nodes, c.InScope a len D) :
    ∀ c ∈ f'.nodes, c.InScope a len D := by
  induction f generalizing f' d0 with
  | leaf c0 =>
      simp only [Forest.modifyLeafAt] at h
      by_cases hc0 : c0.id = id
      · rw [if_pos hc0] at h
        exact hg c0 f' d0 h (hf c0 (by simp [Forest.nodes]))
      · rw [if_neg hc0] at h
        cases h
  | split k p lr rr l r ihl ihr =>
      simp only [Forest.modifyLeafAt] at h
      split at h
      · rename_i l' d' hl
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        intro c hc
        simp only [Forest.nodes, List.mem_cons, List.mem_append] at hc
        rcases hc with hc | hc | hc
        · exact hf c (by simp only [Forest.nodes, List.mem_cons]; exact Or.inl hc)
        · exact ihl hl (fun x hx => hf x (by
            simp only [Forest.nodes, List.mem_cons, List.mem_append]
            exact Or.inr (Or.inl hx))) c hc
        · exact hf c (by
            simp only [Forest.nodes, List.mem_cons, List.mem_append]
            exact Or.inr (Or.inr hc))
      · rename_i hl
        split at h
        · rename_i r' d' hr
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          intro c hc
          simp only [Forest.nodes, List.mem_cons, List.mem_append] at hc
          rcases hc with hc | hc | hc
          · exact hf c (by simp only [Forest.nodes, List.mem_cons]; exact Or.inl hc)
          · exact hf c (by
              simp only [Forest.nodes, List.mem_cons, List.mem_append]
              exact Or.inr (Or.inl hc))
          · exact ihr hr (fun x hx => hf x (by
              simp only [Forest.nodes, List.mem_cons, List.mem_append]
              exact Or.inr (Or.inr hx))) c hc
        · cases h

/-- Every rule descriptor of a coherent forest that has its authority nodes in
scope is itself in scope: allocation, extent and share, without a non-emptiness
requirement (an empty side of a split carries no bytes and no authority). -/
theorem ruleFragments_scope {f : Forest} {a : AllocId} {len D : Nat}
    (hcoh : f.Coherent) (hn : ∀ c ∈ f.nodes, c.InScope a len D) :
    ∀ c ∈ f.ruleFragments, c.alloc = a ∧ c.hi ≤ len ∧ c.q ≤ D := by
  induction f with
  | leaf c => intro c' hc'; simp [Forest.ruleFragments] at hc'
  | split k p lr rr l r ihl ihr =>
      simp only [Forest.Coherent] at hcoh
      obtain ⟨hrule, -, -, hCL, hCR⟩ := hcoh
      intro c' hc'
      simp only [Forest.ruleFragments, List.mem_cons, List.mem_append] at hc'
      rcases hc' with rfl | rfl | hc' | hc'
      · obtain ⟨hla, -, hhi, -, hq⟩ := RuleValid.left_within hrule
        obtain ⟨hpa, hph, -, hpq⟩ := hn p (by simp [Forest.nodes])
        exact ⟨hla.trans hpa, Nat.le_trans hhi hph, Nat.le_trans hq hpq⟩
      · obtain ⟨hra, -, hhi, -, hq⟩ := RuleValid.right_within hrule
        obtain ⟨hpa, hph, -, hpq⟩ := hn p (by simp [Forest.nodes])
        exact ⟨hra.trans hpa, Nat.le_trans hhi hph, Nat.le_trans hq hpq⟩
      · exact ihl hCL (fun c hc => hn c (by
          simp only [Forest.nodes, List.mem_cons, List.mem_append]
          exact Or.inr (Or.inl hc))) c' hc'
      · exact ihr hCR (fun c hc => hn c (by
          simp only [Forest.nodes, List.mem_cons, List.mem_append]
          exact Or.inr (Or.inr hc))) c' hc'

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


/-- A checked spatial split realizes the leaf it subdivides: the split node's
frontier is the parent's budget and every authority node it carries lies within
the parent's resource. -/
theorem spatialLeafSplit_realizes {p p' : Leaf} {x : Forest} {c1 c2 : CapId}
    {lo1 hi1 lo2 hi2 : Nat}
    (h : spatialLeafSplit p c1 c2 lo1 hi1 lo2 hi2 = some (x, p')) :
    x.Realizes p := by
  have hbud := spatialLeafSplit_budget h
  have hvalid := spatialLeafSplit_valid h
  unfold spatialLeafSplit at h
  split at h
  · rename_i _hact
    split at h
    · rename_i _hb
      split at h
      · rename_i _hpart
        split at h
        · rename_i _hid
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _hp'⟩ := h
          refine ⟨hbud, ?_⟩
          intro e he
          simp only [Forest.nodes, List.mem_cons, List.mem_append, List.mem_singleton,
            List.nil_append, List.cons_append, List.mem_nil_iff, or_false] at he
          rcases he with he | he | he
          · rw [he]; exact Leaf.Within.refl _
          · rw [he]; exact RuleValid.left_within hvalid.1
          · rw [he]; exact RuleValid.right_within hvalid.1
        · simp at h
      · simp at h
    · simp at h
  · simp at h

/-- A checked spatial split is itself coherent. -/
theorem spatialLeafSplit_coherent {p p' : Leaf} {x : Forest} {c1 c2 : CapId}
    {lo1 hi1 lo2 hi2 : Nat}
    (h : spatialLeafSplit p c1 c2 lo1 hi1 lo2 hi2 = some (x, p')) :
    x.Coherent := by
  have hvalid := spatialLeafSplit_valid h
  unfold spatialLeafSplit at h
  split at h
  · rename_i _hact
    split at h
    · rename_i _hb
      split at h
      · rename_i _hpart
        split at h
        · rename_i _hid
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _hp'⟩ := h
          exact ⟨hvalid.1, realizes_leaf _, realizes_leaf _, trivial, trivial⟩
        · simp at h
      · simp at h
    · simp at h
  · simp at h


/-- The exact shape of a checked spatial split: the new leaves are the rule
fragments, their intervals are the requested ones, and the parent's resource is
preserved. -/
theorem spatialLeafSplit_shape {p p' : Leaf} {x : Forest} {c1 c2 : CapId}
    {lo1 hi1 lo2 hi2 : Nat}
    (h : spatialLeafSplit p c1 c2 lo1 hi1 lo2 hi2 = some (x, p')) :
    p' = p ∧
    ∃ l r : Leaf, x = .split .spatial p l r (.leaf l) (.leaf r) ∧
      l.lo = lo1 ∧ l.hi = hi1 ∧ r.lo = lo2 ∧ r.hi = hi2 ∧
      l.q = p.q ∧ r.q = p.q ∧ l.alloc = p.alloc ∧ r.alloc = p.alloc ∧
      l.ceiling = p.ceiling ∧ r.ceiling = p.ceiling ∧
      lo1 ≤ hi1 ∧ lo2 ≤ hi2 ∧ lo1 = p.lo ∧ hi1 = lo2 ∧ hi2 = p.hi := by
  unfold spatialLeafSplit at h
  split at h
  · rename_i _hact
    split at h
    · rename_i hb
      split at h
      · rename_i hpart
        split at h
        · rename_i _hid
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, hp'⟩ := h
          exact ⟨hp'.symm, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
            hb.1, hb.2, hpart.1, hpart.2.1, hpart.2.2⟩
        · simp at h
      · simp at h
    · simp at h
  · simp at h

/-- A checked spatial split keeps every node of the result in the parent's
component scope: the suspended parent and both new children. The non-emptiness
guard is what admits the children in a non-empty allocation. -/
theorem spatialLeafSplit_nodes_scope {p p' : Leaf} {x : Forest} {c1 c2 : CapId}
    {lo1 hi1 lo2 hi2 : Nat} {a : AllocId} {len D : Nat}
    (h : spatialLeafSplit p c1 c2 lo1 hi1 lo2 hi2 = some (x, p'))
    (hp : p.InScope a len D)
    (hne : len = 0 ∨ (lo1 < hi1 ∧ lo2 < hi2)) :
    ∀ c ∈ x.nodes, c.InScope a len D := by
  obtain ⟨-, l, r, rfl, hllo, hlhi, hrlo, hrhi, hlq, hrq, hla, hra, -, -, hb1, hb2,
    hpart1, hpart2, hpart3⟩ := spatialLeafSplit_shape h
  obtain ⟨hpa, hph, hpne, hpq⟩ := hp
  intro c hc
  simp only [Forest.nodes, List.mem_cons, List.mem_singleton,
    List.nil_append, List.cons_append, List.mem_nil_iff, or_false] at hc
  rcases hc with hc | hc | hc
  · rw [hc]; exact ⟨hpa, hph, hpne, hpq⟩
  · rw [hc]
    refine ⟨hla.trans hpa, ?_, ?_, ?_⟩
    · rw [hlhi, hpart2]; exact Nat.le_trans hb2 (Nat.le_trans (Nat.le_of_eq hpart3) hph)
    · rcases hne with h0 | ⟨h1, -⟩
      · exact Or.inr h0
      · exact Or.inl (by rw [hllo, hlhi]; exact h1)
    · rw [hlq]; exact hpq
  · rw [hc]
    refine ⟨hra.trans hpa, ?_, ?_, ?_⟩
    · rw [hrhi, hpart3]; exact hph
    · rcases hne with h0 | ⟨-, h2⟩
      · exact Or.inr h0
      · exact Or.inl (by rw [hrlo, hrhi]; exact h2)
    · rw [hrq]; exact hpq

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


/-- A checked spatial subdivision preserves realization of any enclosing
resource. -/
theorem splitSpatialAt_realizes {f f' : Forest} {p : Leaf} {id c1 c2 : CapId}
    {lo1 hi1 lo2 hi2 : Nat} {c : Leaf}
    (h : f.splitSpatialAt id c1 c2 lo1 hi1 lo2 hi2 = some (f', p))
    (hc : f.Realizes c) : f'.Realizes c := by
  unfold Forest.splitSpatialAt at h
  exact realizes_modifyLeafAt h hc
    (fun d x d' hg => spatialLeafSplit_realizes hg)

/-- A checked spatial subdivision preserves forest coherence. -/
theorem splitSpatialAt_coherent {f f' : Forest} {p : Leaf} {id c1 c2 : CapId}
    {lo1 hi1 lo2 hi2 : Nat}
    (h : f.splitSpatialAt id c1 c2 lo1 hi1 lo2 hi2 = some (f', p))
    (hc : f.Coherent) : f'.Coherent := by
  unfold Forest.splitSpatialAt at h
  exact coherent_modifyLeafAt h hc
    (fun d x d' hg => spatialLeafSplit_realizes hg)
    (fun d x d' hg => spatialLeafSplit_coherent hg)


/-- A checked spatial subdivision keeps every resulting node in the parent's
component scope. -/
theorem splitSpatialAt_nodes_scope {f f' : Forest} {p : Leaf} {id c1 c2 : CapId}
    {lo1 hi1 lo2 hi2 : Nat} {a : AllocId} {len D : Nat}
    (h : f.splitSpatialAt id c1 c2 lo1 hi1 lo2 hi2 = some (f', p))
    (hf : ∀ c ∈ f.nodes, c.InScope a len D)
    (hne : len = 0 ∨ (lo1 < hi1 ∧ lo2 < hi2)) :
    ∀ c ∈ f'.nodes, c.InScope a len D := by
  unfold Forest.splitSpatialAt at h
  exact nodes_scope_modifyLeafAt h hf
    (fun d x d' hg hd => spatialLeafSplit_nodes_scope hg hd hne)

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


/-- A checked fractional split realizes the leaf it subdivides. -/
theorem fractionalLeafSplit_realizes {p p' : Leaf} {x : Forest} {c1 c2 : CapId}
    {q1 q2 : Nat}
    (h : fractionalLeafSplit p c1 c2 q1 q2 = some (x, p')) :
    x.Realizes p := by
  have hbud := fractionalLeafSplit_budget h
  have hvalid := fractionalLeafSplit_valid h
  unfold fractionalLeafSplit at h
  split at h
  · rename_i _hact
    split at h
    · rename_i _hpos
      split at h
      · rename_i _hsum
        split at h
        · rename_i _hid
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _hp'⟩ := h
          refine ⟨hbud, ?_⟩
          intro e he
          simp only [Forest.nodes, List.mem_cons, List.mem_append, List.mem_singleton,
            List.nil_append, List.cons_append, List.mem_nil_iff, or_false] at he
          rcases he with he | he | he
          · rw [he]; exact Leaf.Within.refl _
          · rw [he]; exact RuleValid.left_within hvalid.1
          · rw [he]; exact RuleValid.right_within hvalid.1
        · simp at h
      · simp at h
    · simp at h
  · simp at h

/-- A checked fractional split is itself coherent. -/
theorem fractionalLeafSplit_coherent {p p' : Leaf} {x : Forest} {c1 c2 : CapId}
    {q1 q2 : Nat}
    (h : fractionalLeafSplit p c1 c2 q1 q2 = some (x, p')) :
    x.Coherent := by
  have hvalid := fractionalLeafSplit_valid h
  unfold fractionalLeafSplit at h
  split at h
  · rename_i _hact
    split at h
    · rename_i _hpos
      split at h
      · rename_i _hsum
        split at h
        · rename_i _hid
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _hp'⟩ := h
          exact ⟨hvalid.1, realizes_leaf _, realizes_leaf _, trivial, trivial⟩
        · simp at h
      · simp at h
    · simp at h
  · simp at h


/-- The exact shape of a checked fractional split: both children keep the parent
interval, their shares are the requested ones, and they sum to the parent's. -/
theorem fractionalLeafSplit_shape {p p' : Leaf} {x : Forest} {c1 c2 : CapId}
    {q1 q2 : Nat}
    (h : fractionalLeafSplit p c1 c2 q1 q2 = some (x, p')) :
    p' = p ∧
    ∃ l r : Leaf, x = .split .fractional p l r (.leaf l) (.leaf r) ∧
      l.lo = p.lo ∧ l.hi = p.hi ∧ r.lo = p.lo ∧ r.hi = p.hi ∧
      l.q = q1 ∧ r.q = q2 ∧ l.alloc = p.alloc ∧ r.alloc = p.alloc ∧
      l.ceiling = p.ceiling ∧ r.ceiling = p.ceiling ∧
      0 < q1 ∧ 0 < q2 ∧ q1 + q2 = p.q := by
  unfold fractionalLeafSplit at h
  split at h
  · rename_i _hact
    split at h
    · rename_i hpos
      split at h
      · rename_i hsum
        split at h
        · rename_i _hid
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, hp'⟩ := h
          exact ⟨hp'.symm, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
            hpos.1, hpos.2, hsum⟩
        · simp at h
      · simp at h
    · simp at h
  · simp at h

/-- A checked fractional split keeps every node of the result in the parent's
component scope: both children inherit the parent interval, and each share is
bounded by the parent's. -/
theorem fractionalLeafSplit_nodes_scope {p p' : Leaf} {x : Forest} {c1 c2 : CapId}
    {q1 q2 : Nat} {a : AllocId} {len D : Nat}
    (h : fractionalLeafSplit p c1 c2 q1 q2 = some (x, p'))
    (hp : p.InScope a len D) :
    ∀ c ∈ x.nodes, c.InScope a len D := by
  obtain ⟨-, l, r, rfl, hllo, hlhi, hrlo, hrhi, hlq, hrq, hla, hra, -, -, hq1, hq2,
    hsum⟩ := fractionalLeafSplit_shape h
  obtain ⟨hpa, hph, hpne, hpq⟩ := hp
  intro c hc
  simp only [Forest.nodes, List.mem_cons, List.mem_singleton,
    List.nil_append, List.cons_append, List.mem_nil_iff, or_false] at hc
  rcases hc with hc | hc | hc
  · rw [hc]; exact ⟨hpa, hph, hpne, hpq⟩
  · rw [hc]
    refine ⟨hla.trans hpa, ?_, ?_, ?_⟩
    · rw [hlhi]; exact hph
    · rcases hpne with h0 | h1
      · exact Or.inl (by rw [hllo, hlhi]; exact h0)
      · exact Or.inr h1
    · rw [hlq]; omega
  · rw [hc]
    refine ⟨hra.trans hpa, ?_, ?_, ?_⟩
    · rw [hrhi]; exact hph
    · rcases hpne with h0 | h1
      · exact Or.inl (by rw [hrlo, hrhi]; exact h0)
      · exact Or.inr h1
    · rw [hrq]; omega

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


/-- A checked fractional subdivision preserves realization of any enclosing
resource. -/
theorem splitFractionAt_realizes {f f' : Forest} {p : Leaf} {id c1 c2 : CapId}
    {q1 q2 : Nat} {c : Leaf}
    (h : f.splitFractionAt id c1 c2 q1 q2 = some (f', p))
    (hc : f.Realizes c) : f'.Realizes c := by
  unfold Forest.splitFractionAt at h
  exact realizes_modifyLeafAt h hc
    (fun d x d' hg => fractionalLeafSplit_realizes hg)

/-- A checked fractional subdivision preserves forest coherence. -/
theorem splitFractionAt_coherent {f f' : Forest} {p : Leaf} {id c1 c2 : CapId}
    {q1 q2 : Nat}
    (h : f.splitFractionAt id c1 c2 q1 q2 = some (f', p))
    (hc : f.Coherent) : f'.Coherent := by
  unfold Forest.splitFractionAt at h
  exact coherent_modifyLeafAt h hc
    (fun d x d' hg => fractionalLeafSplit_realizes hg)
    (fun d x d' hg => fractionalLeafSplit_coherent hg)


/-- A checked fractional subdivision keeps every resulting node in the parent's
component scope. -/
theorem splitFractionAt_nodes_scope {f f' : Forest} {p : Leaf} {id c1 c2 : CapId}
    {q1 q2 : Nat} {a : AllocId} {len D : Nat}
    (h : f.splitFractionAt id c1 c2 q1 q2 = some (f', p))
    (hf : ∀ c ∈ f.nodes, c.InScope a len D) :
    ∀ c ∈ f'.nodes, c.InScope a len D := by
  unfold Forest.splitFractionAt at h
  exact nodes_scope_modifyLeafAt h hf
    (fun d x d' hg hd => fractionalLeafSplit_nodes_scope hg hd)

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


/-- Reconstruction preserves realization of any enclosing resource: it only
removes authority nodes and the budget is unchanged pointwise. -/
theorem realizes_reconstructAt {f f' : Forest} {id : CapId} {a b : Leaf} {c : Leaf}
    (h : f.reconstructAt id = some (f', a, b)) (hc : f.Realizes c) :
    f'.Realizes c := by
  refine ⟨?_, ?_⟩
  · intro x
    rw [reconstructAt_budget h x]
    exact hc.1 x
  · exact fun e he => hc.2 e (reconstructAt_nodes_sub h he)

/-- Reconstruction preserves forest coherence. -/
theorem coherent_reconstructAt {f f' : Forest} {id : CapId} {a b : Leaf}
    (h : f.reconstructAt id = some (f', a, b)) (hc : f.Coherent) :
    f'.Coherent := by
  induction f generalizing f' a b with
  | leaf c0 => simp [Forest.reconstructAt] at h
  | split k p lr rr l r ihl ihr =>
      simp only [Forest.Coherent] at hc
      obtain ⟨hrule, hL, hR, hCL, hCR⟩ := hc
      simp only [Forest.reconstructAt] at h
      split at h
      · rename_i _hp
        have hf' : f' = .leaf p := reconstructHere_nodes h
        subst hf'
        trivial
      · rename_i _hp
        split at h
        · rename_i l' a' b' hl
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨hrule, realizes_reconstructAt hl hL, hR, ihl hl hCL, hCR⟩
        · rename_i _hl
          split at h
          · rename_i r' a' b' hr
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact ⟨hrule, hL, realizes_reconstructAt hr hR, hCL, ihr hr hCR⟩
          · simp at h

/-- Reconstruction only removes authority nodes, so it keeps every surviving
node in scope. -/
theorem reconstructAt_nodes_scope {f f' : Forest} {id : CapId} {a b : Leaf}
    {a' : AllocId} {len D : Nat}
    (h : f.reconstructAt id = some (f', a, b))
    (hf : ∀ c ∈ f.nodes, c.InScope a' len D) :
    ∀ c ∈ f'.nodes, c.InScope a' len D :=
  fun c hc => hf c (reconstructAt_nodes_sub h hc)

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


/-- Retagging keeps the leaf's resource, so the result realizes the old leaf. -/
theorem retagLeafAt_realizes {newId : CapId} {c : Leaf} {f' : Forest} {d : Leaf}
    (h : retagLeafAt newId c = some (f', d)) : f'.Realizes c := by
  unfold retagLeafAt at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    refine ⟨fun b => ?_, ?_⟩
    · simp [Forest.budget, Leaf.budget]
    · intro e he
      simp only [Forest.nodes, List.mem_singleton] at he
      rw [he]
      exact ⟨rfl, Nat.le_refl _, Nat.le_refl _, rfl, Nat.le_refl _⟩
  · cases h

/-- Retagging a leaf stays coherent. -/
theorem retagLeafAt_coherent {newId : CapId} {c : Leaf} {f' : Forest} {d : Leaf}
    (h : retagLeafAt newId c = some (f', d)) : f'.Coherent := by
  unfold retagLeafAt at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    trivial
  · cases h

/-- Retagging keeps the leaf's allocation, interval and share, hence its scope. -/
theorem retagLeafAt_nodes_scope {newId : CapId} {c : Leaf} {f' : Forest} {d : Leaf}
    (h : retagLeafAt newId c = some (f', d)) {a : AllocId} {len D : Nat}
    (hc : c.InScope a len D) : ∀ e ∈ f'.nodes, e.InScope a len D := by
  unfold retagLeafAt at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    intro e he
    simp only [Forest.nodes, List.mem_singleton] at he
    rw [he]
    exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩
  · cases h

/-- Retagging preserves realization of any enclosing resource. -/
theorem retagLeaf_realizes {f f' : Forest} {id newId : CapId} {p c : Leaf}
    (h : f.retagLeaf id newId = some (f', p)) (hc : f.Realizes c) :
    f'.Realizes c := by
  unfold Forest.retagLeaf at h
  exact realizes_modifyLeafAt h hc (fun d x d' hg => retagLeafAt_realizes hg)

/-- Retagging preserves forest coherence. -/
theorem retagLeaf_coherent {f f' : Forest} {id newId : CapId} {p : Leaf}
    (h : f.retagLeaf id newId = some (f', p)) (hc : f.Coherent) :
    f'.Coherent := by
  unfold Forest.retagLeaf at h
  exact coherent_modifyLeafAt h hc
    (fun d x d' hg => retagLeafAt_realizes hg)
    (fun d x d' hg => retagLeafAt_coherent hg)

/-- Retagging preserves component scope. -/
theorem retagLeaf_nodes_scope {f f' : Forest} {id newId : CapId} {p : Leaf}
    {a : AllocId} {len D : Nat}
    (h : f.retagLeaf id newId = some (f', p))
    (hf : ∀ c ∈ f.nodes, c.InScope a len D) :
    ∀ c ∈ f'.nodes, c.InScope a len D := by
  unfold Forest.retagLeaf at h
  exact nodes_scope_modifyLeafAt h hf
    (fun d x d' hg hd => retagLeafAt_nodes_scope hg hd)

/-! ### Identity recovery through the checked operations

The recovery relation is preserved by every operation that changes a current
leaf or a suspension: a locally recoverable replacement keeps each suspension's
identity dependency, and the operations only grow the restoration list (`borrow`,
the subdivisions) or shrink it by exactly the record a `return` discharges.
-/

/-- Replacing one leaf at a fixed site preserves identity recovery when the
replacement locally recovers the expected identity and each suspension's
identity dependency is monotone in the restoration list. -/
theorem recovers_modifyLeafAt {f : Forest} {id : CapId}
    {g : Leaf → Option (Forest × Leaf)}
    {rs rs' : List Restore}
    (hmono : ∀ {a b : CapId}, RestoreChain rs a b → RestoreChain rs' a b)
    (hlocal : ∀ (d : Leaf) (x : Forest) (d' : Leaf), d.id = id →
      g d = some (x, d') → ∀ {e : CapId},
      (Forest.leaf d).Recovers rs e → x.Recovers rs' e)
    {e : CapId} (hr : f.Recovers rs e) :
    ∀ {f' : Forest} {c : Leaf}, f.modifyLeafAt id g = some (f', c) →
      f'.Recovers rs' e := by
  induction hr with
  | leaf c0 hchain =>
      intro f' c h
      simp only [Forest.modifyLeafAt] at h
      split at h
      · rename_i hcid
        exact hlocal c0 f' c hcid h (Forest.Recovers.leaf c0 hchain)
      · cases h
  | split kind par lrule rrule lf rt hchain hlft hrgt ihl ihr =>
      intro f' c h
      simp only [Forest.modifyLeafAt] at h
      split at h
      · rename_i l' c' hl
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Forest.Recovers.split kind par lrule rrule l' rt (hmono hchain) (ihl hl)
          (Forest.Recovers.chainMono hmono hrgt)
      · rename_i hl
        split at h
        · rename_i r' c' hr'
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact Forest.Recovers.split kind par lrule rrule lf r' (hmono hchain)
            (Forest.Recovers.chainMono hmono hlft) (ihr hr')
        · cases h

/-- Replacing one leaf at a fixed site preserves whole-forest recovery when the
replacement is itself well recovered and the restoration list only grows. -/
theorem wellRecovered_modifyLeafAt {f f' : Forest} {id : CapId}
    {g : Leaf → Option (Forest × Leaf)} {c : Leaf}
    (h : f.modifyLeafAt id g = some (f', c))
    {rs rs' : List Restore} (hsub : ∀ r ∈ rs, r ∈ rs')
    (hlocal : ∀ (d : Leaf) (x : Forest) (d' : Leaf), d.id = id →
      g d = some (x, d') → ∀ {e : CapId},
      (Forest.leaf d).Recovers rs e → x.Recovers rs' e)
    (hlocalW : ∀ (d : Leaf) (x : Forest) (d' : Leaf), d.id = id →
      g d = some (x, d') → x.WellRecovered rs')
    (hw : f.WellRecovered rs) : f'.WellRecovered rs' := by
  induction f generalizing f' c with
  | leaf c0 =>
      simp only [Forest.modifyLeafAt] at h
      split at h
      · rename_i hcid
        exact hlocalW c0 f' c hcid h
      · cases h
  | split k p0 lr rr l r ihl ihr =>
      simp only [Forest.WellRecovered] at hw
      obtain ⟨hL, hR, hWL, hWR⟩ := hw
      simp only [Forest.modifyLeafAt] at h
      split at h
      · rename_i l' c' hl
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨Forest.recovers_modifyLeafAt
            (fun {a b} hc => RestoreChain.mono hsub hc) hlocal hL hl,
          Forest.Recovers.mono hsub hR, ihl hl hWL,
          Forest.WellRecovered.mono hsub hWR⟩
      · rename_i hl
        split at h
        · rename_i r' c' hr'
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨Forest.Recovers.mono hsub hL,
            Forest.recovers_modifyLeafAt
              (fun {a b} hc => RestoreChain.mono hsub hc) hlocal hR hr',
            Forest.WellRecovered.mono hsub hWL, ihr hr' hWR⟩
        · cases h

/-- A subdivision preserves whole-forest recovery: the new suspension's children
are the two fresh leaves, each recovered from its own rule identity. -/
theorem wellRecovered_splitSpatialAt {f f' : Forest} {p : Leaf} {id c1 c2 : CapId}
    {lo1 hi1 lo2 hi2 : Nat}
    (h : f.splitSpatialAt id c1 c2 lo1 hi1 lo2 hi2 = some (f', p))
    {rs : List Restore} (hw : f.WellRecovered rs) : f'.WellRecovered rs := by
  unfold Forest.splitSpatialAt at h
  refine wellRecovered_modifyLeafAt h (fun x hx => hx) ?_ ?_ hw
  · intro d x d' _hid hg e hrec
    obtain ⟨-, l, r, rfl, -⟩ := spatialLeafSplit_shape hg
    cases hrec with
    | leaf c0 hchain =>
        exact Forest.Recovers.split .spatial d l r (.leaf l) (.leaf r) hchain
          (Forest.Recovers.leaf l (RestoreChain.nil l.id))
          (Forest.Recovers.leaf r (RestoreChain.nil r.id))
  · intro d x d' _hid hg
    obtain ⟨-, l, r, rfl, -⟩ := spatialLeafSplit_shape hg
    exact ⟨Forest.Recovers.leaf l (RestoreChain.nil l.id),
      Forest.Recovers.leaf r (RestoreChain.nil r.id), trivial, trivial⟩

/-- A fractional subdivision preserves whole-forest recovery. -/
theorem wellRecovered_splitFractionAt {f f' : Forest} {p : Leaf} {id c1 c2 : CapId}
    {q1 q2 : Nat}
    (h : f.splitFractionAt id c1 c2 q1 q2 = some (f', p))
    {rs : List Restore} (hw : f.WellRecovered rs) : f'.WellRecovered rs := by
  unfold Forest.splitFractionAt at h
  refine wellRecovered_modifyLeafAt h (fun x hx => hx) ?_ ?_ hw
  · intro d x d' _hid hg e hrec
    obtain ⟨-, l, r, rfl, -⟩ := fractionalLeafSplit_shape hg
    cases hrec with
    | leaf c0 hchain =>
        exact Forest.Recovers.split .fractional d l r (.leaf l) (.leaf r) hchain
          (Forest.Recovers.leaf l (RestoreChain.nil l.id))
          (Forest.Recovers.leaf r (RestoreChain.nil r.id))
  · intro d x d' _hid hg
    obtain ⟨-, l, r, rfl, -⟩ := fractionalLeafSplit_shape hg
    exact ⟨Forest.Recovers.leaf l (RestoreChain.nil l.id),
      Forest.Recovers.leaf r (RestoreChain.nil r.id), trivial, trivial⟩

/-- Retagging a leaf for a borrow preserves whole-forest recovery: the new record
links the old identity to the new one, so every chain that ended at the old leaf
identity now ends at the new one. -/
theorem wellRecovered_retagLeaf {f f' : Forest} {id newId : CapId} {p : Leaf}
    (h : f.retagLeaf id newId = some (f', p))
    {rs : List Restore} {r : Restore} (hrl : r.lender = id) (hrb : r.borrower = newId)
    (hw : f.WellRecovered rs) : f'.WellRecovered (r :: rs) := by
  unfold Forest.retagLeaf at h
  refine wellRecovered_modifyLeafAt h (fun x hx => List.mem_cons_of_mem _ hx) ?_ ?_ hw
  · intro d x d' hid hg e hrec
    unfold retagLeafAt at hg
    split at hg
    · simp only [Option.some.injEq, Prod.mk.injEq] at hg
      obtain ⟨rfl, rfl⟩ := hg
      cases hrec with
      | leaf c0 hchain =>
          exact Forest.Recovers.leaf {d with id := newId}
            (hrb ▸ RestoreChain.snoc r
              (RestoreChain.mono (fun y hy => List.mem_cons_of_mem _ hy) hchain)
              List.mem_cons_self (by rw [hrl, ← hid]))
    · cases hg
  · intro d x d' _hid hg
    unfold retagLeafAt at hg
    split at hg
    · simp only [Option.some.injEq, Prod.mk.injEq] at hg
      obtain ⟨rfl, rfl⟩ := hg
      trivial
    · cases hg

/-- Reconstruction preserves identity recovery: a reconstructed suspension is a
leaf carrying the identity its suspension recorded, which is exactly the
expected identity. -/
theorem recovers_reconstructAt {f : Forest} {id : CapId} {restores : List Restore} :
    ∀ {e : CapId}, f.Recovers restores e →
      ∀ {f' : Forest} {a b : Leaf}, f.reconstructAt id = some (f', a, b) →
        f'.Recovers restores e := by
  induction f with
  | leaf c =>
      intro e hr f' a b h
      simp [Forest.reconstructAt] at h
  | split k p0 lr rr l r ihl ihr =>
      intro e hr f' a b h
      cases hr with
      | split kind par lrule rrule lf rt hchain hlft hrgt =>
          simp only [Forest.reconstructAt] at h
          split at h
          · rename_i hp
            have hf' : f' = .leaf p0 := Forest.reconstructHere_nodes h
            subst hf'
            exact Forest.Recovers.leaf p0 hchain
          · rename_i hp
            split at h
            · rename_i l' a' b' hl
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              exact Forest.Recovers.split k p0 lr rr l' r hchain (ihl hlft hl) hrgt
            · rename_i hl
              split at h
              · rename_i r' a' b' hr'
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                exact Forest.Recovers.split k p0 lr rr l r' hchain hlft (ihr hrgt hr')
              · cases h

/-- Reconstruction preserves whole-forest recovery. -/
theorem wellRecovered_reconstructAt {f : Forest} {id : CapId} {restores : List Restore}
    (hw : f.WellRecovered restores) :
    ∀ {f' : Forest} {a b : Leaf}, f.reconstructAt id = some (f', a, b) →
      f'.WellRecovered restores := by
  induction f with
  | leaf c =>
      intro f' a b h
      simp [Forest.reconstructAt] at h
  | split k p0 lr rr l r ihl ihr =>
      intro f' a b h
      simp only [Forest.WellRecovered] at hw
      obtain ⟨hL, hR, hWL, hWR⟩ := hw
      simp only [Forest.reconstructAt] at h
      split at h
      · rename_i hp
        have hf' : f' = .leaf p0 := Forest.reconstructHere_nodes h
        subst hf'
        trivial
      · rename_i hp
        split at h
        · rename_i l' a' b' hl
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨Forest.recovers_reconstructAt hL hl, hR, ihl hWL hl, hWR⟩
        · rename_i hl
          split at h
          · rename_i r' a' b' hr'
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact ⟨hL, Forest.recovers_reconstructAt hR hr', hWL, ihr hWR hr'⟩
          · cases h

/-! ### Return: filtering the discharged record

A `return` retags the borrower back to its lender, retires the borrower name and
removes the discharged record from the restoration list. Identity recovery
survives because the record can only ever be the *last* step of a chain: a chain
that reached another record's lender from the borrower name would make the
borrower an outstanding lender, which the return guard excludes.
-/

/-- A chain either names the same identity twice, or its last record and the
prefix that reaches that record's lender. -/
theorem RestoreChain.unsnoc {restores : List Restore} {a b : CapId}
    (h : RestoreChain restores a b) :
    a = b ∨ ∃ (a' : CapId) (r : Restore), RestoreChain restores a a' ∧
      r ∈ restores ∧ r.lender = a' ∧ r.borrower = b := by
  induction h with
  | nil => exact Or.inl rfl
  | snoc r0 hprev hr hl =>
      exact Or.inr ⟨_, r0, hprev, hr, hl, rfl⟩

/-- A chain that ends away from the discharged borrower survives removing the
records borrowed by that name. -/
theorem RestoreChain.filter_ne {restores : List Restore} {borrower : CapId}
    (hguard : ∀ r ∈ restores, r.lender ≠ borrower) {a b : CapId}
    (h : RestoreChain restores a b) (hb : b ≠ borrower) :
    RestoreChain (restores.filter (fun x => decide (x.borrower ≠ borrower))) a b := by
  induction h with
  | nil => exact RestoreChain.nil _
  | snoc r0 hprev hr hl ih =>
      have hb0 := hguard r0 hr
      rw [hl] at hb0
      have hprev' := ih hb0
      have hmem : r0 ∈ restores.filter (fun x => decide (x.borrower ≠ borrower)) :=
        List.mem_filter.mpr ⟨hr, by simpa using hb⟩
      exact RestoreChain.snoc (a := a) r0 hprev' hmem hl

/-- A chain that ends at the discharged borrower becomes a chain to its lender
after the record is removed. -/
theorem RestoreChain.filter_to_lender {restores : List Restore} {borrower lender a : CapId}
    (hguard : ∀ r ∈ restores, r.lender ≠ borrower)
    (hrec : ∀ r ∈ restores, r.borrower = borrower → r.lender = lender)
    (ha : a ≠ borrower) (h : RestoreChain restores a borrower) :
    RestoreChain (restores.filter (fun x => decide (x.borrower ≠ borrower))) a lender := by
  rcases RestoreChain.unsnoc h with heq | ⟨a', r0, hprev, hr, hl, hb⟩
  · exact absurd heq ha
  · have hla : r0.lender = lender := hrec r0 hr hb
    have hne : a' ≠ borrower := by rw [← hl]; exact hguard r0 hr
    rw [← hla, hl]
    exact RestoreChain.filter_ne hguard hprev hne

/-- The separation facts a `return` needs at a forest: distinct node identities,
the only node carrying the returned name is the retagging site, and no rule
fragment carries it. -/
structure ReturnSite (f : Forest) (borrower : CapId) (p : Leaf) : Prop where
  /-- Authority node identities are distinct. -/
  nodup : (f.nodes.map Leaf.id).Nodup
  /-- The only node carrying the returned name is the retagged leaf. -/
  site : ∀ c ∈ f.nodes, c.id = borrower → c = p
  /-- No rule fragment carries the returned name. -/
  rule : ∀ x ∈ f.ruleIds, x ≠ borrower

/-- A subtree that contains no occurrence of the returned name. -/
structure Avoids (f : Forest) (borrower : CapId) : Prop where
  /-- No authority node carries the returned name. -/
  node : ∀ x ∈ f.nodes.map Leaf.id, x ≠ borrower
  /-- No rule fragment carries the returned name. -/
  rule : ∀ x ∈ f.ruleIds, x ≠ borrower

/-- An identity equal at two positions of a nodup map comes from the same
element. -/
theorem eq_of_mem_of_map_eq {α β : Type} {l : List α} {f : α → β}
    (hn : (l.map f).Nodup) {a b : α} (ha : a ∈ l) (hb : b ∈ l) (h : f a = f b) :
    a = b := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
      rw [List.map_cons, List.nodup_cons] at hn
      obtain ⟨hx, hxs⟩ := hn
      rcases List.mem_cons.mp ha with hhead | htail
      · rcases List.mem_cons.mp hb with hhead' | htailb
        · rw [hhead, hhead']
        · subst hhead
          exact absurd (h.symm ▸ List.mem_map.mpr ⟨b, htailb, rfl⟩) hx
      · rcases List.mem_cons.mp hb with hhead' | htailb
        · subst hhead'
          exact absurd (h ▸ List.mem_map.mpr ⟨a, htail, rfl⟩) hx
        · exact ih hxs htail htailb

/-- Node identities of a left subtree lift to the split. -/
theorem node_ids_mem_left {kind : RuleKind} {p lr rr : Leaf} {l r : Forest}
    {x : CapId} (hx : x ∈ l.nodes.map Leaf.id) :
    x ∈ (Forest.split kind p lr rr l r).nodes.map Leaf.id := by
  simp only [Forest.nodes, List.map_cons, List.map_append]
  exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl hx))

/-- Node identities of a right subtree lift to the split. -/
theorem node_ids_mem_right {kind : RuleKind} {p lr rr : Leaf} {l r : Forest}
    {x : CapId} (hx : x ∈ r.nodes.map Leaf.id) :
    x ∈ (Forest.split kind p lr rr l r).nodes.map Leaf.id := by
  simp only [Forest.nodes, List.map_cons, List.map_append]
  exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr hx))

/-- Rule identities of a left subtree lift to the split. -/
theorem rule_ids_mem_left {kind : RuleKind} {p lr rr : Leaf} {l r : Forest}
    {x : CapId} (hx : x ∈ l.ruleIds) :
    x ∈ (Forest.split kind p lr rr l r).ruleIds := by
  simp only [Forest.ruleIds, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inr (Or.inl hx))

/-- Rule identities of a right subtree lift to the split. -/
theorem rule_ids_mem_right {kind : RuleKind} {p lr rr : Leaf} {l r : Forest}
    {x : CapId} (hx : x ∈ r.ruleIds) :
    x ∈ (Forest.split kind p lr rr l r).ruleIds := by
  simp only [Forest.ruleIds, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inr (Or.inr hx))

/-- A current leaf of the left subtree is not the suspended parent. -/
theorem parent_ne_of_mem_left {kind : RuleKind} {par lrule rrule : Leaf} {lf rt : Forest}
    {p : Leaf}
    (hn : ((Forest.split kind par lrule rrule lf rt).nodes.map Leaf.id).Nodup)
    (hpl : p ∈ lf.nodes) : p ≠ par := by
  intro heq
  have hnd : (par.id :: (lf.nodes.map Leaf.id ++ rt.nodes.map Leaf.id)).Nodup := by
    simpa [Forest.nodes, List.map_cons, List.map_append] using hn
  exact (List.nodup_cons.mp hnd).1
    (heq ▸ List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨p, hpl, rfl⟩)))

/-- A current leaf of the right subtree is not the suspended parent. -/
theorem parent_ne_of_mem_right {kind : RuleKind} {par lrule rrule : Leaf} {lf rt : Forest}
    {p : Leaf}
    (hn : ((Forest.split kind par lrule rrule lf rt).nodes.map Leaf.id).Nodup)
    (hpr : p ∈ rt.nodes) : p ≠ par := by
  intro heq
  have hnd : (par.id :: (lf.nodes.map Leaf.id ++ rt.nodes.map Leaf.id)).Nodup := by
    simpa [Forest.nodes, List.map_cons, List.map_append] using hn
  exact (List.nodup_cons.mp hnd).1
    (heq ▸ List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨p, hpr, rfl⟩)))

/-- The return-site facts restrict to the left subtree. -/
theorem ReturnSite.left {kind : RuleKind} {p0 lr rr : Leaf} {l r : Forest}
    {borrower : CapId} {p : Leaf}
    (h : ReturnSite (Forest.split kind p0 lr rr l r) borrower p) :
    ReturnSite l borrower p := by
  have hnd : (p0.id :: (l.nodes.map Leaf.id ++ r.nodes.map Leaf.id)).Nodup := by
    simpa [Forest.nodes, List.map_cons, List.map_append] using h.nodup
  exact ⟨(List.nodup_append.mp (List.nodup_cons.mp hnd).2).1,
    fun c hc hcid => h.site c
      (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl hc))) hcid,
    fun x hx => h.rule x (rule_ids_mem_left hx)⟩

/-- The return-site facts restrict to the right subtree. -/
theorem ReturnSite.right {kind : RuleKind} {p0 lr rr : Leaf} {l r : Forest}
    {borrower : CapId} {p : Leaf}
    (h : ReturnSite (Forest.split kind p0 lr rr l r) borrower p) :
    ReturnSite r borrower p := by
  have hnd : (p0.id :: (l.nodes.map Leaf.id ++ r.nodes.map Leaf.id)).Nodup := by
    simpa [Forest.nodes, List.map_cons, List.map_append] using h.nodup
  exact ⟨(List.nodup_append.mp (List.nodup_cons.mp hnd).2).2.1,
    fun c hc hcid => h.site c
      (List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr hc))) hcid,
    fun x hx => h.rule x (rule_ids_mem_right hx)⟩

/-- The avoidance facts restrict to the left subtree. -/
theorem Avoids.left {kind : RuleKind} {p0 lr rr : Leaf} {l r : Forest}
    {borrower : CapId} (h : Avoids (Forest.split kind p0 lr rr l r) borrower) :
    Avoids l borrower :=
  ⟨fun x hx => h.node x (node_ids_mem_left hx), fun x hx => h.rule x (rule_ids_mem_left hx)⟩

/-- The avoidance facts restrict to the right subtree. -/
theorem Avoids.right {kind : RuleKind} {p0 lr rr : Leaf} {l r : Forest}
    {borrower : CapId} (h : Avoids (Forest.split kind p0 lr rr l r) borrower) :
    Avoids r borrower :=
  ⟨fun x hx => h.node x (node_ids_mem_right hx), fun x hx => h.rule x (rule_ids_mem_right hx)⟩

/-- The left subtree avoids the returned name when the retagged leaf is a node of
the right subtree: a duplicate identity would break node distinctness. -/
theorem Avoids.left_of_found_right {kind : RuleKind} {p0 lr rr : Leaf} {l r : Forest}
    {borrower : CapId} {p : Leaf}
    (hsite : ReturnSite (Forest.split kind p0 lr rr l r) borrower p)
    (hpr : p ∈ r.nodes) : Avoids l borrower := by
  have hnd : (p0.id :: (l.nodes.map Leaf.id ++ r.nodes.map Leaf.id)).Nodup := by
    simpa [Forest.nodes, List.map_cons, List.map_append] using hsite.nodup
  obtain ⟨-, -, hdisj⟩ := List.nodup_append.mp (List.nodup_cons.mp hnd).2
  refine ⟨?_, fun x hx => hsite.rule x (rule_ids_mem_left hx)⟩
  intro x hx hxb
  obtain ⟨c, hc, hcid⟩ := List.mem_map.mp hx
  have hcf : c ∈ (Forest.split kind p0 lr rr l r).nodes := by
    simp only [Forest.nodes]
    exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl hc))
  have hcp : c = p := hsite.site c hcf (by rw [hcid, hxb])
  exact hdisj c.id (List.mem_map.mpr ⟨c, hc, rfl⟩) p.id
    (List.mem_map.mpr ⟨p, hpr, rfl⟩) (by rw [hcp])

/-- The right subtree avoids the returned name when the retagged leaf is a node
of the left subtree. -/
theorem Avoids.right_of_found_left {kind : RuleKind} {p0 lr rr : Leaf} {l r : Forest}
    {borrower : CapId} {p : Leaf}
    (hsite : ReturnSite (Forest.split kind p0 lr rr l r) borrower p)
    (hpl : p ∈ l.nodes) : Avoids r borrower := by
  have hnd : (p0.id :: (l.nodes.map Leaf.id ++ r.nodes.map Leaf.id)).Nodup := by
    simpa [Forest.nodes, List.map_cons, List.map_append] using hsite.nodup
  obtain ⟨-, -, hdisj⟩ := List.nodup_append.mp (List.nodup_cons.mp hnd).2
  refine ⟨?_, fun x hx => hsite.rule x (rule_ids_mem_right hx)⟩
  intro x hx hxb
  obtain ⟨c, hc, hcid⟩ := List.mem_map.mp hx
  have hcf : c ∈ (Forest.split kind p0 lr rr l r).nodes := by
    simp only [Forest.nodes]
    exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr hc))
  have hcp : c = p := hsite.site c hcf (by rw [hcid, hxb])
  exact hdisj p.id (List.mem_map.mpr ⟨p, hpl, rfl⟩) c.id
    (List.mem_map.mpr ⟨c, hc, rfl⟩) (by rw [hcp])

/-- Removing the discharged record preserves recovery for a subtree that carries
no occurrence of the returned name. -/
theorem recovers_filter {restores : List Restore} {borrower : CapId}
    (hguard : ∀ r ∈ restores, r.lender ≠ borrower) {f : Forest} {e : CapId}
    (hr : f.Recovers restores e) :
    Avoids f borrower →
      f.Recovers (restores.filter (fun x => decide (x.borrower ≠ borrower))) e := by
  induction hr with
  | leaf c0 hchain =>
      intro havoid
      have hcne : c0.id ≠ borrower :=
        havoid.node c0.id (List.mem_map.mpr ⟨c0, by simp [Forest.nodes], rfl⟩)
      exact Forest.Recovers.leaf c0 (RestoreChain.filter_ne hguard hchain hcne)
  | split kind par lrule rrule lf rt hchain hlft hrgt ihl ihr =>
      intro havoid
      have hpne : par.id ≠ borrower :=
        havoid.node par.id (List.mem_map.mpr ⟨par, by simp [Forest.nodes], rfl⟩)
      exact Forest.Recovers.split kind par lrule rrule lf rt
        (RestoreChain.filter_ne hguard hchain hpne)
        (ihl (Avoids.left havoid)) (ihr (Avoids.right havoid))

/-- Removing the discharged record preserves whole-forest recovery for a subtree
that carries no occurrence of the returned name. -/
theorem wellRecovered_filter {restores : List Restore} {borrower : CapId}
    (hguard : ∀ r ∈ restores, r.lender ≠ borrower) {f : Forest}
    (hw : f.WellRecovered restores) (havoid : Avoids f borrower) :
    f.WellRecovered (restores.filter (fun x => decide (x.borrower ≠ borrower))) := by
  induction f with
  | leaf c => trivial
  | split k p0 lr rr l r ihl ihr =>
      simp only [Forest.WellRecovered] at hw ⊢
      exact ⟨recovers_filter hguard hw.1 (Avoids.left havoid), recovers_filter hguard hw.2.1
          (Avoids.right havoid), ihl hw.2.2.1 (Avoids.left havoid),
        ihr hw.2.2.2 (Avoids.right havoid)⟩

/-- Removing the discharged record preserves recovery of the retagged subtree:
a chain to the borrower becomes a chain to the lender. -/
theorem recovers_return {restores : List Restore} {borrower lender : CapId}
    (hguard : ∀ r ∈ restores, r.lender ≠ borrower)
    (hrec : ∀ r ∈ restores, r.borrower = borrower → r.lender = lender) {f : Forest}
    {e : CapId} (hr : f.Recovers restores e) :
    e ≠ borrower → ∀ {p : Leaf} {f' : Forest},
      ReturnSite f borrower p → f.retagLeaf borrower lender = some (f', p) →
        f'.Recovers (restores.filter (fun x => decide (x.borrower ≠ borrower))) e := by
  induction hr with
  | leaf c0 hchain =>
      intro he p f' hsite hret
      unfold Forest.retagLeaf at hret
      simp only [Forest.modifyLeafAt] at hret
      split at hret
      · rename_i hcid
        unfold retagLeafAt at hret
        split at hret
        · simp only [Option.some.injEq, Prod.mk.injEq] at hret
          obtain ⟨rfl, rfl⟩ := hret
          exact Forest.Recovers.leaf {c0 with id := lender}
            (RestoreChain.filter_to_lender hguard hrec he
              (by rwa [hcid] at hchain))
        · cases hret
      · cases hret
  | split kind par lrule rrule lf rt hchain hlft hrgt ihl ihr =>
      intro he p f' hsite hret
      unfold Forest.retagLeaf at hret
      simp only [Forest.modifyLeafAt] at hret
      split at hret
      · rename_i l' c' hl
        simp only [Option.some.injEq, Prod.mk.injEq] at hret
        obtain ⟨rfl, rfl⟩ := hret
        have hpl : c' ∈ lf.nodes := (Forest.retagLeaf_found hl).2
        have hpne : par.id ≠ borrower := by
          intro heq
          have hpar : par = c' := hsite.site par (by simp [Forest.nodes]) heq
          exact (parent_ne_of_mem_left hsite.nodup hpl) hpar.symm
        exact Forest.Recovers.split kind par lrule rrule l' rt
          (RestoreChain.filter_ne hguard hchain hpne)
          (ihl (hsite.rule lrule.id (by simp [Forest.ruleIds])) (ReturnSite.left hsite) hl)
          (recovers_filter hguard hrgt (Avoids.right_of_found_left hsite hpl))
      · rename_i hl
        split at hret
        · rename_i r' c' hr'
          simp only [Option.some.injEq, Prod.mk.injEq] at hret
          obtain ⟨rfl, rfl⟩ := hret
          have hpr : c' ∈ rt.nodes := (Forest.retagLeaf_found hr').2
          have hpne : par.id ≠ borrower := by
            intro heq
            have hpar : par = c' := hsite.site par (by simp [Forest.nodes]) heq
            exact (parent_ne_of_mem_right hsite.nodup hpr) hpar.symm
          exact Forest.Recovers.split kind par lrule rrule lf r'
            (RestoreChain.filter_ne hguard hchain hpne)
            (recovers_filter hguard hlft (Avoids.left_of_found_right hsite hpr))
            (ihr (hsite.rule rrule.id (by simp [Forest.ruleIds])) (ReturnSite.right hsite) hr')
        · cases hret

/-- A `return` preserves whole-forest recovery. -/
theorem wellRecovered_return {restores : List Restore} {borrower lender : CapId}
    (hguard : ∀ r ∈ restores, r.lender ≠ borrower)
    (hrec : ∀ r ∈ restores, r.borrower = borrower → r.lender = lender) {f : Forest}
    (hw : f.WellRecovered restores) :
    ∀ {p : Leaf} {f' : Forest}, ReturnSite f borrower p →
      f.retagLeaf borrower lender = some (f', p) →
        f'.WellRecovered (restores.filter (fun x => decide (x.borrower ≠ borrower))) := by
  induction f with
  | leaf c =>
      intro p f' hsite hret
      unfold Forest.retagLeaf at hret
      simp only [Forest.modifyLeafAt] at hret
      split at hret
      · rename_i hcid
        unfold retagLeafAt at hret
        split at hret
        · simp only [Option.some.injEq, Prod.mk.injEq] at hret
          obtain ⟨rfl, rfl⟩ := hret
          trivial
        · cases hret
      · cases hret
  | split k p0 lr rr l r ihl ihr =>
      intro p f' hsite hret
      simp only [Forest.WellRecovered] at hw
      obtain ⟨hL, hR, hWL, hWR⟩ := hw
      unfold Forest.retagLeaf at hret
      simp only [Forest.modifyLeafAt] at hret
      split at hret
      · rename_i l' c' hl
        simp only [Option.some.injEq, Prod.mk.injEq] at hret
        obtain ⟨rfl, rfl⟩ := hret
        have hpl : c' ∈ l.nodes := (Forest.retagLeaf_found hl).2
        exact ⟨recovers_return hguard hrec hL
            (hsite.rule lr.id (by simp [Forest.ruleIds])) (ReturnSite.left hsite) hl,
          recovers_filter hguard hR (Avoids.right_of_found_left hsite hpl),
          ihl hWL (ReturnSite.left hsite) hl,
          wellRecovered_filter hguard hWR (Avoids.right_of_found_left hsite hpl)⟩
      · rename_i hl
        split at hret
        · rename_i r' c' hr'
          simp only [Option.some.injEq, Prod.mk.injEq] at hret
          obtain ⟨rfl, rfl⟩ := hret
          have hpr : c' ∈ r.nodes := (Forest.retagLeaf_found hr').2
          exact ⟨recovers_filter hguard hL (Avoids.left_of_found_right hsite hpr),
            recovers_return hguard hrec hR
              (hsite.rule rr.id (by simp [Forest.ruleIds])) (ReturnSite.right hsite) hr',
            wellRecovered_filter hguard hWL (Avoids.left_of_found_right hsite hpr),
            ihr hWR (ReturnSite.right hsite) hr'⟩
        · cases hret

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

/-- Outstanding obligations are ordered so that following a delegation strictly
decreases the index in `restores`. Borrowing prepends a record, so a newer
borrower precedes the obligation of the lender it borrowed from; a dependency
therefore runs from a later record to an earlier one. -/
def State.RestoreOrder (s : State) : Prop :=
  ∀ r ∈ s.restores, ∀ r' ∈ s.restores, Restore.Depends r r' →
    s.restores.idxOf r' < s.restores.idxOf r

/-- Positive-length delegation among the outstanding obligations of one state.
Every step stays inside `restores`, so the list order bounds the whole path. -/
inductive State.RestoreReaches (s : State) (r : Restore) : Restore → Prop
  | single {r' : Restore} : r ∈ s.restores → Restore.Depends r r' →
      r' ∈ s.restores → State.RestoreReaches s r r'
  | tail {r' r'' : Restore} : State.RestoreReaches s r r' →
      r' ∈ s.restores → Restore.Depends r' r'' → r'' ∈ s.restores →
      State.RestoreReaches s r r''

/-- A terminal obligation: no outstanding obligation continues from it, and its
recorded resource agrees with a node of the current forest. -/
def State.RestoreTerminal (s : State) (r : Restore) (c : Leaf) : Prop :=
  r ∈ s.restores ∧ (∀ r' ∈ s.restores, ¬ Restore.Depends r r') ∧
  c ∈ s.forest.nodes ∧ c.id = r.borrower ∧ r.Agrees c

/-- The frontier covers every byte of the allocation. -/
def State.Covered (s : State) : Prop :=
  ∀ x, x < s.len → s.forest.budget x = s.D

/-- Every suspension's children recover the rule fragment identities the
suspension records, and every nested suspension does so too. Resource
realization says the authority under a suspension still exists; recovery says the
names a reconstruction must recover are still reachable through accepted
operations, so an outstanding protocol is not stranded on an identity no accepted
transition can produce. -/
def State.Recovers (s : State) : Prop := s.forest.WellRecovered s.restores

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
* `lenders_not_retired` — a lender awaiting return is not a retired name, so the
  identity the return protocol must restore is still a usable access name. The
  dynamic return guard tests the same condition; this account is what makes the
  conclusion hold of every accepted state rather than of guarded operations
  alone.
* `borrower_not_rule` — a borrower identity is not also a rule fragment, so a
  suspension cannot retire a live obligation's identity.
* `restore_realized` — every obligation's borrower either holds a current or
  suspended fragment with the recorded resource, or has lent that fragment
  onward to another outstanding obligation.
* `node_agrees` and `nested_agrees` — the resource recorded by an obligation
  agrees with its live fragment, and nested obligations agree on the same
  resource; this is what prevents one budget from being claimed twice.
* `restore_order` — following an onward delegation strictly decreases the index
  in `restores`, so no cycle of obligations can justify itself; with
  `restore_realized` every obligation then reaches a terminal forest node.
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
  /-- An outstanding lender has not been retired, so the identity the return
  protocol must eventually restore is still a usable access name. The dynamic
  return guard tests the same condition; this account states that no accepted
  transition can leave an obligation whose target is already unusable. -/
  lenders_not_retired : ∀ r ∈ s.restores, r.lender ∉ s.retired
  borrower_not_rule : ∀ r ∈ s.restores, r.borrower ∉ s.forest.ruleIds
  restore_realized : ∀ r ∈ s.restores,
      (∃ c ∈ s.forest.nodes, c.id = r.borrower ∧ r.Agrees c) ∨
      (∃ r' ∈ s.restores, r'.lender = r.borrower)
  node_agrees : ∀ r ∈ s.restores, ∀ c ∈ s.forest.nodes,
      c.id = r.borrower → r.Agrees c
  nested_agrees : ∀ r ∈ s.restores, ∀ r' ∈ s.restores,
      r'.lender = r.borrower → r.SameResource r'
  restore_order : s.RestoreOrder
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

/-- The component scope. Every authority fragment — a current leaf or a suspended
parent — describes this component's allocation, lies inside its extent, is empty
only when the whole allocation is empty, and carries at most the denominator's
share. Every outstanding obligation is described the same way. The denominator is
positive. Scope for the rule descriptors follows from this and coherence
(`State.Scope.rule_scope`); their authority is delayed by construction. -/
structure State.Scope (s : State) : Prop where
  denom_pos : 0 < s.D
  node_scope : ∀ c ∈ s.forest.nodes, c.InScope s.alloc s.len s.D
  restore_scope : ∀ r ∈ s.restores,
    r.alloc = s.alloc ∧ r.hi ≤ s.len ∧ (r.lo < r.hi ∨ s.len = 0) ∧ r.q ≤ s.D

/-- The state's forest is coherent. -/
def State.Coherent (s : State) : Prop := s.forest.Coherent

/-- The reconstruction invariant: the frontier is covered, every recorded rule
is checked, the ownership accounts are complete, the forest is coherent — every
current subtree realizes the rule fragment it was recorded for — every fragment
is in the component's allocation scope, and every suspension's rule identities
are recoverable. -/
def State.Inv (s : State) : Prop :=
  s.Covered ∧ s.forest.Valid ∧ s.Accounts ∧ s.Coherent ∧ s.Scope ∧ s.Recovers

/-- The covered half of the invariant. -/
theorem State.Inv.covered {s : State} (h : s.Inv) : s.Covered := h.1

/-- The validity half of the invariant. -/
theorem State.Inv.valid {s : State} (h : s.Inv) : s.forest.Valid := h.2.1

/-- The ownership accounts. -/
theorem State.Inv.accounts {s : State} (h : s.Inv) : s.Accounts := h.2.2.1

/-- Forest coherence. -/
theorem State.Inv.coherent {s : State} (h : s.Inv) : s.forest.Coherent := h.2.2.2.1

/-- Component allocation scope. -/
theorem State.Inv.scope {s : State} (h : s.Inv) : s.Scope := h.2.2.2.2.1

/-- Identity recovery of every suspension's rule fragments. -/
theorem State.Inv.recoverable {s : State} (h : s.Inv) : s.Recovers := h.2.2.2.2.2

/-- An invariant state's every suspension records rule identities its children
can still recover. -/
theorem State.Inv.suspension_recovers {s : State} (h : s.Inv) {susp : Forest.Suspension}
    (hs : susp ∈ s.forest.suspensions) :
    susp.left.Recovers s.restores susp.leftRule.id ∧
      susp.right.Recovers s.restores susp.rightRule.id :=
  Forest.wellRecovered_suspension h.recoverable hs

/-- An invariant state's outstanding lenders are not retired. -/
theorem State.Inv.lenders_not_retired {s : State} (h : s.Inv) {r : Restore}
    (hr : r ∈ s.restores) : r.lender ∉ s.retired :=
  h.accounts.lenders_not_retired r hr

/-- Rule descriptors are in scope: their allocation, extent and share are bounded
by the component's. An empty descriptor is admitted (it carries no bytes and no
current authority), which is why no non-emptiness is required here. -/
theorem State.Scope.rule_scope {s : State} (h : s.Scope) (hc : s.forest.Coherent) :
    ∀ c ∈ s.forest.ruleFragments, c.alloc = s.alloc ∧ c.hi ≤ s.len ∧ c.q ≤ s.D :=
  Forest.ruleFragments_scope hc h.node_scope

/-- Replacing the heap keeps the component scope: scope mentions only the
allocation, extent, denominator, forest and obligations. -/
theorem State.Scope.setHeap {s : State} (h : s.Scope) (h' : Heap) :
    ({ s with heap := h' } : State).Scope :=
  { denom_pos := h.denom_pos
    node_scope := h.node_scope
    restore_scope := h.restore_scope }

/-- Replacing the heap keeps the ownership accounts: no account field mentions
the heap. -/
theorem State.Accounts.setHeap {s : State} (h : s.Accounts) (h' : Heap) :
    ({ s with heap := h' } : State).Accounts :=
  { nodeIds_nodup := h.nodeIds_nodup
    issue_covers := h.issue_covers
    retired_absent := h.retired_absent
    restores_issued := h.restores_issued
    borrowers_nodup := h.borrowers_nodup
    lenders_nodup := h.lenders_nodup
    lender_ne_borrower := h.lender_ne_borrower
    dormant_absent := h.dormant_absent
    lenders_not_retired := h.lenders_not_retired
    borrower_not_rule := h.borrower_not_rule
    restore_realized := h.restore_realized
    node_agrees := h.node_agrees
    nested_agrees := h.nested_agrees
    restore_order := h.restore_order
    rule_fragments_issued := h.rule_fragments_issued }

/-- Replacing the heap keeps identity recovery: recovery mentions only the forest
and the outstanding obligations. -/
theorem State.Recovers.setHeap {s : State} (h : s.Recovers) (h' : Heap) :
    ({ s with heap := h' } : State).Recovers := h

/-- A state whose forest and obligations are unchanged keeps identity recovery. -/
theorem State.Recovers.of_forest {s s' : State} (hf : s'.forest = s.forest)
    (hrs : s'.restores = s.restores) (h : s.Recovers) : s'.Recovers := by
  unfold State.Recovers at h ⊢
  rwa [hf, hrs]

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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
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
        lenders_not_retired := ?_
        borrower_not_rule := ?_
        restore_realized := ?_
        node_agrees := ?_
        nested_agrees := ?_
        restore_order := ?_
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
    · intro r hr
      simp [State.initial] at hr
    · intro r hr
      simp [State.initial] at hr
    · intro id hid
      simp [State.initial, Forest.ruleIds] at hid
  · show (State.initial a n D pos rootId disposalId).forest.Coherent
    trivial
  · refine ⟨pos, ?_, ?_⟩
    · intro c hc
      simp only [State.initial, Forest.nodes, List.mem_singleton] at hc
      rcases hc with rfl
      refine ⟨rfl, Nat.le_refl _, ?_, Nat.le_refl _⟩
      show 0 < n ∨ n = 0
      omega
    · intro r hr
      simp [State.initial] at hr
  · show (State.initial a n D pos rootId disposalId).forest.WellRecovered []
    trivial

/-- Delegation paths compose. -/
theorem State.RestoreReaches.trans {s : State} {a b c : Restore}
    (hab : State.RestoreReaches s a b) (hbc : State.RestoreReaches s b c) :
    State.RestoreReaches s a c := by
  induction hbc with
  | single hb hd hc => exact .tail hab hb hd hc
  | tail _ hb hd hc ih => exact .tail ih hb hd hc

/-- Every positive delegation step strictly decreases the list index. -/
theorem State.Accounts.restoreReaches_idx_lt {s : State} (h : s.Accounts)
    {r r' : Restore} (hp : State.RestoreReaches s r r') :
    s.restores.idxOf r' < s.restores.idxOf r := by
  induction hp with
  | single hr hd hmem => exact h.restore_order _ hr _ hmem hd
  | tail _ hmem hd hmem' ih =>
      exact Nat.lt_trans (h.restore_order _ hmem _ hmem' hd) ih

/-- Restoration dependencies are acyclic: no outstanding obligation reaches
itself by a positive-length delegation path. -/
theorem State.Accounts.dependency_wellFounded {s : State} (h : s.Accounts)
    {r : Restore} : ¬ State.RestoreReaches s r r := by
  intro hp
  have := h.restoreReaches_idx_lt hp
  exact Nat.lt_irrefl _ this

/-- Resource agreement is transported along a delegation path. -/
theorem State.Accounts.restoreReaches_sameResource {s : State} (h : s.Accounts)
    {r r' : Restore} (hp : State.RestoreReaches s r r') :
    r.SameResource r' := by
  induction hp with
  | single hr hd hmem => exact h.nested_agrees _ hr _ hmem hd
  | tail _ hmem hd hmem' ih =>
      exact ih.trans (h.nested_agrees _ hmem _ hmem' hd)

/-- Every outstanding obligation reaches a terminal forest node by a finite
delegation path, and the obligation's recorded resource agrees with that node.
The terminal may be an active current leaf or a suspended reconstruction parent;
`restore_terminal_agrees` transports the resource agreement back along the
path, and `Forest.suspended_frontier_realizes` connects a suspended parent to
its rule descendants. -/
theorem State.Accounts.restore_reaches_terminal {s : State} (h : s.Accounts)
    {r : Restore} (hr : r ∈ s.restores) :
    ∃ r' : Restore, ∃ c : Leaf,
      State.RestoreTerminal s r' c ∧ (r' = r ∨ State.RestoreReaches s r r') ∧
      r.Agrees c := by
  have key : ∀ n : Nat, ∀ r : Restore, r ∈ s.restores →
      s.restores.idxOf r < n →
      ∃ r' : Restore, ∃ c : Leaf,
        State.RestoreTerminal s r' c ∧
        (r' = r ∨ State.RestoreReaches s r r') ∧ r.Agrees c := by
    intro n
    induction n with
    | zero =>
        intro r _ hlt
        omega
    | succ n ih =>
        intro r hr hlt
        by_cases hdel : ∃ r' ∈ s.restores, Restore.Depends r r'
        · obtain ⟨r', hr', hd⟩ := hdel
          have hidx : s.restores.idxOf r' < s.restores.idxOf r :=
            h.restore_order r hr r' hr' hd
          obtain ⟨rT, c, hterm, hpath, hrag⟩ := ih r' hr' (by omega)
          refine ⟨rT, c, hterm, ?_, ?_⟩
          · rcases hpath with rfl | hp
            · exact Or.inr (State.RestoreReaches.single hr hd hr')
            · exact Or.inr ((State.RestoreReaches.single hr hd hr').trans hp)
          · exact Restore.Agrees.of_sameResource
              (h.nested_agrees r hr r' hr' hd).symm hrag
        · rcases h.restore_realized r hr with hnode | hdeleg
          · obtain ⟨c, hc, hcid, hag⟩ := hnode
            exact ⟨r, c,
              ⟨hr, (fun r' hr' hd => hdel ⟨r', hr', hd⟩), hc, hcid, hag⟩,
              Or.inl rfl, hag⟩
          · exact absurd hdeleg hdel
  exact key (s.restores.idxOf r + 1) r hr (Nat.lt_succ_self _)

/-- The resource agreement of a terminal node is the agreement of every
obligation on the delegation path that reaches it. -/
theorem State.Accounts.restore_terminal_agrees {s : State} (h : s.Accounts)
    {r r' : Restore} {c : Leaf} (hr : r ∈ s.restores)
    (hp : r' = r ∨ State.RestoreReaches s r r')
    (ht : State.RestoreTerminal s r' c) : r.Agrees c := by
  have hs : r.SameResource r' := by
    rcases hp with rfl | hp
    · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · exact h.restoreReaches_sameResource hp
  exact Restore.Agrees.of_sameResource hs.symm ht.2.2.2.2

/-- The invariant derives terminal resource realization without any caller-
supplied subtree budget: every outstanding obligation reaches a terminal node
whose recorded resource agrees with the obligation, and that node's recorded
resource is realized by everything actually below it. -/
theorem State.Inv.restore_terminal_frontier {s : State} (h : s.Inv) {r : Restore}
    (hr : r ∈ s.restores) :
    ∃ r' c, State.RestoreTerminal s r' c ∧
      (r' = r ∨ State.RestoreReaches s r r') ∧ r.Agrees c ∧
      s.forest.NodeRealized c := by
  obtain ⟨-, -, hacct, hcoh, -, -⟩ := h
  obtain ⟨r', c, hterm, hpath, hag⟩ := hacct.restore_reaches_terminal hr
  exact ⟨r', c, hterm, hpath, hag, Forest.coherent_nodeRealized hcoh hterm.2.2.1⟩

/-- A terminal suspended parent is realized by the two current subtrees its
suspension records: their frontier budget is the parent's and they lie inside the
parent's resource. No extra hypothesis is supplied. -/
theorem State.Inv.terminal_suspended_realizes {s : State} (h : s.Inv)
    (susp : Forest.Suspension) (hs : susp ∈ s.forest.suspensions) :
    (∀ x, susp.left.budget x + susp.right.budget x = (Forest.leaf susp.parent).budget x) ∧
      susp.left.Inside susp.parent ∧ susp.right.Inside susp.parent :=
  Forest.coherent_suspension_realizes h.coherent hs

/-- The index of an element distinct from a prepended head shifts by one. -/
private theorem idxOf_cons_ne_restore {l : List Restore} {a b : Restore} (h : a ≠ b) :
    (a :: l).idxOf b = l.idxOf b + 1 := by
  simp [List.idxOf_cons, h]

/-- Filtering preserves the strict index order of two retained records. -/
private theorem idxOf_filter_lt_restore {l : List Restore} {p : Restore → Bool}
    {a b : Restore} (ha : a ∈ l.filter p) (hb : b ∈ l.filter p)
    (h : l.idxOf a < l.idxOf b) :
    (l.filter p).idxOf a < (l.filter p).idxOf b := by
  induction l with
  | nil => exact absurd ha (by simp)
  | cons x xs ih =>
      by_cases hx : p x
      · rw [List.filter_cons, if_pos hx] at ha hb ⊢
        rcases List.mem_cons.mp ha with h_eq_a | ha
        · subst a
          rcases List.mem_cons.mp hb with h_eq_b | hb
          · subst b
            exact absurd h (Nat.lt_irrefl _)
          · have hxb : x ≠ b := by
              intro hbeq
              subst b
              rw [List.idxOf_cons_self] at h
              omega
            rw [List.idxOf_cons_self, idxOf_cons_ne_restore hxb]
            omega
        · rcases List.mem_cons.mp hb with h_eq_b | hb
          · subst b
            rw [List.idxOf_cons_self] at h
            omega
          · by_cases hxa : x = a
            · subst a
              have hxb : x ≠ b := by
                intro hbeq
                subst b
                rw [List.idxOf_cons_self] at h
                omega
              rw [List.idxOf_cons_self, idxOf_cons_ne_restore hxb]
              omega
            · have hxb : x ≠ b := by
                intro hbeq
                subst b
                rw [List.idxOf_cons_self] at h
                omega
              have hx' : xs.idxOf a < xs.idxOf b := by
                rw [idxOf_cons_ne_restore hxa,
                  idxOf_cons_ne_restore hxb] at h
                omega
              have hrec := ih ha hb hx'
              rw [idxOf_cons_ne_restore hxa, idxOf_cons_ne_restore hxb]
              omega
      · rw [List.filter_cons, if_neg hx] at ha hb ⊢
        have hpa : p a := (List.mem_filter.mp ha).2
        have hpb : p b := (List.mem_filter.mp hb).2
        have hxa : x ≠ a := by
          intro heq
          exact hx (heq ▸ hpa)
        have hxb : x ≠ b := by
          intro heq
          exact hx (heq ▸ hpb)
        rw [idxOf_cons_ne_restore hxa, idxOf_cons_ne_restore hxb] at h
        have hx' : xs.idxOf a < xs.idxOf b := by omega
        exact ih ha hb hx'

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

/-- The write guard. A write is authorised by a current active fragment of *this*
component's allocation, holding the whole share at a read--write ceiling and
covering the offset. The allocation conjunct binds the authority to the bytes the
write actually updates. -/
def State.WriteGuard (s : State) (c : Leaf) (i : Nat) : Prop :=
  c.state = .active ∧ c.q = s.D ∧ c.ceiling = .readWrite ∧ c.alloc = s.alloc ∧
  c.lo ≤ i ∧ i < c.hi

instance (s : State) (c : Leaf) (i : Nat) : Decidable (s.WriteGuard c i) := by
  unfold State.WriteGuard
  infer_instance

/-- Write a byte through an active whole-share fragment of a read--write
ceiling. The access name must be a current leaf of this component. -/
def State.write (s : State) (id : CapId) (i : Nat) (v : UInt8) : Option State :=
  match s.forest.findLeaf? id with
  | none => none
  | some c =>
      if h : s.WriteGuard c i then
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
  · rename_i c _hfind
    split at h
    · rename_i _hg
      cases hw : s.heap.write? s.alloc i v with
      | none => simp [hw] at h
      | some h' =>
          simp only [hw, Option.some.injEq] at h
          subst h
          exact ⟨hinv.1, hinv.2.1, State.Accounts.setHeap hinv.2.2.1 h',
            hinv.2.2.2.1, State.Scope.setHeap hinv.2.2.2.2.1 h',
            State.Recovers.setHeap hinv.2.2.2.2.2 h'⟩
    · simp at h

/-- An accepted write is authorised by a current leaf of this component's
allocation, and updates that allocation. This is the guard theorem for the
allocation binding added to `State.WriteGuard`. -/
theorem State.write_guard {s s' : State} {id : CapId} {i : Nat} {v : UInt8}
    (h : s.write id i v = some s') :
    ∃ c : Leaf, s.forest.findLeaf? id = some c ∧ s.WriteGuard c i ∧
      c.alloc = s.alloc ∧ s'.alloc = s.alloc ∧ s'.len = s.len := by
  unfold State.write at h
  split at h
  · simp at h
  · rename_i c hfind
    split at h
    · rename_i hg
      cases hw : s.heap.write? s.alloc i v with
      | none => simp [hw] at h
      | some h' =>
          simp only [hw, Option.some.injEq] at h
          subst h
          exact ⟨c, hfind, hg, hg.2.2.2.1, rfl, rfl⟩
    · simp at h

/-- An accepted write's authorising fragment is in the component's allocation
scope, so the allocation its guard names is the one the write updates. This reads
the guard together with the invariant rather than the guard alone. -/
theorem State.Inv.write_scope {s s' : State} {id : CapId} {i : Nat} {v : UInt8}
    (h : s.write id i v = some s') (hinv : s.Inv) :
    ∃ c : Leaf, s.forest.findLeaf? id = some c ∧ c.alloc = s.alloc ∧
      c.hi ≤ s.len ∧ c.q = s.D ∧ c.lo ≤ i ∧ i < c.hi := by
  obtain ⟨c, hfind, hguard, halloc, -, -⟩ := State.write_guard h
  obtain ⟨hcleaf, -⟩ := Forest.findLeaf?_mem_leaves hfind
  have hsc := hinv.scope.node_scope c (Forest.mem_nodes_of_mem_leaves hcleaf)
  exact ⟨c, hfind, halloc, hsc.2.1, hguard.2.1, hguard.2.2.2.2.1, hguard.2.2.2.2.2⟩

/-- An accepted write updates the allocation its authorising fragment names, so
the authority and the bytes written agree. -/
theorem State.write_alloc {s s' : State} {id : CapId} {i : Nat} {v : UInt8}
    (h : s.write id i v = some s') :
    ∃ c : Leaf, ∃ h' : Heap, s.forest.findLeaf? id = some c ∧
      c.alloc = s.alloc ∧ s.heap.write? s.alloc i v = some h' ∧ s'.heap = h' := by
  unfold State.write at h
  split at h
  · simp at h
  · rename_i c hfind
    split at h
    · rename_i hg
      cases hw : s.heap.write? s.alloc i v with
      | none => simp [hw] at h
      | some h' =>
          simp only [hw, Option.some.injEq] at h
          subst h
          exact ⟨c, h', hfind, hg.2.2.2.1, rfl, rfl⟩
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
      if h : (c1 ∉ s.issued ∧ c2 ∉ s.issued ∧ c1 ∉ s.retired ∧ c2 ∉ s.retired) ∧
              (s.len = 0 ∨ (lo1 < hi1 ∧ lo2 < hi2)) then
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

/-- A checked spatial subdivision keeps identity recovery: the operation changes
one leaf into the suspension whose own children are freshly recovered. -/
theorem State.Recovers.splitSpatial {s s' : State} {parentId c1 c2 : CapId}
    {lo1 hi1 lo2 hi2 : Nat}
    (h : s.splitSpatial parentId c1 c2 lo1 hi1 lo2 hi2 = some s')
    (hs : s.Recovers) : s'.Recovers := by
  unfold State.splitSpatial at h
  split at h
  · simp at h
  · rename_i f' p hsplit
    split at h
    · rename_i _
      simp only [Option.some.injEq] at h
      subst h
      have hw := Forest.wellRecovered_splitSpatialAt (p := p) hsplit hs
      simpa [State.Recovers] using hw
    · simp at h

/-- A checked fractional subdivision keeps identity recovery. -/
theorem State.Recovers.splitFraction {s s' : State} {parentId c1 c2 : CapId}
    {q1 q2 : Nat}
    (h : s.splitFraction parentId c1 c2 q1 q2 = some s')
    (hs : s.Recovers) : s'.Recovers := by
  unfold State.splitFraction at h
  split at h
  · simp at h
  · rename_i f' p hsplit
    split at h
    · rename_i _
      simp only [Option.some.injEq] at h
      subst h
      have hw := Forest.wellRecovered_splitFractionAt (p := p) hsplit hs
      simpa [State.Recovers] using hw
    · simp at h

/-- Beginning a borrow keeps identity recovery: the new record links the leaf's
old identity to its new one. -/
theorem State.Recovers.borrow {s s' : State} {lender borrower : CapId}
    (h : s.borrow lender borrower = some s') (hs : s.Recovers) : s'.Recovers := by
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
        have hw := Forest.wellRecovered_retagLeaf (id := lender) (newId := borrower)
          (r := { lender := lender, borrower := borrower, alloc := p.alloc, lo := p.lo,
                  hi := p.hi, q := p.q, ceiling := p.ceiling })
          hretag rfl rfl hs
        simpa [State.Recovers] using hw
    · simp at h

/-- Reconstruction keeps identity recovery. -/
theorem State.Recovers.reconstruct {s s' : State} {parentId : CapId}
    (h : s.reconstruct parentId = some s') (hs : s.Recovers) : s'.Recovers := by
  unfold State.reconstruct at h
  split at h
  · simp at h
  · rename_i f' lf rf hrec
    simp only [Option.some.injEq] at h
    subst h
    have hw := Forest.wellRecovered_reconstructAt (f := s.forest) (id := parentId)
      (restores := s.restores) hs hrec
    simpa [State.Recovers] using hw

/-- Returning a borrow keeps identity recovery: the discharged record can only be
the last step of a chain, so the chain now ends at the restored lender. -/
theorem State.Recovers.return {s s' : State} {borrower : CapId}
    (h : s.return borrower = some s') (hinv : s.Inv) : s'.Recovers := by
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
          have hrmem : r ∈ s.restores := List.mem_of_find?_eq_some hrestore
          have hrb : r.borrower = borrower := by
            have hb := List.find?_some hrestore
            simpa using hb
          have hguard : ∀ r' ∈ s.restores, r'.lender ≠ borrower :=
            fun r' hr' => hok.2.2.2.2.2.2.2 r' hr'
          have hrec : ∀ r' ∈ s.restores, r'.borrower = borrower → r'.lender = r.lender := by
            intro r' hr' hbr
            have heq : r' = r :=
              Forest.eq_of_mem_of_map_eq hinv.accounts.borrowers_nodup hr' hrmem
                (by rw [hbr, hrb])
            rw [heq]
          have hp := Forest.retagLeaf_found hretag
          have hsite : Forest.ReturnSite s.forest borrower p :=
            { nodup := hinv.accounts.nodeIds_nodup
              site := by
                intro c' hc' hcid
                exact Forest.eq_of_mem_of_map_eq hinv.accounts.nodeIds_nodup hc' hp.2
                  (by rw [hcid, hp.1])
              rule := by
                intro x hx heq
                exact (hrb ▸ hinv.accounts.borrower_not_rule r hrmem) (heq ▸ hx) }
          have hw := Forest.wellRecovered_return (restores := s.restores)
            (borrower := borrower) (lender := r.lender) hguard hrec hinv.recoverable
            hsite hretag
          simpa [State.Recovers] using hw
      · simp at h

/-- A checked spatial subdivision preserves the reconstruction invariant. -/
theorem State.splitSpatial_inv {s s' : State} {parentId c1 c2 : CapId}
    {lo1 hi1 lo2 hi2 : Nat}
    (h : s.splitSpatial parentId c1 c2 lo1 hi1 lo2 hi2 = some s')
    (hinv : s.Inv) : s'.Inv := by
  obtain ⟨hcov, hval, hacct, hcoh, hscope, hrecov⟩ := hinv
  have hrecResult := State.Recovers.splitSpatial h hrecov
  unfold State.splitSpatial at h
  split at h
  · simp at h
  · rename_i f' p hsplit
    split at h
    · rename_i hok
      obtain ⟨hfresh, hne⟩ := hok
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
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
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
            lenders_not_retired := hacct.lenders_not_retired
            borrower_not_rule := ?_
            restore_realized := ?_
            node_agrees := ?_
            nested_agrees := ?_
            restore_order := ?_
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
        · exact hacct.restore_order
        · intro id hid
          rcases Forest.splitSpatialAt_ruleIds_mem hsplit hid with ho | ho | ho
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (hacct.rule_fragments_issued id ho))
          · exact ho ▸ List.mem_cons_self
          · exact ho ▸ List.mem_cons_of_mem _ List.mem_cons_self
      · exact Forest.splitSpatialAt_coherent hsplit hcoh
      · exact ⟨hscope.denom_pos,
          Forest.splitSpatialAt_nodes_scope hsplit hscope.node_scope hne,
          fun r hr => hscope.restore_scope r hr⟩
      · exact hrecResult
    · simp at h

/-- A checked fractional subdivision preserves the reconstruction invariant. -/
theorem State.splitFraction_inv {s s' : State} {parentId c1 c2 : CapId}
    {q1 q2 : Nat}
    (h : s.splitFraction parentId c1 c2 q1 q2 = some s')
    (hinv : s.Inv) : s'.Inv := by
  obtain ⟨hcov, hval, hacct, hcoh, hscope, hrecov⟩ := hinv
  have hrecResult := State.Recovers.splitFraction h hrecov
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
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
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
            lenders_not_retired := hacct.lenders_not_retired
            borrower_not_rule := ?_
            restore_realized := ?_
            node_agrees := ?_
            nested_agrees := ?_
            restore_order := ?_
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
        · exact hacct.restore_order
        · intro id hid
          rcases Forest.splitFractionAt_ruleIds_mem hsplit hid with ho | ho | ho
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (hacct.rule_fragments_issued id ho))
          · exact ho ▸ List.mem_cons_self
          · exact ho ▸ List.mem_cons_of_mem _ List.mem_cons_self
      · exact Forest.splitFractionAt_coherent hsplit hcoh
      · exact ⟨hscope.denom_pos,
          Forest.splitFractionAt_nodes_scope hsplit hscope.node_scope,
          fun r hr => hscope.restore_scope r hr⟩
      · exact hrecResult
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
  obtain ⟨hcov, hval, hacct, hcoh, hscope, hrecov⟩ := hinv
  have hrecResult := State.Recovers.reconstruct h hrecov
  unfold State.reconstruct at h
  split at h
  · simp at h
  · rename_i f' lf rf hrec
    simp only [Option.some.injEq] at h
    subst h
    have hsub : ∀ {c : Leaf}, c ∈ f'.nodes → c ∈ s.forest.nodes :=
      fun hc => Forest.reconstructAt_nodes_sub hrec hc
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
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
          lenders_not_retired := ?_
          borrower_not_rule := ?_
          restore_realized := ?_
          node_agrees := ?_
          nested_agrees := ?_
          restore_order := ?_
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
      · intro r hr hret
        obtain ⟨ha, hb⟩ := Forest.reconstructAt_removed_mem_nodes hrec
        have hne_l : r.lender ≠ lf.id := by
          intro heq
          exact hacct.dormant_absent r hr
            (heq ▸ List.mem_map.mpr ⟨lf, ha, rfl⟩)
        have hne_r : r.lender ≠ rf.id := by
          intro heq
          exact hacct.dormant_absent r hr
            (heq ▸ List.mem_map.mpr ⟨rf, hb, rfl⟩)
        rcases List.mem_cons.mp hret with heq | hret
        · exact hne_l heq
        · rcases List.mem_cons.mp hret with heq | hret
          · exact hne_r heq
          · exact hacct.lenders_not_retired r hr hret
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
      · exact hacct.restore_order
      · intro id hid
        exact hacct.rule_fragments_issued id
          (Forest.reconstructAt_ruleIds_mem hrec hid)
    · exact Forest.coherent_reconstructAt hrec hcoh
    · exact ⟨hscope.denom_pos,
        Forest.reconstructAt_nodes_scope hrec hscope.node_scope,
        fun r hr => hscope.restore_scope r hr⟩
    · exact hrecResult

/-- Beginning a borrow preserves the reconstruction invariant. -/
theorem State.borrow_inv {s s' : State} {lender borrower : CapId}
    (h : s.borrow lender borrower = some s') (hinv : s.Inv) : s'.Inv := by
  obtain ⟨hcov, hval, hacct, hcoh, hscope, hrecov⟩ := hinv
  have hrecResult := State.Recovers.borrow h hrecov
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
        have hhead_ne : ∀ r ∈ s.restores,
            (⟨lender, borrower, p.alloc, p.lo, p.hi, p.q, p.ceiling⟩ : Restore) ≠ r := by
          intro r hr heq
          have hb : r.borrower = borrower :=
            (congrArg Restore.borrower heq).symm
          exact hok.2.1 (by rw [← hb]; exact (hacct.restores_issued r hr).2)
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
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
              lenders_not_retired := ?_
              borrower_not_rule := ?_
              restore_realized := ?_
              node_agrees := ?_
              nested_agrees := ?_
              restore_order := ?_
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
          · intro r hr
            rcases List.mem_cons.mp hr with rfl | hr
            · exact hacct.retired_absent lender hLenderNode
            · exact hacct.lenders_not_retired r hr
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
          · intro r hr r' hr' hrel
            rcases List.mem_cons.mp hr with rfl | hr
            · rcases List.mem_cons.mp hr' with rfl | hr'
              · exact absurd (by simpa [Restore.Depends] using hrel) (Ne.symm hne)
              · have hrel' : r'.lender = borrower := by
                  simpa [Restore.Depends] using hrel
                exact absurd (hrel' ▸ (hacct.restores_issued r' hr').1) hok.2.1
            · rcases List.mem_cons.mp hr' with rfl | hr'
              · rw [List.idxOf_cons_self,
                  idxOf_cons_ne_restore (hhead_ne r hr)]
                omega
              · have hord := hacct.restore_order r hr r' hr' hrel
                rw [idxOf_cons_ne_restore (hhead_ne r' hr'),
                    idxOf_cons_ne_restore (hhead_ne r hr)]
                omega
          · intro id hid
            exact List.mem_cons_of_mem _
              (hacct.rule_fragments_issued id (Forest.retagLeaf_ruleIds_mem hretag hid))
        · exact Forest.retagLeaf_coherent hretag hcoh
        · refine ⟨hscope.denom_pos,
            Forest.retagLeaf_nodes_scope hretag hscope.node_scope, ?_⟩
          intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · exact hscope.node_scope p (Forest.retagLeaf_found hretag).2
          · exact hscope.restore_scope r hr
        · exact hrecResult
    · simp at h

/-- Returning a borrow preserves the reconstruction invariant. -/
theorem State.return_inv {s s' : State} {borrower : CapId}
    (h : s.return borrower = some s') (hinv : s.Inv) : s'.Inv := by
  have hrecResult := State.Recovers.return h hinv
  obtain ⟨hcov, hval, hacct, hcoh, hscope, hrecov⟩ := hinv
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
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
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
                lenders_not_retired := ?_
                borrower_not_rule := ?_
                restore_realized := ?_
                node_agrees := ?_
                nested_agrees := ?_
                restore_order := ?_
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
            · intro r' hr'
              obtain ⟨hr'_old, _⟩ := List.mem_filter.mp hr'
              intro hmem
              rcases List.mem_cons.mp hmem with heq | hmem
              · exact hok.2.2.2.2.2.2.2 r' hr'_old heq
              · exact hacct.lenders_not_retired r' hr'_old hmem
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
            · intro r' hr' r'' hr'' hrel
              change r' ∈ s.restores.filter
                (fun x => decide (x.borrower ≠ borrower)) at hr'
              change r'' ∈ s.restores.filter
                (fun x => decide (x.borrower ≠ borrower)) at hr''
              exact idxOf_filter_lt_restore
                (p := fun x => decide (x.borrower ≠ borrower))
                hr'' hr'
                (hacct.restore_order r' (List.mem_filter.mp hr').1 r''
                  (List.mem_filter.mp hr'').1 hrel)
            · intro id hid
              exact hacct.rule_fragments_issued id
                (Forest.retagLeaf_ruleIds_mem hretag hid)
          · exact Forest.retagLeaf_coherent hretag hcoh
          · refine ⟨hscope.denom_pos,
              Forest.retagLeaf_nodes_scope hretag hscope.node_scope, ?_⟩
            intro r' hr'
            exact hscope.restore_scope r' (List.mem_filter.mp hr').1
          · exact hrecResult
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
    · rename_i hok
      exact (hok.1.1 h).elim
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
