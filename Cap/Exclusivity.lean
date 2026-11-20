/-
Exclusivity of write authority.

The ledger's coverage invariant (`Owner.Covered`) is a per-byte conservation
statement. These lemmas turn it into the property the discipline exists for: at
any byte, at most one capability is writable. The proof is arithmetic once the
budget is known to count leaves: a present, unconsumed leaf whose footprint
contains the byte contributes its share to the budget, and two distinct such
leaves contribute both shares; a byte whose budget is `D` therefore cannot host
two whole shares.
-/
import Cap.Ledger
import Cap.Share
import Cap.Core
import Cap.Invariant

namespace Cap

namespace Tree

/-- A present, unconsumed leaf covering `x` contributes its share to the budget. -/
theorem budget_leaf_ge (t : Tree) (id : CapId) (c : Leaf) (x : Nat)
    (hfind : t.find? id = some c) (hstate : c.state ≠ .consumed)
    (hlo : c.lo ≤ x) (hhi : x < c.hi) :
    c.q ≤ t.budget x := by
  induction t with
  | leaf d =>
    simp only [Tree.find?] at hfind
    split at hfind
    · rename_i hid
      cases hfind
      simp [Tree.budget, Leaf.budget, hstate, hlo, hhi]
    · simp at hfind
  | frac n l r ihl ihr =>
    simp only [Tree.budget]
    cases hp : l.find? id with
    | some cl =>
      simp only [Tree.find?, hp] at hfind
      cases hfind
      have := ihl hp
      omega
    | none =>
      simp only [Tree.find?, hp] at hfind
      have := ihr hfind
      omega
  | spatial n l r ihl ihr =>
    simp only [Tree.budget]
    cases hp : l.find? id with
    | some cl =>
      simp only [Tree.find?, hp] at hfind
      cases hfind
      have := ihl hp
      omega
    | none =>
      simp only [Tree.find?, hp] at hfind
      have := ihr hfind
      omega

/-- Two distinct present, unconsumed leaves covering `x` contribute both shares. -/
theorem budget_two_leaves (t : Tree) :
    ∀ (id1 id2 : CapId) (c1 c2 : Leaf) (x : Nat), id1 ≠ id2 →
      t.find? id1 = some c1 → t.find? id2 = some c2 →
      c1.state ≠ .consumed → c2.state ≠ .consumed →
      c1.lo ≤ x → x < c1.hi → c2.lo ≤ x → x < c2.hi →
      c1.q + c2.q ≤ t.budget x := by
  induction t with
  | leaf d =>
    intro id1 id2 c1 c2 x h12 h1 h2 hs1 hs2 hl1 hh1 hl2 hh2
    simp only [Tree.find?] at h1 h2
    split at h1
    · rename_i hid1
      split at h2
      · rename_i hid2
        cases h1
        cases h2
        exact absurd (hid1.symm.trans hid2) h12
      · simp at h2
    · simp at h1
  | frac n l r ihl ihr =>
    intro id1 id2 c1 c2 x h12 h1 h2 hs1 hs2 hl1 hh1 hl2 hh2
    simp only [Tree.budget]
    cases hp1 : l.find? id1 with
    | some cl1 =>
      simp only [Tree.find?, hp1] at h1
      have h1L : l.find? id1 = some c1 := by rw [hp1]; exact h1
      cases hp2 : l.find? id2 with
      | some cl2 =>
        simp only [Tree.find?, hp2] at h2
        have h2L : l.find? id2 = some c2 := by rw [hp2]; exact h2
        have := ihl id1 id2 c1 c2 x h12 h1L h2L hs1 hs2 hl1 hh1 hl2 hh2
        omega
      | none =>
        simp only [Tree.find?, hp2] at h2
        have h1' := Tree.budget_leaf_ge l id1 c1 x h1L hs1 hl1 hh1
        have h2' := Tree.budget_leaf_ge r id2 c2 x h2 hs2 hl2 hh2
        omega
    | none =>
      simp only [Tree.find?, hp1] at h1
      cases hp2 : l.find? id2 with
      | some cl2 =>
        simp only [Tree.find?, hp2] at h2
        have h2L : l.find? id2 = some c2 := by rw [hp2]; exact h2
        have h1' := Tree.budget_leaf_ge r id1 c1 x h1 hs1 hl1 hh1
        have h2' := Tree.budget_leaf_ge l id2 c2 x h2L hs2 hl2 hh2
        omega
      | none =>
        simp only [Tree.find?, hp2] at h2
        have := ihr id1 id2 c1 c2 x h12 h1 h2 hs1 hs2 hl1 hh1 hl2 hh2
        omega
  | spatial n l r ihl ihr =>
    intro id1 id2 c1 c2 x h12 h1 h2 hs1 hs2 hl1 hh1 hl2 hh2
    simp only [Tree.budget]
    cases hp1 : l.find? id1 with
    | some cl1 =>
      simp only [Tree.find?, hp1] at h1
      have h1L : l.find? id1 = some c1 := by rw [hp1]; exact h1
      cases hp2 : l.find? id2 with
      | some cl2 =>
        simp only [Tree.find?, hp2] at h2
        have h2L : l.find? id2 = some c2 := by rw [hp2]; exact h2
        have := ihl id1 id2 c1 c2 x h12 h1L h2L hs1 hs2 hl1 hh1 hl2 hh2
        omega
      | none =>
        simp only [Tree.find?, hp2] at h2
        have h1' := Tree.budget_leaf_ge l id1 c1 x h1L hs1 hl1 hh1
        have h2' := Tree.budget_leaf_ge r id2 c2 x h2 hs2 hl2 hh2
        omega
    | none =>
      simp only [Tree.find?, hp1] at h1
      cases hp2 : l.find? id2 with
      | some cl2 =>
        simp only [Tree.find?, hp2] at h2
        have h2L : l.find? id2 = some c2 := by rw [hp2]; exact h2
        have h1' := Tree.budget_leaf_ge r id1 c1 x h1 hs1 hl1 hh1
        have h2' := Tree.budget_leaf_ge l id2 c2 x h2L hs2 hl2 hh2
        omega
      | none =>
        simp only [Tree.find?, hp2] at h2
        have := ihr id1 id2 c1 c2 x h12 h1 h2 hs1 hs2 hl1 hh1 hl2 hh2
        omega

end Tree

/-- At a byte of a well-formed owner, at most one capability is writable: two
writable capabilities at the same index have the same identifier. -/
theorem Owner.no_two_writable {o : Owner} {D : Nat} {id1 id2 : CapId} {i : Nat}
    (hwf : o.WellFormed D)
    (h1 : o.writableB D id1 i = true) (h2 : o.writableB D id2 i = true) :
    id1 = id2 := by
  by_cases h : id1 = id2
  · exact h
  · exfalso
    obtain ⟨c1, hf1, ha1, hq1, _, hl1, hh1⟩ := Owner.writableB_sound h1
    obtain ⟨c2, hf2, ha2, hq2, _, hl2, hh2⟩ := Owner.writableB_sound h2
    have hwithin := hwf.2.1
    have hle1 : c1.hi ≤ o.len := (hwithin id1 c1 hf1).2
    have hcov : o.root.budget i = D := hwf.1 i (by omega)
    have hsum : c1.q + c2.q ≤ o.root.budget i :=
      Tree.budget_two_leaves o.root id1 id2 c1 c2 i h hf1 hf2
        (by simp [ha1]) (by simp [ha2]) hl1 hh1 hl2 hh2
    have hsum' : D + D ≤ D := by
      calc D + D = c1.q + c2.q := by rw [hq1, hq2]
        _ ≤ o.root.budget i := hsum
        _ = D := hcov
    have hDpos : 0 < D := by rw [← hq1]; exact c1.pos
    omega

end Cap
