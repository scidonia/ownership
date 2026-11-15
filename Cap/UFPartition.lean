/-
A functional union-find model, independent of the ownership layer.

`Arr` is a parent array. `step` follows one parent pointer, `Reachable` is one or
more pointer steps, and `Reach` adds the zero-step case. `Same p a b` means that
`a` and `b` have a common descendant under zero-or-more steps; this is the
partition relation of the functional graph, and on such a graph it is an
equivalence relation (`same_refl`, `same_symm`, `same_trans`). The zero-step
case is what makes `Same` reflexive: `Reachable` on its own is one-or-more.

`union p a b` is `p.set b a`: it links `b` directly under `a`, without finding
roots, without path compression, and without rank balancing. When `b` is in
range, the union makes `a` and `b` `Same` (`union_same`). A union leaves a
`Same` class untouched when neither of the two representatives ever reaches the
overwritten index (`union_preserves_other`). This is not a general union-find:
an out-of-range `b` is left unchanged by `List.set`.

The concrete run

  [0,1,2,3] --1→0--> [0,0,2,3] --3→2--> [0,0,2,2] --2→0--> [0,0,0,2]

is `uf0`, `uf1`, `uf2`, `uf3`. `uf3_same_all` proves that every pair of the four
indices is `Same` in the final array.

Proved: the reachability lemmas, that `Same` is an equivalence relation, the
union lemmas above, and the concrete run. Not proved or modelled: ownership,
capabilities, or memory behaviour; path compression; union by rank; any
complexity or termination claim; a `find` operation (none is defined here); and
no claim that the `set`-based `union` is a general union-find (`union_same`
therefore assumes `b < p.length`).
-/
import Std

namespace Cap.UF

abbrev Arr := List Nat

def parentOf (p : Arr) (x : Nat) : Nat := p.getD x x

def step (p : Arr) (x : Nat) : Nat := parentOf p x

/-- One or more parent steps from `a` reach `b`. -/
inductive Reachable (p : Arr) : Nat → Nat → Prop
  | one {a b} : step p a = b → Reachable p a b
  | more {a b c} : step p a = b → Reachable p b c → Reachable p a c

/-- `x` is a fixed point of the parent map. -/
def IsRoot (p : Arr) (x : Nat) : Prop := step p x = x

/-- Zero or more parent steps from `a` reach `b`. -/
def Reach (p : Arr) (a b : Nat) : Prop := a = b ∨ Reachable p a b

/-- `a` and `b` have a common descendant under zero-or-more parent steps. -/
def Same (p : Arr) (a b : Nat) : Prop :=
  ∃ r, Reach p a r ∧ Reach p b r

/-- Link `b` directly under `a`. This is not union by rank. -/
def union (p : Arr) (a b : Nat) : Arr := p.set b a

/-- The `n`-fold iterate of the parent map, applied to `x`. -/
def iter (p : Arr) : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => step p (iter p n x)

theorem reachable_trans {p : Arr} {a b c : Nat}
    (hab : Reachable p a b) (hbc : Reachable p b c) : Reachable p a c := by
  induction hab with
  | one h => exact Reachable.more h hbc
  | more h _ ih => exact Reachable.more h (ih hbc)

theorem reach_trans {p : Arr} {a b c : Nat}
    (hab : Reach p a b) (hbc : Reach p b c) : Reach p a c := by
  rcases hab with rfl | hab
  · exact hbc
  · rcases hbc with rfl | hbc
    · exact Or.inr hab
    · exact Or.inr (reachable_trans hab hbc)

theorem iter_succ_apply (p : Arr) (n x : Nat) :
    iter p n (step p x) = step p (iter p n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change step p (iter p n (step p x)) = step p (step p (iter p n x))
      rw [ih]

theorem iter_add (p : Arr) (m n x : Nat) :
    iter p (m + n) x = iter p m (iter p n x) := by
  induction m generalizing x with
  | zero =>
      rw [Nat.zero_add]
      rfl
  | succ m ih =>
      rw [Nat.succ_add]
      change step p (iter p (m + n) x) = step p (iter p m (iter p n x))
      rw [ih]

theorem reachable_iterate_succ (p : Arr) (a : Nat) :
    ∀ k, Reachable p a (iter p (k + 1) a)
  | 0 => Reachable.one rfl
  | k + 1 => by
      have ih := reachable_iterate_succ p a k
      exact reachable_trans ih (Reachable.one rfl)

theorem reachable_iff_iterate {p : Arr} {a b : Nat} :
    Reachable p a b ↔ ∃ n, 1 ≤ n ∧ iter p n a = b := by
  constructor
  · intro h
    induction h with
    | one h =>
        exact ⟨1, by omega, by simpa [iter] using h⟩
    | more htail _hrest ih =>
        case more a_start a_mid a_end =>
          obtain ⟨n, hn, hx⟩ := ih
          refine ⟨n + 1, by omega, ?_⟩
          have hshift : iter p (n + 1) a_start = iter p n (step p a_start) := by
            rw [iter_succ_apply]
            rfl
          rw [hshift, htail, hx]
  · rintro ⟨n, hn, h⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simpa [h] using reachable_iterate_succ p a k

theorem reach_iff_iterate {p : Arr} {a b : Nat} :
    Reach p a b ↔ ∃ n, iter p n a = b := by
  constructor
  · rintro (rfl | h)
    · exact ⟨0, rfl⟩
    · obtain ⟨n, _, hn⟩ := reachable_iff_iterate.mp h
      exact ⟨n, hn⟩
  · rintro ⟨n, h⟩
    cases n with
    | zero =>
        change a = b at h
        exact Or.inl h
    | succ k =>
        exact Or.inr (reachable_iff_iterate.mpr ⟨k + 1, by omega, h⟩)

/-- Two forward orbits from the same node meet. -/
theorem reachable_join {p : Arr} {a b c : Nat}
    (hab : Reachable p a b) (hac : Reachable p a c) :
    ∃ t, Reachable p b t ∧ Reachable p c t := by
  obtain ⟨n, hn, hnb⟩ := reachable_iff_iterate.mp hab
  obtain ⟨m, hm, hmc⟩ := reachable_iff_iterate.mp hac
  let K := max n m + 1
  have hdn : 1 ≤ K - n := by omega
  have hdm : 1 ≤ K - m := by omega
  have hb : iter p (K - n) b = iter p K a := by
    have hKn : (K - n) + n = K := by omega
    rw [← hnb, ← iter_add, hKn]
  have hc : iter p (K - m) c = iter p K a := by
    have hKm : (K - m) + m = K := by omega
    rw [← hmc, ← iter_add, hKm]
  exact ⟨iter p K a,
    reachable_iff_iterate.mpr ⟨K - n, hdn, hb⟩,
    reachable_iff_iterate.mpr ⟨K - m, hdm, hc⟩⟩

/-- Two zero-or-more forward orbits from the same node meet. -/
theorem reach_join {p : Arr} {a b c : Nat}
    (hab : Reach p a b) (hac : Reach p a c) :
    ∃ t, Reach p b t ∧ Reach p c t := by
  obtain ⟨n, hnb⟩ := reach_iff_iterate.mp hab
  obtain ⟨m, hmc⟩ := reach_iff_iterate.mp hac
  let K := max n m + 1
  have hdn : 1 ≤ K - n := by omega
  have hdm : 1 ≤ K - m := by omega
  have hb : iter p (K - n) b = iter p K a := by
    have hKn : (K - n) + n = K := by omega
    rw [← hnb, ← iter_add, hKn]
  have hc : iter p (K - m) c = iter p K a := by
    have hKm : (K - m) + m = K := by omega
    rw [← hmc, ← iter_add, hKm]
  exact ⟨iter p K a,
    reach_iff_iterate.mpr ⟨K - n, hb⟩,
    reach_iff_iterate.mpr ⟨K - m, hc⟩⟩

theorem same_refl (p : Arr) (a : Nat) : Same p a a :=
  ⟨a, Or.inl rfl, Or.inl rfl⟩

theorem same_symm {p : Arr} {a b : Nat} (h : Same p a b) : Same p b a := by
  obtain ⟨r, ha, hb⟩ := h
  exact ⟨r, hb, ha⟩

theorem same_trans {p : Arr} {a b c : Nat}
    (hab : Same p a b) (hbc : Same p b c) : Same p a c := by
  obtain ⟨r, har, hbr⟩ := hab
  obtain ⟨s, hbs, hcs⟩ := hbc
  obtain ⟨t, hrt, hst⟩ := reach_join hbr hbs
  exact ⟨t, reach_trans har hrt, reach_trans hcs hst⟩

/-- Distinct nodes with a common descendant also have one joined by one-or-more steps. -/
theorem reachable_of_same {p : Arr} {a b : Nat} (h : Same p a b) (hne : a ≠ b) :
    ∃ r, Reachable p a r ∧ Reachable p b r := by
  obtain ⟨r, har, hbr⟩ := h
  rcases har with har | har
  · subst har
    rcases hbr with hbr | hbr
    · exact absurd hbr.symm hne
    · exact ⟨step p a, Reachable.one rfl, reachable_trans hbr (Reachable.one rfl)⟩
  · rcases hbr with hbr | hbr
    · subst hbr
      exact ⟨step p b, reachable_trans har (Reachable.one rfl), Reachable.one rfl⟩
    · exact ⟨r, har, hbr⟩

theorem step_set_of_ne (p : Arr) (a b x : Nat) (hx : x ≠ b) :
    step (p.set b a) x = step p x := by
  unfold step parentOf
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set]
  have hbx : b ≠ x := fun h => hx h.symm
  simp [hbx]

theorem union_same (p : Arr) (a b : Nat) (hb : b < p.length) :
    Same (union p a b) a b := by
  have hstep : step (union p a b) b = a := by
    unfold union step parentOf
    rw [List.getD_eq_getElem?_getD, List.getElem?_set]
    simp [hb]
  exact ⟨a, Or.inl rfl, Or.inr (Reachable.one hstep)⟩

theorem union_same_left (p : Arr) (a b : Nat) (hb : b < p.length) :
    Same (union p a b) a b :=
  union_same p a b hb

theorem union_same_right (p : Arr) (a b : Nat) (hb : b < p.length) :
    Same (union p a b) b a :=
  same_symm (union_same p a b hb)

/-- If `c`'s orbit never visits `b`, overwriting index `b` does not change it. -/
theorem reach_set_of_not_reach_b {p : Arr} {a b c r : Nat}
    (h : Reach p c r) (hb : ¬ Reach p c b) :
    Reach (p.set b a) c r := by
  obtain ⟨n, hn⟩ := reach_iff_iterate.mp h
  have hiter : ∀ k, iter (p.set b a) k c = iter p k c := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        change step (p.set b a) (iter (p.set b a) k c) = step p (iter p k c)
        rw [ih]
        apply step_set_of_ne
        intro heq
        exact hb (reach_iff_iterate.mpr ⟨k, heq⟩)
  exact reach_iff_iterate.mpr ⟨n, by rw [hiter, hn]⟩

/-- A union that no orbit of `c` or `d` reaches preserves their `Same` class. -/
theorem union_preserves_other {p : Arr} {a b c d : Nat}
    (h : Same p c d) (hc : ¬ Reach p c b) (hd : ¬ Reach p d b) :
    Same (union p a b) c d := by
  obtain ⟨r, hcr, hdr⟩ := h
  exact ⟨r, reach_set_of_not_reach_b hcr hc, reach_set_of_not_reach_b hdr hd⟩

/-! ## The concrete run -/

/-- The initial array of four singletons. -/
def uf0 : Arr := [0, 1, 2, 3]

/-- Link `1` under `0`. -/
def uf1 : Arr := union uf0 0 1

/-- Link `3` under `2`. -/
def uf2 : Arr := union uf1 2 3

/-- Link `2` under `0`. -/
def uf3 : Arr := union uf2 0 2

theorem uf1_eq : uf1 = [0, 0, 2, 3] := by decide

theorem uf2_eq : uf2 = [0, 0, 2, 2] := by decide

theorem uf3_eq : uf3 = [0, 0, 0, 2] := by decide

theorem uf3_step_0 : step uf3 0 = 0 := by decide

theorem uf3_step_1 : step uf3 1 = 0 := by decide

theorem uf3_step_2 : step uf3 2 = 0 := by decide

theorem uf3_step_3 : step uf3 3 = 2 := by decide

/-- In the final array every index reaches `0`. -/
theorem uf3_reach_zero (x : Nat) (hx : x < 4) : Reach uf3 x 0 := by
  have hx' : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by omega
  rcases hx' with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Reachable.one uf3_step_1)
  · exact Or.inr (Reachable.one uf3_step_2)
  · exact Or.inr (Reachable.more uf3_step_3 (Reachable.one uf3_step_2))

/-- Every pair of the four indices is in the same class of the final array. -/
theorem uf3_same_all (x y : Nat) (hx : x < 4) (hy : y < 4) :
    Same uf3 x y :=
  ⟨0, uf3_reach_zero x hx, uf3_reach_zero y hy⟩

end Cap.UF
