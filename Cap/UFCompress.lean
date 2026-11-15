/-
Bounded root search and one-step compression on the functional union-find model.

`findRootF p fuel start` follows parent pointers from `start` for at most `fuel`
steps. When it meets a fixed point `r` (`step p r = r`) it returns `r`; when the
fuel runs out first it returns the node it has reached. `StopsAt p fuel start`
records that the search does reach a fixed point before the fuel runs out, and
`findRootF_root` proves the result is a fixed point under that hypothesis.
`findRootF_reachable` proves, unconditionally, that the result is reachable from
`start` under `Reach` (the zero-step case included).

`compress p x r` is `p.set x r`: it rewrites `x`'s parent pointer to `r` and
leaves every other index alone. This is one-step compression on this functional
model, not full path compression. It does not walk to the root first, does not
rewrite the nodes above `x`, and has neither rank nor an amortized analysis.

The partition facts are the ones this one-step rewrite supports.
`compress_step_self` gives the rewritten pointer and `compress_same_self` shows
`x` and `r` are `Same` afterwards. `compress_same` states that `Same` is
unchanged for pairs whose orbits never visit `x`, so their classes are untouched;
`compress_preserves_same` is its one-directional form. `compress_same_of_reach_x`
shows that every node that did reach `x` is still in one class, since all of them
now reach `r`. Conversely `compress_same_sound` shows that when `x` reaches `r`,
the rewrite creates no new `Same` pair: the compressed array's classes are all
classes of `p`. `compress_self_of_root` records the case where `x` is already a
fixed point, so the rewrite is the identity.

Proved: the bounded search's root and reachability facts, the one-step rewrite
lemmas, and the partition-preservation statements above. Not proved or modelled:
full path compression, union by rank, termination without fuel, any complexity or
amortization claim, and anything about ownership, capabilities, or memory. This
file does not import the ownership layer; `Cap.Invariant` is not involved.
-/
import Cap.UFPartition

namespace Cap.UF

/-! ## Bounded root search -/

/-- Follow parent pointers from `start`, stopping at a fixed point or when the
fuel runs out. On exhaustion the node reached so far is returned. -/
def findRootF (p : Arr) : Nat → Nat → Nat
  | 0, x => x
  | fuel + 1, x =>
      if step p x = x then x else findRootF p fuel (step p x)

/-- The search in `fuel` steps reaches a fixed point rather than exhausting its
fuel. -/
def StopsAt (p : Arr) : Nat → Nat → Prop
  | 0, _ => False
  | fuel + 1, x =>
      IsRoot p x ∨ (¬ IsRoot p x ∧ StopsAt p fuel (step p x))

theorem findRootF_zero (p : Arr) (x : Nat) : findRootF p 0 x = x := rfl

theorem findRootF_succ (p : Arr) (fuel x : Nat) :
    findRootF p (fuel + 1) x =
      (if step p x = x then x else findRootF p fuel (step p x)) := rfl

theorem stopsAt_zero (p : Arr) (x : Nat) : ¬ StopsAt p 0 x := fun h => h

theorem stopsAt_succ (p : Arr) (fuel x : Nat) :
    StopsAt p (fuel + 1) x ↔
      (IsRoot p x ∨ (¬ IsRoot p x ∧ StopsAt p fuel (step p x))) :=
  Iff.rfl

/-- When the search stops, it stops at a fixed point. -/
theorem findRootF_root {p : Arr} {fuel x : Nat} (h : StopsAt p fuel x) :
    IsRoot p (findRootF p fuel x) := by
  induction fuel generalizing x with
  | zero => exact (stopsAt_zero p x h).elim
  | succ fuel ih =>
      rw [findRootF_succ]
      by_cases hr : step p x = x
      · rw [ite_eq_left hr]
        exact hr
      · rw [ite_eq_right hr]
        rcases (stopsAt_succ p fuel x).mp h with hroot | ⟨_, htail⟩
        · exact absurd hroot hr
        · exact ih htail

/-- The search never leaves the orbit of its start. -/
theorem findRootF_reachable (p : Arr) (fuel start : Nat) :
    Reach p start (findRootF p fuel start) := by
  induction fuel generalizing start with
  | zero => exact Or.inl rfl
  | succ fuel ih =>
      rw [findRootF_succ]
      by_cases hr : step p start = start
      · rw [ite_eq_left hr]
        exact Or.inl rfl
      · rw [ite_eq_right hr]
        exact reach_trans (Or.inr (Reachable.one rfl)) (ih (step p start))

/-- The reachability statement in the form the search is usually used with: the
result is the start itself or is reached from it. -/
theorem findRootF_reachable_or_eq (p : Arr) (fuel start : Nat) :
    start = findRootF p fuel start ∨ Reachable p start (findRootF p fuel start) :=
  findRootF_reachable p fuel start

/-! ## One-step compression -/

/-- Rewrite `x`'s parent pointer to `r`. Every other index is unchanged. -/
def compress (p : Arr) (x r : Nat) : Arr := p.set x r

theorem compress_def (p : Arr) (x r : Nat) : compress p x r = p.set x r := rfl

/-- The rewritten pointer, when `x` is in range. -/
theorem compress_step_self {p : Arr} {x r : Nat} (hx : x < p.length) :
    step (compress p x r) x = r := by
  unfold compress step parentOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_set]
  simp [hx]

/-- An index other than the rewritten one keeps its parent. -/
theorem compress_step_of_ne {p : Arr} {x r y : Nat} (h : y ≠ x) :
    step (compress p x r) y = step p y :=
  step_set_of_ne (p := p) (a := r) (b := x) (x := y) h

/-- The rewritten node reaches its new parent. -/
theorem compress_reach_self {p : Arr} {x r : Nat} (hx : x < p.length) :
    Reach (compress p x r) x r :=
  Or.inr (Reachable.one (compress_step_self hx))

/-- The rewritten node and its new parent are in the same class. -/
theorem compress_same_self {p : Arr} {x r : Nat} (hx : x < p.length) :
    Same (compress p x r) x r :=
  ⟨r, compress_reach_self hx, Or.inl rfl⟩

/-- Compressing a fixed point to itself leaves the array unchanged. -/
theorem compress_self_of_root {p : Arr} {x : Nat} (hx : x < p.length)
    (hr : IsRoot p x) : compress p x x = p := by
  have hp : p[x] = x := by
    have h := hr
    unfold IsRoot step parentOf at h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx] at h
    simpa using h
  unfold compress
  have hset : p.set x x = p.set x p[x] := by rw [hp]
  rw [hset, List.set_getElem_self hx]

/-! ## Orbits that avoid the rewritten index -/

/-- If the orbit of `a` never visits `x`, compression does not change it. -/
theorem iter_compress_of_avoids {p : Arr} {x r a : Nat}
    (h : ¬ Reach p a x) (k : Nat) :
    iter (compress p x r) k a = iter p k a := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change step (compress p x r) (iter (compress p x r) k a) = step p (iter p k a)
      rw [ih]
      exact compress_step_of_ne (fun heq => h (reach_iff_iterate.mpr ⟨k, heq⟩))

/-- A path that avoids the rewritten index is a path of the original array. -/
theorem reach_of_compress_of_not_reach {p : Arr} {x r a t : Nat}
    (hreach : Reach (compress p x r) a t) (ha : ¬ Reach p a x) :
    Reach p a t := by
  obtain ⟨n, hn⟩ := reach_iff_iterate.mp hreach
  exact reach_iff_iterate.mpr
    ⟨n, by rw [← iter_compress_of_avoids ha n]; exact hn⟩

/-- A path of the original array that avoids the rewritten index survives. -/
theorem reach_compress_of_not_reach {p : Arr} {x r c t : Nat}
    (h : Reach p c t) (hc : ¬ Reach p c x) :
    Reach (compress p x r) c t :=
  reach_set_of_not_reach_b (p := p) (a := r) (b := x) (c := c) (r := t) h hc

/-! ## Orbits that reach the rewritten index -/

/-- If `a` reaches `x`, then in the compressed array `a` reaches the new parent
`r`; the part of the orbit before the first visit to `x` is unchanged. -/
theorem reach_compress_of_reach_x {p : Arr} {x r a : Nat} (hx : x < p.length)
    (h : Reach p a x) : Reach (compress p x r) a r := by
  obtain ⟨n, hn⟩ := reach_iff_iterate.mp h
  have key : ∀ n b, iter p n b = x → Reach (compress p x r) b r := by
    intro n
    induction n with
    | zero =>
        intro b hb
        have hb' : b = x := hb
        subst hb'
        exact Or.inr (Reachable.one (compress_step_self hx))
    | succ n ih =>
        intro b hb
        by_cases hb' : b = x
        · subst hb'
          exact Or.inr (Reachable.one (compress_step_self hx))
        · have hs : step (compress p x r) b = step p b := compress_step_of_ne hb'
          have hstep : iter p n (step p b) = x := by
            rw [iter_succ_apply]
            exact hb
          exact reach_trans (Or.inr (Reachable.one hs)) (ih (step p b) hstep)
  exact key n a hn

/-- Every node that reached the rewritten index stays in one class: all of them
now reach the new parent. -/
theorem compress_same_of_reach_x {p : Arr} {x r a b : Nat} (hx : x < p.length)
    (ha : Reach p a x) (hb : Reach p b x) :
    Same (compress p x r) a b :=
  ⟨r, reach_compress_of_reach_x hx ha, reach_compress_of_reach_x hx hb⟩

/-! ## Partition preservation -/

/-- For a pair whose orbits avoid the rewritten index, compression preserves
`Same` in both directions. -/
theorem compress_same {p : Arr} {x r a b : Nat}
    (ha : ¬ Reach p a x) (hb : ¬ Reach p b x) :
    Same (compress p x r) a b ↔ Same p a b := by
  constructor
  · rintro ⟨t, hat, hbt⟩
    exact ⟨t, reach_of_compress_of_not_reach hat ha,
      reach_of_compress_of_not_reach hbt hb⟩
  · rintro ⟨t, hat, hbt⟩
    exact ⟨t, reach_compress_of_not_reach hat ha,
      reach_compress_of_not_reach hbt hb⟩

/-- Compression does not break a class none of whose orbits visits `x`. -/
theorem compress_preserves_same {p : Arr} {x r a b : Nat}
    (h : Same p a b) (ha : ¬ Reach p a x) (hb : ¬ Reach p b x) :
    Same (compress p x r) a b :=
  (compress_same ha hb).mpr h

/-- If `x` reaches its new parent, compression creates no new `Same` pair. -/
theorem compress_same_sound {p : Arr} {x r : Nat} (hx : x < p.length)
    (hxr : Reach p x r) : ∀ {a b : Nat}, Same (compress p x r) a b → Same p a b := by
  intro a b h
  obtain ⟨t, hat, hbt⟩ := h
  have hstep : ∀ {y z : Nat}, step (compress p x r) y = z → Reach p y z := by
    intro y z hs
    by_cases hy : y = x
    · subst hy
      have hz : z = r := by rw [← hs]; exact compress_step_self hx
      subst hz
      exact hxr
    · have he : step (compress p x r) y = step p y := compress_step_of_ne hy
      rw [he] at hs
      exact Or.inr (Reachable.one hs)
  have hreachable : ∀ {a t : Nat}, Reachable (compress p x r) a t → Reach p a t := by
    intro a t hp
    induction hp with
    | one hs => exact hstep hs
    | more hs _ ih => exact reach_trans (hstep hs) ih
  have key : ∀ {a t : Nat}, Reach (compress p x r) a t → Reach p a t := by
    intro a t hp
    rcases hp with rfl | hp
    · exact Or.inl rfl
    · exact hreachable hp
  exact ⟨t, key hat, key hbt⟩

/-! ## A concrete instance -/

/-- The root search on the final array of `uf3` finds the root of index `1`. -/
theorem uf3_findRootF_1 : findRootF uf3 4 1 = 0 := by decide

/-- The root search on the final array of `uf3` finds the root of index `3`. -/
theorem uf3_findRootF_3 : findRootF uf3 4 3 = 0 := by decide

/-- From index `3` the search reaches a fixed point within four steps. -/
theorem uf3_stopsAt_3 : StopsAt uf3 4 3 := by
  simp [StopsAt, IsRoot, uf3_step_3, uf3_step_2, uf3_step_0]

/-- Therefore the node returned from `3` is a fixed point. -/
theorem uf3_findRootF_3_root : IsRoot uf3 (findRootF uf3 4 3) :=
  findRootF_root uf3_stopsAt_3

/-- One-step compression of index `3` onto the root `0`. -/
theorem uf3_compress_3 : compress uf3 3 0 = [0, 0, 0, 0] := by decide

end Cap.UF
