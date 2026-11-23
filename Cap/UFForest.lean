/-
A forest construction predicate for the functional union-find.

`Built p n rank` records how the parent array was built: start from the identity
forest (`List.range n`, every node a root, rank its index) and repeatedly link
two roots, the second of strictly larger rank under the first. This is a
rank-decreasing union: the measure the chase needs, not the usual
smaller-under-larger balancing. The rank is an index of the predicate, so the construction carries the measure it needs;
`built_ranked` proves the array satisfies `Ranked` with that same rank, and
`forest_acyclic` derives the acyclicity predicate from it.

The identity base is the singleton forest. The step requires both endpoints to
be roots and `rank a < rank b`; it links `b` under `a`. Neither condition is
recoverable from the final array, which is why the predicate is a history rather
than a property of one list.
-/
import Cap.UFChecked

namespace Cap

open UF

/-- The identity forest's step fixes every in-range node. -/
theorem step_range {n i : Nat} (hi : i < n) :
    UF.step (List.range n) i = i := by
  unfold UF.step UF.parentOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_range hi]
  rfl

/-- The zero forest's step is zero for every in-range node. -/
theorem step_replicate_zero {n i : Nat} (hi : i < n) :
    UF.step (List.replicate n 0) i = 0 := by
  unfold UF.step UF.parentOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  simp [hi]

/-- Linking `b` under `a` rewrites `b`'s parent to `a`. -/
theorem step_union_self {p : UF.Arr} {a b : Nat} (hb : b < p.length) :
    UF.step (UF.union p a b) b = a := by
  unfold UF.union UF.step UF.parentOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_set]
  simp [hb]

/-- Linking `b` under `a` leaves every other parent unchanged. -/
theorem step_union_of_ne {p : UF.Arr} {a b x : Nat} (hx : x ≠ b) :
    UF.step (UF.union p a b) x = UF.step p x :=
  UF.step_set_of_ne p a b x hx

/-- A parent array built from the identity or zero forest by rank-decreasing
union: link a larger-ranked root under a smaller-ranked one. The rank is an
index, so each step carries its measure. -/
inductive Built : UF.Arr → Nat → (Nat → Nat) → Prop
  | init (n : Nat) : Built (List.range n) n (fun i => i)
  | zero (n : Nat) : Built (List.replicate n 0) n (fun i => i)
  | union {p : UF.Arr} {n : Nat} {rank : Nat → Nat} (h : Built p n rank)
      {a b : Nat} (ha : UF.IsRoot p a) (hb : UF.IsRoot p b)
      (haN : a < n) (hbN : b < n) (hlt : rank a < rank b) :
      Built (UF.union p a b) n rank

/-- A built array has the represented length. -/
theorem built_length : ∀ {p : UF.Arr} {n : Nat} {rank : Nat → Nat},
    Built p n rank → p.length = n
  | _, _, _, .init n => by simp
  | _, _, _, .zero n => by simp
  | _, _, _, .union h _ _ _ _ _ => by
    rw [UF.union, List.length_set, built_length h]

/-- A built array is ranked by the construction's own rank. The union step keeps
the rank: the linked root `b` now steps to the strictly smaller `a`, and the
other nodes are unchanged. -/
theorem built_ranked : ∀ {p : UF.Arr} {n : Nat} {rank : Nat → Nat},
    Built p n rank → Ranked p n rank
  | _, _, _, .init n => by
    constructor
    · intro i hi
      rw [step_range hi]
      exact hi
    · intro i hi
      left
      unfold UF.IsRoot
      rw [step_range hi]
  | _, _, _, .zero n => by
    constructor
    · intro i hi
      rw [step_replicate_zero hi]
      omega
    · intro i hi
      by_cases h0 : i = 0
      · left
        unfold UF.IsRoot
        subst h0
        rw [step_replicate_zero hi]
      · right
        rw [step_replicate_zero hi]
        change 0 < i
        omega
  | _, _, _, @Built.union p n rank h a b ha hb haN hbN hlt => by
    have hr := built_ranked h
    have hlen := built_length h
    constructor
    · intro i hi
      by_cases hib : i = b
      · subst hib
        rw [step_union_self (by omega)]
        exact haN
      · rw [step_union_of_ne hib]
        exact hr.1 i hi
    · intro i hi
      by_cases hib : i = b
      · subst hib
        right
        rw [step_union_self (by omega)]
        exact hlt
      · by_cases hroot : UF.IsRoot p i
        · left
          unfold UF.IsRoot at hroot ⊢
          rw [step_union_of_ne hib]
          exact hroot
        · right
          have hdec := (hr.2 i hi).resolve_left hroot
          rw [step_union_of_ne hib]
          exact hdec

/-- A built array is in range: every in-range step stays in range. -/
theorem built_bounds {p : UF.Arr} {n : Nat} {rank : Nat → Nat}
    (h : Built p n rank) : ∀ i, i < n → UF.step p i < n :=
  (built_ranked h).1

/-- A built array is acyclic. -/
theorem built_acyclic {p : UF.Arr} {n : Nat} {rank : Nat → Nat}
    (h : Built p n rank) : Acyclic p n :=
  acyclic_of_ranked (built_ranked h)

/-- A forest is an array with some union-by-rank construction history. -/
def Forest (p : UF.Arr) (n : Nat) : Prop :=
  ∃ rank, Built p n rank

/-- A forest carries a rank witness. -/
theorem forest_ranked {p : UF.Arr} {n : Nat} (h : Forest p n) :
    ∃ rank, Ranked p n rank := by
  obtain ⟨rank, hb⟩ := h
  exact ⟨rank, built_ranked hb⟩

/-- A forest is acyclic. -/
theorem forest_acyclic {p : UF.Arr} {n : Nat} (h : Forest p n) : Acyclic p n := by
  obtain ⟨rank, hb⟩ := h
  exact acyclic_of_ranked (built_ranked hb)

/-- The identity forest is built. -/
example : Built (List.range 4) 4 (fun i => i) := .init 4

/-- A concrete union-by-rank step links 1 under 0. -/
example : Built (UF.union (List.range 4) 0 1) 4 (fun i => i) :=
  .union (.init 4)
    (by unfold UF.IsRoot; rw [step_range (by omega)])
    (by unfold UF.IsRoot; rw [step_range (by omega)])
    (by omega) (by omega) (by omega)

/-- The concrete step is acyclic. -/
example : Acyclic (UF.union (List.range 4) 0 1) 4 :=
  forest_acyclic ⟨fun i => i, .union (.init 4)
    (by unfold UF.IsRoot; rw [step_range (by omega)])
    (by unfold UF.IsRoot; rw [step_range (by omega)])
    (by omega) (by omega) (by omega)⟩

end Cap
