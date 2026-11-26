/-
A reusable two-find computation on the functional union-find.

The starting parent array is `[0,0,1,2,2]`, a five-node ranked forest whose
single component is rooted at `0`. The first operation runs the chase from node
`3`, reading the compression path off the orbit (`rootPath`), and compresses
every node on it to the root the chase stopped at. The result is exactly
`[0,0,0,0,2]`. The second operation consumes that post-state: it chases from
node `4`, compresses the path it reads, and lands on exactly `[0,0,0,0,0]`.

Between them, the intermediate array is not merely an array with the same
representatives. `reuseFirst_ranked` proves it is still a ranked forest under
the identity rank, and `reuseFirst_accepts_second` packages exactly the
preconditions the second operation is typed by: the rank bound that makes its
chase stop, the root it stops at, and the in-range reachability of every node on
its path. The partition preservation of both operations is derived from
`compressAll_same_iff` on those witnesses, so the second operation's input
certificate is the first operation's output certificate rather than a restated
assumption about `[0,0,0,0,2]`.

`decide` is used only for finite list arithmetic: the exact arrays, the derived
paths and roots, and the per-index cases of the ranked-forest proofs. It
produces a kernel-checked proof term by computation over concrete lists; there
is no `native_decide` and no new axiom.

Scope: this is the functional model (`UF.Arr`). The sealed `UFRunner` in
`Cap/UFCertified.lean` stores its world, representation predicate and rank
privately and exposes only one find's observation, so it has no operation that
returns a successor runner to feed a second call; threading its invariant would
require a new rank certificate for the post-state. The reusable surface
therefore is the functional path compression the certified writes refine
(`compressAll` and `map_compressBuf`), not the single-find sealed wrapper.
-/
import Cap.UFCertified

namespace Cap

open UF

/-! ### The starting forest -/

/-- The five-node starting parent array. -/
def reuseStart : Arr := [0, 0, 1, 2, 2]

/-- The identity rank: every non-root steps to a strictly smaller node. -/
def reuseRank : Nat → Nat := fun i => i

/-- A node below the five-node bound is one of the five indices. -/
theorem reuse_node_cases {i : Nat} (hi : i < 5) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
  omega

/-- The starting array is a ranked forest. -/
theorem reuseStart_ranked : Ranked reuseStart 5 reuseRank := by
  constructor
  · intro i hi
    rcases reuse_node_cases hi with rfl | rfl | rfl | rfl | rfl <;> decide
  · intro i hi
    rcases reuse_node_cases hi with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (by unfold IsRoot; decide)
    · exact Or.inr (by unfold reuseRank; decide)
    · exact Or.inr (by unfold reuseRank; decide)
    · exact Or.inr (by unfold reuseRank; decide)
    · exact Or.inr (by unfold reuseRank; decide)

/-! ### The first find and full-path compression -/

/-- The chase's root from node `3`. -/
def reuseFirstRoot : Nat := findRootF reuseStart (reuseRank 3 + 1) 3

/-- The compression path read off the chase from node `3`. -/
def reuseFirstPath : List Nat := rootPath reuseStart (reuseRank 3 + 1) 3

/-- The first full-path compression: every node of the chase's path to the root. -/
def reuseFirst : Arr := compressAll reuseStart reuseFirstRoot reuseFirstPath

/-- The first chase's path is `3 → 2 → 1`. -/
theorem reuseFirstPath_eq : reuseFirstPath = [3, 2, 1] := by decide

/-- The first chase stops at root `0`. -/
theorem reuseFirstRoot_eq : reuseFirstRoot = 0 := by decide

/-- The first full-path compression yields exactly `[0,0,0,0,2]`. -/
theorem reuseFirst_eq : reuseFirst = [0, 0, 0, 0, 2] := by decide

/-- The chase from node `3` stops at a root within the rank bound. -/
theorem reuseFirst_stops : StopsAt reuseStart (reuseRank 3 + 1) 3 :=
  stopsAt_of_ranked reuseStart_ranked (reuseRank 3 + 1) 3 (by decide) (by decide)

/-- The root the first chase returns is a fixed point of the starting array. -/
theorem reuseFirstRoot_isRoot : IsRoot reuseStart reuseFirstRoot :=
  findRootF_root reuseFirst_stops

/-- Every node on the first path is in range and reaches the first root. -/
theorem reuseFirstPath_ok :
    ∀ y ∈ reuseFirstPath, y < reuseStart.length ∧ Reach reuseStart y reuseFirstRoot := by
  intro y hy
  have hreach : Reach reuseStart 3 y := rootPath_mem_reach_from hy
  have hylt : y < 5 := Ranked.reach_lt reuseStart_ranked (by decide) hreach
  exact ⟨by simpa [reuseStart] using hylt, rootPath_mem_reach_result hy⟩

/-- The first compression preserves the partition in both directions. -/
theorem reuseFirst_same_iff (p q : Nat) :
    Same reuseFirst p q ↔ Same reuseStart p q :=
  compressAll_same_iff reuseFirstRoot_isRoot reuseFirstPath_ok

/-! ### The second operation on the intermediate post-state -/

/-- The chase's root from node `4` on the first operation's post-state. -/
def reuseSecondRoot : Nat := findRootF reuseFirst (reuseRank 4 + 1) 4

/-- The compression path read off the second chase from node `4`. -/
def reuseSecondPath : List Nat := rootPath reuseFirst (reuseRank 4 + 1) 4

/-- The intermediate array is still a ranked forest. -/
theorem reuseFirst_ranked : Ranked reuseFirst 5 reuseRank := by
  constructor
  · intro i hi
    rcases reuse_node_cases hi with rfl | rfl | rfl | rfl | rfl <;> decide
  · intro i hi
    rcases reuse_node_cases hi with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (by unfold IsRoot; decide)
    · exact Or.inr (by unfold reuseRank; decide)
    · exact Or.inr (by unfold reuseRank; decide)
    · exact Or.inr (by unfold reuseRank; decide)
    · exact Or.inr (by unfold reuseRank; decide)

/-- The second chase stops at a root within the rank bound. -/
theorem reuseSecond_stops : StopsAt reuseFirst (reuseRank 4 + 1) 4 :=
  stopsAt_of_ranked reuseFirst_ranked (reuseRank 4 + 1) 4 (by decide) (by decide)

/-- The second chase's root is a fixed point of the intermediate array. -/
theorem reuseSecondRoot_isRoot : IsRoot reuseFirst reuseSecondRoot :=
  findRootF_root reuseSecond_stops

/-- Every node on the second path is in range and reaches the second root. -/
theorem reuseSecondPath_ok :
    ∀ y ∈ reuseSecondPath, y < reuseFirst.length ∧ Reach reuseFirst y reuseSecondRoot := by
  intro y hy
  have hreach : Reach reuseFirst 4 y := rootPath_mem_reach_from hy
  have hylt : y < 5 := Ranked.reach_lt reuseFirst_ranked (by decide) hreach
  have hlen : reuseFirst.length = 5 := by decide
  exact ⟨by rw [hlen]; exact hylt, rootPath_mem_reach_result hy⟩

/-- The intermediate post-state is accepted by a second verified find: it is a
ranked forest, its chase stops at the root it returns, and every node of the
path that find compresses is in range and reaches that root. These are exactly
the hypotheses of the second operation's preservation theorem. -/
theorem reuseFirst_accepts_second :
    Ranked reuseFirst 5 reuseRank ∧ IsRoot reuseFirst reuseSecondRoot ∧
      ∀ y ∈ reuseSecondPath,
        y < reuseFirst.length ∧ Reach reuseFirst y reuseSecondRoot :=
  ⟨reuseFirst_ranked, reuseSecondRoot_isRoot, reuseSecondPath_ok⟩

/-- The intermediate forest is acyclic. -/
theorem reuseFirst_acyclic : Acyclic reuseFirst 5 :=
  acyclic_of_ranked reuseFirst_ranked

/-- The second full-path compression, on the first operation's output. -/
def reuseSecond : Arr := compressAll reuseFirst reuseSecondRoot reuseSecondPath

/-- The second chase's path is `4 → 2`. -/
theorem reuseSecondPath_eq : reuseSecondPath = [4, 2] := by decide

/-- The second chase stops at root `0`. -/
theorem reuseSecondRoot_eq : reuseSecondRoot = 0 := by decide

/-- The second full-path compression yields exactly `[0,0,0,0,0]`. -/
theorem reuseSecond_eq : reuseSecond = [0, 0, 0, 0, 0] := by decide

/-- The second compression preserves the partition in both directions. -/
theorem reuseSecond_same_iff (p q : Nat) :
    Same reuseSecond p q ↔ Same reuseFirst p q :=
  compressAll_same_iff reuseSecondRoot_isRoot reuseSecondPath_ok

/-- Composing the two operations preserves the starting partition. -/
theorem reuseSecond_same_iff_start (p q : Nat) :
    Same reuseSecond p q ↔ Same reuseStart p q :=
  (reuseSecond_same_iff p q).trans (reuseFirst_same_iff p q)

/-- The final forest is a ranked forest. -/
theorem reuseSecond_ranked : Ranked reuseSecond 5 reuseRank := by
  constructor
  · intro i hi
    rcases reuse_node_cases hi with rfl | rfl | rfl | rfl | rfl <;> decide
  · intro i hi
    rcases reuse_node_cases hi with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (by unfold IsRoot; decide)
    · exact Or.inr (by unfold reuseRank; decide)
    · exact Or.inr (by unfold reuseRank; decide)
    · exact Or.inr (by unfold reuseRank; decide)
    · exact Or.inr (by unfold reuseRank; decide)

/-- The final forest is acyclic. -/
theorem reuseSecond_acyclic : Acyclic reuseSecond 5 :=
  acyclic_of_ranked reuseSecond_ranked

/-! ### The reusable client -/

/-- The two operations in sequence on the starting array. -/
def reuseTwoFinds : Arr := reuseSecond

/-- The reusable client's exact output. -/
theorem reuseTwoFinds_eq : reuseTwoFinds = [0, 0, 0, 0, 0] :=
  reuseSecond_eq

/-- The reusable client's partition is the starting partition. -/
theorem reuseTwoFinds_same_iff (p q : Nat) :
    Same reuseTwoFinds p q ↔ Same reuseStart p q :=
  reuseSecond_same_iff_start p q

end Cap
