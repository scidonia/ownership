/-
A state-threaded, sealed union-find runner over the functional model.

`PathRunner origin n rank` is a structure with a private constructor and private
fields: the current parent array, its length, the ranked-forest certificate, a
partition witness against the origin array, and the recorded history of
full-path compressions that produced the current array from `origin`.
`PathRunner.find` runs one find at a node and returns the root together with the
*successor* runner whose array is the current array with that chase's whole path
compressed to the root. The successor is built from the predecessor, so a second
call reads the first call's output array and the first call's chase witness.

The reusable property is general over finite recorded histories. Starting from
any runner whose origin supplies a length, a `Ranked` certificate for a fixed
rank function and the trivial partition witness, a finite sequence of `find`
calls is supported: each successor carries the length and the same
`Ranked`/`Acyclic` certificate (rank is preserved because every compressed path
node reaches the root with a strictly smaller rank), and its partition witness
composes the previous witness with the path-compression `Same` theorem.

Scope and limits. This is the functional `UF.Arr` model, not the sealed
`UFCertified.UFRunner`: that structure wraps a world and a representation
predicate and exposes a single observation, while this runner threads the
functional array from call to call. The supported states are exactly those
reachable by the runner's own recorded `find` calls; the private constructor
means an external array cannot be injected without a length, rank and partition
certificate, and the rank function is fixed for the whole run. There is no union
operation, no amortised-complexity claim and no byte-backend correspondence
here. Fuel for a chase is `rank x + 1`, so each call needs the ranked-forest
measure to make its chase stop.
-/
import Cap.UFReuse

namespace Cap

open UF

/-! ### Recorded compressions and their replay -/

/-- One recorded full-path compression, read off the chase: the root the search
stopped at and the nodes it compressed. -/
structure Compression where
  root : Nat
  path : List Nat
  deriving Repr, DecidableEq

/-- Replay recorded compressions from a starting array. -/
def replay (p : UF.Arr) : List Compression → UF.Arr
  | [] => p
  | c :: cs => replay (UF.compressAll p c.root c.path) cs

/-- Replaying a concatenated history replays the prefix first. -/
theorem replay_append (p : UF.Arr) (s t : List Compression) :
    replay p (s ++ t) = replay (replay p s) t := by
  induction s generalizing p with
  | nil => rfl
  | cons c cs ih =>
      change replay (UF.compressAll p c.root c.path) (cs ++ t) =
        replay (replay (UF.compressAll p c.root c.path) cs) t
      exact ih (UF.compressAll p c.root c.path)

/-! ### Compression preserves the ranked-forest certificate -/

/-- Full compression preserves the array's length. -/
theorem compressAll_length (p : UF.Arr) (r : Nat) (ys : List Nat) :
    (UF.compressAll p r ys).length = p.length := by
  induction ys generalizing p with
  | nil => rfl
  | cons y ys ih =>
      show (UF.compressAll (UF.compress p y r) r ys).length = p.length
      rw [ih (UF.compress p y r), UF.compress, List.length_set]

/-- The chase's rank never increases. -/
theorem findRootF_rank_le {p : UF.Arr} {n : Nat} {rank : Nat → Nat}
    (hr : Ranked p n rank) :
    ∀ {fuel x : Nat}, x < n → rank (UF.findRootF p fuel x) ≤ rank x := by
  intro fuel
  induction fuel with
  | zero =>
      intro x _
      rw [UF.findRootF_zero]
      omega
  | succ fuel ih =>
      intro x hx
      rw [UF.findRootF_succ]
      by_cases hroot : UF.step p x = x
      · rw [if_pos hroot]
        omega
      · rw [if_neg hroot]
        have hstep : UF.step p x < n := hr.1 x hx
        have hlt : rank (UF.step p x) < rank x :=
          (hr.2 x hx).resolve_left hroot
        have hle := ih hstep
        omega

/-- Every node on the chase's path has a strictly larger rank than the root the
chase stops at. -/
theorem rootPath_rank_lt {p : UF.Arr} {n : Nat} {rank : Nat → Nat}
    (hr : Ranked p n rank) :
    ∀ {fuel x y : Nat}, x < n → y ∈ rootPath p fuel x →
      rank (UF.findRootF p fuel x) < rank y := by
  intro fuel
  induction fuel with
  | zero =>
      intro x y _ hy
      simp [rootPath] at hy
  | succ fuel ih =>
      intro x y hx hy
      rw [rootPath] at hy
      by_cases hroot : UF.step p x = x
      · simp [hroot] at hy
      · rw [if_neg hroot] at hy
        have hstep : UF.step p x < n := hr.1 x hx
        have hlt : rank (UF.step p x) < rank x :=
          (hr.2 x hx).resolve_left hroot
        rcases List.mem_cons.mp hy with rfl | htail
        · rw [UF.findRootF_succ, if_neg hroot]
          have hle := findRootF_rank_le (fuel := fuel) hr hstep
          omega
        · rw [UF.findRootF_succ, if_neg hroot]
          exact ih hstep htail

/-- Compressing one path node to a strictly smaller-ranked root preserves the
ranked-forest certificate. -/
theorem ranked_compress {p : UF.Arr} {n : Nat} {rank : Nat → Nat}
    (hlen : p.length = n) (hr : Ranked p n rank)
    {y r : Nat} (hyn : y < n) (hrn : r < n) (hlt : rank r < rank y) :
    Ranked (UF.compress p y r) n rank := by
  have hyLen : y < p.length := by rwa [hlen]
  constructor
  · intro i hi
    by_cases hiy : i = y
    · subst hiy
      rw [UF.compress_step_self hyLen]
      exact hrn
    · rw [UF.compress_step_of_ne hiy]
      exact hr.1 i hi
  · intro i hi
    by_cases hiy : i = y
    · subst hiy
      exact Or.inr (by rw [UF.compress_step_self hyLen]; exact hlt)
    · change UF.step (UF.compress p y r) i = i ∨
        rank (UF.step (UF.compress p y r) i) < rank i
      rw [UF.compress_step_of_ne hiy]
      exact hr.2 i hi

/-- Compressing a whole list of in-range nodes to a root of strictly smaller
rank preserves the ranked-forest certificate. -/
theorem ranked_compressAll {p : UF.Arr} {n : Nat} {rank : Nat → Nat}
    (hlen : p.length = n) (hr : Ranked p n rank) {r : Nat} (hrn : r < n)
    {ys : List Nat} (hys : ∀ y ∈ ys, y < n)
    (hrank : ∀ y ∈ ys, rank r < rank y) :
    Ranked (UF.compressAll p r ys) n rank := by
  induction ys generalizing p with
  | nil => exact hr
  | cons y ys ih =>
      have hyn : y < n := hys y (List.mem_cons_self ..)
      have hlen' : (UF.compress p y r).length = n := by
        rw [UF.compress, List.length_set, hlen]
      exact ih hlen'
        (ranked_compress hlen hr hyn hrn (hrank y (List.mem_cons_self ..)))
        (fun z hz => hys z (List.mem_cons_of_mem y hz))
        (fun z hz => hrank z (List.mem_cons_of_mem y hz))

/-- Full-path compression along the chase keeps the ranked-forest certificate:
each path node reaches the root, and the root's rank is strictly smaller. -/
theorem compressAll_chase_ranked {p : UF.Arr} {n : Nat} {rank : Nat → Nat}
    (hlen : p.length = n) (hr : Ranked p n rank) {x : Nat} (hx : x < n) :
    Ranked (UF.compressAll p (UF.findRootF p (rank x + 1) x)
      (rootPath p (rank x + 1) x)) n rank := by
  refine ranked_compressAll hlen hr (findRootF_lt hr.1 hx) ?_ ?_
  · intro y hy
    exact Ranked.reach_lt hr hx (rootPath_mem_reach_from hy)
  · intro y hy
    exact rootPath_rank_lt hr hx hy

/-- Full-path compression along the chase preserves the partition in both
directions. -/
theorem compressAll_chase_same_iff {p : UF.Arr} {n : Nat} {rank : Nat → Nat}
    (hlen : p.length = n) (hr : Ranked p n rank) {x : Nat} (hx : x < n)
    (a b : Nat) :
    UF.Same (UF.compressAll p (UF.findRootF p (rank x + 1) x)
      (rootPath p (rank x + 1) x)) a b ↔ UF.Same p a b := by
  have hstop : UF.StopsAt p (rank x + 1) x :=
    stopsAt_of_ranked hr (rank x + 1) x hx (by omega)
  have hroot : UF.IsRoot p (UF.findRootF p (rank x + 1) x) :=
    UF.findRootF_root hstop
  refine compressAll_same_iff hroot ?_
  intro y hy
  exact ⟨by rw [hlen]; exact Ranked.reach_lt hr hx (rootPath_mem_reach_from hy),
    rootPath_mem_reach_result hy⟩

/-! ### The sealed runner -/

/-- A sealed state of a reusable find-and-compress computation. `origin` is the
array the run started from; `n` and `rank` are the fixed domain and forest
measure. The current array is private, as are its certificates and the recorded
history that produced it. -/
structure PathRunner (origin : UF.Arr) (n : Nat) (rank : Nat → Nat) where
  private mk ::
  private arr : UF.Arr
  private hlen : arr.length = n
  private hrank : Ranked arr n rank
  private hsame : ∀ a b, UF.Same arr a b ↔ UF.Same origin a b
  private hist : List Compression
  private history : arr = replay origin hist

namespace PathRunner

/-- The current parent array. -/
def parent (s : PathRunner origin n rank) : UF.Arr := s.arr

/-- The recorded compression history. -/
def trace (s : PathRunner origin n rank) : List Compression := s.hist

/-- The current array has the runner's domain length. -/
theorem length_eq (s : PathRunner origin n rank) : s.parent.length = n :=
  s.hlen

/-- The current array is a ranked forest. -/
theorem ranked (s : PathRunner origin n rank) : Ranked s.parent n rank :=
  s.hrank

/-- The current array is acyclic. -/
theorem acyclic (s : PathRunner origin n rank) : Acyclic s.parent n :=
  acyclic_of_ranked s.hrank

/-- The current array's partition is the origin's. -/
theorem same_iff (s : PathRunner origin n rank) (a b : Nat) :
    UF.Same s.parent a b ↔ UF.Same origin a b :=
  s.hsame a b

/-- The current array is the replay of the recorded history. -/
theorem replay_eq (s : PathRunner origin n rank) :
    s.parent = replay origin s.trace :=
  s.history

/-- The root the chase from `x` stops at, at the current state. -/
def findRoot (s : PathRunner origin n rank) (x : Nat) : Nat :=
  UF.findRootF s.parent (rank x + 1) x

/-- The path the chase from `x` compresses, at the current state. -/
def chasePath (s : PathRunner origin n rank) (x : Nat) : List Nat :=
  rootPath s.parent (rank x + 1) x

/-- Run one find-and-compress: return the root and the successor runner whose
array is the current array with the chase's whole path compressed to that root.
The successor records the compression and keeps the origin, the domain, the
rank function and the partition witness. -/
def find (s : PathRunner origin n rank) (x : Nat) (hx : x < n) :
    Nat × PathRunner origin n rank :=
  let c : Compression := { root := s.findRoot x, path := s.chasePath x }
  (s.findRoot x,
    mk (UF.compressAll s.parent (s.findRoot x) (s.chasePath x))
      (by rw [compressAll_length]; exact s.hlen)
      (compressAll_chase_ranked s.hlen s.hrank hx)
      (fun a b => (compressAll_chase_same_iff s.hlen s.hrank hx a b).trans
        (s.hsame a b))
      (s.hist ++ [c])
      (by
        rw [replay_append, ← s.history]
        rfl))

/-- The value a find returns is its chase's root. -/
theorem find_root (s : PathRunner origin n rank) (x : Nat) (hx : x < n) :
    (s.find x hx).1 = UF.findRootF s.parent (rank x + 1) x := rfl

/-- The successor's array is the predecessor's array with the chase's path
compressed to the root. -/
theorem find_parent (s : PathRunner origin n rank) (x : Nat) (hx : x < n) :
    (s.find x hx).2.parent =
      UF.compressAll s.parent (UF.findRootF s.parent (rank x + 1) x)
        (rootPath s.parent (rank x + 1) x) := rfl

/-- The successor records the compression the predecessor's chase computed. -/
theorem find_trace (s : PathRunner origin n rank) (x : Nat) (hx : x < n) :
    (s.find x hx).2.trace =
      s.trace ++ [{ root := UF.findRootF s.parent (rank x + 1) x,
                    path := rootPath s.parent (rank x + 1) x }] := rfl

/-- A find keeps the ranked-forest certificate. -/
theorem find_ranked (s : PathRunner origin n rank) (x : Nat) (hx : x < n) :
    Ranked (s.find x hx).2.parent n rank := by
  rw [find_parent]
  exact compressAll_chase_ranked s.length_eq s.ranked hx

/-- A find keeps acyclicity. -/
theorem find_acyclic (s : PathRunner origin n rank) (x : Nat) (hx : x < n) :
    Acyclic (s.find x hx).2.parent n :=
  acyclic_of_ranked (find_ranked s x hx)

/-- A find preserves the partition in both directions. -/
theorem find_same_iff (s : PathRunner origin n rank) (x : Nat) (hx : x < n)
    (a b : Nat) :
    UF.Same (s.find x hx).2.parent a b ↔ UF.Same s.parent a b := by
  rw [find_parent]
  exact compressAll_chase_same_iff s.length_eq s.ranked hx a b

/-- The successor's recorded history is the predecessor's with the new step. -/
theorem find_replay (s : PathRunner origin n rank) (x : Nat) (hx : x < n) :
    (s.find x hx).2.parent =
      replay s.parent [{ root := UF.findRootF s.parent (rank x + 1) x,
                         path := rootPath s.parent (rank x + 1) x }] := by
  rw [find_parent]
  rfl

end PathRunner

/-! ### The two-call reusable client -/

/-- The starting runner over `[0,0,1,2,2]`. -/
def reuseRunnerStart : PathRunner reuseStart 5 reuseRank :=
  PathRunner.mk reuseStart rfl reuseStart_ranked (fun _ _ => Iff.rfl) [] rfl

/-- The successor of the first find, from node `3`. -/
def reuseRunnerFirst : PathRunner reuseStart 5 reuseRank :=
  (PathRunner.find reuseRunnerStart 3 (by decide)).2

/-- The successor of the second find, run on the first successor from node `4`. -/
def reuseRunnerSecond : PathRunner reuseStart 5 reuseRank :=
  (PathRunner.find reuseRunnerFirst 4 (by decide)).2

/-- A fresh find from node `4` on the origin, for the control that the second
call is not this one. -/
def reuseRunnerFreshFour : PathRunner reuseStart 5 reuseRank :=
  (PathRunner.find reuseRunnerStart 4 (by decide)).2

/-- The starting runner's array is the origin. -/
theorem reuseRunnerStart_parent : reuseRunnerStart.parent = reuseStart := rfl

/-- The first call's root is `0`. -/
theorem reuseRunnerFirst_root :
    (PathRunner.find reuseRunnerStart 3 (by decide)).1 = 0 := by
  rw [PathRunner.find_root]
  decide

/-- The first successor's array is the first compression `reuseFirst`. -/
theorem reuseRunnerFirst_parent : reuseRunnerFirst.parent = reuseFirst := by
  unfold reuseRunnerFirst
  rw [PathRunner.find_parent]
  rfl

/-- The first call's successor array is exactly `[0,0,0,0,2]`. -/
theorem reuseRunnerFirst_parent_eq :
    reuseRunnerFirst.parent = [0, 0, 0, 0, 2] := by
  rw [reuseRunnerFirst_parent, reuseFirst_eq]

/-- The first successor's recorded history is the single path `[3,2,1]`. -/
theorem reuseRunnerFirst_trace :
    reuseRunnerFirst.trace = [{ root := 0, path := [3, 2, 1] }] := by
  unfold reuseRunnerFirst
  rw [PathRunner.find_trace]
  show ([] : List Compression) ++
      [{ root := UF.findRootF reuseStart (reuseRank 3 + 1) 3,
         path := rootPath reuseStart (reuseRank 3 + 1) 3 }] =
    [{ root := 0, path := [3, 2, 1] }]
  decide

/-- The second call's root is `0`. -/
theorem reuseRunnerSecond_root :
    (PathRunner.find reuseRunnerFirst 4 (by decide)).1 = 0 := by
  rw [PathRunner.find_root]
  decide

/-- The second successor's array is the second compression `reuseSecond`. -/
theorem reuseRunnerSecond_parent : reuseRunnerSecond.parent = reuseSecond := by
  unfold reuseRunnerSecond
  rw [PathRunner.find_parent, reuseRunnerFirst_parent]
  rfl

/-- The second call's successor array is exactly `[0,0,0,0,0]`. -/
theorem reuseRunnerSecond_parent_eq :
    reuseRunnerSecond.parent = [0, 0, 0, 0, 0] := by
  rw [reuseRunnerSecond_parent, reuseSecond_eq]

/-- The second successor's history is the two recorded paths `[3,2,1]` and
`[4,2]`. -/
theorem reuseRunnerSecond_trace :
    reuseRunnerSecond.trace =
      [{ root := 0, path := [3, 2, 1] }, { root := 0, path := [4, 2] }] := by
  unfold reuseRunnerSecond
  rw [PathRunner.find_trace, reuseRunnerFirst_parent, reuseRunnerFirst_trace]
  decide

/-- A fresh find from node `4` records the longer single path `[4,2,1]` on the
origin. It compresses that path only, so node `3` is left pointing at `2` and
the final array is `[0,0,0,2,0]`, not the two-step run's `[0,0,0,0,0]`. -/
theorem reuseRunnerFreshFour_parent :
    reuseRunnerFreshFour.parent = [0, 0, 0, 2, 0] := by
  unfold reuseRunnerFreshFour
  rw [PathRunner.find_parent]
  rfl

/-- A fresh find from node `4` records the longer single path `[4,2,1]` on the
origin, not the successor's two-step history. -/
theorem reuseRunnerFreshFour_trace :
    reuseRunnerFreshFour.trace = [{ root := 0, path := [4, 2, 1] }] := by
  unfold reuseRunnerFreshFour
  rw [PathRunner.find_trace]
  show ([] : List Compression) ++
      [{ root := UF.findRootF reuseStart (reuseRank 4 + 1) 4,
         path := rootPath reuseStart (reuseRank 4 + 1) 4 }] =
    [{ root := 0, path := [4, 2, 1] }]
  decide

/-- The second call consumes the first call's successor, not a fresh start: its
input array is `reuseFirst`, distinct from the origin, its history is the
two-step record, and the fresh alternative from node `4` on the origin both
records a different history and leaves a different final array. -/
theorem reuseRunnerSecond_consumes :
    reuseRunnerSecond = (PathRunner.find reuseRunnerFirst 4 (by decide)).2 ∧
    reuseRunnerFirst = (PathRunner.find reuseRunnerStart 3 (by decide)).2 ∧
    reuseRunnerFirst.parent = reuseFirst ∧
    reuseRunnerFirst.parent ≠ reuseRunnerStart.parent ∧
    reuseRunnerSecond.parent = reuseSecond ∧
    reuseRunnerSecond.trace =
      [{ root := 0, path := [3, 2, 1] }, { root := 0, path := [4, 2] }] ∧
    reuseRunnerFreshFour.parent = [0, 0, 0, 2, 0] ∧
    reuseRunnerFreshFour.parent ≠ reuseSecond ∧
    reuseRunnerFreshFour.trace = [{ root := 0, path := [4, 2, 1] }] := by
  refine ⟨rfl, rfl, reuseRunnerFirst_parent, ?_, reuseRunnerSecond_parent,
    reuseRunnerSecond_trace, reuseRunnerFreshFour_parent, ?_,
    reuseRunnerFreshFour_trace⟩
  · rw [reuseRunnerFirst_parent, reuseRunnerStart_parent]
    decide
  · rw [reuseRunnerFreshFour_parent, reuseSecond_eq]
    decide

/-- Every state the runner reaches keeps the origin's partition. -/
theorem reuseRunnerSecond_same_iff (a b : Nat) :
    UF.Same reuseRunnerSecond.parent a b ↔ UF.Same reuseStart a b :=
  reuseRunnerSecond.same_iff a b

/-- The first successor's partition is the origin's. -/
theorem reuseRunnerFirst_same_iff (a b : Nat) :
    UF.Same reuseRunnerFirst.parent a b ↔ UF.Same reuseStart a b :=
  reuseRunnerFirst.same_iff a b

/-- The first successor is still a ranked forest. -/
theorem reuseRunnerFirst_ranked : Ranked reuseRunnerFirst.parent 5 reuseRank :=
  reuseRunnerFirst.ranked

/-- The second successor is still a ranked forest. -/
theorem reuseRunnerSecond_ranked : Ranked reuseRunnerSecond.parent 5 reuseRank :=
  reuseRunnerSecond.ranked

/-- The second successor is acyclic. -/
theorem reuseRunnerSecond_acyclic : Acyclic reuseRunnerSecond.parent 5 :=
  reuseRunnerSecond.acyclic

end Cap
