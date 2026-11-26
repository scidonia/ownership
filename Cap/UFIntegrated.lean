/-
Two full-path union-find finds through the integrated sealed boundary, as an
instance of the general result.

`Cap.UFGeneric` states and proves the general theorem: for an arbitrary
represented ranked forest with whole-fragment write authority, a find at the
rank-derived fuel returns the functional root, leaves exactly the full-path
compression, preserves the ranked/acyclic/partition certificates, frames every
unrelated allocation, and returns a successor satisfying the next call's
preconditions. This module instantiates it on the five-node forest
`[0,0,1,2,2]`; `decide` only identifies the concrete arrays, paths and roots, and
the compiled controls in `bench/CapUFIntegrated.lean` run the same definitions.

The fixture: allocation `⟨0⟩` of five bytes with whole-share read--write
capability `⟨1⟩` and disposal name `⟨2⟩`. Setup writes `[0,0,1,2,2]` through
`⟨1⟩`. The first call runs from node `3`, the second consumes the first call's
returned sealed state from node `4`, and a second allocation carries unrelated
bytes through both calls unchanged. A fresh find from node `4` on the starting
state instead records the longer single path and leaves `[0,0,0,2,0]`, so the
second call is not a rebuild from the origin.

Read evidence here is existence and bounds only: `Sealed.read?` is the heap's
index read. Write evidence is the whole-share fragment (`UFGeneric.Writable`), which is
what makes each sealed write accepted. Framing is per allocation observation:
`WriteFrame` preserves the unrelated allocation's snapshot and every allocation's
authority, retired names and return obligations; the global `State.Inv` is
re-exported by the boundary rather than derived per untouched allocation.
-/
import Cap.UFGeneric

namespace Cap

namespace UFIntegrated

open UF
open UFGeneric

/-! ### The fixture's representation -/

/-- The five-byte parent allocation: allocation `⟨0⟩`, whole-share read--write
capability `⟨1⟩`, disposal name `⟨2⟩`. -/
def parentAlloc : Sealed := Sealed.initial ⟨0⟩ 5 5 (by decide) ⟨1⟩ ⟨2⟩

/-- Setup writes the starting parent array `reuseStart = [0,0,1,2,2]` through the
whole-share capability: byte `2` becomes `1`, bytes `3` and `4` become `2`. -/
def setup : Except String Sealed := do
  let s1 ← parentAlloc.write ⟨0⟩ ⟨1⟩ 2 1
  let s2 ← s1.write ⟨0⟩ ⟨1⟩ 3 2
  s2.write ⟨0⟩ ⟨1⟩ 4 2

/-- The starting sealed state; `setup_ok` proves the fallback is not taken. -/
def ufStart : Sealed := setup.toOption.getD parentAlloc

/-- Setup is accepted. -/
theorem setup_ok : setup.isOk = true := by decide

/-- The starting state holds the parent array `[0,0,1,2,2]`. -/
theorem ufStart_snapshot : ufStart.snapshot ⟨0⟩ = some [0, 0, 1, 2, 2] := by decide

/-- The starting state represents the functional origin array. -/
theorem ufStart_rep : UFGeneric.Rep ufStart ⟨0⟩ reuseStart :=
  ⟨[0, 0, 1, 2, 2], ufStart_snapshot, by decide⟩

/-- The starting array is a ranked forest under the identity rank. -/
theorem ufStart_ranked : Ranked reuseStart 5 reuseRank := reuseStart_ranked

/-- Setup's writes need the whole-share capability, and they preserve it: the
starting state still holds the whole active read--write fragment. -/
theorem ufStart_writable : UFGeneric.Writable ufStart ⟨0⟩ ⟨1⟩ 5 := by
  show UFGeneric.writableB ufStart ⟨0⟩ ⟨1⟩ 5 = true
  decide

/-- The starting state satisfies the general find's preconditions. -/
theorem ufStart_precondition : UFGeneric.Precondition ufStart ⟨0⟩ ⟨1⟩ reuseStart 5 reuseRank :=
  { rep := ufStart_rep
    length := by decide
    ranked := ufStart_ranked
    fits := by decide
    writable := ufStart_writable }

/-! ### The first find -/

/-- The first find: node `3`, fuel `rank 3 + 1 = 4`, through capability `⟨1⟩`. -/
def ufFirst : Except String (Nat × Sealed) := UFGeneric.sealedFind ufStart ⟨0⟩ ⟨1⟩ 4 3

/-- The successor sealed state of the first find. -/
def ufFirstState : Sealed :=
  match ufFirst with
  | .ok (_, s) => s
  | .error _ => ufStart

/-- The first call is accepted and returns root `0`. -/
theorem ufFirst_root_option : ufFirst.toOption.map (fun p => p.1) = some 0 := by decide

/-- The first call leaves `[0,0,0,0,2]`. -/
theorem ufFirst_snapshot_option :
    ufFirst.toOption.map (fun p => p.2.snapshot ⟨0⟩) =
      some (some [0, 0, 0, 0, 2]) := by decide

/-- The sealed chase on the starting state is the functional origin chase. -/
theorem ufFirst_chase :
    UFGeneric.chase? ufStart ⟨0⟩ 4 3 =
      some (UF.findRootF reuseStart 4 3, rootPath reuseStart 4 3) :=
  UFGeneric.chase?_eq_ranked ufStart_rep (by decide) ufStart_ranked (by decide)

/-- The first find, straight from the general theorem. -/
theorem ufFirst_spec :
    ∃ r s', ufFirst = .ok (r, s') ∧
      r = UF.findRootF reuseStart (reuseRank 3 + 1) 3 ∧
      UFGeneric.Precondition s' ⟨0⟩ ⟨1⟩
        (UF.compressAll reuseStart r (rootPath reuseStart (reuseRank 3 + 1) 3))
        5 reuseRank ∧
      UFGeneric.Rep s' ⟨0⟩
        (UF.compressAll reuseStart r (rootPath reuseStart (reuseRank 3 + 1) 3)) ∧
      s'.state.Inv ∧ WriteFrame ufStart s' ⟨0⟩ := by
  obtain ⟨r, s', h, hr, -, hpre, -, -, hinv, hframe⟩ :=
    UFGeneric.findRanked_spec ufStart_precondition (by decide : 3 < 5)
  refine ⟨r, s', ?_, hr, hpre, hpre.rep, hinv, hframe⟩
  rw [show ufFirst = UFGeneric.findRanked ufStart ⟨0⟩ ⟨1⟩ reuseRank 3 from rfl, h]

/-- The first find's root is the functional root and, by computation, `0`; its
successor represents the functional compression, which is `reuseFirst`. -/
theorem ufFirst_general :
    ∃ s1, ufFirst = .ok (0, s1) ∧
      UFGeneric.Precondition s1 ⟨0⟩ ⟨1⟩ reuseFirst 5 reuseRank ∧
      UFGeneric.Rep s1 ⟨0⟩ reuseFirst ∧ s1.state.Inv ∧ WriteFrame ufStart s1 ⟨0⟩ := by
  obtain ⟨r, s', h, hr, hpre, hrep, hinv, hframe⟩ := ufFirst_spec
  have hr0 : r = 0 := by rw [hr]; decide
  subst hr0
  have harr : UF.compressAll reuseStart 0
      (rootPath reuseStart (reuseRank 3 + 1) 3) = reuseFirst := by decide
  refine ⟨s', h, ?_, ?_, hinv, hframe⟩
  · rw [← harr]; exact hpre
  · rw [← harr]; exact hrep

/-- An accepted first call returns root `0`. -/
theorem ufFirst_root {r : Nat} {s' : Sealed} (h : ufFirst = .ok (r, s')) :
    r = 0 := by
  obtain ⟨s1, hspec, -⟩ := ufFirst_general
  have hok : Except.ok (r, s') = Except.ok (0, s1) := h.symm.trans hspec
  have heq : (r, s') = (0, s1) := by simpa using hok
  exact congrArg Prod.fst heq

/-- An accepted first call leaves `[0,0,0,0,2]`. -/
theorem ufFirst_snapshot {r : Nat} {s' : Sealed} (h : ufFirst = .ok (r, s')) :
    s'.snapshot ⟨0⟩ = some [0, 0, 0, 0, 2] := by
  obtain ⟨s1, hspec, -, hrep1, -, -⟩ := ufFirst_general
  have hok : Except.ok (r, s') = Except.ok (0, s1) := h.symm.trans hspec
  have heq : (r, s') = (0, s1) := by simpa using hok
  have hs : s' = s1 := by simpa using congrArg Prod.snd heq
  rw [hs]
  rw [UFGeneric.Rep.snapshot_eq hrep1 (UFGeneric.Rep.fits hrep1)]
  decide

/-- An accepted first call represents `reuseFirst = [0,0,0,0,2]`. -/
theorem ufFirst_rep {r : Nat} {s' : Sealed} (h : ufFirst = .ok (r, s')) :
    UFGeneric.Rep s' ⟨0⟩ reuseFirst := by
  obtain ⟨s1, hspec, -, hrep1, -, -⟩ := ufFirst_general
  have hok : Except.ok (r, s') = Except.ok (0, s1) := h.symm.trans hspec
  have heq : (r, s') = (0, s1) := by simpa using hok
  have hs : s' = s1 := by simpa using congrArg Prod.snd heq
  rw [hs]
  exact hrep1

/-- The first call's successor satisfies the second call's preconditions. -/
theorem ufFirst_precondition {r : Nat} {s' : Sealed}
    (h : ufFirst = .ok (r, s')) :
    UFGeneric.Precondition s' ⟨0⟩ ⟨1⟩ reuseFirst 5 reuseRank := by
  obtain ⟨s1, hspec, hpre, -, -, -⟩ := ufFirst_general
  have hok : Except.ok (r, s') = Except.ok (0, s1) := h.symm.trans hspec
  have heq : (r, s') = (0, s1) := by simpa using hok
  have hs : s' = s1 := by simpa using congrArg Prod.snd heq
  rw [hs]
  exact hpre

/-- The first call frames the starting state's ownership observations. -/
theorem ufFirst_frame {r : Nat} {s' : Sealed} (h : ufFirst = .ok (r, s')) :
    WriteFrame ufStart s' ⟨0⟩ := by
  obtain ⟨s1, hspec, -, -, -, hframe⟩ := ufFirst_general
  have hok : Except.ok (r, s') = Except.ok (0, s1) := h.symm.trans hspec
  have heq : (r, s') = (0, s1) := by simpa using hok
  have hs : s' = s1 := by simpa using congrArg Prod.snd heq
  rw [hs]
  exact hframe

/-- The first call's root is the root of the functional chase. -/
theorem ufFirst_root_spec {r : Nat} {s' : Sealed} (h : ufFirst = .ok (r, s')) :
    r = UF.findRootF reuseStart (reuseRank 3 + 1) 3 := by
  obtain ⟨s1, hspec, -⟩ := ufFirst_general
  have hok : Except.ok (r, s') = Except.ok (0, s1) := h.symm.trans hspec
  have heq : (r, s') = (0, s1) := by simpa using hok
  rw [show r = 0 from congrArg Prod.fst heq]
  decide

/-- The first call matches the functional runner: the same root and the same
represented array as `PathRunner.find reuseRunnerStart 3`. -/
theorem ufFirst_matches_runner {r : Nat} {s' : Sealed}
    (h : ufFirst = .ok (r, s')) :
    r = (PathRunner.find reuseRunnerStart 3 (by decide)).1 ∧
      UFGeneric.Rep s' ⟨0⟩ (PathRunner.find reuseRunnerStart 3 (by decide)).2.parent := by
  refine ⟨?_, ?_⟩
  · rw [ufFirst_root h]
    exact reuseRunnerFirst_root.symm
  · have harr : (PathRunner.find reuseRunnerStart 3 (by decide)).2.parent =
        reuseFirst := by
      simpa [reuseRunnerFirst] using reuseRunnerFirst_parent
    rw [harr]
    exact ufFirst_rep h

/-- The successor state's bytes are the first compression result. -/
theorem ufFirstState_snapshot : ufFirstState.snapshot ⟨0⟩ = some [0, 0, 0, 0, 2] := by
  decide

/-- On the state the first call returned, the sealed chase is the functional chase
of the intermediate array. -/
theorem ufSecond_chase {r1 : Nat} {s1 : Sealed} (h1 : ufFirst = .ok (r1, s1)) :
    UFGeneric.chase? s1 ⟨0⟩ 5 4 =
      some (UF.findRootF reuseFirst 5 4, rootPath reuseFirst 5 4) := by
  have hs : s1 = ufFirstState := by simp [ufFirstState, h1]
  rw [hs]
  have hrep : UFGeneric.Rep ufFirstState ⟨0⟩ reuseFirst := by
    rw [← hs]
    exact ufFirst_rep h1
  exact UFGeneric.chase?_eq_ranked hrep (by decide) reuseFirst_ranked
    (by decide : 4 < 5)

/-! ### The second find on the successor state -/

/-- The second find as a function of the sealed state it is given. -/
def sealedFindSecond (s : Sealed) : Except String (Nat × Sealed) :=
  UFGeneric.sealedFind s ⟨0⟩ ⟨1⟩ 5 4

/-- The second find consumes the state the first find returned, from node `4`
with fuel `5`. -/
def ufSecond : Except String (Nat × Sealed) :=
  match ufFirst with
  | .ok (_, s) => sealedFindSecond s
  | .error e => .error e

/-- Under an accepted first call, the second call runs on precisely the returned
sealed state. -/
theorem ufSecond_run {r1 : Nat} {s1 : Sealed} (h : ufFirst = .ok (r1, s1)) :
    ufSecond = sealedFindSecond s1 := by
  unfold ufSecond
  rw [h]

/-- The second call, straight from the general theorem run on the first call's
successor. -/
theorem ufSecond_general {r1 : Nat} {s1 : Sealed} (h1 : ufFirst = .ok (r1, s1)) :
    ∃ s2, ufSecond = .ok (0, s2) ∧
      UFGeneric.Precondition s2 ⟨0⟩ ⟨1⟩ reuseSecond 5 reuseRank ∧
      UFGeneric.Rep s2 ⟨0⟩ reuseSecond ∧ s2.state.Inv ∧ WriteFrame ufStart s2 ⟨0⟩ := by
  obtain ⟨s1', hspec1, hpre1, -, -, hframe1⟩ := ufFirst_general
  have hok1 : Except.ok (r1, s1) = Except.ok (0, s1') := h1.symm.trans hspec1
  have heq1 : (r1, s1) = (0, s1') := by simpa using hok1
  have hs1 : s1 = s1' := by simpa using congrArg Prod.snd heq1
  rw [← hs1] at hpre1 hframe1
  obtain ⟨r2, s2, hspec2, hr2, -, hpre2, -, -, hinv2, hframe2⟩ :=
    UFGeneric.findRanked_spec hpre1 (by decide : 4 < 5)
  have hr20 : r2 = 0 := by rw [hr2]; decide
  subst hr20
  have huf : ufSecond = UFGeneric.findRanked s1 ⟨0⟩ ⟨1⟩ reuseRank 4 := by
    rw [ufSecond_run h1]
    rfl
  have harr : UF.compressAll reuseFirst 0
      (rootPath reuseFirst (reuseRank 4 + 1) 4) = reuseSecond := by decide
  refine ⟨s2, ?_, ?_, ?_, hinv2, hframe1.trans hframe2⟩
  · rw [huf]; exact hspec2
  · rw [← harr]; exact hpre2
  · rw [← harr]; exact hpre2.rep

/-- The second call is accepted and returns root `0`. -/
theorem ufSecond_root_option : ufSecond.toOption.map (fun p => p.1) = some 0 := by decide

/-- The second call leaves `[0,0,0,0,0]`. -/
theorem ufSecond_snapshot_option :
    ufSecond.toOption.map (fun p => p.2.snapshot ⟨0⟩) =
      some (some [0, 0, 0, 0, 0]) := by decide

/-- An accepted second call returns root `0`. -/
theorem ufSecond_root {r : Nat} {s' : Sealed} (h : ufSecond = .ok (r, s')) :
    r = 0 := by
  have hc := ufSecond_root_option
  rw [h] at hc
  change some r = some 0 at hc
  simpa using hc

/-- An accepted second call leaves `[0,0,0,0,0]`. -/
theorem ufSecond_snapshot {r : Nat} {s' : Sealed} (h : ufSecond = .ok (r, s')) :
    s'.snapshot ⟨0⟩ = some [0, 0, 0, 0, 0] := by
  have hc := ufSecond_snapshot_option
  rw [h] at hc
  change some (s'.snapshot ⟨0⟩) = some (some [0, 0, 0, 0, 0]) at hc
  simpa using hc

/-- The second call's root is the root of the functional chase on the intermediate
array. -/
theorem ufSecond_root_spec {r1 : Nat} {s1 : Sealed} {r : Nat} {s' : Sealed}
    (h1 : ufFirst = .ok (r1, s1)) (h : sealedFindSecond s1 = .ok (r, s')) :
    r = UF.findRootF reuseFirst 5 4 := by
  obtain ⟨path, hchase, -⟩ := UFGeneric.sealedFind_some h
  rw [ufSecond_chase h1] at hchase
  simp only [Option.some.injEq, Prod.mk.injEq] at hchase
  exact hchase.1.symm

/-- An accepted second call represents `reuseSecond = [0,0,0,0,0]`. -/
theorem ufSecond_rep {r : Nat} {s' : Sealed} (h : ufSecond = .ok (r, s')) :
    UFGeneric.Rep s' ⟨0⟩ reuseSecond :=
  ⟨[0, 0, 0, 0, 0], ufSecond_snapshot h, by decide⟩

/-- The second call matches the functional runner's second call: the same root
and the same represented array as `PathRunner.find reuseRunnerFirst 4`. -/
theorem ufSecond_matches_runner {r : Nat} {s' : Sealed}
    (h : ufSecond = .ok (r, s')) :
    r = (PathRunner.find reuseRunnerFirst 4 (by decide)).1 ∧
      UFGeneric.Rep s' ⟨0⟩ (PathRunner.find reuseRunnerFirst 4 (by decide)).2.parent := by
  refine ⟨?_, ?_⟩
  · rw [ufSecond_root h]
    exact reuseRunnerSecond_root.symm
  · have harr : (PathRunner.find reuseRunnerFirst 4 (by decide)).2.parent =
        reuseSecond := by
      simpa [reuseRunnerSecond] using reuseRunnerSecond_parent
    rw [harr]
    exact ufSecond_rep h

/-! ### Threading, not rebuilding -/

/-- A fresh find from node `4` on the starting state, for the control that the
second call does not rebuild from the origin. -/
def ufFreshFour : Except String (Nat × Sealed) := UFGeneric.sealedFind ufStart ⟨0⟩ ⟨1⟩ 5 4

/-- A fresh find from node `4` on the origin records the longer single path and
leaves `[0,0,0,2,0]`, not the two-step run's `[0,0,0,0,0]`. -/
theorem ufFreshFour_snapshot_option :
    ufFreshFour.toOption.map (fun p => p.2.snapshot ⟨0⟩) =
      some (some [0, 0, 0, 2, 0]) := by decide

/-- The two calls thread the actual sealed state: the second call takes the first
call's successor state, the first call changed the bytes, the second call's result
is `[0,0,0,0,0]`, and a fresh find from node `4` on the starting state would
instead stop at `[0,0,0,2,0]`. -/
theorem ufSecond_consumes {r1 : Nat} {s1 : Sealed} (h1 : ufFirst = .ok (r1, s1)) :
    ufSecond = sealedFindSecond s1 ∧
      s1.snapshot ⟨0⟩ = some [0, 0, 0, 0, 2] ∧
      s1.snapshot ⟨0⟩ ≠ ufStart.snapshot ⟨0⟩ ∧
      ufFreshFour.toOption.map (fun p => p.2.snapshot ⟨0⟩) =
        some (some [0, 0, 0, 2, 0]) ∧
      ufSecond.toOption.map (fun p => p.2.snapshot ⟨0⟩) =
        some (some [0, 0, 0, 0, 0]) := by
  refine ⟨ufSecond_run h1, ufFirst_snapshot h1, ?_,
    ufFreshFour_snapshot_option, ufSecond_snapshot_option⟩
  rw [ufFirst_snapshot h1, ufStart_snapshot]
  decide

/-! ### An unrelated allocation is preserved -/

/-- The starting state plus a second allocation `⟨1⟩` of three bytes, root
capability `⟨10⟩` and disposal `⟨11⟩`, whose byte `0` is written to `5`. -/
def withOther : Except String Sealed := do
  let s ← ufStart.alloc ⟨1⟩ 3 3 (by decide) ⟨10⟩ ⟨11⟩
  s.write ⟨1⟩ ⟨10⟩ 0 5

/-- The two-allocation starting state. -/
def ufStartWithOther : Sealed := withOther.toOption.getD ufStart

/-- The first find over the two-allocation state. -/
def ufFirstOther : Except String (Nat × Sealed) :=
  UFGeneric.sealedFind ufStartWithOther ⟨0⟩ ⟨1⟩ 4 3

/-- The second find over the two-allocation state, on the first call's output. -/
def ufSecondOther : Except String (Nat × Sealed) :=
  match ufFirstOther with
  | .ok (_, s) => sealedFindSecond s
  | .error e => .error e

/-- Both calls are accepted on the two-allocation state, the parent allocation
still ends at `[0,0,0,0,0]`, the unrelated allocation keeps its bytes `[5,0,0]`,
and both allocations remain live and distinct. -/
theorem ufSecondOther_frames :
    ufSecondOther.toOption.map (fun p =>
      (p.2.snapshot ⟨0⟩, p.2.snapshot ⟨1⟩, p.2.allocations)) =
      some (some [0, 0, 0, 0, 0], some [5, 0, 0], [⟨1⟩, ⟨0⟩]) := by decide

/-- The whole `[0,5)` read--write fragment of the parent allocation. -/
def wholeParent : Reconstruction.Fragment :=
  { alloc := ⟨0⟩, lo := 0, hi := 5, q := 5, ceiling := .readWrite, state := .active }

/-- The whole `[0,3)` read--write fragment of the unrelated allocation. -/
def wholeOther : Reconstruction.Fragment :=
  { alloc := ⟨1⟩, lo := 0, hi := 3, q := 3, ceiling := .readWrite, state := .active }

/-- The ownership facts the two finds must leave alone: both allocations' current
fragments are still their whole active read--write fragments, no access name was
retired, no return obligation was recorded, both heaps hold their arrays, and both
allocations are live and distinct. -/
def OwnershipFrames (s : Sealed) : Prop :=
  s.authority? ⟨0⟩ ⟨1⟩ = some wholeParent ∧
    s.authority? ⟨1⟩ ⟨10⟩ = some wholeOther ∧
    s.retiredOf ⟨0⟩ = [] ∧
    s.retiredOf ⟨1⟩ = [] ∧
    s.restoresOf ⟨0⟩ = [] ∧
    s.restoresOf ⟨1⟩ = [] ∧
    s.snapshot ⟨0⟩ = some [0, 0, 0, 0, 0] ∧
    s.snapshot ⟨1⟩ = some [5, 0, 0] ∧
    s.allocations = [⟨1⟩, ⟨0⟩]

/-- Both allocations' current capabilities after the two calls. -/
theorem ufSecondOther_authority :
    ufSecondOther.toOption.map (fun p =>
      (p.2.authority? ⟨0⟩ ⟨1⟩, p.2.authority? ⟨1⟩ ⟨10⟩)) =
      some (some wholeParent, some wholeOther) := by decide

/-- No access name is retired by either allocation after the two calls. -/
theorem ufSecondOther_retired :
    ufSecondOther.toOption.map (fun p =>
      (p.2.retiredOf ⟨0⟩, p.2.retiredOf ⟨1⟩)) =
      some (([] : List CapId), ([] : List CapId)) := by decide

/-- No return obligation is outstanding after the two calls. -/
theorem ufSecondOther_restores :
    ufSecondOther.toOption.map (fun p =>
      (p.2.restoresOf ⟨0⟩, p.2.restoresOf ⟨1⟩)) =
      some (([] : List Reconstruction.Restore),
        ([] : List Reconstruction.Restore)) := by decide

/-- The two finds' writes touch only bytes: every ownership fact in
`OwnershipFrames` survives both calls, including the unrelated allocation's
authority and bytes. -/
theorem ufSecondOwnershipFrames_of_ok {r : Nat} {s' : Sealed}
    (h : ufSecondOther = .ok (r, s')) : OwnershipFrames s' := by
  have ha := ufSecondOther_authority
  have hr := ufSecondOther_retired
  have hs := ufSecondOther_restores
  have hf := ufSecondOther_frames
  rw [h] at ha hr hs hf
  change some (s'.authority? ⟨0⟩ ⟨1⟩, s'.authority? ⟨1⟩ ⟨10⟩) =
    some (some wholeParent, some wholeOther) at ha
  change some (s'.retiredOf ⟨0⟩, s'.retiredOf ⟨1⟩) =
    some (([] : List CapId), ([] : List CapId)) at hr
  change some (s'.restoresOf ⟨0⟩, s'.restoresOf ⟨1⟩) =
    some (([] : List Reconstruction.Restore),
      ([] : List Reconstruction.Restore)) at hs
  change some (s'.snapshot ⟨0⟩, s'.snapshot ⟨1⟩, s'.allocations) =
    some (some [0, 0, 0, 0, 0], some [5, 0, 0], [⟨1⟩, ⟨0⟩]) at hf
  simp only [Option.some.injEq, Prod.mk.injEq] at ha hr hs hf
  exact ⟨ha.1, ha.2, hr.1, hr.2, hs.1, hs.2, hf.1, hf.2.1, hf.2.2⟩

/-- The second find's result satisfies the integrated invariant: every sealed
state carries it, and the writes are sealed operations. -/
theorem ufSecond_invariant {r : Nat} {s' : Sealed}
    (_h : ufSecond = .ok (r, s')) : s'.state.Inv := s'.state_inv

/-- The two-call state's result satisfies the integrated invariant for its whole
multi-allocation state, so the unrelated allocation is inside the preserved
invariant as well. -/
theorem ufSecondOther_invariant {r : Nat} {s' : Sealed}
    (_h : ufSecondOther = .ok (r, s')) : s'.state.Inv := s'.state_inv

end UFIntegrated

end Cap
