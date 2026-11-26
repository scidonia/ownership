/-
Two full-path union-find finds through the integrated sealed boundary.

`Cap.UFReuseRunner` proves a reusable functional runner: `PathRunner.find` returns
a root and a successor runner whose array is the current array with the chase's
whole path compressed. This module runs the same two calls on the *sealed*
execution machine instead of on a private `UF.Arr`. A parent array is held in one
integrated allocation's bytes, the chase reads each parent with `Sealed.read?`,
and every compressed parent is written with `Sealed.write` through the whole-share
read--write capability the allocation started with. Nothing here touches the heap
directly: the only mutation is the sealed write operation, so every accepted write
carries the integrated invariant from `Cap.Integrated`.

### The representation relation

`decode bs` reads a byte buffer as a parent array, one byte per parent value, so
every decoded value is below 256. `Rep s a arr` says the allocation's bytes decode
to `arr`, and `Rep.fits` records that consequence. It is stated over the public
snapshot observation, so it names no private field of the sealed state.

### The two-call example

The fixture is allocation `⟨0⟩` of five bytes with whole-share read--write
capability `⟨1⟩` and disposal name `⟨2⟩`. Setup writes the starting parent array
`reuseStart = [0,0,1,2,2]` through `⟨1⟩`. The first call runs `sealedFind` from
node `3` with the rank-bound fuel `4`; the second call runs on the successor
sealed state that the first call returned, from node `4` with fuel `5`. The
represented arrays are `reuseFirst = [0,0,0,0,2]` and then
`reuseSecond = [0,0,0,0,0]`, the arrays `PathRunner.find` produces; a fresh find
from node `4` on the starting state instead records the longer single path and
leaves `[0,0,0,2,0]`, so the second call is not a rebuild from the origin. A
second allocation carries unrelated bytes through both calls unchanged.

### Read evidence, ownership and the write obligation

The chase is proved to be the functional one in general: `chase?_eq` shows that if
a sealed state's reads agree with an array at every in-range index, then the
sealed chase returns exactly `UF.findRootF` and `rootPath` at the same fuel. Both
successive parent allocations discharge that hypothesis by kernel computation
(`ufStart_reads` on `reuseStart`, `ufFirstState_reads` on `reuseFirst`).

Every accepted write is a `Sealed.write`, and every state the sealed boundary
returns carries the integrated invariant; `ufSecond_invariant` and
`ufSecondOther_invariant` re-export that through `Sealed.state_inv`, so the
second find's result satisfies `State.Inv` (coverage, forest validity and storage
for the multi-allocation state). `ufSecondOwnershipFrames_of_ok` records the
ownership facts the writes leave alone — both whole-share capabilities, the
retired names, the return obligations, both heaps and both live identities.

What is *not* proved is a general per-write refinement law over the sealed
boundary: that one accepted `Sealed.write` sets the represented byte at that index
and frames every other index, for an arbitrary state, array and capability. The
boundary's `Sealed.write_ok_iff` and `Sealed.state` expose the underlying accepted
`State.exec` step from which such a law would be derived, but this module does not
carry that derivation. The final array equality here is therefore established by
kernel-checked computation of the actual sealed run — the reads above drive the
chase and each `Sealed.write` really executes — not by per-write lemmas. Likewise
the unrelated allocation's framing is shown by computation for this example, not
by a general frame theorem over sealed command lists. The same computation
witnesses write eligibility: each `Sealed.write` either is accepted or the run is
refused.
-/
import Cap.Sealed
import Cap.UFReuseRunner

namespace Cap

namespace UFIntegrated

open UF

/-! ### The representation relation -/

/-- The parent array a byte buffer encodes. -/
def decode (bs : List UInt8) : UF.Arr := bs.map UInt8.toNat

/-- Every value of a parent array fits in one byte. -/
def FitsBytes (arr : UF.Arr) : Prop := ∀ x ∈ arr, x < 256

/-- One sealed allocation represents a parent array when its bytes decode to that
array. Because the bytes are `UInt8`, a represented array's entries are all below
256 and its length is the buffer's. -/
def Rep (s : Sealed) (a : AllocId) (arr : UF.Arr) : Prop :=
  ∃ bs, s.snapshot a = some bs ∧ decode bs = arr

/-- A represented array has no value outside the byte range. -/
theorem Rep.fits {s : Sealed} {a : AllocId} {arr : UF.Arr} (h : Rep s a arr) :
    FitsBytes arr := by
  obtain ⟨bs, -, hdec⟩ := h
  intro x hx
  have hx' : x ∈ decode bs := by rw [hdec]; exact hx
  unfold decode at hx'
  obtain ⟨b, -, hb⟩ := List.mem_map.mp hx'
  rw [← hb]
  exact b.toNat_lt_size

/-- The starting parent array's representation. -/
theorem origin_rep {s : Sealed} {a : AllocId}
    (h : s.snapshot a = some [0, 0, 1, 2, 2]) : Rep s a reuseStart :=
  ⟨[0, 0, 1, 2, 2], h, by decide⟩

/-! ### Reading a parent and chasing through the sealed state -/

/-- Read one parent pointer through the sealed boundary. -/
def readParent? (s : Sealed) (a : AllocId) (x : Nat) : Option Nat :=
  (s.read? a x).map (fun b => b.toNat)

/-- Chase from `x` through the bytes of one allocation: the node the chase stops
at and the nodes before it on the path, in the order `UF.rootPath` lists them.
Fuel is the rank bound, as in `UF.findRootF` and `rootPath`. -/
def chase? (s : Sealed) (a : AllocId) : Nat → Nat → Option (Nat × List Nat)
  | 0, x => some (x, [])
  | fuel + 1, x =>
      match readParent? s a x with
      | none => none
      | some y =>
          if y = x then some (x, [])
          else
            match chase? s a fuel y with
            | none => none
            | some (r, path) => some (r, x :: path)

/-- When a sealed state's reads agree with an array and every in-range step stays
in range, the sealed chase is exactly the functional chase: the same root and the
same path, at the same fuel. This is the read half of the refinement; the example
below discharges its hypothesis by computation on the two successive parent
allocations. -/
theorem chase?_eq {s : Sealed} {a : AllocId} {arr : UF.Arr}
    (hread : ∀ i, i < arr.length → readParent? s a i = some (UF.step arr i))
    (hstep : ∀ i, i < arr.length → UF.step arr i < arr.length) :
    ∀ (fuel x : Nat), x < arr.length →
      chase? s a fuel x =
        some (UF.findRootF arr fuel x, rootPath arr fuel x) := by
  intro fuel
  induction fuel with
  | zero =>
      intro x _
      rfl
  | succ fuel ih =>
      intro x hx
      rw [chase?]
      rw [hread x hx]
      dsimp only
      rw [UF.findRootF_succ, rootPath]
      split
      · rename_i hstop
        simp [hstop]
      · rename_i hstop
        rw [ih (UF.step arr x) (hstep x hx)]

/-! ### Writing the compressed parents -/

/-- Write `root` at every node of `path` through the sealed boundary, in path
order. Each step is one `Sealed.write`; there is no other mutation. -/
def compressPath (s : Sealed) (a : AllocId) (id : CapId) (root : Nat) :
    List Nat → Except String Sealed
  | [] => .ok s
  | x :: xs =>
      match s.write a id x (UInt8.ofNat root) with
      | .ok s' => compressPath s' a id root xs
      | .error e => .error e

/-- One find-and-compress through the sealed boundary: read the chase, then write
the root at every node of its path. -/
def sealedFind (s : Sealed) (a : AllocId) (id : CapId) (fuel x : Nat) :
    Except String (Nat × Sealed) :=
  match chase? s a fuel x with
  | none => .error "find refused: a parent read failed"
  | some (r, path) =>
      match compressPath s a id r path with
      | .ok s' => .ok (r, s')
      | .error e => .error e

/-- An accepted find returns the root its chase read, and it wrote exactly that
path's nodes to that root through `Sealed.write`. -/
theorem sealedFind_chase {s : Sealed} {a : AllocId} {id : CapId} {fuel x r : Nat}
    {s' : Sealed} (h : sealedFind s a id fuel x = .ok (r, s')) :
    ∃ path, chase? s a fuel x = some (r, path) ∧
      compressPath s a id r path = .ok s' := by
  unfold sealedFind at h
  cases hc : chase? s a fuel x with
  | none =>
      rw [hc] at h
      simp at h
  | some p =>
      obtain ⟨r0, path⟩ := p
      rw [hc] at h
      dsimp only at h
      cases hw : compressPath s a id r0 path with
      | error e =>
          rw [hw] at h
          simp at h
      | ok s1 =>
          rw [hw] at h
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨path, rfl, hw⟩

/-! ### The fixture -/

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
theorem ufStart_rep : Rep ufStart ⟨0⟩ reuseStart :=
  origin_rep ufStart_snapshot

/-- Every in-range read of the starting state is the origin array's parent. -/
theorem ufStart_reads :
    ∀ i, i < 5 → readParent? ufStart ⟨0⟩ i = some (UF.step reuseStart i) := by
  intro i hi
  rcases reuse_node_cases hi with rfl | rfl | rfl | rfl | rfl <;> decide

/-- Every in-range parent of the origin array is in range. -/
theorem origin_steps : ∀ i, i < 5 → UF.step reuseStart i < 5 := by
  intro i hi
  rcases reuse_node_cases hi with rfl | rfl | rfl | rfl | rfl <;> decide

/-- The origin chase values: the search from node `3` at fuel `4` stops at root
`0` after the path `[3,2,1]`. -/
theorem origin_chase :
    (UF.findRootF reuseStart 4 3, rootPath reuseStart 4 3) = (0, [3, 2, 1]) := by
  decide

/-- The sealed chase on the starting state is the functional origin chase. -/
theorem ufStart_chase :
    chase? ufStart ⟨0⟩ 4 3 =
      some (UF.findRootF reuseStart 4 3, rootPath reuseStart 4 3) :=
  chase?_eq (s := ufStart) (a := ⟨0⟩) (arr := reuseStart)
    ufStart_reads origin_steps 4 3 (by decide)

/-! ### The first find -/

/-- The first find: node `3`, fuel `rank 3 + 1 = 4`, writes through capability
`⟨1⟩`. -/
def ufFirst : Except String (Nat × Sealed) := sealedFind ufStart ⟨0⟩ ⟨1⟩ 4 3

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

/-- An accepted first call returns root `0`. -/
theorem ufFirst_root {r : Nat} {s' : Sealed} (h : ufFirst = .ok (r, s')) :
    r = 0 := by
  have hc := ufFirst_root_option
  rw [h] at hc
  change some r = some 0 at hc
  simpa using hc

/-- An accepted first call leaves `[0,0,0,0,2]`. -/
theorem ufFirst_snapshot {r : Nat} {s' : Sealed} (h : ufFirst = .ok (r, s')) :
    s'.snapshot ⟨0⟩ = some [0, 0, 0, 0, 2] := by
  have hc := ufFirst_snapshot_option
  rw [h] at hc
  change some (s'.snapshot ⟨0⟩) = some (some [0, 0, 0, 0, 2]) at hc
  simpa using hc

/-- The first call's root is the root of the functional chase. -/
theorem ufFirst_root_spec {r : Nat} {s' : Sealed} (h : ufFirst = .ok (r, s')) :
    r = UF.findRootF reuseStart 4 3 := by
  obtain ⟨path, hchase, -⟩ := sealedFind_chase h
  rw [ufStart_chase] at hchase
  simp only [Option.some.injEq, Prod.mk.injEq] at hchase
  exact hchase.1.symm

/-- An accepted first call represents `reuseFirst = [0,0,0,0,2]`. -/
theorem ufFirst_rep {r : Nat} {s' : Sealed} (h : ufFirst = .ok (r, s')) :
    Rep s' ⟨0⟩ reuseFirst :=
  ⟨[0, 0, 0, 0, 2], ufFirst_snapshot h, by decide⟩

/-- The first call matches the functional runner: the same root and the same
represented array as `PathRunner.find reuseRunnerStart 3`. -/
theorem ufFirst_matches_runner {r : Nat} {s' : Sealed}
    (h : ufFirst = .ok (r, s')) :
    r = (PathRunner.find reuseRunnerStart 3 (by decide)).1 ∧
      Rep s' ⟨0⟩ (PathRunner.find reuseRunnerStart 3 (by decide)).2.parent := by
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

/-- The successor state's reads are the intermediate array `reuseFirst`. -/
theorem ufFirstState_reads :
    ∀ i, i < 5 → readParent? ufFirstState ⟨0⟩ i = some (UF.step reuseFirst i) := by
  intro i hi
  rcases reuse_node_cases hi with rfl | rfl | rfl | rfl | rfl <;> decide

/-- Every in-range parent of the intermediate array is in range. -/
theorem intermediate_steps : ∀ i, i < 5 → UF.step reuseFirst i < 5 := by
  intro i hi
  rcases reuse_node_cases hi with rfl | rfl | rfl | rfl | rfl <;> decide

/-! ### The second find on the successor state -/

/-- The second find as a function of the sealed state it is given. -/
def sealedFindSecond (s : Sealed) : Except String (Nat × Sealed) :=
  sealedFind s ⟨0⟩ ⟨1⟩ 5 4

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

/-- On the state the first call returned, the sealed chase is the functional chase
of the intermediate array. -/
theorem ufSecond_chase {r1 : Nat} {s1 : Sealed} (h : ufFirst = .ok (r1, s1)) :
    chase? s1 ⟨0⟩ 5 4 =
      some (UF.findRootF reuseFirst 5 4, rootPath reuseFirst 5 4) := by
  have hs : s1 = ufFirstState := by simp [ufFirstState, h]
  rw [hs]
  exact chase?_eq (s := ufFirstState) (a := ⟨0⟩) (arr := reuseFirst)
    ufFirstState_reads intermediate_steps 5 4 (by decide)

/-- The second call's root is the root of the functional chase on the intermediate
array. -/
theorem ufSecond_root_spec {r1 : Nat} {s1 : Sealed} {r : Nat} {s' : Sealed}
    (h1 : ufFirst = .ok (r1, s1)) (h : sealedFindSecond s1 = .ok (r, s')) :
    r = UF.findRootF reuseFirst 5 4 := by
  obtain ⟨path, hchase, -⟩ := sealedFind_chase h
  rw [ufSecond_chase h1] at hchase
  simp only [Option.some.injEq, Prod.mk.injEq] at hchase
  exact hchase.1.symm

/-- An accepted second call represents `reuseSecond = [0,0,0,0,0]`. -/
theorem ufSecond_rep {r : Nat} {s' : Sealed} (h : ufSecond = .ok (r, s')) :
    Rep s' ⟨0⟩ reuseSecond :=
  ⟨[0, 0, 0, 0, 0], ufSecond_snapshot h, by decide⟩

/-- The second call matches the functional runner's second call: the same root
and the same represented array as `PathRunner.find reuseRunnerFirst 4`. -/
theorem ufSecond_matches_runner {r : Nat} {s' : Sealed}
    (h : ufSecond = .ok (r, s')) :
    r = (PathRunner.find reuseRunnerFirst 4 (by decide)).1 ∧
      Rep s' ⟨0⟩ (PathRunner.find reuseRunnerFirst 4 (by decide)).2.parent := by
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
def ufFreshFour : Except String (Nat × Sealed) := sealedFind ufStart ⟨0⟩ ⟨1⟩ 5 4

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
  sealedFind ufStartWithOther ⟨0⟩ ⟨1⟩ 4 3

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
