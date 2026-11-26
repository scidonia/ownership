/-
A sealed boundary for the borrowed-reconstruction state machine.

`Cap.Sealed` seals the observable world: it accepts a checked `UCmd` list and
observes one allocation's bytes. Its split and join commands still consult the
allocation-wide loan test, so `World.splitAtChecked_refuses_with_loan` refuses
any subdivision of an allocation while a loan on it is outstanding. That is the
world path, and this module does not change it.

This module is the second sealed boundary, over `Reconstruction.State`. The
constructor is private and so is the carried `State.Inv` proof, so a client can
hold and use a reconstruction state but can obtain one only by an operation the
checker accepted: `write`, `borrow`, `splitSpatial`, `splitFraction`,
`reconstruct`, and `return`. Every accepted operation returns a sealed state with
the invariant rebuilt from its preservation theorem; a refused operation returns
an error and no state. The observations are a heap snapshot, per-fragment
authority descriptions, the retired access names and the live return
obligations; the `State` itself and its proof are not exported.

The two boundaries are complementary rather than one routed through the other.
This is the borrowed-subdivision lifecycle along its own state machine, including
the allocation-wide-guard gap that `Cap.Reconstruction`'s module note describes.
The world path remains the executable `UCmd` semantics with its allocation-wide
guard; routing `World.splitAtChecked` through this forest is not claimed here.

The same model boundary applies as at `Cap.Sealed`: the state is pure data, a
copy shares its representation, and the private constructor — not affineness —
is what prevents manufacture.
-/
import Cap.Reconstruction

namespace Cap.Reconstruction

/-- A reconstruction state reachable only through this module's checked
operations, carrying the reconstruction invariant. -/
structure Sealed where
  private mk ::
  private s : State
  private inv : s.Inv

private def mkSealed (s : State) (h : s.Inv) : Sealed := Sealed.mk s h

private def openSealed (s : Sealed) : State := s.s

/-- A plain-data description of a current fragment: allocation, interval, share,
ceiling and state. This is the exported view of a leaf; the proof fields stay
inside the boundary. -/
structure Fragment where
  alloc : AllocId
  lo : Nat
  hi : Nat
  q : Nat
  ceiling : Ceiling
  state : CapState
deriving DecidableEq, Repr

/-- Every sealed state, however obtained, satisfies the reconstruction
invariant. -/
theorem Sealed.invariant (s : Sealed) : s.s.Inv := s.inv

/-- The canonical sealed state is a whole fresh allocation: `n` zero bytes with
whole share `D`, a root access name and an unused disposal name. -/
def Sealed.initial (a : AllocId) (n D : Nat) (pos : 0 < D)
    (rootId disposalId : CapId) : Sealed :=
  mkSealed (State.initial a n D pos rootId disposalId)
    (State.initial_inv a n D pos rootId disposalId)

/-- The 64-byte fixture: allocation `⟨0⟩` over `[0,64)` with share `64`, root
access name `⟨1⟩` and disposal name `⟨2⟩`. -/
def Sealed.initial64 : Sealed :=
  Sealed.initial ⟨0⟩ 64 64 (by decide) ⟨1⟩ ⟨2⟩

/-- Write one byte through a current active whole-share fragment of a
read--write ceiling. -/
def Sealed.write (s : Sealed) (id : CapId) (i : Nat) (v : UInt8) :
    Except String Sealed :=
  match h : (openSealed s).write id i v with
  | some s' => .ok (mkSealed s' (State.write_inv h s.inv))
  | none =>
      .error
        "write refused: not an active whole-share read--write fragment or offset out of range"

/-- Borrow a current active fragment, recording the lender's restoration
obligation for the same footprint and share. -/
def Sealed.borrow (s : Sealed) (lender borrower : CapId) :
    Except String Sealed :=
  match h : (openSealed s).borrow lender borrower with
  | some s' => .ok (mkSealed s' (State.borrow_inv h s.inv))
  | none =>
      .error
        "borrow refused: lender is not an active current fragment or borrower name is not fresh"

/-- Spatially subdivide a current fragment; the children must exactly partition
its interval and their names must never have been issued or retired. -/
def Sealed.splitSpatial (s : Sealed) (parentId c1 c2 : CapId)
    (lo1 hi1 lo2 hi2 : Nat) : Except String Sealed :=
  match h : (openSealed s).splitSpatial parentId c1 c2 lo1 hi1 lo2 hi2 with
  | some s' => .ok (mkSealed s' (State.splitSpatial_inv h s.inv))
  | none =>
      .error
        "splitSpatial refused: children do not partition an active fragment or a child name is not fresh"

/-- Fractionally subdivide a current fragment; the child shares must be positive
and sum to the parent's, and their names must never have been issued or
retired. -/
def Sealed.splitFraction (s : Sealed) (parentId c1 c2 : CapId)
    (q1 q2 : Nat) : Except String Sealed :=
  match h : (openSealed s).splitFraction parentId c1 c2 q1 q2 with
  | some s' => .ok (mkSealed s' (State.splitFraction_inv h s.inv))
  | none =>
      .error
        "splitFraction refused: child shares are not positive and equal to the parent's or a child name is not fresh"

/-- Reconstruct a suspended fragment from its two rule fragments. Refused while
either child is subdivided or lent further. -/
def Sealed.reconstruct (s : Sealed) (parentId : CapId) : Except String Sealed :=
  match h : (openSealed s).reconstruct parentId with
  | some s' => .ok (mkSealed s' (State.reconstruct_inv h s.inv))
  | none =>
      .error
        "reconstruct refused: no suspension with that parent or a descendant is still subdivided or lent"

/-- Return a borrowed fragment, restoring the dormant lender's access name. The
resource must have been reconstructed first. -/
def Sealed.return (s : Sealed) (borrower : CapId) : Except String Sealed :=
  match h : (openSealed s).return borrower with
  | some s' => .ok (mkSealed s' (State.return_inv h s.inv))
  | none =>
      .error
        "return refused: no matching obligation or the borrowed resource is not the reconstructed whole fragment"

/-- The heap bytes of one allocation, as a copy. -/
def Sealed.snapshot (s : Sealed) (a : AllocId) : Option (List UInt8) :=
  (openSealed s).heap.snapshot? a

/-- Read one byte of the represented heap. -/
def Sealed.read? (s : Sealed) (a : AllocId) (i : Nat) : Option UInt8 :=
  (openSealed s).heap.read? a i

/-- The current fragment with the given access name. `none` means the name is
not in the current frontier. -/
def Sealed.authority? (s : Sealed) (id : CapId) : Option Fragment :=
  ((openSealed s).forest.findLeaf? id).map
    (fun c => { alloc := c.alloc, lo := c.lo, hi := c.hi, q := c.q,
                ceiling := c.ceiling, state := c.state })

/-- The access names retired so far, most recent first. -/
def Sealed.retired (s : Sealed) : List CapId := (openSealed s).retired

/-- The outstanding return obligations, most recent first. -/
def Sealed.restores (s : Sealed) : List Restore := (openSealed s).restores

/-- The 64-byte lifecycle: borrow the whole fragment `⟨1⟩` as `⟨3⟩`, split it
into `⟨4⟩ : [0,32)` and `⟨5⟩ : [32,64)`, write both halves, reconstruct
`[0,64)`, and return `⟨3⟩` to `⟨1⟩`. -/
def Sealed.lifecycle (s : Sealed) : Except String Sealed := do
  let s1 ← s.borrow ⟨1⟩ ⟨3⟩
  let s2 ← s1.splitSpatial ⟨3⟩ ⟨4⟩ ⟨5⟩ 0 32 32 64
  let s3 ← s2.write ⟨4⟩ 0 7
  let s4 ← s3.write ⟨5⟩ 40 9
  let s5 ← s4.reconstruct ⟨3⟩
  s5.return ⟨3⟩

/-- A second full cycle on the output of the first: borrow the restored whole
fragment `⟨1⟩` as `⟨6⟩`, split it, write both halves at different offsets, and
return `⟨6⟩`. -/
def Sealed.reuseLifecycle (s : Sealed) : Except String Sealed := do
  let s1 ← s.borrow ⟨1⟩ ⟨6⟩
  let s2 ← s1.splitSpatial ⟨6⟩ ⟨7⟩ ⟨8⟩ 0 32 32 64
  let s3 ← s2.write ⟨7⟩ 1 12
  let s4 ← s3.write ⟨8⟩ 33 13
  let s5 ← s4.reconstruct ⟨6⟩
  s5.return ⟨6⟩

/-- The restored whole fragment of the 64-byte fixture, as observed. -/
def wholeFragment : Fragment :=
  { alloc := ⟨0⟩, lo := 0, hi := 64, q := 64,
    ceiling := .readWrite, state := .active }

/-- The heap after the first lifecycle: byte 0 written through `⟨4⟩` and byte 40
through `⟨5⟩`. -/
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

/-! ### The first lifecycle -/

/-- The 64-byte lifecycle completes. -/
theorem lifecycle_ok : (Sealed.lifecycle Sealed.initial64).isOk = true := by
  decide

/-- The only observation of the completed lifecycle: the bytes the two children
wrote survive reconstruction and return. -/
theorem lifecycle_snapshot :
    (Sealed.lifecycle Sealed.initial64).toOption.map
        (fun s => s.snapshot ⟨0⟩) = some (some firstSnapshot) := by
  decide

/-- The restored lender is the whole `[0,64)` fragment and the parent and child
names are gone from the current frontier. -/
theorem lifecycle_authority :
    (Sealed.lifecycle Sealed.initial64).toOption.map
        (fun s => (s.authority? ⟨1⟩, s.authority? ⟨3⟩,
          s.authority? ⟨4⟩, s.authority? ⟨5⟩)) =
      some (some wholeFragment, none, none, none) := by
  decide

/-- The borrowed and child names are retired and the obligation is discharged. -/
theorem lifecycle_retired :
    (Sealed.lifecycle Sealed.initial64).toOption.map Sealed.retired =
      some [⟨3⟩, ⟨4⟩, ⟨5⟩] := by
  decide

/-- The completed lifecycle leaves no outstanding return obligation. -/
theorem lifecycle_restores :
    (Sealed.lifecycle Sealed.initial64).toOption.map Sealed.restores =
      some ([] : List Restore) := by
  decide

/-- An accepted lifecycle observes exactly the two written bytes. -/
theorem lifecycle_snapshot_of_ok {s' : Sealed}
    (h : Sealed.lifecycle Sealed.initial64 = .ok s') :
    s'.snapshot ⟨0⟩ = some firstSnapshot := by
  have hc := lifecycle_snapshot
  rw [h] at hc
  change some (s'.snapshot ⟨0⟩) = some (some firstSnapshot) at hc
  simpa using hc

/-- An accepted lifecycle restores the whole lender fragment and retires the
parent and both children. -/
theorem lifecycle_authority_of_ok {s' : Sealed}
    (h : Sealed.lifecycle Sealed.initial64 = .ok s') :
    s'.authority? ⟨1⟩ = some wholeFragment ∧ s'.authority? ⟨3⟩ = none ∧
      s'.authority? ⟨4⟩ = none ∧ s'.authority? ⟨5⟩ = none := by
  have hc := lifecycle_authority
  rw [h] at hc
  change some (s'.authority? ⟨1⟩, s'.authority? ⟨3⟩,
      s'.authority? ⟨4⟩, s'.authority? ⟨5⟩) =
      some (some wholeFragment, none, none, none) at hc
  simpa only [Option.some.injEq, Prod.mk.injEq, and_assoc] using hc

/-- An accepted lifecycle retires the borrowed and child names. -/
theorem lifecycle_retired_of_ok {s' : Sealed}
    (h : Sealed.lifecycle Sealed.initial64 = .ok s') :
    s'.retired = [⟨3⟩, ⟨4⟩, ⟨5⟩] := by
  have hc := lifecycle_retired
  rw [h] at hc
  change some s'.retired = some [⟨3⟩, ⟨4⟩, ⟨5⟩] at hc
  simpa using hc

/-- An accepted lifecycle leaves no outstanding return obligation. -/
theorem lifecycle_restores_of_ok {s' : Sealed}
    (h : Sealed.lifecycle Sealed.initial64 = .ok s') :
    s'.restores = [] := by
  have hc := lifecycle_restores
  rw [h] at hc
  change some s'.restores = some ([] : List Restore) at hc
  simpa using hc

/-- An accepted lifecycle carries the reconstruction invariant. -/
theorem lifecycle_inv_of_ok {s' : Sealed}
    (_h : Sealed.lifecycle Sealed.initial64 = .ok s') : s'.s.Inv := s'.inv

/-! ### Reuse: a second verified cycle on the output -/

/-- The first lifecycle followed by a second full borrow/split/write/
reconstruct/return cycle on the restored fragment. -/
def lifecycleThenReuse : Except String Sealed := do
  let s ← Sealed.lifecycle Sealed.initial64
  s.reuseLifecycle

/-- The second cycle is accepted on the first cycle's output. -/
theorem reuse_ok : lifecycleThenReuse.isOk = true := by
  decide

/-- Both cycles' writes are observed: the first cycle's bytes survive the
second cycle, and the second cycle's bytes are added. -/
theorem reuse_snapshot :
    lifecycleThenReuse.toOption.map (fun s => s.snapshot ⟨0⟩) =
      some (some secondSnapshot) := by
  decide

/-- After both cycles the lender again holds the whole fragment and all four
borrower and child names of the second cycle are gone. -/
theorem reuse_authority :
    lifecycleThenReuse.toOption.map
        (fun s => (s.authority? ⟨1⟩, s.authority? ⟨6⟩,
          s.authority? ⟨7⟩, s.authority? ⟨8⟩)) =
      some (some wholeFragment, none, none, none) := by
  decide

/-- Both cycles' names are retired, most recent first. -/
theorem reuse_retired :
    lifecycleThenReuse.toOption.map Sealed.retired =
      some [⟨6⟩, ⟨7⟩, ⟨8⟩, ⟨3⟩, ⟨4⟩, ⟨5⟩] := by
  decide

/-- An accepted second cycle observes both cycles' bytes. -/
theorem reuse_snapshot_of_ok {s' : Sealed}
    (h : lifecycleThenReuse = .ok s') : s'.snapshot ⟨0⟩ = some secondSnapshot := by
  have hc := reuse_snapshot
  rw [h] at hc
  change some (s'.snapshot ⟨0⟩) = some (some secondSnapshot) at hc
  simpa using hc

/-- An accepted second cycle again restores the whole lender fragment. -/
theorem reuse_authority_of_ok {s' : Sealed}
    (h : lifecycleThenReuse = .ok s') :
    s'.authority? ⟨1⟩ = some wholeFragment ∧ s'.authority? ⟨6⟩ = none ∧
      s'.authority? ⟨7⟩ = none ∧ s'.authority? ⟨8⟩ = none := by
  have hc := reuse_authority
  rw [h] at hc
  change some (s'.authority? ⟨1⟩, s'.authority? ⟨6⟩,
      s'.authority? ⟨7⟩, s'.authority? ⟨8⟩) =
      some (some wholeFragment, none, none, none) at hc
  simpa only [Option.some.injEq, Prod.mk.injEq, and_assoc] using hc

/-- An accepted second cycle carries the reconstruction invariant. -/
theorem reuse_inv_of_ok {s' : Sealed}
    (_h : lifecycleThenReuse = .ok s') : s'.s.Inv := s'.inv

end Cap.Reconstruction
