/-
The sealed execution boundary.

Lean has no module opacity: a public `World` can be built and taken apart
anywhere. This module narrows the boundary the only way the language permits —
a structure whose constructor is private to this file, so other modules can hold
and use a sealed world but cannot manufacture one or destructure it. A sealed
world is produced only from a command list the checker accepted, and its
observable interface is a snapshot of one allocation.

What is proved here is the *bookkeeping* boundary: every sealed world reaches
the outside through an accepted run; running more commands is deterministic; and
the physical claims at the executable edge are listed with their status rather
than asserted. What is deliberately not claimed is storage independence: the
model's backends are pure lists, a copy of a program and its world shares them,
and nothing here says two executed programs have independent physical storage.
That is the C runner's contract (`runtime-bridge/`), stated as a runtime
assumption, not a theorem of this model.
-/
import Cap.FullInv

namespace Cap

/-- A world reachable only through this module's constructors, carrying the
combined invariant. -/
structure Sealed where
  private mk ::
  private w : World
  private h : World.FullInv w

private def mkSealed (w : World) (h : World.FullInv w) : Sealed := Sealed.mk w h

private def openSealed (s : Sealed) : World := s.w

/-- The canonical sealed state starts from the empty world. -/
def Sealed.empty : Sealed := mkSealed World.emptyWorld World.emptyWorld_fullInv

/-- A certified imported model state, for proofs that need to start elsewhere.
The full invariant is required, so malformed worlds cannot enter. This is the
proof-facing API; executable clients start from `Sealed.empty`. -/
def Sealed.importCertified (w : World) (h : w.FullInv) : Sealed := mkSealed w h

/-- Run commands inside the sealed boundary. The invariant is carried by the
constructor, so an accepted run yields a sealed world that satisfies it; a
refused run yields no state. -/
def Sealed.run (s : Sealed) (cmds : List UCmd) : Except String Sealed :=
  match h : checkWorld (openSealed s) cmds with
  | .ok w' => .ok (mkSealed w' (World.checkWorld_fullInv _ _ _ h s.h))
  | .error e => .error e

/-- The only observation: a copy of one allocation's bytes. The result is an
immutable list, so a snapshot cannot alias a mutable buffer. -/
def Sealed.snapshot (s : Sealed) (a : AllocId) : Option (List UInt8) :=
  (openSealed s).heaps a |>.map (·.buf)

/-- Snapshotting a sealed world returns the bytes of its represented backend. -/
theorem Sealed.snapshot_eq (s : Sealed) (a : AllocId) (b : Backend)
    (hb : (openSealed s).heaps a = some b) :
    s.snapshot a = some b.buf := by
  unfold Sealed.snapshot
  rw [hb]
  rfl

/-- Every sealed state, however obtained, satisfies the combined invariant. -/
theorem Sealed.invariant (s : Sealed) : s.w.FullInv := s.h

/-- The canonical state satisfies the combined invariant. -/
theorem Sealed.empty_invariant : Sealed.empty.w.FullInv := Sealed.empty.h

/-- A certified import satisfies the combined invariant. -/
theorem Sealed.importCertified_invariant (w : World) (h : w.FullInv) :
    (Sealed.importCertified w h).w.FullInv :=
  (Sealed.importCertified w h).h

/-- A completed run's sealed state satisfies the combined invariant. -/
theorem Sealed.run_invariant {s s' : Sealed} {cmds : List UCmd}
    (h : s.run cmds = .ok s') : s'.w.FullInv := s'.h

/-- The status of a claim at the executable boundary. -/
inductive TrustLevel where
  /-- Proved about the pure model. -/
  | proved
  /-- A runtime contract: relied on at the executable edge, not proved here. -/
  | runtimeContract (name : String)
  /-- Outside the fragment entirely. -/
  | excluded
  deriving DecidableEq

/-- The claims at the executable boundary and their status. The physical claims
are runtime contracts, not theorems of this model. -/
def boundaryClaims : List (String × TrustLevel) :=
  [ ("the checker's accepted command list is executed exactly", .proved),
    ("an accepted run preserves the world invariant", .proved),
    ("the sealed interface observes only a snapshot", .proved),
    ("the C runtime performs the same store trace", .runtimeContract "A-perf"),
    ("counted references correspond to physical reference counts", .runtimeContract "A-count"),
    ("a copy of a program has physically independent storage", .runtimeContract "A-copy"),
    ("concurrent execution of copied programs", .excluded) ]

/-- No physical claim is asserted as proved: the boundary says which claims are
runtime contracts and which are out of scope. -/
theorem boundary_no_physical_proof :
    ∀ c ∈ boundaryClaims, c.2 = .proved → c.1 ∈
      ["the checker's accepted command list is executed exactly",
       "an accepted run preserves the world invariant",
       "the sealed interface observes only a snapshot"] := by
  decide

/-! ### A delegation program through the sealed boundary -/

/-- A sealed delegation run: allocate a 4-byte owner, borrow its root for a
fresh borrower, write through the borrower, return it, and write through the
lender's restored capability. -/
def sealedDelegationCmds : List UCmd :=
  [ .alloc 4 ⟨1⟩ ⟨2⟩,
    .beginBorrow ⟨0⟩ ⟨1⟩ ⟨3⟩ ⟨10⟩,
    .write ⟨0⟩ ⟨3⟩ 0 7,
    .endBorrow ⟨0⟩ ⟨10⟩,
    .write ⟨0⟩ ⟨1⟩ 1 9 ]

/-- The sealed boundary accepts the delegation program. -/
theorem sealedDelegation_ok :
    (Sealed.empty.run sealedDelegationCmds).isOk = true := by
  decide

/-- The only observation of the delegation run is a copy of the allocation's
bytes: the byte the borrower wrote and the byte the restored lender wrote. -/
theorem sealedDelegation_snapshot :
    (Sealed.empty.run sealedDelegationCmds).toOption.map
      (fun s => s.snapshot ⟨0⟩) = some (some ([7, 9, 0, 0] : List UInt8)) := by
  decide

/-- A completed delegation run's sealed state carries the combined invariant and
observes exactly those bytes. -/
theorem sealedDelegation_run {s' : Sealed}
    (h : Sealed.empty.run sealedDelegationCmds = .ok s') :
    s'.w.FullInv ∧ s'.snapshot ⟨0⟩ = some ([7, 9, 0, 0] : List UInt8) := by
  refine ⟨Sealed.run_invariant h, ?_⟩
  have h' := sealedDelegation_snapshot
  rw [h] at h'
  change some (s'.snapshot ⟨0⟩) = some (some ([7, 9, 0, 0] : List UInt8)) at h'
  simpa using h'

end Cap
