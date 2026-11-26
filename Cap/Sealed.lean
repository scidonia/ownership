/-
The sealed execution boundary.

`Cap.Integrated.Sealed` is the one sealed path: a multi-allocation
reconstruction state whose constructor and carried invariant are private, so a
client can hold and observe a state but obtain one only from `initial`, an
accepted command, or `run`. This module re-exports that boundary under the
historical `Cap.Sealed` name; the `World`/`UCmd` wrapper that used to live here
is gone. The world command path and its `World.FullInv` remain as their own
theorems, but they are not a sealed entry point.

The operations are `alloc`, `write`, `borrow`, `splitSpatial`, `splitFraction`,
`reconstruct`, `return`, `free`, and the whole-run `run`; every accepted call
returns a sealed state with the integrated invariant rebuilt from its
preservation theorem, and a refused call returns an error and no state. The
observations are a per-allocation heap snapshot, a byte read, a fragment
description, the retired access names, the outstanding return obligations, the
live allocation list, and a read-only integrated state projection for composed
proofs; the constructor, invariant field and mutations remain sealed.

What is proved is the bookkeeping boundary: every sealed state carries the
integrated invariant, a run reaches the outside only through accepted
commands, and an accepted run frames every allocation it does not target. The
state is pure data, so a copied sealed value shares its representation; the
execution-edge claims are listed with their status in `boundaryClaims` rather
than asserted.
-/
import Cap.Integrated

namespace Cap

/-- The sealed state is the integrated multi-allocation state. -/
abbrev Sealed := Integrated.Sealed

namespace Sealed

/-- The canonical sealed state: one whole fresh allocation. -/
abbrev initial (a : AllocId) (n D : Nat) (pos : 0 < D)
    (rootId disposalId : CapId) : Sealed :=
  Integrated.Sealed.initial a n D pos rootId disposalId

/-- The 64-byte fixture: allocation `⟨0⟩`, root `⟨1⟩`, disposal `⟨2⟩`. -/
abbrev initial64 : Sealed := Integrated.Sealed.initial64

/-- Run an integrated command list inside the sealed boundary. -/
abbrev run (s : Sealed) (cmds : List Integrated.Cmd) : Except String Sealed :=
  Integrated.Sealed.run s cmds

/-- Every sealed state carries the integrated invariant. -/
abbrev invariant := Integrated.Sealed.invariant

/-- What an accepted sealed run leaves alone for an allocation no command
targets: the same component, bytes and `Storage` certificate. -/
abbrev RunFrame (s s' : Sealed) (b : AllocId) : Prop :=
  Integrated.Sealed.RunFrame s s' b

/-- An accepted sealed run frames every allocation no command targets. -/
abbrev run_frames_other {s s' : Sealed} {cmds : List Integrated.Cmd}
    (h : s.run cmds = .ok s') {b : AllocId}
    (hmiss : ∀ c ∈ cmds, c.allocId ≠ b) : RunFrame s s' b :=
  Integrated.Sealed.run_frames_other h hmiss

/-- The live allocation identifiers. -/
abbrev allocations (s : Sealed) : List AllocId := Integrated.Sealed.allocations s

/-- Add a fresh allocation. -/
abbrev alloc (s : Sealed) (a : AllocId) (n D : Nat) (pos : 0 < D)
    (rootId disposalId : CapId) : Except String Sealed :=
  Integrated.Sealed.alloc s a n D pos rootId disposalId

/-- Write one byte through a current fragment. -/
abbrev write (s : Sealed) (a : AllocId) (id : CapId) (i : Nat) (v : UInt8) :
    Except String Sealed :=
  Integrated.Sealed.write s a id i v

/-- Borrow a current active fragment. -/
abbrev borrow (s : Sealed) (a : AllocId) (lender borrower : CapId) :
    Except String Sealed :=
  Integrated.Sealed.borrow s a lender borrower

/-- Spatially subdivide a current fragment. -/
abbrev splitSpatial (s : Sealed) (a : AllocId) (parentId c1 c2 : CapId)
    (lo1 hi1 lo2 hi2 : Nat) : Except String Sealed :=
  Integrated.Sealed.splitSpatial s a parentId c1 c2 lo1 hi1 lo2 hi2

/-- Fractionally subdivide a current fragment. -/
abbrev splitFraction (s : Sealed) (a : AllocId) (parentId c1 c2 : CapId)
    (q1 q2 : Nat) : Except String Sealed :=
  Integrated.Sealed.splitFraction s a parentId c1 c2 q1 q2

/-- Reconstruct a suspended fragment. -/
abbrev reconstruct (s : Sealed) (a : AllocId) (parentId : CapId) :
    Except String Sealed :=
  Integrated.Sealed.reconstruct s a parentId

/-- Return a borrowed fragment. -/
abbrev «return» (s : Sealed) (a : AllocId) (borrower : CapId) :
    Except String Sealed :=
  Integrated.Sealed.return s a borrower

/-- Free a whole active allocation with no outstanding obligation. -/
abbrev free (s : Sealed) (a : AllocId) : Except String Sealed :=
  Integrated.Sealed.free s a

/-- A copy of one allocation's bytes. -/
abbrev snapshot (s : Sealed) (a : AllocId) : Option (List UInt8) :=
  Integrated.Sealed.snapshot s a

/-- Read one byte of one allocation. -/
abbrev read? (s : Sealed) (a : AllocId) (i : Nat) : Option UInt8 :=
  Integrated.Sealed.read? s a i

/-- The current fragment of one allocation with the given access name. -/
abbrev authority? (s : Sealed) (a : AllocId) (id : CapId) :
    Option Reconstruction.Fragment :=
  Integrated.Sealed.authority? s a id

/-- The access names retired by one allocation, most recent first. -/
abbrev retiredOf (s : Sealed) (a : AllocId) : List CapId :=
  Integrated.Sealed.retiredOf s a

/-- The outstanding return obligations of one allocation, most recent first. -/
abbrev restoresOf (s : Sealed) (a : AllocId) : List Reconstruction.Restore :=
  Integrated.Sealed.restoresOf s a

end Sealed

/-! ### Executable-edge claims -/

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
  [ ("the integrated checker's accepted command list is executed exactly", .proved),
    ("an accepted run preserves the integrated invariant", .proved),
    ("an accepted run frames every allocation no command targets", .proved),
    ("the sealed interface observes only snapshots, reads, fragments, retired names, obligations and a read-only integrated state; its constructor, invariant field and mutations remain sealed", .proved),
    ("the C runtime performs the same store trace", .runtimeContract "A-perf"),
    ("counted references correspond to physical reference counts", .runtimeContract "A-count"),
    ("a copy of a program has physically independent storage", .runtimeContract "A-copy"),
    ("concurrent execution of copied programs", .excluded) ]

set_option maxRecDepth 20000 in
/-- No physical claim is asserted as proved: the boundary says which claims are
runtime contracts and which are out of scope. -/
theorem boundary_no_physical_proof :
    ∀ c ∈ boundaryClaims, c.2 = .proved → c.1 ∈
      ["the integrated checker's accepted command list is executed exactly",
       "an accepted run preserves the integrated invariant",
       "an accepted run frames every allocation no command targets",
       "the sealed interface observes only snapshots, reads, fragments, retired names, obligations and a read-only integrated state; its constructor, invariant field and mutations remain sealed"] := by
  decide

end Cap
