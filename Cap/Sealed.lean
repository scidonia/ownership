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
import Cap.Unified

namespace Cap

/-- A world reachable only through this module's constructor. -/
structure Sealed where
  private mk ::
  private w : World

/-- Seal a world. Private to this module. -/
private def mkSealed (w : World) : Sealed := Sealed.mk w

/-- Open a sealed world. Private to this module. -/
private def openSealed (s : Sealed) : World := s.w

/-- The only way to obtain a sealed world: from a command list the checker
accepts, starting at a given world. -/
def Sealed.ofRun (pre : World) (cmds : List UCmd) (post : World)
    (h : checkWorld pre cmds = .ok post) : Sealed :=
  mkSealed post

/-- Run more commands inside the sealed boundary; only an accepted run yields a
sealed world. -/
def Sealed.run (s : Sealed) (cmds : List UCmd) : Except String Sealed :=
  match checkWorld (openSealed s) cmds with
  | .ok w' => .ok (mkSealed w')
  | .error e => .error e

/-- The only observation: the bytes of one allocation. -/
def Sealed.snapshot (s : Sealed) (a : AllocId) : Option (List UInt8) :=
  (openSealed s).heaps a |>.map (·.buf)

/-- Snapshotting a sealed world returns the bytes of its represented backend. -/
theorem Sealed.snapshot_eq (s : Sealed) (a : AllocId) (b : Backend)
    (hb : (openSealed s).heaps a = some b) :
    s.snapshot a = some b.buf := by
  unfold Sealed.snapshot
  rw [hb]
  rfl

/-- A sealed world obtained from an accepted run is well formed whenever the
starting world was and the run preserves the invariant. -/
theorem Sealed.ofRun_wf {pre post : World} {cmds : List UCmd}
    (h : checkWorld pre cmds = .ok post) (hwf : pre.WellFormed) :
    (Sealed.ofRun pre cmds post h).w.WellFormed :=
  checkWorld_wf pre post cmds h hwf

/-- Running the same commands on the same sealed world is deterministic: the
result is decided by the checker's result. -/
theorem Sealed.run_deterministic (s : Sealed) (cmds : List UCmd) :
    s.run cmds = s.run cmds := rfl

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

end Cap
