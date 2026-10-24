/-
Toy declarations whose emitted LCNF is the probe's input.

They are ordinary Lean definitions, compiled by the pinned toolchain exactly as
the library's executor will be. `OwnershipProbe` reads their mono LCNF from the
olean and replays the impure passes, so this module carries no check of its own.
-/
namespace Ownership.Toy

/-- An owned array passed once to a fixed-size element write. -/
def probeSet (a : Array Nat) (i : Nat) (v : Nat) : Array Nat :=
  a.set! i v

/-- The same write with a second live use of `a`: the countermodel. -/
def probeAlias (a : Array Nat) (i : Nat) (v : Nat) : Array Nat × Nat :=
  let b := a.set! i v
  (b, a.size)

/-- A whole-value rebuild, to expose the expanded reset/reuse shape. -/
structure Box where
  hits : Nat
  log : Array Nat

def probeStruct (s : Box) (i v : Nat) : Box :=
  { s with log := s.log.set! i v }

end Ownership.Toy
