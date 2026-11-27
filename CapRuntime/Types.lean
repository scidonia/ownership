/-
Runtime data for the erased execution path.

Nothing in this file imports `Cap`: no forest, restoration obligation,
capability ledger, invariant or proof state is part of a runtime value.
-/

namespace CapRuntime

/-- Runtime allocation identity. This is an index, not a ghost allocation. -/
abbrev AllocId := Nat

/-- A runtime handle. Validity is checked against the live allocation table. -/
structure Handle where
  alloc : Nat
  generation : Nat
  offset : Nat
  deriving Repr, DecidableEq, BEq

/-- One live or retired allocation. Bytes are raw `ByteArray` storage. -/
structure Allocation where
  bytes : ByteArray
  live : Bool
  generation : Nat

/-- Runtime state: only allocation storage and generation bookkeeping. -/
structure State where
  allocations : Array Allocation := #[]
  nextGeneration : Nat := 0

/-- The empty runtime. -/
def State.empty : State := {}

end CapRuntime
