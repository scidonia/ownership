/-
Identity types for the ownership subsystem.

Allocation, capability, loan and lifetime names are distinct types so that a
capability cannot stand where an allocation is expected and a reused number does
not silently denote a different kind of thing. The values are abstract: the
reference model uses `Nat` for readability, and generation handling belongs to
the arena that issues them, not to this module.
-/

namespace Cap

structure AllocId where
  val : Nat
deriving DecidableEq, Repr

structure CapId where
  val : Nat
deriving DecidableEq, Repr

structure LoanId where
  val : Nat
deriving DecidableEq, Repr

structure LifetimeId where
  val : Nat
deriving DecidableEq, Repr

theorem AllocId.ext {a b : AllocId} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp_all

end Cap
