/-
Codes for the value universe.

A code denotes a first-order value type by construction, so `El c` is its own
representation and a type is admitted to the subsystem by demonstrating a
bijection to `El c`. The universe is closed on purpose: there is no code for a
reference, a function or a closure.
-/

namespace Cap

inductive Code where
  | nat
  | bool
  | uint8
  | unit
  | prod (a b : Code)
  | sum (a b : Code)
  | list (a : Code)
deriving DecidableEq, Repr

/-- The denotation of a code. -/
def El : Code → Type
  | .nat => Nat
  | .bool => Bool
  | .uint8 => UInt8
  | .unit => Unit
  | .prod a b => El a × El b
  | .sum a b => Sum (El a) (El b)
  | .list a => List (El a)

end Cap
