/-
Codes for the value universe.

A code denotes a first-order value type by construction, so `El c` is its own
representation and storage holds `El c`, never an arbitrary type. The universe is
closed on purpose: there is no code for a reference, a function or a closure.

That closure does not make every type isomorphic to a coded type harmless.
`Unit → Nat` is bijective with `El .nat`, and a particular function of that type
can capture an array. A bijection is an encoding property; it is not a statement
about what a value retains. This is why storage is restricted to `El c`.
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
