/-
A universe of value codes.

A code denotes a first-order value type by construction, so the representation of
`El c` is `El c` itself and the two inverse laws are `rfl`: no isomorphism has to
be found or proved. This is the definitional route to admission, and it is why a
coded type is automatic while an arbitrary structure is not.

The universe is closed on purpose. It has no code for a reference, a function or a
closure, so a resource-bearing type cannot be denoted here. That is the property
the coding buys; it does not buy admission for a type outside the universe, which
still needs either an alias to a code or a proved bijection.
-/
import Cap.Admission

namespace Cap

/-- Codes for the first-order value types. -/
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

/-- Every coded type is in the allowlist by construction. -/
def repCode : (c : Code) → SafeRep (El c)
  | .nat => SafeRep.nat
  | .bool => SafeRep.bool
  | .uint8 => SafeRep.uint8
  | .unit => SafeRep.unit
  | .prod a b => SafeRep.prod (repCode a) (repCode b)
  | .sum a b => SafeRep.sum (repCode a) (repCode b)
  | .list a => SafeRep.list (repCode a)

/-- Admission of a coded type needs no search: the representation is itself. -/
instance (c : Code) : SafeValue (El c) where
  Rep := El c
  rep := repCode c
  toRep := id
  ofRep := id
  left := by intro t; rfl
  right := by intro r; rfl

end Cap
