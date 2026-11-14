/-
Admitting a new value type.

A type enters the subsystem only with a `SafeValue` instance: a proof that it is
equivalent to an allowed representation, built from `Nat`, `Bool`, `UInt8` and
products. The equivalence's two inverse laws are what make the type's shape a
kernel-checked fact; nothing here reads the elaborator's environment.

Reflection can automate the instance for a plain structure, but it cannot
authorise one: a generated instance is accepted only because the kernel checks
its proof. A type with a field outside the representation has no instance, so
`#admit_type` refuses it without any structural guesswork.

`new` is the initialiser the allocator applies against a fresh allocation id: the
identifier is supplied by the arena, the bytes by the allocation, and the
constructor produces the stored value.
-/

import Lean
import Cap.Id

open Lean Meta Elab Command

namespace Cap

/-- Allowed value representations. A resource-bearing or function field has no
constructor here, so it cannot appear in an admitted type. -/
inductive SafeRep : Type → Prop where
  | nat : SafeRep Nat
  | bool : SafeRep Bool
  | uint8 : SafeRep UInt8
  | prod {A B : Type} : SafeRep A → SafeRep B → SafeRep (A × B)

/-- A type with a proved bijection to an allowed representation. -/
class SafeValue (T : Type) where
  Rep : Type
  rep : SafeRep Rep
  toRep : T → Rep
  ofRep : Rep → T
  left : ∀ t, ofRep (toRep t) = t
  right : ∀ r, toRep (ofRep r) = r

/-- A type admitted to the subsystem, with the initialiser used by allocation. -/
structure SafeType where
  T : Type
  inst : SafeValue T
  new : Array UInt8 → T

/-- The allocator calls this with the bytes for the fresh allocation. -/
def SafeType.init (st : SafeType) (bytes : Array UInt8) : st.T := st.new bytes

/-- Admission gate: the kernel must already hold a `SafeValue` instance. -/
syntax "#admit_type " ident : command

elab_rules : command
  | `(#admit_type $t:ident) => do
    liftTermElabM do
      let ty := mkApp (mkConst ``SafeValue) (mkConst t.getId)
      let _ ← synthInstance ty
    logInfo m!"admitted '{t}': a SafeValue instance was found"

end Cap
