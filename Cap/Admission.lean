/-
Admitting a value type by demonstrating a bijection into the coded universe.

There is deliberately no `SafeValue` class and no deriving route. A certificate is
a value: a code `c` and a `Bij T (El c)` with both inverse laws. A user who wants
a type admitted must write that bijection; the kernel checks it, and
`#admit_type` reflects the named demonstration, confirms its type is
`Bij T (El c)` for some closed code, and audits its axioms. Nothing can be
auto-generated into admission, and nothing is accepted because an instance
happened to exist.

The universe is closed against references, functions and closures, so a type that
hides a live resource has no code to be bijective with. A type outside the
universe is not storable; that is a usability limit, not an unsoundness.
-/

import Lean
import Cap.Code

open Lean Meta Elab Command

namespace Cap

/-- Allowed value representations. -/
inductive SafeRep : Type → Prop where
  | nat : SafeRep Nat
  | bool : SafeRep Bool
  | uint8 : SafeRep UInt8
  | unit : SafeRep Unit
  | prod {A B : Type} : SafeRep A → SafeRep B → SafeRep (A × B)
  | sum {A B : Type} : SafeRep A → SafeRep B → SafeRep (Sum A B)
  | list {A : Type} : SafeRep A → SafeRep (List A)

/-- Every coded type is in the allowlist by construction. -/
def repCode : (c : Code) → SafeRep (El c)
  | .nat => SafeRep.nat
  | .bool => SafeRep.bool
  | .uint8 => SafeRep.uint8
  | .unit => SafeRep.unit
  | .prod a b => SafeRep.prod (repCode a) (repCode b)
  | .sum a b => SafeRep.sum (repCode a) (repCode b)
  | .list a => SafeRep.list (repCode a)

/-- A bijection, with both inverse laws. -/
structure Bij (α β : Type) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b

/-- Logical encodability: a code and a bijection to its denotation.

This is not a confinement property. `Unit → Nat` is bijective with `El .nat` and a
particular such function can capture storage; extensional equality of functions
says nothing about their compiled environments. What the certificate establishes
is that the type's values can be encoded as the coded first-order data, not that a
value of the type carries nothing else. Storage therefore never holds an
arbitrary `T`: it holds `El code`. -/
structure SafeValue (T : Type) where
  code : Code
  bij : Bij T (El code)

/-- Storage eligibility: a code and an initialiser producing that code's
denotation. No arbitrary type appears here, so an initialiser cannot return a
closure over the protected storage. -/
structure SafeType where
  code : Code
  new : Array UInt8 → El code

/-- The allocator calls this with the bytes for the fresh allocation. -/
def SafeType.init (st : SafeType) (bytes : Array UInt8) : El st.code :=
  st.new bytes

/-- Encoding gate: reflect the named demonstration and check that it is a
bijection of the named type to some closed code. It does not admit the type to
storage; storage is `El code` only. -/
syntax "#admit_encoding " ident ident : command

elab_rules : command
  | `(#admit_encoding $t:ident $b:ident) => do
    liftTermElabM do
      let env ← getEnv
      let d ← match env.find? b.getId with
        | some (.defnInfo d) => pure d
        | some _ => throwError "'{b}' is not a definition"
        | none => throwError "unknown declaration '{b}'"
      let c ← mkFreshExprMVar (mkConst ``Code)
      let expected := mkApp2 (mkConst ``Bij) (mkConst t.getId) (mkApp (mkConst ``El) c)
      unless ← isDefEq d.type expected do
        throwError "the demonstration '{b}' does not have type Bij {t} (El c)"
      let c ← instantiateMVars c
      if c.hasMVar || c.hasFVar then
        throwError "the code in '{b}' is not closed"
      let axs ← collectAxioms b.getId
      let standard : List Name := [``propext, ``Classical.choice, ``Quot.sound]
      let bad := axs.filter (fun a => !standard.contains a)
      unless bad.isEmpty do
        throwError "the demonstration '{b}' depends on non-standard axioms {bad.toList}"
      logInfo m!"'{t}' is encoded by code {c}"

end Cap
