import Cap.Admission

open Cap

/-- The identity bijection, used to admit a type that *is* a code's denotation. -/
def idBij (α : Type) : Bij α α where
  toFun a := a
  invFun a := a
  left_inv := by intro a; rfl
  right_inv := by intro a; rfl

structure Wrap (α : Type) where
  val : α

/-- A wrapper's bijection is the parameter's, lifted. -/
def Wrap.bij {α : Type} {c : Code} (b : Bij α (El c)) : Bij (Wrap α) (El c) where
  toFun w := b.toFun w.val
  invFun x := ⟨b.invFun x⟩
  left_inv := by intro w; cases w; rw [Bij.left_inv b]
  right_inv := by intro x; rw [Bij.right_inv b]

structure Both (α β : Type) where
  fst : α
  snd : β

def Both.bij {α β : Type} {c d : Code} (b1 : Bij α (El c)) (b2 : Bij β (El d)) :
    Bij (Both α β) (El (.prod c d)) where
  toFun p := (b1.toFun p.fst, b2.toFun p.snd)
  invFun r := ⟨b1.invFun r.1, b2.invFun r.2⟩
  left_inv := by
    intro p
    cases p
    rw [Bij.left_inv b1, Bij.left_inv b2]
  right_inv := by
    intro r
    cases r
    rw [Bij.right_inv b1, Bij.right_inv b2]

/-- Coded types are admitted by identity; no search and no axiom. -/
def listCert : SafeValue (El (.list .nat)) := ⟨.list .nat, idBij _⟩

def wrapNatCert : SafeValue (Wrap Nat) := ⟨.nat, Wrap.bij (idBij Nat)⟩

def bothCert : SafeValue (Both Nat Bool) :=
  ⟨.prod .nat .bool, Both.bij (idBij Nat) (idBij Bool)⟩
