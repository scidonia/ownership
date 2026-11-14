import Cap.Admission

open Cap

/-- Coded types are admitted by the identity bijection: no search takes place. -/
def idBij (α : Type) : Bij α α where
  toFun a := a
  invFun a := a
  left_inv := by intro a; rfl
  right_inv := by intro a; rfl

def listCert : SafeValue (El (.list (.prod .nat .bool))) :=
  ⟨.list (.prod .nat .bool), idBij _⟩

def listTy : SafeType := ⟨El (.list .nat), ⟨.list .nat, idBij _⟩, fun _ => []⟩

example : listTy.init #[] = ([] : List Nat) := rfl
