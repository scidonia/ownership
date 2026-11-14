import Cap.Admission

open Cap

structure Pair where
  x : Nat
  y : Nat

/-- The user's demonstration: a bijection to a code, with both inverse laws. -/
def Pair.bij : Bij Pair (El (.prod .nat .nat)) where
  toFun p := (p.x, p.y)
  invFun r := ⟨r.1, r.2⟩
  left_inv := by intro p; cases p; rfl
  right_inv := by intro r; cases r; rfl

#admit_encoding Pair Pair.bij

def Pair.new (_ : Array UInt8) : Pair := ⟨0, 0⟩

/-- Storage holds the code's denotation, not `Pair` itself. -/
def pairTy : SafeType := ⟨.prod .nat .nat, fun _ => ((0 : Nat), (0 : Nat))⟩

example : pairTy.init #[1, 2] = ((0 : Nat), (0 : Nat)) := rfl
