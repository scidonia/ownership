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

#admit_type Pair Pair.bij

def Pair.new (_ : Array UInt8) : Pair := ⟨0, 0⟩

def pairTy : SafeType := ⟨Pair, ⟨(.prod .nat .nat), Pair.bij⟩, Pair.new⟩

example : pairTy.init #[1, 2] = ⟨0, 0⟩ := rfl
