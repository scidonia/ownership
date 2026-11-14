import Cap.Admission

open Cap

/-- A plain structure: admitted through a proved equivalence to `Nat × Nat`. -/
structure Pair where
  x : Nat
  y : Nat

def Pair.new (_ : Array UInt8) : Pair := ⟨0, 0⟩

instance : SafeValue Pair where
  Rep := Nat × Nat
  rep := SafeRep.prod SafeRep.nat SafeRep.nat
  toRep p := (p.x, p.y)
  ofRep r := ⟨r.1, r.2⟩
  left := by intro p; cases p; rfl
  right := by intro r; cases r; rfl

#admit_type Pair

def pairTy : SafeType := ⟨Pair, inferInstance, Pair.new⟩

/-- The allocator applies `new` against the bytes of a fresh allocation. -/
example : pairTy.init #[1, 2] = ⟨0, 0⟩ := rfl
