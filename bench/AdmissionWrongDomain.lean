import Cap.Admission

open Cap

structure Pair where
  x : Nat
  y : Nat

structure Other where
  n : Nat

def Other.bij : Bij Other (El .nat) where
  toFun o := o.n
  invFun n := ⟨n⟩
  left_inv := by intro o; cases o; rfl
  right_inv := by intro n; rfl

-- A real bijection, but not of the type being admitted.
#admit_type Pair Other.bij
