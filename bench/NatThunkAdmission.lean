import Cap.Admission

open Cap

/-- A function type is bijective with `Nat`: encoding is not confinement. -/
abbrev NatThunk := Unit → Nat

def thunkBij : Bij NatThunk (El .nat) where
  toFun f := f ()
  invFun n := fun _ => n
  left_inv f := by funext u; cases u; rfl
  right_inv n := rfl

#print axioms thunkBij
#admit_encoding NatThunk thunkBij

/-- A particular thunk can retain a buffer; the encoding says nothing about that. -/
def retainBuffer (bytes : Array UInt8) : NatThunk := fun _ => bytes.size

/-- Storage cannot hold it: `SafeType.new` must produce `El code`, and `NatThunk`
is not a coded denotation. The retention hazard is removed by the storage type,
not by refusing the encoding. -/
example (bytes : Array UInt8) : NatThunk := retainBuffer bytes
