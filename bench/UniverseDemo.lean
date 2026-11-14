import Cap.Universe

open Cap

/-- A coded type is admitted by construction: the representation is itself. -/
example : SafeValue (El (.list (.prod .nat .bool))) := inferInstance
example : SafeValue (El (.sum .uint8 (.list .nat))) := inferInstance

/-- And it initialises against a fresh allocation's bytes. -/
def listTy : SafeType := ⟨El (.list .nat), inferInstance, fun _ => []⟩

example : listTy.init #[] = ([] : List Nat) := rfl
