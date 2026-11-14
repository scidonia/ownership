import Cap.Admission

open Cap

/-- A unary wrapper: admitted exactly when its parameter is. -/
structure Wrap (α : Type) where
  val : α

instance [i : SafeValue α] : SafeValue (Wrap α) where
  Rep := i.Rep
  rep := i.rep
  toRep w := i.toRep w.val
  ofRep r := ⟨i.ofRep r⟩
  left := by intro w; cases w; rw [i.left _]
  right := by intro r; exact i.right r

/-- A binary product: both parameters are required. -/
structure Both (α β : Type) where
  fst : α
  snd : β

instance [i : SafeValue α] [j : SafeValue β] : SafeValue (Both α β) where
  Rep := i.Rep × j.Rep
  rep := SafeRep.prod i.rep j.rep
  toRep p := (i.toRep p.fst, j.toRep p.snd)
  ofRep r := ⟨i.ofRep r.1, j.ofRep r.2⟩
  left := by intro p; cases p; simp [i.left, j.left]
  right := by intro r; cases r; simp [i.right, j.right]

-- The parameter's admission is what carries the wrapper's.
example : SafeValue (Wrap Nat) := inferInstance
example : SafeValue (Wrap (Wrap Bool)) := inferInstance
example : SafeValue (Both Nat (Wrap UInt8)) := inferInstance

/-- Admitting the parameter admits the wrapper; refusal propagates. -/
def wrapTy : SafeType := ⟨Wrap Nat, inferInstance, fun _ => ⟨0⟩⟩

example : wrapTy.init #[] = ⟨0⟩ := rfl
