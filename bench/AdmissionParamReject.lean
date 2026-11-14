import Cap.Admission

open Cap

structure Wrap (α : Type) where
  val : α

instance [i : SafeValue α] : SafeValue (Wrap α) where
  Rep := i.Rep
  rep := i.rep
  toRep w := i.toRep w.val
  ofRep r := ⟨i.ofRep r⟩
  left := by intro w; cases w; rw [i.left _]
  right := by intro r; exact i.right r

/-- No `SafeValue` for `Bad`, so the wrapper's premise cannot be met. -/
structure Bad where
  r : IO.Ref Nat

example : SafeValue (Wrap Bad) := inferInstance
