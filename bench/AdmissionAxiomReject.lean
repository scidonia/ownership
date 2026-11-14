import Cap.Admission

open Cap

structure Bad where
  r : IO.Ref Nat

/-- The forgery: axioms supply the bijection the fields do not. -/
axiom badTo : Bad → Nat
axiom badFrom : Nat → Bad
axiom badLeft : ∀ b, badFrom (badTo b) = b
axiom badRight : ∀ n, badTo (badFrom n) = n

instance : SafeValue Bad where
  Rep := Nat
  rep := SafeRep.nat
  toRep := badTo
  ofRep := badFrom
  left := badLeft
  right := badRight

#admit_type Bad
