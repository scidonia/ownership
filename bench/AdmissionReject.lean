import Cap.Admission

open Cap

structure Bad where
  r : IO.Ref Nat

/-- The forgery: axioms supply the bijection the type's fields do not have. -/
axiom badTo : Bad → Nat
axiom badFrom : Nat → Bad
axiom badLeft : ∀ b, badFrom (badTo b) = b
axiom badRight : ∀ n, badTo (badFrom n) = n

noncomputable def badBij : Bij Bad (El .nat) where
  toFun := badTo
  invFun := badFrom
  left_inv := badLeft
  right_inv := badRight

#admit_type Bad badBij
