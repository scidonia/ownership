import Cap.Admission

open Cap

/-- A resource-bearing type: there is no `SafeRep` path to `IO.Ref`, so no
`SafeValue` instance exists and the gate must refuse it. -/
structure Bad where
  r : IO.Ref Nat

#admit_type Bad
