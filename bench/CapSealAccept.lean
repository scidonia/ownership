import Cap.Sealed
open Cap

-- The canonical sealed state is the empty world; running an empty command list
-- is accepted, and its only observation is a snapshot.
example : Sealed := Sealed.empty

example : (Sealed.empty.run []).isOk = true := by rfl

example : Sealed.empty.snapshot ⟨0⟩ = none := by rfl
