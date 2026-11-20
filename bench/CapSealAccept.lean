import Cap.Sealed
open Cap

-- A sealed world is obtainable only from an accepted run, and its only
-- observation is a snapshot of one allocation.
example : Sealed :=
  Sealed.ofRun uWorld [] uWorld (by rfl)

example :
    (Sealed.ofRun uWorld [] uWorld (by rfl)).snapshot ⟨0⟩ =
      some (List.replicate 64 0) := by
  rfl
