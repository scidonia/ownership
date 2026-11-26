import Cap.Sealed
open Cap

-- The canonical sealed state is one whole fresh allocation, and its observations
-- come from the integrated multi-allocation state.
example : Sealed := Sealed.initial64

example : (Sealed.initial64.run []).isOk = true := by rfl

example : Sealed.initial64.snapshot ⟨0⟩ = some (List.replicate 64 0) := by decide

-- `Sealed.run` executes the integrated command language, not `World`/`UCmd`.
example : (Sealed.initial64.run [Integrated.Cmd.write ⟨0⟩ ⟨1⟩ 0 7]).isOk = true := by
  decide

example :
    (Sealed.initial64.run [Integrated.Cmd.write ⟨0⟩ ⟨1⟩ 0 7]).toOption.map
        (fun s => s.snapshot ⟨0⟩) =
      some (some (7 :: List.replicate 63 0)) := by
  decide
