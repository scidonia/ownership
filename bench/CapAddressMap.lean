import Cap.AddressMap

open Cap
open Cap.AddressMap

/-!
Executable controls for the finite address map.

The positive fixture is the two-allocation state: allocation `⟨0⟩` has the
`[4096, 4160)` window and allocation `⟨3⟩` has `[8192, 8224)`. The controls
exercise an in-window address, a write that leaves the other allocation's window
and bytes unchanged, and the three refusals: an overlapping window, a missing
live window and an out-of-window offset.
-/

#guard twoAllocMap.lookup? ⟨0⟩ == some window0
#guard twoAllocMap.lookup? ⟨3⟩ == some window3
#guard twoAllocMap.addr? ⟨0⟩ 5 == some 4101
#guard twoAllocMap.withinB ⟨0⟩ 5

#guard (twoAllocState.exec exampleWrite).isSome
#guard (match twoAllocState.exec exampleWrite with
  | some s' => s'.snapshot ⟨3⟩ == some (List.replicate 32 0)
  | none => false)

/- Overlapping, missing and out-of-window requests are refused. -/
#guard (twoAllocMap.alloc ⟨9⟩ { base := 4128, len := 16 }).isNone
#guard twoAllocMap.addr? ⟨9⟩ 0 == none
#guard twoAllocMap.withinB ⟨9⟩ 0 == false
#guard twoAllocMap.addr? ⟨0⟩ 64 == none
#guard twoAllocMap.withinB ⟨0⟩ 64 == false
#guard (twoAllocMap.alloc ⟨9⟩ { base := 2 ^ 64, len := 1 }).isNone

/- An accepted fresh allocation adds only its own window. -/
#guard match twoAllocMap.alloc ⟨9⟩ { base := 16384, len := 8 } with
  | some m =>
      m.lookup? ⟨9⟩ == some { base := 16384, len := 8 } &&
        m.lookup? ⟨0⟩ == some window0 && m.lookup? ⟨3⟩ == some window3
  | none => false

/-! ### A command list that targets one allocation -/

#guard (Integrated.State.run twoAllocState exampleRun).isSome
#guard (match Integrated.State.run twoAllocState exampleRun with
  | some s' =>
      s'.read? ⟨0⟩ 0 == some 11 && s'.read? ⟨0⟩ 63 == some 12 &&
        s'.snapshot ⟨3⟩ == some (List.replicate 32 0)
  | none => false)
