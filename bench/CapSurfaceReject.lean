/-
A negative control for the surface front end: the checker refuses the program at
elaboration time, so this file is expected to fail. It is not part of any library
target, so the refusal never affects the library build. -/
import Cap.Surface

open Cap

def rejectOwner : Owner :=
  Owner.init ⟨0⟩ 64 64 (by decide) ⟨0⟩ ⟨1⟩

-- Fails: index 100 lies outside the root leaf's footprint.
#own_prog rejectOwner 64 {
  write ⟨0⟩ 100
}

-- Fails: the spatial split point 100 lies outside the root leaf's footprint.
#own_prog rejectOwner 64 {
  splitAt ⟨0⟩ ⟨2⟩ ⟨3⟩ 100
}

-- Fails: the shares 3 and 5 do not add up to the root leaf's share 64.
#own_prog rejectOwner 64 {
  splitFraction ⟨0⟩ ⟨2⟩ ⟨3⟩ 3 5
}
