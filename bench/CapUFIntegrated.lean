import Cap.UFIntegrated

/-!
Executable controls for the two-call full-path union-find through the integrated
sealed boundary.

The proof module `Cap.UFIntegrated` holds a parent array in one allocation's
bytes, reads each parent with `Sealed.read?` and writes each compressed parent
with `Sealed.write`. These guards compile the same definitions and check the
arrays, the writes and the capability checks the example names:

* setup writes `[0,0,1,2,2]` through the whole-share capability and the sealed
  state reads it back;
* the first find from node `3` returns root `0` and leaves `[0,0,0,0,2]`;
* the second find, run on the first call's successor state from node `4`,
  returns root `0` and leaves `[0,0,0,0,0]`;
* a fresh find from node `4` on the starting state leaves `[0,0,0,2,0]`, so the
  two-step result is not a rebuild from the origin;
* a second allocation keeps its bytes through both calls;
* writes need a current whole-share capability and an in-range offset, and a
  write at one offset leaves the other bytes alone.
-/

open Cap

#guard (Cap.UFIntegrated.ufStart.snapshot ⟨0⟩ == some [0, 0, 1, 2, 2])
#guard (Cap.UFIntegrated.setup.isOk)

#guard (Cap.UFIntegrated.ufFirst.toOption.map (fun p => p.1) == some 0)
#guard (Cap.UFIntegrated.ufFirst.toOption.map (fun p => p.2.snapshot ⟨0⟩) ==
  some (some [0, 0, 0, 0, 2]))

#guard (Cap.UFIntegrated.ufSecond.toOption.map (fun p => p.1) == some 0)
#guard (Cap.UFIntegrated.ufSecond.toOption.map (fun p => p.2.snapshot ⟨0⟩) ==
  some (some [0, 0, 0, 0, 0]))

#guard (Cap.UFIntegrated.ufFreshFour.toOption.map (fun p => p.2.snapshot ⟨0⟩) ==
  some (some [0, 0, 0, 2, 0]))

#guard (Cap.UFIntegrated.ufSecondOther.toOption.map (fun p =>
  (p.2.snapshot ⟨0⟩, p.2.snapshot ⟨1⟩, p.2.allocations)) ==
  some (some [0, 0, 0, 0, 0], some [5, 0, 0], [⟨1⟩, ⟨0⟩]))

/-! ### Capability-checked writes -/

/- The whole-share capability writes. -/
#guard (Cap.UFIntegrated.ufStart.write ⟨0⟩ ⟨1⟩ 4 0).isOk
/- A name that is not a current fragment (the disposal name) cannot write. -/
#guard (Cap.UFIntegrated.ufStart.write ⟨0⟩ ⟨2⟩ 0 1).isOk = false
/- An offset outside the five bytes is refused. -/
#guard (Cap.UFIntegrated.ufStart.write ⟨0⟩ ⟨1⟩ 5 1).isOk = false
/- A capability name is scoped to its allocation. -/
#guard (Cap.UFIntegrated.ufStart.write ⟨1⟩ ⟨1⟩ 0 1).isOk = false
/- A read outside the five bytes is absent. -/
#guard (Cap.UFIntegrated.ufStart.read? ⟨0⟩ 5).isNone

/- A write at one offset is visible at that offset and leaves the others alone. -/
#guard (match Cap.UFIntegrated.ufStart.write ⟨0⟩ ⟨1⟩ 4 0 with
  | .ok s => s.read? ⟨0⟩ 4 == some 0 && s.read? ⟨0⟩ 3 == some 2 &&
      s.read? ⟨0⟩ 0 == some 0 &&
      s.snapshot ⟨0⟩ == some [0, 0, 1, 2, 0]
  | .error _ => false)
