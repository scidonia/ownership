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

/-! ### The completion contract of the general find -/

/- The bounded chase never reports an exhausted search as a root: zero fuel is
none, not the pair `(3, [])` the old bounded helper returned. -/
#guard (Cap.UFGeneric.chase? Cap.UFIntegrated.ufStart ⟨0⟩ 0 3).isNone
/- One step short of the rank bound: the chase from node 3 needs four steps
(3 → 2 → 1 → 0). -/
#guard (Cap.UFGeneric.chase? Cap.UFIntegrated.ufStart ⟨0⟩ 3 3).isNone
/- At the rank bound the chase completes and returns a root and path. -/
#guard (Cap.UFGeneric.chase? Cap.UFIntegrated.ufStart ⟨0⟩ 4 3).isSome
/- An exhausted chase makes the find refuse; it carries no state. -/
#guard (Cap.UFGeneric.sealedFind Cap.UFIntegrated.ufStart ⟨0⟩ ⟨1⟩ 0 3).isOk = false
#guard (Cap.UFGeneric.sealedFind Cap.UFIntegrated.ufStart ⟨0⟩ ⟨1⟩ 3 3).isOk = false
#guard (Cap.UFGeneric.sealedFind Cap.UFIntegrated.ufStart ⟨0⟩ ⟨1⟩ 0 3).toOption.isNone

/-! ### Whole-fragment write authority -/

/- The whole-share capability is a writable whole fragment of the five bytes. -/
#guard (Cap.UFGeneric.writableB Cap.UFIntegrated.ufStart ⟨0⟩ ⟨1⟩ 5)
/- The disposal name is not a write authority. -/
#guard (Cap.UFGeneric.writableB Cap.UFIntegrated.ufStart ⟨0⟩ ⟨2⟩ 5 = false)
/- A fragment claiming the wrong length is not this allocation's whole share. -/
#guard (Cap.UFGeneric.writableB Cap.UFIntegrated.ufStart ⟨0⟩ ⟨1⟩ 6 = false)

/-! ### The single-write frame on the two-allocation state -/

/- The control write is accepted. -/
#guard Cap.UFIntegrated.selfWrite.isOk

/- The write changes allocation `⟨0⟩`'s own bytes and leaves allocation `⟨1⟩`'s
bytes exactly as they were. -/
#guard (match Cap.UFIntegrated.selfWrite with
  | .ok s => s.snapshot ⟨0⟩ == some [0, 0, 1, 2, 0] &&
      s.snapshot ⟨0⟩ != Cap.UFIntegrated.ufStartWithOther.snapshot ⟨0⟩ &&
      s.snapshot ⟨1⟩ == Cap.UFIntegrated.ufStartWithOther.snapshot ⟨1⟩
  | .error _ => false)

/- The unrelated allocation's component is still keyed to the same identifier. -/
#guard (match Cap.UFIntegrated.selfWrite with
  | .ok s => decide ((s.state.find? ⟨1⟩).map Reconstruction.State.alloc =
      (Cap.UFIntegrated.ufStartWithOther.state.find? ⟨1⟩).map
        Reconstruction.State.alloc)
  | .error _ => false)
