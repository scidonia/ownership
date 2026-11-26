import Cap.Integrated

open Cap
open Cap.Integrated

/-!
Executable controls for the integrated multi-allocation reconstruction path.

The fixture is the same 64-byte allocation as the retired single-allocation
sealed controls, now one component of a multi-allocation state. The controls
exercise:

* two allocations borrowed independently, written and returned in either order;
* a split of an independent sibling region while a loan on the same allocation
  is outstanding, and the ordering rules for reconstruct and return;
* the free guard: only a single whole active allocation with no outstanding
  obligation can be freed, and freeing one allocation leaves the others intact;
* the 64-byte lifecycle and its reuse through the integrated sealed boundary.

Every refusal is paired with an affirmative control on the same fixture, so a
failure is never a wholesale rejection.
-/

/-- The whole `[0,64)` fragment of allocation `⟨0⟩`. -/
private def whole0 : Reconstruction.Fragment :=
  { alloc := ⟨0⟩, lo := 0, hi := 64, q := 64, ceiling := .readWrite, state := .active }

/-- The whole `[0,32)` fragment of allocation `⟨1⟩`. -/
private def whole1 : Reconstruction.Fragment :=
  { alloc := ⟨1⟩, lo := 0, hi := 32, q := 32, ceiling := .readWrite, state := .active }

/-! ### Two allocations borrowed independently -/

private def twoAlloc : Sealed :=
  match Sealed.initial64.alloc ⟨1⟩ 32 32 (by decide) ⟨10⟩ ⟨11⟩ with
  | .ok s => s
  | .error _ => Sealed.initial64

#guard (Sealed.initial64.alloc ⟨1⟩ 32 32 (by decide) ⟨10⟩ ⟨11⟩).isOk
#guard decide (twoAlloc.allocations = [⟨1⟩, ⟨0⟩])

private def twoBorrowed : Sealed :=
  match twoAlloc.borrow ⟨0⟩ ⟨1⟩ ⟨3⟩ with
  | .ok s =>
      match s.borrow ⟨1⟩ ⟨10⟩ ⟨12⟩ with
      | .ok s' => s'
      | .error _ => s
  | .error _ => twoAlloc

#guard (twoAlloc.borrow ⟨0⟩ ⟨1⟩ ⟨3⟩).isOk
#guard (match twoAlloc.borrow ⟨0⟩ ⟨1⟩ ⟨3⟩ with
  | .ok s => (s.borrow ⟨1⟩ ⟨10⟩ ⟨12⟩).isOk
  | .error _ => false)

/- Each borrower writes through its own allocation; neither lender can write. -/
#guard (twoBorrowed.write ⟨0⟩ ⟨3⟩ 0 7).isOk
#guard (twoBorrowed.write ⟨1⟩ ⟨12⟩ 0 9).isOk
#guard (twoBorrowed.write ⟨0⟩ ⟨1⟩ 0 7).isOk = false
#guard (twoBorrowed.write ⟨1⟩ ⟨10⟩ 0 9).isOk = false
/- A capability name is scoped to its allocation. -/
#guard (twoBorrowed.write ⟨0⟩ ⟨12⟩ 0 7).isOk = false
#guard (twoBorrowed.write ⟨1⟩ ⟨3⟩ 0 9).isOk = false

private def twoWritten : Sealed :=
  match twoBorrowed.write ⟨0⟩ ⟨3⟩ 0 7 with
  | .ok s =>
      match s.write ⟨1⟩ ⟨12⟩ 0 9 with
      | .ok s' => s'
      | .error _ => s
  | .error _ => twoBorrowed

#guard twoWritten.read? ⟨0⟩ 0 == some 7
#guard twoWritten.read? ⟨1⟩ 0 == some 9
#guard twoWritten.read? ⟨0⟩ 40 == some 0
#guard twoWritten.read? ⟨1⟩ 31 == some 0

/- Returning the two independent obligations is accepted in either order. -/
#guard (twoWritten.return ⟨0⟩ ⟨3⟩).isOk
#guard (match twoWritten.return ⟨0⟩ ⟨3⟩ with
  | .ok s => (s.return ⟨1⟩ ⟨12⟩).isOk
  | .error _ => false)
#guard (match twoWritten.return ⟨1⟩ ⟨12⟩ with
  | .ok s => (s.return ⟨0⟩ ⟨3⟩).isOk
  | .error _ => false)
/- A return names the allocation of its obligation. -/
#guard (twoWritten.return ⟨0⟩ ⟨12⟩).isOk = false
#guard (twoWritten.return ⟨1⟩ ⟨3⟩).isOk = false
#guard (twoWritten.return ⟨2⟩ ⟨3⟩).isOk = false

private def twoReturned : Sealed :=
  match twoWritten.return ⟨0⟩ ⟨3⟩ with
  | .ok s =>
      match s.return ⟨1⟩ ⟨12⟩ with
      | .ok s' => s'
      | .error _ => s
  | .error _ => twoWritten

#guard decide (twoReturned.restoresOf ⟨0⟩ = ([] : List Reconstruction.Restore))
#guard decide (twoReturned.restoresOf ⟨1⟩ = ([] : List Reconstruction.Restore))
#guard decide (twoReturned.authority? ⟨0⟩ ⟨1⟩ = some whole0)
#guard decide (twoReturned.authority? ⟨1⟩ ⟨10⟩ = some whole1)
#guard twoReturned.read? ⟨0⟩ 0 == some 7
#guard twoReturned.read? ⟨1⟩ 0 == some 9

/- Freeing one whole allocation drops only that component. -/
#guard (twoReturned.free ⟨0⟩).isOk
#guard (twoReturned.free ⟨1⟩).isOk

private def twoFreed0 : Sealed :=
  match twoReturned.free ⟨0⟩ with
  | .ok s => s
  | .error _ => twoReturned

#guard (twoFreed0.snapshot ⟨0⟩).isNone
#guard decide (twoFreed0.allocations = [⟨1⟩])
#guard twoFreed0.read? ⟨1⟩ 0 == some 9
#guard (twoFreed0.free ⟨0⟩).isOk = false

/-! ### An independent sibling split while a loan is outstanding -/

private def outerSplit : Sealed :=
  match Sealed.initial64.splitSpatial ⟨0⟩ ⟨1⟩ ⟨3⟩ ⟨4⟩ 0 32 32 64 with
  | .ok s => s
  | .error _ => Sealed.initial64

private def leftBorrowed : Sealed :=
  match outerSplit.borrow ⟨0⟩ ⟨3⟩ ⟨5⟩ with
  | .ok s => s
  | .error _ => outerSplit

private def rightSplit : Sealed :=
  match leftBorrowed.splitSpatial ⟨0⟩ ⟨4⟩ ⟨6⟩ ⟨7⟩ 32 48 48 64 with
  | .ok s => s
  | .error _ => leftBorrowed

#guard (Sealed.initial64.splitSpatial ⟨0⟩ ⟨1⟩ ⟨3⟩ ⟨4⟩ 0 32 32 64).isOk
#guard (outerSplit.borrow ⟨0⟩ ⟨3⟩ ⟨5⟩).isOk
/- The sibling region `[32,64)` is subdivided although `[0,32)` is lent. -/
#guard (leftBorrowed.splitSpatial ⟨0⟩ ⟨4⟩ ⟨6⟩ ⟨7⟩ 32 48 48 64).isOk
#guard (rightSplit.write ⟨0⟩ ⟨6⟩ 32 1).isOk
#guard (rightSplit.write ⟨0⟩ ⟨7⟩ 48 2).isOk
/- The borrowed left fragment is still writable. -/
#guard (rightSplit.write ⟨0⟩ ⟨5⟩ 0 3).isOk

/- The sibling's reconstruction is accepted while the left loan stands. -/
#guard (rightSplit.reconstruct ⟨0⟩ ⟨4⟩).isOk
/- The outer suspension is not reconstructible until the sibling is a leaf. -/
#guard (rightSplit.reconstruct ⟨0⟩ ⟨1⟩).isOk = false

private def rightReconstructed : Sealed :=
  match rightSplit.reconstruct ⟨0⟩ ⟨4⟩ with
  | .ok s => s
  | .error _ => rightSplit

/- Returning the left loan is accepted while the outer suspension remains. -/
#guard (rightReconstructed.return ⟨0⟩ ⟨5⟩).isOk
#guard (rightReconstructed.reconstruct ⟨0⟩ ⟨1⟩).isOk = false

private def rightReconstructedReturned : Sealed :=
  match rightReconstructed.return ⟨0⟩ ⟨5⟩ with
  | .ok s => s
  | .error _ => rightReconstructed

#guard (rightReconstructedReturned.reconstruct ⟨0⟩ ⟨1⟩).isOk

private def siblingDone : Sealed :=
  match rightReconstructedReturned.reconstruct ⟨0⟩ ⟨1⟩ with
  | .ok s => s
  | .error _ => rightReconstructedReturned

#guard decide (siblingDone.authority? ⟨0⟩ ⟨1⟩ = some whole0)
#guard decide (siblingDone.restoresOf ⟨0⟩ = ([] : List Reconstruction.Restore))
#guard (siblingDone.free ⟨0⟩).isOk

/- The free guard refuses a suspended allocation and an outstanding loan. -/
#guard (leftBorrowed.free ⟨0⟩).isOk = false
#guard (rightSplit.free ⟨0⟩).isOk = false
#guard (outerSplit.free ⟨0⟩).isOk = false
#guard (rightReconstructedReturned.free ⟨0⟩).isOk = false

private def siblingFreed : Sealed :=
  match siblingDone.free ⟨0⟩ with
  | .ok s => s
  | .error _ => siblingDone

#guard (siblingFreed.snapshot ⟨0⟩).isNone

/-! ### Fractional subdivision of an independent sibling -/

private def fracSibling : Sealed :=
  match leftBorrowed.splitFraction ⟨0⟩ ⟨4⟩ ⟨8⟩ ⟨9⟩ 40 24 with
  | .ok s => s
  | .error _ => leftBorrowed

#guard (leftBorrowed.splitFraction ⟨0⟩ ⟨4⟩ ⟨8⟩ ⟨9⟩ 40 24).isOk
#guard (leftBorrowed.splitFraction ⟨0⟩ ⟨4⟩ ⟨8⟩ ⟨9⟩ 32 30).isOk = false
#guard (leftBorrowed.splitFraction ⟨0⟩ ⟨4⟩ ⟨8⟩ ⟨9⟩ 0 64).isOk = false
/- A fractional fragment does not carry the whole share, so it cannot write. -/
#guard (fracSibling.write ⟨0⟩ ⟨8⟩ 32 1).isOk = false
#guard (fracSibling.write ⟨0⟩ ⟨9⟩ 32 1).isOk = false
#guard (fracSibling.reconstruct ⟨0⟩ ⟨4⟩).isOk

/-! ### Return/refusal order on the 64-byte loan -/

private def lifecycleBorrowed : Sealed :=
  match Sealed.initial64.borrow ⟨0⟩ ⟨1⟩ ⟨3⟩ with
  | .ok s => s
  | .error _ => Sealed.initial64

private def lifecycleSplit : Sealed :=
  match lifecycleBorrowed.splitSpatial ⟨0⟩ ⟨3⟩ ⟨4⟩ ⟨5⟩ 0 32 32 64 with
  | .ok s => s
  | .error _ => lifecycleBorrowed

private def lifecycleProcessed : Sealed :=
  match lifecycleSplit.write ⟨0⟩ ⟨4⟩ 0 7 with
  | .ok s =>
      match s.write ⟨0⟩ ⟨5⟩ 40 9 with
      | .ok s' => s'
      | .error _ => s
  | .error _ => lifecycleSplit

private def lifecycleReconstructed : Sealed :=
  match lifecycleProcessed.reconstruct ⟨0⟩ ⟨3⟩ with
  | .ok s => s
  | .error _ => lifecycleProcessed

#guard (lifecycleBorrowed.return ⟨0⟩ ⟨3⟩).isOk
#guard (lifecycleSplit.return ⟨0⟩ ⟨3⟩).isOk = false
#guard (lifecycleProcessed.return ⟨0⟩ ⟨3⟩).isOk = false
#guard (lifecycleReconstructed.return ⟨0⟩ ⟨3⟩).isOk

/-! ### The exact 64-byte lifecycle and its reuse -/

#guard lifecycle64ThenReuse.isOk
#guard (match lifecycle64ThenReuse.toOption with
  | some s =>
      s.snapshot ⟨0⟩ == some Reconstruction.secondSnapshot &&
        decide (s.authority? ⟨0⟩ ⟨1⟩ = some whole0) &&
        decide (s.restoresOf ⟨0⟩ = ([] : List Reconstruction.Restore)) &&
        decide (s.retiredOf ⟨0⟩ = [⟨6⟩, ⟨7⟩, ⟨8⟩, ⟨3⟩, ⟨4⟩, ⟨5⟩])
  | none => false)

#guard lifecycle64ThenAlloc.isOk
#guard (match lifecycle64ThenAlloc.toOption with
  | some s =>
      s.snapshot ⟨0⟩ == some Reconstruction.firstSnapshot &&
        s.snapshot ⟨1⟩ == some secondAllocBytes &&
        s.read? ⟨1⟩ 0 == some 5 &&
        decide (s.authority? ⟨1⟩ ⟨10⟩ = some whole1)
  | none => false)

/-! ### Refusal controls retained from the retired single-allocation boundary -/

/- The dormant lender is not a current leaf while the borrow is outstanding; the
affirmative control is the write through the borrower. -/
#guard (lifecycleBorrowed.write ⟨0⟩ ⟨1⟩ 0 7).isOk = false
#guard (lifecycleBorrowed.write ⟨0⟩ ⟨3⟩ 0 7).isOk

/- After the split the suspended parent name is not a current leaf. -/
#guard (lifecycleSplit.write ⟨0⟩ ⟨3⟩ 0 7).isOk = false
#guard (lifecycleSplit.splitSpatial ⟨0⟩ ⟨3⟩ ⟨10⟩ ⟨11⟩ 0 32 32 64).isOk = false

/- Child names are retired after reconstruction and cannot write; the
affirmative control is the write through a child before reconstruction. -/
#guard (lifecycleReconstructed.write ⟨0⟩ ⟨4⟩ 0 7).isOk = false
#guard (lifecycleReconstructed.write ⟨0⟩ ⟨5⟩ 40 9).isOk = false
#guard (lifecycleSplit.write ⟨0⟩ ⟨4⟩ 0 7).isOk

/- A return before reconstruction is refused; the affirmative control is the
accepted return after reconstruction. -/
#guard (lifecycleSplit.return ⟨0⟩ ⟨3⟩).isOk = false
#guard (lifecycleProcessed.return ⟨0⟩ ⟨3⟩).isOk = false
#guard (lifecycleReconstructed.return ⟨0⟩ ⟨3⟩).isOk

/- A return through the lender name is refused; the lender is not a borrower. -/
#guard (lifecycleReconstructed.return ⟨0⟩ ⟨1⟩).isOk = false
#guard (Sealed.initial64.return ⟨0⟩ ⟨1⟩).isOk = false

/- A reconstruction without a suspension is refused; the affirmative control is
the reconstruction of the suspended `⟨3⟩`. -/
#guard (Sealed.initial64.reconstruct ⟨0⟩ ⟨1⟩).isOk = false
#guard (lifecycleBorrowed.reconstruct ⟨0⟩ ⟨1⟩).isOk = false
#guard (lifecycleProcessed.reconstruct ⟨0⟩ ⟨3⟩).isOk

/- A write through a name that was never issued is refused. -/
#guard (Sealed.initial64.write ⟨0⟩ ⟨12⟩ 0 7).isOk = false
#guard (Sealed.initial64.write ⟨0⟩ ⟨1⟩ 0 7).isOk

/- Overlapping, incomplete and out-of-parent child intervals are refused; the
affirmative control is the exact partition. -/
#guard (lifecycleBorrowed.splitSpatial ⟨0⟩ ⟨3⟩ ⟨4⟩ ⟨5⟩ 0 32 30 64).isOk = false
#guard (lifecycleBorrowed.splitSpatial ⟨0⟩ ⟨3⟩ ⟨4⟩ ⟨5⟩ 0 32 40 64).isOk = false
#guard (lifecycleBorrowed.splitSpatial ⟨0⟩ ⟨3⟩ ⟨4⟩ ⟨5⟩ 0 32 32 65).isOk = false
#guard (lifecycleBorrowed.splitSpatial ⟨0⟩ ⟨3⟩ ⟨4⟩ ⟨5⟩ 0 32 32 64).isOk

/- Shares that do not sum to the parent, or that are zero, are refused; the
affirmative control is the exact share sum. -/
#guard (lifecycleBorrowed.splitFraction ⟨0⟩ ⟨3⟩ ⟨4⟩ ⟨5⟩ 32 30).isOk = false
#guard (lifecycleBorrowed.splitFraction ⟨0⟩ ⟨3⟩ ⟨4⟩ ⟨5⟩ 0 64).isOk = false
#guard (lifecycleBorrowed.splitFraction ⟨0⟩ ⟨3⟩ ⟨4⟩ ⟨5⟩ 40 40).isOk = false
#guard (lifecycleBorrowed.splitFraction ⟨0⟩ ⟨3⟩ ⟨4⟩ ⟨5⟩ 40 24).isOk

/- A retired child name cannot be issued again; the affirmative control is a
split with fresh names on the reconstructed borrower. -/
#guard (lifecycleReconstructed.splitSpatial ⟨0⟩ ⟨4⟩ ⟨6⟩ ⟨7⟩ 0 16 16 32).isOk = false
#guard (lifecycleReconstructed.splitSpatial ⟨0⟩ ⟨3⟩ ⟨4⟩ ⟨6⟩ 0 32 32 64).isOk = false
#guard (lifecycleReconstructed.splitSpatial ⟨0⟩ ⟨3⟩ ⟨6⟩ ⟨7⟩ 0 32 32 64).isOk

private def lifecycleReturned : Sealed :=
  match lifecycleReconstructed.return ⟨0⟩ ⟨3⟩ with
  | .ok s => s
  | .error _ => lifecycleReconstructed

/- A returned borrower name cannot be borrowed again; the affirmative control is
a borrow with a fresh name. -/
#guard (lifecycleReturned.borrow ⟨0⟩ ⟨1⟩ ⟨3⟩).isOk = false
#guard (lifecycleReturned.borrow ⟨0⟩ ⟨1⟩ ⟨6⟩).isOk

/- A descendant obligation blocks reconstruction of the suspended parent and
return of the outer loan; discharging it unblocks the reconstruction. -/
private def childBorrowed : Sealed :=
  match lifecycleSplit.borrow ⟨0⟩ ⟨4⟩ ⟨6⟩ with
  | .ok s => s
  | .error _ => lifecycleSplit

#guard (lifecycleSplit.borrow ⟨0⟩ ⟨4⟩ ⟨6⟩).isOk
#guard (childBorrowed.reconstruct ⟨0⟩ ⟨3⟩).isOk = false
#guard (childBorrowed.return ⟨0⟩ ⟨3⟩).isOk = false
#guard (childBorrowed.return ⟨0⟩ ⟨6⟩).isOk
#guard (match childBorrowed.return ⟨0⟩ ⟨6⟩ with
  | .ok s => (s.reconstruct ⟨0⟩ ⟨3⟩).isOk
  | .error _ => false)

/- Fractional subdivision through the integrated boundary: the two children keep
the parent footprint and split its share, and reconstruction restores it. -/
private def lifecycleFrac : Sealed :=
  match lifecycleBorrowed.splitFraction ⟨0⟩ ⟨3⟩ ⟨4⟩ ⟨5⟩ 40 24 with
  | .ok s => s
  | .error _ => lifecycleBorrowed

#guard lifecycleFrac.authority? ⟨0⟩ ⟨4⟩ |>.isSome
#guard lifecycleFrac.authority? ⟨0⟩ ⟨5⟩ |>.isSome
#guard (lifecycleFrac.write ⟨0⟩ ⟨4⟩ 0 7).isOk = false
#guard (lifecycleFrac.reconstruct ⟨0⟩ ⟨3⟩).isOk
