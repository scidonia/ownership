import Cap.ReconstructionSealed

open Cap
open Cap.Reconstruction

/-!
Executable controls for the sealed borrowed-reconstruction path.

The fixture is the 64-byte worked example driven through the sealed boundary:
borrow the whole fragment `⟨1⟩` over `[0,64)` as `⟨3⟩`, split it spatially into
`⟨4⟩ : [0,32)` and `⟨5⟩ : [32,64)`, write both halves, reconstruct `[0,64)`, and
return `⟨3⟩` to `⟨1⟩`. A second full cycle then borrows `⟨1⟩` as `⟨6⟩`, splits it,
writes both halves, and returns it, so the first cycle's output is accepted by a
further verified operation.

Every refusal is paired with an affirmative control using the same operation on
the same fixture, so a failure is never a wholesale rejection of the fixture.
-/

/-! ### Observations -/

/-- The observed fragment has the given interval and share, on the fixture's
allocation, with a read--write ceiling and an active state. -/
private def fragmentIs (o : Option Fragment) (lo hi q : Nat) : Bool :=
  match o with
  | some f =>
      f.alloc == (⟨0⟩ : AllocId) && f.lo == lo && f.hi == hi && f.q == q &&
        f.ceiling == Ceiling.readWrite && f.state == CapState.active
  | none => false

/-! ### The 64-byte lifecycle -/

private def opened : Sealed := Sealed.initial64

private def borrowed : Sealed :=
  match opened.borrow ⟨1⟩ ⟨3⟩ with
  | .ok s => s
  | .error _ => opened

private def split : Sealed :=
  match borrowed.splitSpatial ⟨3⟩ ⟨4⟩ ⟨5⟩ 0 32 32 64 with
  | .ok s => s
  | .error _ => borrowed

private def processed : Sealed :=
  match split.write ⟨4⟩ 0 7 with
  | .ok s =>
      match s.write ⟨5⟩ 40 9 with
      | .ok s' => s'
      | .error _ => s
  | .error _ => split

private def reconstructed : Sealed :=
  match processed.reconstruct ⟨3⟩ with
  | .ok s => s
  | .error _ => processed

private def returned : Sealed :=
  match reconstructed.return ⟨3⟩ with
  | .ok s => s
  | .error _ => reconstructed

/-! ### Positive controls: the worked lifecycle -/

#guard (opened.borrow ⟨1⟩ ⟨3⟩).isOk
#guard (borrowed.splitSpatial ⟨3⟩ ⟨4⟩ ⟨5⟩ 0 32 32 64).isOk
#guard (split.write ⟨4⟩ 0 7).isOk
#guard (split.write ⟨5⟩ 40 9).isOk
#guard (processed.reconstruct ⟨3⟩).isOk
#guard (reconstructed.return ⟨3⟩).isOk

/-! ### The exact post-state -/

#guard (fragmentIs (returned.authority? ⟨1⟩) 0 64 64)
#guard (returned.authority? ⟨3⟩).isNone
#guard (returned.authority? ⟨4⟩).isNone
#guard (returned.authority? ⟨5⟩).isNone
#guard (returned.snapshot ⟨0⟩ == some firstSnapshot)
#guard (returned.read? ⟨0⟩ 0 == some 7)
#guard (returned.read? ⟨0⟩ 40 == some 9)
#guard returned.restores.isEmpty
#guard decide (⟨3⟩ ∈ returned.retired)
#guard decide (⟨4⟩ ∈ returned.retired)
#guard decide (⟨5⟩ ∈ returned.retired)

/-! ### A fractional subdivision through the same boundary -/

private def fracSplit : Sealed :=
  match borrowed.splitFraction ⟨3⟩ ⟨4⟩ ⟨5⟩ 40 24 with
  | .ok s => s
  | .error _ => borrowed

private def fracReconstructed : Sealed :=
  match fracSplit.reconstruct ⟨3⟩ with
  | .ok s => s
  | .error _ => fracSplit

private def fracReturned : Sealed :=
  match fracReconstructed.return ⟨3⟩ with
  | .ok s => s
  | .error _ => fracReconstructed

#guard (fragmentIs (fracSplit.authority? ⟨4⟩) 0 64 40)
#guard (fragmentIs (fracSplit.authority? ⟨5⟩) 0 64 24)
#guard (fracSplit.reconstruct ⟨3⟩).isOk
#guard (fracReconstructed.return ⟨3⟩).isOk
#guard (fragmentIs (fracReturned.authority? ⟨1⟩) 0 64 64)
#guard (fracReturned.authority? ⟨4⟩).isNone
#guard (fracReturned.authority? ⟨5⟩).isNone

/-! ### Negative controls: authority and ordering -/

/- The dormant lender cannot write while the borrow is outstanding. The
affirmative control is the accepted write through `⟨3⟩`. -/
#guard (borrowed.write ⟨1⟩ 0 7).isOk = false
#guard (borrowed.write ⟨3⟩ 0 7).isOk

/- The suspended parent name is not a current leaf after the split. -/
#guard (split.write ⟨3⟩ 0 7).isOk = false
#guard (split.splitSpatial ⟨3⟩ ⟨6⟩ ⟨7⟩ 0 32 32 64).isOk = false

/- A child name is retired after reconstruction and cannot write. The
affirmative control is the accepted write through the child before
reconstruction. -/
#guard (reconstructed.write ⟨4⟩ 0 7).isOk = false
#guard (reconstructed.write ⟨5⟩ 40 9).isOk = false
#guard (split.write ⟨4⟩ 0 7).isOk

/- A return before reconstruction is refused. The affirmative control is the
accepted return after reconstruction. -/
#guard (split.return ⟨3⟩).isOk = false
#guard (processed.return ⟨3⟩).isOk = false
#guard (reconstructed.return ⟨3⟩).isOk

/- A return through the wrong name is refused; the lender is not a borrower. -/
#guard (reconstructed.return ⟨1⟩).isOk = false
#guard (opened.return ⟨1⟩).isOk = false

/- A reconstruction without a suspension is refused. The affirmative control is
the accepted reconstruction of `⟨3⟩`. -/
#guard (opened.reconstruct ⟨1⟩).isOk = false
#guard (borrowed.reconstruct ⟨1⟩).isOk = false
#guard (processed.reconstruct ⟨3⟩).isOk

/- A write through a name that was never issued is refused. -/
#guard (opened.write ⟨3⟩ 0 7).isOk = false
#guard (opened.write ⟨1⟩ 0 7).isOk

/-! ### Negative controls: the checked partition and shares -/

/- Overlapping child intervals are refused. -/
#guard (borrowed.splitSpatial ⟨3⟩ ⟨4⟩ ⟨5⟩ 0 32 30 64).isOk = false
/- An incomplete partition is refused. -/
#guard (borrowed.splitSpatial ⟨3⟩ ⟨4⟩ ⟨5⟩ 0 32 40 64).isOk = false
/- A child interval outside the parent is refused. -/
#guard (borrowed.splitSpatial ⟨3⟩ ⟨4⟩ ⟨5⟩ 0 32 32 65).isOk = false
/- The affirmative control is the exact partition. -/
#guard (borrowed.splitSpatial ⟨3⟩ ⟨4⟩ ⟨5⟩ 0 32 32 64).isOk

/- Shares that do not sum to the parent share are refused. -/
#guard (borrowed.splitFraction ⟨3⟩ ⟨4⟩ ⟨5⟩ 32 30).isOk = false
/- A zero share is refused. -/
#guard (borrowed.splitFraction ⟨3⟩ ⟨4⟩ ⟨5⟩ 0 64).isOk = false
/- A share sum above the parent share is refused. -/
#guard (borrowed.splitFraction ⟨3⟩ ⟨4⟩ ⟨5⟩ 40 40).isOk = false
/- The affirmative control is the exact share sum. -/
#guard (borrowed.splitFraction ⟨3⟩ ⟨4⟩ ⟨5⟩ 40 24).isOk

/-! ### Negative controls: stale names are never reissued -/

/- A retired child name cannot be issued again after reconstruction. The
affirmative control is a split with fresh names on the restored whole
fragment. -/
#guard (reconstructed.splitSpatial ⟨3⟩ ⟨4⟩ ⟨6⟩ 0 32 32 64).isOk = false
#guard (reconstructed.splitSpatial ⟨4⟩ ⟨6⟩ ⟨7⟩ 0 16 16 32).isOk = false
#guard (returned.splitSpatial ⟨1⟩ ⟨6⟩ ⟨7⟩ 0 32 32 64).isOk

/- A returned borrower name cannot be borrowed again. The affirmative control
is a borrow with a fresh name, which is the second cycle. -/
#guard (returned.borrow ⟨1⟩ ⟨3⟩).isOk = false
#guard (returned.borrow ⟨1⟩ ⟨6⟩).isOk

/-! ### Negative controls: a descendant obligation blocks reconstruction -/

/- Borrow from the left child while the parent is suspended. -/
private def childBorrowed : Sealed :=
  match split.borrow ⟨4⟩ ⟨6⟩ with
  | .ok s => s
  | .error _ => split

#guard (split.borrow ⟨4⟩ ⟨6⟩).isOk
#guard (childBorrowed.reconstruct ⟨3⟩).isOk = false
#guard (childBorrowed.return ⟨3⟩).isOk = false
#guard (childBorrowed.return ⟨6⟩).isOk
#guard (match childBorrowed.return ⟨6⟩ with
  | .ok s => (s.reconstruct ⟨3⟩).isOk
  | .error _ => false)

/-! ### Reuse: the second full cycle -/

#guard lifecycleThenReuse.isOk
#guard (match lifecycleThenReuse.toOption with
  | some s =>
      s.snapshot ⟨0⟩ == some secondSnapshot &&
        fragmentIs (s.authority? ⟨1⟩) 0 64 64 &&
        (s.authority? ⟨6⟩).isNone && (s.authority? ⟨7⟩).isNone &&
        (s.authority? ⟨8⟩).isNone &&
        decide (s.retired = [⟨6⟩, ⟨7⟩, ⟨8⟩, ⟨3⟩, ⟨4⟩, ⟨5⟩]) && s.restores.isEmpty
  | none => false)
