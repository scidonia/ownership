import Cap.Reconstruction

open Cap
open Cap.Reconstruction

/-!
Executable controls for borrowed subdivision and reconstruction.

The fixture is the 64-byte worked example of the design note. The whole
capability `⟨1⟩` over `[0,64)` has share `64`; it is borrowed to `⟨3⟩`, the
borrowed resource is split spatially into `⟨4⟩ : [0,32)` and
`⟨5⟩ : [32,64)`, both halves are written, the borrowed resource is
reconstructed, and the lender `⟨1⟩` is restored by the return.

Every refusal is paired with an affirmative control using the same detector on
the same fixture, so a failure is never a wholesale rejection of the fixture.
-/

/-! ### The 64-byte fixture -/

/- Whole authority over `[0,64)` with share `64`. -/
private def own : State :=
  State.initial ⟨0⟩ 64 64 (by decide) ⟨1⟩ ⟨2⟩

/- The root borrowed to `⟨3⟩`. -/
private def borrowed : State :=
  match own.borrow ⟨1⟩ ⟨3⟩ with
  | some s => s
  | none => own

/- The borrowed resource split into `[0,32)` and `[32,64)`. -/
private def split : State :=
  match borrowed.splitSpatial ⟨3⟩ ⟨4⟩ ⟨5⟩ 0 32 32 64 with
  | some s => s
  | none => borrowed

/- Both halves are written, at offsets `0` and `40`. -/
private def processed : State :=
  match split.write ⟨4⟩ 0 7 with
  | some s =>
      match s.write ⟨5⟩ 40 9 with
      | some s' => s'
      | none => s
  | none => split

/- The borrowed resource reconstructed over `[0,64)`. -/
private def reconstructed : State :=
  match processed.reconstruct ⟨3⟩ with
  | some s => s
  | none => processed

/- The lender `⟨1⟩` restored, with the processed bytes. -/
private def returned : State :=
  match reconstructed.return ⟨3⟩ with
  | some s => s
  | none => reconstructed

/- A fractional split of the borrowed resource into shares `40` and `24`. -/
private def fractional : State :=
  match borrowed.splitFraction ⟨3⟩ ⟨4⟩ ⟨5⟩ 40 24 with
  | some s => s
  | none => borrowed

/- The fractional split reconstructed and returned. -/
private def fractionalReturned : State :=
  match fractional.reconstruct ⟨3⟩ with
  | some s =>
      match s.return ⟨3⟩ with
      | some s' => s'
      | none => s
  | none => fractional

/-! ### Positive controls: the worked lifecycle -/

#guard (own.borrow ⟨1⟩ ⟨3⟩).isSome
#guard (borrowed.splitSpatial ⟨3⟩ ⟨4⟩ ⟨5⟩ 0 32 32 64).isSome
#guard (split.write ⟨4⟩ 0 7).isSome
#guard (split.write ⟨5⟩ 40 9).isSome
#guard (processed.reconstruct ⟨3⟩).isSome
#guard (reconstructed.return ⟨3⟩).isSome
#guard (borrowed.splitFraction ⟨3⟩ ⟨4⟩ ⟨5⟩ 40 24).isSome
#guard (match fractional.forest.findLeaf? ⟨4⟩, fractional.forest.findLeaf? ⟨5⟩ with
  | some l, some r => l.q == 40 && r.q == 24 && l.lo == 0 && l.hi == 64 &&
      r.lo == 0 && r.hi == 64
  | _, _ => false)
#guard (fractional.reconstruct ⟨3⟩).isSome
#guard (match fractionalReturned.forest.findLeaf? ⟨1⟩ with
  | some c => c.q == 64 && c.lo == 0 && c.hi == 64 && c.state == CapState.active
  | none => false)
#guard (fractionalReturned.forest.findLeaf? ⟨4⟩).isNone
#guard (fractionalReturned.forest.findLeaf? ⟨5⟩).isNone

/-! ### The exact post-state of the 64-byte example -/

/- The restored lender is the whole `[0,64)` fragment with share `64`. -/
#guard (match returned.forest.findLeaf? ⟨1⟩ with
  | some c =>
      c.alloc == (⟨0⟩ : AllocId) && c.lo == 0 && c.hi == 64 && c.q == 64 &&
      c.ceiling == Ceiling.readWrite && c.state == CapState.active
  | none => false)

/- The parent name and both child names are gone from the current frontier. -/
#guard (returned.forest.findLeaf? ⟨3⟩).isNone
#guard (returned.forest.findLeaf? ⟨4⟩).isNone
#guard (returned.forest.findLeaf? ⟨5⟩).isNone

/- The processed bytes survive the reconstruction and the return. -/
#guard (returned.heap.read? ⟨0⟩ 0 == some (7 : UInt8))
#guard (returned.heap.read? ⟨0⟩ 40 == some (9 : UInt8))

/- The return obligation is discharged, and the borrowed and child names are
retired. -/
#guard returned.restores.isEmpty
#guard (⟨3⟩ ∈ returned.retired)
#guard (⟨4⟩ ∈ returned.retired)
#guard (⟨5⟩ ∈ returned.retired)

/-! ### Negative controls: authority and ordering -/

/- The dormant lender cannot write while the borrow is outstanding. The
affirmative control is the accepted write through `⟨3⟩` below. -/
#guard (borrowed.write ⟨1⟩ 0 7).isSome = false
#guard (borrowed.write ⟨3⟩ 0 7).isSome

/- The suspended parent name is not a current leaf after the split. -/
#guard (split.write ⟨3⟩ 0 7).isSome = false

/- A child name is retired after reconstruction and cannot write. -/
#guard (reconstructed.write ⟨4⟩ 0 7).isSome = false
#guard (reconstructed.write ⟨5⟩ 40 9).isSome = false

/- A return before reconstruction is refused; the affirmative control is the
accepted return above. -/
#guard (split.return ⟨3⟩).isSome = false
#guard (processed.return ⟨3⟩).isSome = false
#guard (reconstructed.return ⟨3⟩).isSome

/- A reconstruction without a suspension is refused. -/
#guard (own.reconstruct ⟨1⟩).isSome = false
#guard (borrowed.reconstruct ⟨1⟩).isSome = false

/- A return without a borrow is refused. -/
#guard (own.return ⟨1⟩).isSome = false

/- A stale child name cannot be issued again after reconstruction. The
affirmative control is the accepted split above. -/
#guard (reconstructed.splitSpatial ⟨3⟩ ⟨4⟩ ⟨6⟩ 0 32 32 64).isSome = false
#guard (reconstructed.splitSpatial ⟨4⟩ ⟨6⟩ ⟨7⟩ 0 16 16 32).isSome = false

/- A stale name that was issued but never retired is also refused. -/
#guard (borrowed.splitSpatial ⟨3⟩ ⟨1⟩ ⟨6⟩ 0 32 32 64).isSome = false

/-! ### Negative controls: the checked partition and shares -/

/- Overlapping child intervals are refused. -/
#guard (borrowed.splitSpatial ⟨3⟩ ⟨4⟩ ⟨5⟩ 0 32 30 64).isSome = false
/- An incomplete partition is refused. -/
#guard (borrowed.splitSpatial ⟨3⟩ ⟨4⟩ ⟨5⟩ 0 32 40 64).isSome = false
/- A child interval outside the parent is refused. -/
#guard (borrowed.splitSpatial ⟨3⟩ ⟨4⟩ ⟨5⟩ 0 32 32 65).isSome = false

/- Shares that do not sum to the parent share are refused. -/
#guard (borrowed.splitFraction ⟨3⟩ ⟨4⟩ ⟨5⟩ 32 30).isSome = false
/- A zero share is refused. -/
#guard (borrowed.splitFraction ⟨3⟩ ⟨4⟩ ⟨5⟩ 0 64).isSome = false
/- A share sum above the parent share is refused. -/
#guard (borrowed.splitFraction ⟨3⟩ ⟨4⟩ ⟨5⟩ 40 40).isSome = false

/- Overlapping and incomplete rules are refused at reconstruction even when the
current children are leaves of those names. -/
private def ruleParent : Leaf :=
  { id := ⟨3⟩, alloc := ⟨0⟩, lo := 0, hi := 64, ordered := by decide,
    q := 64, pos := by decide, ceiling := .readWrite, state := .active }

private def overlapLeft : Leaf :=
  { ruleParent with id := ⟨4⟩, hi := 32, ordered := by decide }

private def overlapRight : Leaf :=
  { ruleParent with id := ⟨5⟩, lo := 30, ordered := by decide }

private def gapLeft : Leaf :=
  { ruleParent with id := ⟨4⟩, hi := 32, ordered := by decide }

private def gapRight : Leaf :=
  { ruleParent with id := ⟨5⟩, lo := 40, ordered := by decide }

/- A leaf pair whose intervals overlap; the rule is invalid. -/
private def overlapForest : Forest :=
  .split .spatial ruleParent overlapLeft overlapRight
    (.leaf overlapLeft) (.leaf overlapRight)

/- A leaf pair whose intervals leave a gap; the rule is invalid. -/
private def gapForest : Forest :=
  .split .spatial ruleParent gapLeft gapRight
    (.leaf gapLeft) (.leaf gapRight)

/- The valid rule pair over the same fixture — the affirmative control for the
two refusals below. -/
private def goodLeft : Leaf :=
  { ruleParent with id := ⟨4⟩, hi := 32, ordered := by decide }

private def goodRight : Leaf :=
  { ruleParent with id := ⟨5⟩, lo := 32, ordered := by decide }

private def goodForest : Forest :=
  .split .spatial ruleParent goodLeft goodRight
    (.leaf goodLeft) (.leaf goodRight)

#guard (overlapForest.reconstructAt ⟨3⟩).isNone
#guard (gapForest.reconstructAt ⟨3⟩).isNone
#guard (goodForest.reconstructAt ⟨3⟩).isSome

/- The valid reconstruction retires the two child fragments. -/
#guard (match goodForest.reconstructAt ⟨3⟩ with
  | some (f, lf, rf) =>
      lf.id == (⟨4⟩ : CapId) && rf.id == (⟨5⟩ : CapId) &&
      (f.findLeaf? ⟨3⟩).isSome && (f.findLeaf? ⟨4⟩).isNone
  | none => false)

/-! ### Negative controls: a descendant loan blocks reconstruction and return -/

/- Borrow from the left child while the parent is suspended. -/
private def childBorrowed : State :=
  match split.borrow ⟨4⟩ ⟨6⟩ with
  | some s => s
  | none => split

#guard (split.borrow ⟨4⟩ ⟨6⟩).isSome
#guard ((childBorrowed.reconstruct ⟨3⟩).isSome = false)
#guard ((childBorrowed.return ⟨3⟩).isSome = false)
#guard (childBorrowed.return ⟨6⟩).isSome
#guard (match childBorrowed.return ⟨6⟩ with
  | some s => (s.reconstruct ⟨3⟩).isSome
  | none => false)

/-! ### G5: an independent right sibling splits while the left is borrowed -/

/- The whole allocation split into left `[0,32)` and right `[32,64)`. -/
private def g5 : State :=
  match own.splitSpatial ⟨1⟩ ⟨3⟩ ⟨4⟩ 0 32 32 64 with
  | some s => s
  | none => own

/- The left sibling borrowed to `⟨5⟩`. -/
private def g5LeftBorrowed : State :=
  match g5.borrow ⟨3⟩ ⟨5⟩ with
  | some s => s
  | none => g5

/- The independent right sibling split while the left is borrowed. -/
private def g5RightSplit : State :=
  match g5LeftBorrowed.splitSpatial ⟨4⟩ ⟨6⟩ ⟨7⟩ 32 48 48 64 with
  | some s => s
  | none => g5LeftBorrowed

/- The right sibling splits while the left loan is outstanding: the
allocation-wide guard would refuse here, but the reconstruction model permits
the independent authority. -/
#guard (g5LeftBorrowed.splitSpatial ⟨4⟩ ⟨6⟩ ⟨7⟩ 32 48 48 64).isSome

/- The borrowed left sibling is untouched by the right split. -/
#guard (match g5RightSplit.forest.findLeaf? ⟨5⟩ with
  | some c => c.alloc == (⟨0⟩ : AllocId) && c.lo == 0 && c.hi == 32 && c.q == 64
  | none => false)

/- The right split is accepted while the left sibling is borrowed. -/
theorem g5_right_split_accepted :
    (g5LeftBorrowed.splitSpatial ⟨4⟩ ⟨6⟩ ⟨7⟩ 32 48 48 64).isSome = true := by
  decide

/- The outstanding left return obligation is untouched by the right split. -/
theorem g5_right_split_frame :
    g5RightSplit.restores = g5LeftBorrowed.restores := rfl

/- The left loan still returns after the right sibling has been split: the
right split framed it. -/
#guard (g5RightSplit.return ⟨5⟩).isSome
#guard (match g5RightSplit.return ⟨5⟩ with
  | some s => (s.forest.findLeaf? ⟨3⟩).isSome && (s.forest.findLeaf? ⟨5⟩).isNone
  | none => false)
