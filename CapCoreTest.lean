import CapCore

open CapCore

/-- A context with denominator 2 over four bytes. -/
def c0 : Ctx := Ctx.new 2 4 0 (by decide)

-- Whole-share writes are admitted; half shares are not.
#guard c0.writeAllowed 0 1
#guard (Ctx.splitFraction? c0 0 1 2 1 1 (by decide) (by decide)).isSome

def cf : Ctx :=
  match Ctx.splitFraction? c0 0 1 2 1 1 (by decide) (by decide) with
  | some c => c
  | none => c0

#guard cf.readAllowed 1 && cf.readAllowed 2
#guard !cf.writeAllowed 1 1 && !cf.writeAllowed 2 1
#guard !cf.has 0

-- The old parent cannot be used after the split.
#guard !cf.writeAllowed 0 1

-- A spatial split of a whole-share capability is writable on both halves.
def cs : Ctx :=
  match Ctx.splitSpatial? c0 0 3 4 2 with
  | some c => c
  | none => c0

#guard cs.writeAllowed 3 0 && cs.writeAllowed 4 3
#guard !cs.writeAllowed 5 0

def cb : Ctx :=
  match Ctx.borrow? c0 0 10 with
  | some c => c
  | none => c0
#guard cb.readAllowed 10 && !cb.readAllowed 0

def cr : Ctx :=
  match Ctx.return? cb 10 0 with
  | some c => c
  | none => cb
#guard cr.readAllowed 0 && !cr.readAllowed 10


-- Rejections: stale parent, half-share write, duplicate ids, out of range,
-- reused borrower, freed capability, and a spatial split outside the region.
#guard !cf.writeAllowed 0 1
#guard !cf.writeAllowed 1 9
#guard (Ctx.splitFraction? c0 0 1 1 1 1 (by decide) (by decide)).isNone
#guard (Ctx.splitSpatial? c0 0 3 4 9).isNone
#guard (Ctx.borrow? c0 0 0).isNone
#guard (Ctx.borrow? c0 0 0).isNone
#guard (match Ctx.free? c0 0 with | some c => !c.readAllowed 0 | none => false)
#guard (Ctx.free? c0 7).isNone
