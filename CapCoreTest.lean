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


open CapCore

-- A whole-share program is accepted: read, write, borrow, restore, free.
def goodCmd : List Cmd :=
  [.read 0, .write 0 1, .borrow 0 10, .write 10 2, .restore 10 0, .free 0]

#guard (run c0 goodCmd).isSome

-- The same shape is refused after the parent share is split.
def staleAfterSplit : List Cmd :=
  [.splitFraction 0 1 2 1 1 (by decide) (by decide), .write 0 1]

#guard !(run c0 staleAfterSplit).isSome

-- A half share cannot perform a second write program step.
def halfWrite : List Cmd :=
  [.splitFraction 0 1 2 1 1 (by decide) (by decide), .write 1 1]

#guard !(run c0 halfWrite).isSome

-- A container/tuple of commands still threads one context; the withdrawn id is
-- dead for every later command in the list.
def aliasTuple : List Cmd × List Cmd :=
  ([.splitSpatial 0 3 4 2], [.write 0 1])

#guard
  match aliasTuple with
  | (first, second) => !(run c0 (first ++ second)).isSome

-- A reusable whole-share capability may be read twice.
#guard (run c0 [.read 0, .read 0]).isSome

-- Freed or borrowed-away names are refused by the next command.
#guard !(run c0 [.free 0, .read 0]).isSome
#guard !(run c0 [.borrow 0 10, .read 0]).isSome

-- A checked certificate for the accepted sequence.
def goodProg : Prog where
  pre := c0
  cmds := goodCmd
  accepted := by decide

#guard goodProg.execute.isSome

-- Checker acceptance yields the semantic access evidence.
example : CanRead c0 0 := canRead_of_readAllowed (by decide)
example : CanWrite c0 0 1 := canWrite_of_writeAllowed (by decide)


-- Fractional reconstruction restores whole-share write authority.
def splitForJoin : List Cmd :=
  [.splitFraction 0 1 2 1 1 (by decide) (by decide)]

def joined : Ctx :=
  match run c0 splitForJoin with
  | some c =>
      match c.reconstruct? 1 2 5 with
      | some c' => c'
      | none => c
  | none => c0

#guard joined.writeAllowed 5 1
#guard !joined.readAllowed 1 && !joined.readAllowed 2

-- A removed id becomes available for the joined whole capability.
#guard (match cf.reconstruct? 1 2 0 with
  | some c => c.writeAllowed 0 1
  | none => false)

-- Reused live ids and a non-whole share sum are refused.
#guard (Ctx.reconstruct? cf 1 2 1).isNone
#guard (Ctx.reconstruct? cs 3 4 5).isNone
