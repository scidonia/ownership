import Cap.Sealed
open Cap

-- Outside `Cap.Sealed`, a sealed world cannot be manufactured: its constructor
-- is private.
example (w : World) (h : w.FullInv) : Sealed := Sealed.mk w h

-- Nor is there an arbitrary-world entry point: the old `ofRun` took a
-- caller-supplied world and an empty accepted run.
example (w : World) : Sealed := Sealed.ofRun w [] w (by rfl)
