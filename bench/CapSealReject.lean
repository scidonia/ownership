import Cap.Sealed
open Cap

-- Outside `Cap.Sealed`, a sealed world cannot be manufactured: its constructor
-- is private. This file must fail to elaborate.
example (w : World) : Sealed := Sealed.mk w
