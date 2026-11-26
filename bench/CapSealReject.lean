import Cap.Sealed
open Cap

-- Outside the integrated module, a sealed state cannot be manufactured: the
-- constructor is private there and the `Cap.Sealed` alias does not expose it.
example (s : Integrated.State) (h : s.Inv) : Sealed := Sealed.mk s h

-- Nor is there a world entry point: the old certified import is gone, so the
-- sealed boundary cannot be fed a `World`/`UCmd` state.
example : Sealed.importCertified = Sealed.importCertified := rfl
