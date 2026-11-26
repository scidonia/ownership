import Cap.Integrated
open Cap
open Cap.Integrated

-- An integrated sealed state's representation and constructor are private: the
-- field cannot be read and the structure cannot be manufactured outside the
-- module. This file must fail to elaborate.
example (s : Sealed) : State := s.s

example (s : State) (h : s.Inv) : Sealed := Sealed.mk s h
