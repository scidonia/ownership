import Cap.Sealed
open Cap

-- A sealed state's representation is private: its field cannot be read outside
-- the module. This file must fail to elaborate.
example (s : Sealed) : Integrated.State := s.s
