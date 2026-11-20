import Cap.Sealed
open Cap

-- A sealed world's representation is private: its field cannot be read outside
-- the module. This file must fail to elaborate.
example (s : Sealed) : World := s.w
