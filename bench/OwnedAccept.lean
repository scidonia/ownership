import OwnedStatic

open Owned

/-- One binding, one transfer: accepted. -/
def good : Owned Nat :=
  let a := new #[0, 0]
  let a := write a 0 1
  write a 1 2

#own_check good
