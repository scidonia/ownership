import OwnedStatic

open Owned

/-- The same handle used twice: the check must reject this definition. -/
def bad : Owned Nat :=
  let a := new #[0, 0]
  let _ := write a 0 1
  write a 1 2

#own_check bad
